# HOAG evaluator: demand-driven with co-located _eval memoization.
#
# Nix's native lazy evaluation provides scheduling, memoization, and cycle
# detection (Mokhov et al., 2018). Every attribute evaluates exactly once per
# node — including on dynamically synthesized nodes (Vogt et al., 1989).
#
# The key insight: Nix attrset VALUES are lazy but KEYS are eager. The only way
# to get O(1) attribute access is an attrset entry. We co-locate the memoization
# cache (_eval) ON each node when it is materialized by its parent's `children`
# or `derived-children` attribute.
{ prelude }:
let
  eval =
    {
      roots,
      attributes,
      parseParent ? null,
      priorResults ? { },
      isClean ? (_: false),
    }:
    prelude.fix (
      self:
      let
        # One per-attribute evaluator, shared by rootEval + wrapChild._eval.
        # children/derived-children always recompute the structure (descendant
        # _eval caches are built by recursing through wrapChild). A clean node's
        # leaf attr present in priorResults is served without forcing fn (warm,
        # relocatable); otherwise cold demand. With the defaults (isClean = _: false)
        # the warm branch never fires, so eval stays byte-identical.
        evalAttr =
          nodeId: attrName: fn:
          if attrName == "children" || attrName == "derived-children" then
            let
              raw = fn self nodeId;
            in
            builtins.mapAttrs (_: wrapChild) raw
          else if isClean nodeId && (priorResults.${nodeId} or { }) ? ${attrName} then
            priorResults.${nodeId}.${attrName}
          else
            fn self nodeId;
        wrapChild =
          childNode:
          childNode
          // {
            _eval = builtins.mapAttrs (attrName: fn: evalAttr childNode.id attrName fn) attributes;
          };
        rootEval = prelude.mapAttrs (
          id: _: builtins.mapAttrs (attrName: fn: evalAttr id attrName fn) attributes
        ) roots;

        # Resolve a node by ID.
        # Roots: direct lookup. Non-roots: via parseParent or generic walk.
        resolveNode =
          id:
          if roots ? ${id} then
            roots.${id}
          else if parseParent != null then
            let
              parentId = parseParent id;
            in
            if parentId == null then
              genericResolve id
            else
              let
                children = self.get parentId "children";
                derived = if attributes ? "derived-children" then self.get parentId "derived-children" else { };
                all = children // derived;
              in
              if all ? ${id} then
                all.${id}
              else
                throw "gen-scope: node '${id}' not reachable (parent: ${parentId})"
          else
            genericResolve id;

        # Fallback resolution: walk from all roots through children.
        # O(n) worst case — use parseParent for production scale.
        genericResolve =
          id:
          let
            walkChildren =
              parentId:
              let
                children = self.get parentId "children";
                derived = if attributes ? "derived-children" then self.get parentId "derived-children" else { };
                all = children // derived;
              in
              if all ? ${id} then
                all.${id}
              else
                prelude.foldl' (acc: childId: if acc != null then acc else walkChildren childId) null (
                  builtins.attrNames all
                );
            found = prelude.foldl' (acc: rootId: if acc != null then acc else walkChildren rootId) null (
              builtins.attrNames roots
            );
          in
          if found != null then found else throw "gen-scope: node '${id}' not reachable from roots";
      in
      {
        node = resolveNode;

        get =
          id: attrName:
          builtins.addErrorContext "evaluating '${attrName}' on '${id}'" (
            if !(attributes ? ${attrName}) then
              throw "gen-scope: unknown attribute '${attrName}' on node '${id}'"
            else if rootEval ? ${id} then
              rootEval.${id}.${attrName}
            else
              let
                n = self.node id;
              in
              if n ? _eval then n._eval.${attrName} else attributes.${attrName} self id # fallback (shouldn't happen)
          );

        # --- Tier 2: Materialization (forces evaluation, memoized) ---

        # Internal: walk children/derived-children from a node.
        _walkFrom =
          id:
          let
            children = if attributes ? "children" then self.get id "children" else { };
            derived = if attributes ? "derived-children" then self.get id "derived-children" else { };
            all = children // derived;
          in
          [
            {
              name = id;
              value = self.node id;
            }
          ]
          ++ prelude.concatMap self._walkFrom (builtins.attrNames all);

        # Full tree materialization. Forces all children attributes recursively.
        # O(n) — each node computed once. Use for gen-graph global ops, diagrams.
        allNodes = prelude.listToAttrs (prelude.concatMap self._walkFrom (builtins.attrNames roots));

        # Selective materialization: forces only nodes matching a predicate.
        # Predicate receives structural node data. Descends into ALL children
        # but only INCLUDES matching nodes in the result.
        # O(n) walk but result size ≤ matching nodes.
        allNodesWhere =
          pred:
          let
            walkFrom =
              id:
              let
                node = self.node id;
                children = if attributes ? "children" then self.get id "children" else { };
                derived = if attributes ? "derived-children" then self.get id "derived-children" else { };
                all = children // derived;
                childResults = prelude.concatMap walkFrom (builtins.attrNames all);
              in
              (
                if pred node then
                  [
                    {
                      name = id;
                      value = node;
                    }
                  ]
                else
                  [ ]
              )
              ++ childResults;
          in
          prelude.listToAttrs (prelude.concatMap walkFrom (builtins.attrNames roots));

        # Subtree materialization: forces only the subtree rooted at a given node.
        # O(subtree size). Does not touch nodes outside the subtree.
        subtreeOf = rootId: prelude.listToAttrs (self._walkFrom rootId);

        # Type-targeted materialization: all nodes of a given type.
        # Walks full tree but only includes matching types.
        # O(n) walk, result size = nodes of that type.
        nodesOfType = type: self.allNodesWhere (node: node.type == type);
      }
    );

  # Diagnostic variant with shadow-stack cycle tracing.
  #
  # Uses attrset-based visited (O(1) cycle check) + parallel list for ordered
  # trace output. Cycles produce: "gen-scope: cycle: a.x -> b.x -> a.x"
  #
  # Trade-off: defeats Nix's native memoization — every get call creates a
  # new self with updated visited/traceList. Use eval for production.
  evalDebug =
    {
      roots,
      attributes,
      parseParent ? null,
    }:
    let
      mkSelf = visited: traceList: {
        node =
          id:
          if roots ? ${id} then
            roots.${id}
          else if parseParent != null then
            let
              parentId = parseParent id;
              s = mkSelf visited traceList;
              children = if parentId != null then s.get parentId "children" else { };
              derived =
                if parentId != null && attributes ? "derived-children" then
                  s.get parentId "derived-children"
                else
                  { };
            in
            (children // derived).${id} or (throw "gen-scope: node '${id}' not reachable")
          else
            throw "gen-scope: evalDebug requires parseParent for non-root nodes";

        get =
          id: attrName:
          let
            traceEntry = "${id}.${attrName}";
          in
          if !(attributes ? ${attrName}) then
            throw "gen-scope: unknown attribute '${attrName}' on node '${id}'"
          else if visited ? ${traceEntry} then
            throw "gen-scope: cycle detected: ${builtins.concatStringsSep " -> " (traceList ++ [ traceEntry ])}"
          else
            attributes.${attrName} (mkSelf (visited // { ${traceEntry} = true; }) (
              traceList ++ [ traceEntry ]
            )) id;

        allNodes = throw "gen-scope: evalDebug does not support allNodes (use eval for materialization)";
      };
    in
    mkSelf { } [ ];

  # Relocatable warm-cache evaluator. Same interface as `eval`; a clean node's
  # leaf attr present in priorResults is served without forcing its compute fn,
  # while children/derived-children are never warm-served (structure always
  # recomputed, so dirty descendants stay reachable). Thin wrapper over `eval` —
  # a single code path, with `eval`'s defaults being the warm-off case.
  # (Informed by Acar's self-adjusting computation: reusing clean prior results.)
  evalWarm =
    {
      roots,
      attributes,
      parseParent ? null,
      priorResults,
      isClean,
    }:
    eval {
      inherit
        roots
        attributes
        parseParent
        priorResults
        isClean
        ;
    };

  # First-class inspectable projection of the consumer's declared read-edges. Pure,
  # zero memo cost (never runs through `get`). The dynamic read-set — the attributes
  # a node actually self.get's — is only recoverable via evalDebug's fresh-self-per-get,
  # which defeats the memo; there is no pure, memo-preserving way to capture it, so the
  # declared edges are the inspectable contract. (Acar's self-adjusting computation:
  # the read edges of a dynamic dependence graph.)
  recordedDeps = { declaredEdges }: id: declaredEdges id;
in
{
  inherit
    eval
    evalDebug
    evalWarm
    recordedDeps
    ;
}
