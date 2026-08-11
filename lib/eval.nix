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
  structural = import ./structural.nix { inherit prelude; };
  interface = import ./interface.nix { inherit prelude; };

  eval =
    {
      roots,
      attributes,
      parseParent ? null,
      prior ? null,
      decision ? interface.coldDecision,
      provenance ? [ ],
    }:
    prelude.fix (
      self:
      let
        # The reuse vocabulary: this attribute set minus the structural partition. A structural
        # name is absent from it, so it contributes nothing to what may be served — there is
        # nothing for it to intersect with. The attribute set is one set for every node, so the
        # projection is node-independent here; the per-node signature is the interface's,
        # because a substrate whose attribute set varies by node must still answer per node.
        resolutionalNamesAll = structural.resolutionalNames (builtins.attrNames attributes);
        resolutionalAt = _nodeId: resolutionalNamesAll;
        structuralNamesAll = builtins.filter structural.structural (builtins.attrNames attributes);

        # served nodeId = reusable nodeId ∩ resolutional nodeId. A total function, not a check
        # that can fail.
        servedAt =
          nodeId: builtins.filter (a: builtins.elem a resolutionalNamesAll) (decision.reusable nodeId);

        servePrior =
          nodeId: attrName:
          if prior == null then
            throw "gen-scope: the decision reuses '${attrName}' on '${nodeId}' but no prior evaluation was supplied"
          else
            prior.get nodeId attrName;

        # One per-attribute evaluator, shared by rootEval + wrapChild._eval.
        #
        # THE STRUCTURAL BRANCH FIRES FIRST AND NEVER CONSULTS THE DECISION — by branch order,
        # not by a check. Structure is always recomputed, so dirty descendants stay reachable
        # and a labelled reachability relation is never read stale. That the branch tests the
        # PARTITION rather than two literal names is what extends the law from the child
        # attributes to the whole `edges-*` family and to `includes`.
        #
        # THE COST OF THAT, ON THE RECORD: edge sets are never reused, so a warm evaluation
        # pays edge-set recomputation. That is a cost fact, not a correctness fact, and it is
        # taken deliberately — an edge set IS the labelled reachability relation, and the
        # reason structure is always recomputed applies to it exactly. If the recomputation
        # proves dominant the answer is to make the structural recompute cheaper, never to
        # serve structure from a prior evaluation.
        #
        # The second branch consults the SERVED INTERSECTION, not the decision's raw list. The
        # structural branch has already fired, so the two agree at this call site — and that is
        # exactly why the intersection is written here rather than assumed: an agreement that
        # holds because of a neighbouring branch is a fact about today's branch order, and the
        # clause this implements is about what may be served, not about which branch ran. Both
        # halves are real; neither is decoration for the other.
        evalAttr =
          nodeId: attrName: fn:
          if structural.structural attrName then
            let
              raw = fn self nodeId;
            in
            if structural.childBearing attrName then builtins.mapAttrs (_: wrapChild) raw else raw
          else if decision.isClean nodeId && builtins.elem attrName (servedAt nodeId) then
            servePrior nodeId attrName
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

        # The materialization walk itself, before it is collapsed into an attrset. Both
        # `allNodes` and `allNodeIds` are projections of this ONE list, so a consumer that
        # wants the node set AND its order pays for a single walk.
        walkEntries = prelude.concatMap self._walkFrom (builtins.attrNames roots);
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
        # An attrset is a SET: `attrNames` on it answers in bytewise codepoint order, and the
        # order the walk found the nodes in is not recoverable from this value. Consumers
        # that need that order read `allNodeIds`.
        allNodes = prelude.listToAttrs walkEntries;

        # The SAME node set as `allNodes`, as an ORDERED list of ids in MATERIALIZATION
        # order: root order, then pre-order depth-first through `children` /
        # `derived-children`, so a subtree is contiguous and a parent precedes its
        # descendants. This is the survey order an attribute-grammar collection or reverse
        # reference attribute is defined over (Hedin & Magnusson 2003 inter-type
        # declarations; Sloane 2010 §7 collection attributes) — contributions combine in a
        # traversal order of the tree, not in a codepoint order of node names.
        #
        # Two tie-breaks, declared because a declared order is the whole point:
        #
        # 1. Root and sibling ties break on `attrNames`, which is BYTEWISE CODEPOINT order,
        #    not dictionary order — `attrNames { z; A; a; _b; "1"; }` is
        #    `[ "1" "A" "_b" "a" "z" ]`, uppercase before underscore before lowercase. This
        #    is NOT because an attrset "carries no order". The algebraic graph layer carries
        #    a declaration-ordered vertex LIST (`lib/graph.nix`, where `overlay` and
        #    `connect` concatenate), and `lib/build-nodes.nix` collapses that list through
        #    `listToAttrs` and back out through `attrNames` — the same construction this
        #    walk exists to stop doing — so `eval` receives `roots` already set-shaped and
        #    the declared order is gone before anything here runs. The codepoint tie-break
        #    is that collapse's residue. Recovering the declared order is a change to the
        #    constructor, not to this walk.
        #
        # 2. A `derived-children` node INTERLEAVES with its `children` siblings rather than
        #    following them: `_walkFrom` descends `children // derived` as ONE attrset, so a
        #    derived id sorts into the sibling run under the same codepoint rule and nothing
        #    in this list marks it as derived.
        #
        # Repeats are dropped FIRST-OCCURRENCE-WINS, the same rule `listToAttrs` applies to
        # `allNodes`, so `allNodeIds` is exactly `attrNames allNodes` as a set. A node
        # reached both as a root and as another root's child is common (`buildNodes` makes
        # every vertex a root), so the walk really does repeat. The dedup is index-based —
        # one `listToAttrs` recording first positions, one pass reading them back — because
        # a fold carrying a `seen` attrset copies that attrset per node (quadratic) and
        # recurses once per node (Nix's call-depth ceiling), and this is an O(n) surface.
        allNodeIds =
          let
            names = map (e: e.name) walkEntries;
            n = builtins.length names;
            firstAt = prelude.listToAttrs (
              prelude.genList (i: {
                name = builtins.elemAt names i;
                value = i;
              }) n
            );
          in
          prelude.concatMap (
            i:
            let
              nodeId = builtins.elemAt names i;
            in
            prelude.optional (firstAt.${nodeId} == i) nodeId
          ) (prelude.genList (i: i) n);

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

        # --- The plane interface ---

        # What an incremental plane reads this evaluation through. It is handed the FACADE,
        # never `self`: the materialization surfaces, the node accessor and the combinators are
        # absent from the RECORD, so a read outside those three names cannot be written against
        # this value at all.
        #
        # ★ That closes the KEY SET, not reachability. `get id "children"` answers node records
        # carrying `decls` / `parent` and the co-located `_eval` cache, so a caller holding one
        # can evaluate through `_eval` without passing through `get`; and `get` takes any
        # string, so a dynamically constructed name is issuable whether or not the combinators
        # travel. Measured, and pinned by the facade cells. What survives that residual is the
        # property reuse rests on — the always-recompute branch below fires before the decision
        # is consulted, so no structural value is ever served from a prior evaluation.
        facade = interface.mkFacade {
          get = self.get;
          nodeIds = self.allNodeIds;
          resolutional = resolutionalAt;
        };

        # The reuse vocabulary, per node, and the subset of a decision's request that is
        # actually served. Both are the same projection the facade carries, exposed so the
        # intersection is inspectable rather than only inferable from behaviour.
        resolutional = resolutionalAt;
        served = servedAt;

        # THE STRUCTURAL EDGE SET THE SUBSTRATE CONSTRUCTED — the children /
        # derived-children / edges-* / includes relation, materialized by the always-recompute
        # branch, readable WITHOUT forcing any resolutional attribute. Reads derive from it
        # statically. It is derived rather than declared: the substrate constructed these
        # edges, so no impossibility argument is owed for them.
        structuralEdges = id: prelude.genAttrs structuralNamesAll (name: self.get id name);

        # The debug-mode validator, as a value. Nothing in the production path forces it, so it
        # alters no production result and is not a rule the plane must obey; forcing it reports
        # every attribute a decision named that this node's vocabulary does not contain.
        decisionFindings = interface.decisionFindings {
          inherit decision;
          resolutional = resolutionalAt;
          nodeIds = self.allNodeIds;
        };

        # PROVENANCE RIDES THE RESULT. Plain data the caller receives with its answer, never a
        # side channel and never debug-only: a print goes to stderr, which the evaluation cache
        # swallows after the first run, and a debug-only field is invisible in ordinary use.
        # A field that IS the result survives caching because it is what was cached.
        #
        # This library carries the field and never invents a record for it. The facts that get
        # stamped — an input past a benchmark-verified bound, and the bound itself — are the
        # engine's, derived from a cost curve measured there; the substrate holds no threshold
        # and makes no comparison. Carried, so no layer between the engine and the caller can
        # silently drop it.
        inherit provenance;
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
      mkSelf =
        visited: traceList:
        let
          # THE TRACE IS A RESULT, NOT A THROW FRAGMENT. `getTraced` answers with the read path
          # AND the value, and the path is readable WITHOUT forcing the value — so the trace is
          # available in exactly the case where it used to be reachable only by parsing a throw
          # message. It is the dynamic read recording, run against the same names the static
          # structural derivation is defined over, and it stays in the debug evaluator because
          # the fresh-self-per-get that records it is what defeats memoization.
          #
          # WHAT IT IS AND IS NOT: the path from the root read to this one. The union of reads
          # across sibling branches is not recoverable here — the thread runs downward into the
          # consumer's attribute functions, and their results are values, so nothing carries a
          # read set back up.
          getTraced =
            id: attrName:
            let
              traceEntry = "${id}.${attrName}";
              path = traceList ++ [ traceEntry ];
            in
            {
              trace = path;
              value =
                if !(attributes ? ${attrName}) then
                  throw "gen-scope: unknown attribute '${attrName}' on node '${id}'"
                else if visited ? ${traceEntry} then
                  throw "gen-scope: cycle detected: ${builtins.concatStringsSep " -> " path}"
                else
                  attributes.${attrName} (mkSelf (visited // { ${traceEntry} = true; }) path) id;
            };
        in
        {
          inherit getTraced;

          # The read path this accessor was reached along, as a value.
          trace = traceList;

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

          get = id: attrName: (getTraced id attrName).value;

          allNodes = throw "gen-scope: evalDebug does not support allNodes (use eval for materialization)";

          allNodeIds = throw "gen-scope: evalDebug does not support allNodeIds (use eval for materialization)";
        };
    in
    mkSelf { } [ ];

  # Reuse-driven evaluator. Same interface as `eval` with the plane's two arguments made
  # MANDATORY: an evaluation that means to reuse says which prior it reuses from and which
  # decision authorises it, rather than inheriting a default that decides for it. A thin
  # wrapper over `eval` — one code path, whose cold case is the same path under a decision
  # saying nothing is clean.
  #
  # THE PRIOR IS AN ACCESSOR, NOT A RESULT MAP. The plane is handed the prior evaluation to
  # read, never a snapshot to hold: a projection is something the EVALUATOR performs on demand
  # from the accessor, not an artefact the plane constructs and carries. The accessor is live
  # inside the same evaluation — this reuse is INTRA-EVALUATION, over the override cone and
  # across targets composed within one evaluation. Nothing here persists from one invocation of
  # the evaluator to the next, and nothing here may claim to.
  # (Informed by Acar's self-adjusting computation: reusing clean prior results.)
  evalWarm =
    {
      roots,
      attributes,
      parseParent ? null,
      prior,
      decision,
      provenance ? [ ],
    }:
    eval {
      inherit
        roots
        attributes
        parseParent
        prior
        decision
        provenance
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
