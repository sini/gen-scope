# Resolution primitives and named attribute constructors.
#
# Neron (2015) and van Antwerpen (2018) resolution semantics.
# Kiama-inspired vocabulary (Sloane et al., 2010) for attribute definitions.
#
# Key design: import edges are COMPUTED ATTRIBUTES (self.get id relations.imports),
# not structural fields. This allows dynamic import resolution.
#
# The relation NAME is not written down here. It comes from `lib/traversal-names.nix`, the one
# binding this module and the structural classifier both read: a relation this resolver traverses
# must be reserved as structural, or a warm evaluation may serve it from a prior graph and answer
# over a stale import relation without saying so. Two agreeing literals would make that a
# coincidence; one binding makes it a property.
{ prelude }:
let
  relations = import ./traversal-names.nix;

  # Shadow: merge two declaration sets, inner shadows outer (Neron §5 Def. 1).
  shadow = inner: outer: inner // prelude.filterAttrs (k: _: !(inner ? ${k})) outer;

  # Resolve with specificity ordering D < I < P (Neron Fig. 2).
  resolve =
    {
      local ? null,
      imported ? null,
      inherited ? null,
      localShadowsImport ? true,
      importShadowsParent ? true,
    }:
    if local != null && localShadowsImport then
      local
    else if imported != null && importShadowsParent then
      imported
    else if local != null then
      local
    else if imported != null then
      imported
    else
      inherited;

  # Generalized query combinator (van Antwerpen §2.1).
  # Import edges come from self.get id relations.imports (computed attribute).
  # _seen tracks visited scopes to prevent import self-resolution (Neron §2.4, rule X).
  query =
    {
      dataFilter,
      localShadowsImport ? true,
      importShadowsParent ? true,
      transitiveImports ? false,
      _seen ? { },
    }:
    self: id:
    let
      node = self.node id;
      local = dataFilter node;
      importIds = self.get id relations.imports;
      unseenImports = builtins.filter (iid: !(_seen ? ${iid})) importIds;
      collectFromImport =
        seen: importId:
        let
          v = dataFilter (self.node importId);
          direct = prelude.optional (v != null) v;
          transitive =
            if transitiveImports then
              let
                nextImports = self.get importId relations.imports;
                nextUnseen = builtins.filter (iid: !(seen ? ${iid})) nextImports;
                nextSeen = seen // {
                  ${importId} = true;
                };
              in
              prelude.concatMap (collectFromImport nextSeen) nextUnseen
            else
              [ ];
        in
        direct ++ transitive;
      imported =
        let
          results = prelude.concatMap (collectFromImport (_seen // { ${id} = true; })) unseenImports;
        in
        if results == [ ] then
          null
        else if builtins.isAttrs (builtins.head results) then
          prelude.foldl' (acc: v: shadow v acc) { } results
        else
          builtins.head results;
      inherited =
        if node.parent != null then
          query {
            inherit
              dataFilter
              localShadowsImport
              importShadowsParent
              transitiveImports
              ;
            _seen =
              _seen
              // builtins.listToAttrs (
                map (iid: {
                  name = iid;
                  value = true;
                }) importIds
              );
          } self node.parent
        else
          null;
    in
    resolve {
      inherit
        local
        imported
        inherited
        localShadowsImport
        importShadowsParent
        ;
    };

  # Return all reachable results without shadowing (Neron §2.3, rule R).
  queryAll =
    {
      dataFilter,
      transitiveImports ? false,
      _seen ? { },
    }:
    self: id:
    let
      node = self.node id;
      local = dataFilter node;
      importIds = self.get id relations.imports;
      unseenImports = builtins.filter (iid: !(_seen ? ${iid})) importIds;
      collectFromImportAll =
        seen: importId:
        let
          v = dataFilter (self.node importId);
          direct = prelude.optional (v != null) v;
          transitive =
            if transitiveImports then
              let
                nextImports = self.get importId relations.imports;
                nextUnseen = builtins.filter (iid: !(seen ? ${iid})) nextImports;
                nextSeen = seen // {
                  ${importId} = true;
                };
              in
              prelude.concatMap (collectFromImportAll nextSeen) nextUnseen
            else
              [ ];
        in
        direct ++ transitive;
      importResults = prelude.concatMap (collectFromImportAll (_seen // { ${id} = true; })) unseenImports;
      parentResults =
        if node.parent != null then
          queryAll {
            inherit dataFilter transitiveImports;
            _seen =
              _seen
              // builtins.listToAttrs (
                map (iid: {
                  name = iid;
                  value = true;
                }) importIds
              );
          } self node.parent
        else
          [ ];
    in
    (prelude.optional (local != null) local) ++ importResults ++ parentResults;

  # Reverse reference attribute — `neededBy` (Hedin & Magnusson 2003, inter-type
  # declarations): gather `dataFilter` over every node that IMPORTS `id` (the reverse of
  # the `includes`/imports relation). A node does not know its importers locally, so this
  # forces the full node set via `allNodes` (Tier 2, like `collect`). Gather-all, no
  # shadowing; DIRECT importers by default — set `transitive = true` to walk the
  # reverse-import closure. Dual of `queryAll` (which walks imports forward).
  #
  # ORDER — reverse-walk DISCOVERY order. The result is emitted in the order the reverse
  # walk reaches its contributors: a pre-order depth-first traversal of the reverse-import
  # relation rooted at `id`, in which a node's importers are enumerated in MATERIALIZATION
  # order (`self.allNodeIds` — root order, then pre-order through children; see eval.nix).
  # The duality is what fixes the choice. `queryAll`'s answer order is its traversal order,
  # taken from each node's DECLARED `imports` list; a dual whose order came instead from
  # the codepoint key order of the node set would not be the dual of a traversal-ordered
  # read, and the reverse relation carries no declared list of its own to walk. Attribute
  # grammars answer this the same way: a reverse reference attribute is a survey of the
  # tree, and its contributions combine in a traversal order of the tree (Hedin & Magnusson
  # 2003; Sloane 2010 §7 collection attributes).
  #
  # This library does NOT sort and does NOT deduplicate the answer. A node reachable along
  # two reverse paths contributes twice, because a reverse gather counts contributions. A
  # caller that needs a stable total order regardless of walk shape — or a set — sorts or
  # deduplicates at its own call site and says so there.
  #
  # Where the tree settles no order, the tie-break is `allNodeIds`' and is declared with it:
  # root and sibling ties break on `attrNames`, i.e. BYTEWISE CODEPOINT order, and a
  # `derived-children` node interleaves with its `children` siblings under the same rule.
  # That tie-break is a residue, not a law of attrsets — the algebraic graph layer carries a
  # declaration-ordered vertex list and `lib/build-nodes.nix` collapses it through
  # `listToAttrs`/`attrNames` before `eval` is handed `roots`. On a FLAT graph (every node a
  # root, no children) the walk therefore coincides with codepoint order; on a nested one it
  # does not, and subtree contiguity is what the reader sees.
  queryReverse =
    {
      dataFilter,
      transitive ? false,
      _seen ? { },
    }:
    self: id:
    let
      allIds = self.allNodeIds;
      importersOf =
        nid: builtins.filter (other: builtins.elem nid (self.get other relations.imports)) allIds;
      collectFrom =
        seen: importerId:
        let
          v = dataFilter (self.node importerId);
          direct = prelude.optional (v != null) v;
          trans =
            if transitive then
              let
                nextSeen = seen // {
                  ${importerId} = true;
                };
                nextUnseen = builtins.filter (i: !(nextSeen ? ${i})) (importersOf importerId);
              in
              prelude.concatMap (collectFrom nextSeen) nextUnseen
            else
              [ ];
        in
        direct ++ trans;
      directImporters = builtins.filter (i: !(_seen ? ${i})) (importersOf id);
    in
    prelude.concatMap (collectFrom (_seen // { ${id} = true; })) directImporters;

  # Ambiguity detection (van Antwerpen §2.3).
  ambiguous =
    args: self: id:
    builtins.length (queryAll args self id) > 1;

  # Convenience: resolve single visible declaration from a scope.
  visibleFrom =
    dataFilter: self: nodeId:
    query { inherit dataFilter; } self nodeId;

  # Inherited attribute: walks parent chain until resolve returns non-null.
  # _visited prevents cycles on malformed parent relations.
  inherit' =
    {
      resolve,
      _visited ? { },
    }:
    self: id:
    let
      node = self.node id;
      result = resolve node;
    in
    if _visited ? ${id} then
      throw "gen-scope: parent cycle detected at '${id}'"
    else if result != null then
      result
    else if node.parent == null then
      null
    else
      inherit' {
        inherit resolve;
        _visited = _visited // {
          ${id} = true;
        };
      } self node.parent;

  # Inherited accumulator: walks parent chain collecting ALL values.
  inheritAll =
    {
      extract,
      combine ? a: b: a ++ b,
      _visited ? { },
    }:
    self: id:
    let
      node = self.node id;
      local = extract node;
      localResults = if local != null then (if builtins.isList local then local else [ local ]) else [ ];
    in
    if _visited ? ${id} then
      localResults
    else if node.parent == null then
      localResults
    else
      let
        parentResults = inheritAll {
          inherit extract combine;
          _visited = _visited // {
            ${id} = true;
          };
        } self node.parent;
      in
      combine localResults parentResults;

  # Inherited SET accumulator: the set-discipline sibling of `inheritAll`. A node's
  # value = its own contribution ∪ every ancestor's, walking UP the P-edge parent chain,
  # deduplicated. Where `inheritAll` is an ORDERED-LIST discipline (`combine = ++`,
  # keeps duplicates and depends on traversal order), `inheritSet` is a SET discipline:
  # an idempotent union, so a value contributed by several ancestors appears once and
  # the accumulated set stays bounded by the DISTINCT contributions along a deep chain
  # (a control-fact set — e.g. suppressed-policy names — tested by membership, where
  # order and multiplicity carry no meaning). This is the idempotent-`combine` case the
  # collection-attribute note distinguishes (Sloane 2010 §7; Van Wyk 2010 fold
  # operators): a semilattice merge whose result is order-independent, in contrast to
  # the ordered-list `++`. Nearest-first order is retained for a deterministic
  # rendering, but membership is the semantics.
  #
  # Delegates the parent walk (and thus cycle-safety) to `inheritAll`, then folds out
  # duplicates by `eq` (default structural `==`, matching the optional-`eq` idiom of
  # `circular`/`subtypeOf`). Demand-driven: only the queried node's parent chain is
  # forced. Extract contract is `inheritAll`'s: `node -> [value] | value | null`.
  #
  # A typed inherited-attribute channel for a control fact: a consumer rides a
  # first-class `suppressedPolicies :: [Name]` attribute (self ∪ ancestors) rather than
  # smuggling the set as a reserved decls key through the generic context inheritance.
  inheritSet =
    {
      extract,
      eq ? (a: b: a == b),
      _visited ? { },
    }:
    self: id:
    let
      all = inheritAll { inherit extract _visited; } self id;
    in
    builtins.foldl' (acc: x: if builtins.any (y: eq y x) acc then acc else acc ++ [ x ]) [ ] all;

  # Parameterized attribute (Sloane 2010 §3, JastAdd).
  paramAttr =
    f: self: id: param:
    f self id param;

  # Circular attribute: iterate from initial value until fixed-point (Sloane 2010 §2.2).
  circular =
    {
      init,
      eq ? a: b: a == b,
      maxIter ? 100,
    }:
    f: self: id:
    let
      go =
        n: prev:
        let
          next = f self id prev;
        in
        if n >= maxIter then
          throw "gen-scope: circular attribute on '${id}' did not converge after ${toString maxIter} iterations"
        else if eq prev next then
          next
        else
          go (n + 1) next;
    in
    go 0 init;

  # Collection attribute combinator (Sloane 2010 §7).
  # Traversal uses COMPUTED attributes (self.get), not structural fields.
  collectionAttr =
    {
      traverse,
      extract,
      combine ? a: b: a ++ b,
      filter ? _: true,
    }:
    self: id:
    let
      targets =
        if builtins.isFunction traverse then
          traverse self id
        else if traverse == relations.imports then
          self.get id relations.imports
        else if traverse == "children" then
          builtins.attrNames (self.get id "children")
        else if traverse == "siblings" then
          let
            p = (self.node id).parent;
          in
          if p == null then
            [ ]
          else
            builtins.filter (cid: cid != id) (builtins.attrNames (self.get p "children"))
        else if traverse == "ancestors" then
          let
            go =
              visited: nid:
              if nid == null || visited ? ${nid} then
                [ ]
              else
                [ nid ] ++ go (visited // { ${nid} = true; }) (self.node nid).parent;
          in
          go { ${id} = true; } (self.node id).parent
        else if traverse == "neron" then
          let
            neronCollect =
              seen: nid:
              let
                node = self.node nid;
                selfSeen = seen // {
                  ${nid} = true;
                };
                importIds = self.get nid relations.imports;
                unseenImports = builtins.filter (iid: !(selfSeen ? ${iid})) importIds;
                newSeen =
                  selfSeen
                  // builtins.listToAttrs (
                    map (iid: {
                      name = iid;
                      value = true;
                    }) importIds
                  );
                parentContribs =
                  if node.parent != null && !(newSeen ? ${node.parent}) then
                    neronCollect newSeen node.parent
                  else
                    [ ];
              in
              [ nid ] ++ unseenImports ++ parentContribs;
          in
          neronCollect { } id
        else if prelude.hasPrefix "label:" traverse then
          self.get id "edges-${prelude.removePrefix "label:" traverse}"
        else
          throw "gen-scope: collectionAttr: unknown traverse '${traverse}'";
      filtered = builtins.filter (tid: filter (self.node tid)) targets;
      perTarget = map (
        tid:
        let
          r = extract self tid;
        in
        if r == null then
          [ ]
        else if builtins.isList r then
          r
        else
          [ r ]
      ) filtered;
    in
    builtins.foldl' combine [ ] perTarget;

  # Import-scoped collection: demand-driven (Neron §2.4, rule I).
  collectImports =
    extract: self: id:
    prelude.concatMap (importId: extract self importId) (self.get id relations.imports);

  # Global collection (WARNING: forces full tree via allNodes — Tier 2).
  collect =
    {
      filter ? _: true,
    }:
    extract: self:
    prelude.concatMap (
      id:
      let
        node = self.node id;
      in
      if filter node then extract self id else [ ]
    ) (builtins.attrNames self.allNodes);

  # Typed collection: filter nodes by type field.
  collectByType =
    type: extract: self:
    collect { filter = n: n.type == type; } extract self;

  # Follow a custom edge label from a node.
  followEdge =
    label: self: id:
    self.get id "edges-${label}";

  # Collect data from nodes reachable via a custom edge label.
  collectByLabel =
    label: extract: self: id:
    prelude.concatMap (targetId: extract self targetId) (followEdge label self id);

  # Structural subtyping (van Antwerpen §2.3).
  subtypeOf =
    {
      eq ?
        _k: _a: _b:
        true,
    }:
    self: idA: idB:
    let
      declsA = (self.node idA).decls;
      declsB = (self.node idB).decls;
    in
    builtins.all (k: declsB ? ${k} && eq k declsA.${k} declsB.${k}) (builtins.attrNames declsA);
in
{
  inherit
    shadow
    resolve
    query
    queryAll
    queryReverse
    ambiguous
    visibleFrom
    inherit'
    inheritAll
    inheritSet
    paramAttr
    circular
    collectionAttr
    collectImports
    collect
    collectByType
    followEdge
    collectByLabel
    subtypeOf
    ;
}
