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
#
# The EDGE NAMESPACE is not written down here either, and the argument runs the other way round.
# Labelled edges are an OPEN family (Neron et al. 2015, Fig. 2), so the classifier reserves them by
# a PREFIX predicate rather than by a list — and this module is what CONSTRUCTS the names that
# predicate decides about, at `followEdge` and at `collectionAttr`'s `label:` traversal. The prefix
# is a joint fact of the two modules, so it is taken from the one that owns and publishes it. A
# classifier reserving one prefix while the resolver builds another fails exactly as a drifted
# relation name does: the constructed name falls outside the reserved namespace, is classified
# resolutional, and is served from a prior — a complete, well-typed answer over a stale edge set,
# with nothing in the result saying so.
#
# WHAT THAT DOES NOT CLOSE, because the wide reading of it would be false: it makes the two
# spellings one for the names THIS module builds, and for no others. A caller assembling the name
# itself still escapes, since a predicate over attribute names has no access to a caller's
# literals. That residual belongs to `structural`'s stated domain and is named at `interface.nix`'s
# facade note; it is not closed here.
{ prelude }:
let
  relations = import ./traversal-names.nix;

  # The reserved structural namespace, read from the classifier that owns and publishes it rather
  # than re-spelled — the prefix below and the prefix the partition tests are one value.
  structural = import ./structural.nix { inherit prelude; };

  # The applicability approximation the kind registry also decides its `resolve` with, taken from
  # the one binding rather than re-approximated here.
  callable = import ./callable.nix;

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

  # Reverse reference attribute — `neededBy`, and this library's OWN dual, claimed from no
  # paper: gather `dataFilter` over every node that IMPORTS `id` (the reverse of
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
  # read, and the reverse relation carries no declared list of its own to walk. A reverse
  # reference attribute is a survey of the tree, and its contributions combine in a
  # traversal order of the tree.
  #
  # THE CITATION THIS COMMENT USED TO CARRY WAS WRONG TWICE OVER, so it is gone rather than
  # softened. It read "Hedin & Magnusson 2003, inter-type declarations" for the construct
  # and "Hedin & Magnusson 2003; Sloane 2010 §7 collection attributes" for the order.
  # Measured at the primaries: `inter-type` occurs 0 times in Hedin & Magnusson (live
  # controls in the same run: `aspect` 80, `attribute` 93) — their word is `introduction`,
  # credited to AspectJ, and an introduction adds a member to a class, which is not a
  # reverse query; `contribution` and `traversal order` are likewise 0 there; and Sloane §7
  # is Conclusion and Future Work, whose whole content on the subject is "we are adding
  # collection attributes". Hedin 2000, the reference-attribute paper gen-scope does
  # implement, carries no reverse direction either (`reverse`/`inverse`/`backward` 0 against
  # `reference attribute` 47). The duality argument above needs none of them.
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

  # ── THE CIRCULAR ATTRIBUTE, AND THE CARRIER ITS SOUNDNESS RESTS ON ──
  #
  # THEORY. A circular attribute's value is the least fixed point of its equation, and that is
  # well defined only under conditions on the value domain: "Circular attributes are well-defined
  # as the least fixed-point solution to their equations, IF their semantic functions are monotonic
  # and yield values over a lattice of bounded height" (Söderberg & Hedin 2013 §2.4, printed 305),
  # restated at §4.1, printed 311, with the third term explicit — "a lattice of bounded height, that
  # the semantic function is monotonic, and that a BOTTOM VALUE is provided as the starting point of
  # the fixed-point iteration". Those three terms are exactly what `carrier` declares. The condition
  # is Söderberg's; the SIGNATURE this combinator used to carry, a bare `init` with no stated
  # relation to any order, came from Kiama's API table (Sloane 2010, printed 211), which states no
  # soundness condition and never claimed to.
  #
  # NONE OF THE THREE IS DERIVABLE FROM `f`. The step arrives as an opaque caller-supplied function
  # over an open vocabulary, so nothing here can recover an order the caller did not state.
  # Declaring them is the only honest option, and the declaration is REQUIRED and TOTAL: absence is
  # refused BY NAME rather than defaulted, because a default here would be this library choosing a
  # lattice for a value space it has never seen. The formal carries a `null` sentinel whose only
  # job is to let the arm underneath name that refusal — written as a formal with no default, an
  # omitted `carrier` is refused by NIX at application, a termination this library never names and
  # `tryEval` does not contain.
  #
  # THE ITERATION BOUND IS DERIVED, AND IT IS A THEOREM RATHER THAN A CAP. On a lattice of declared
  # height `h`, at most `h` steps can strictly ascend from the bottom and one further step observes
  # that none did, so `h + 1` step evaluations exhaust the ascent by Noetherian induction on ℕ.
  # That is a fact about the fixpoint, not a budget on what a caller may express — the distinction
  # `least-model.nix` draws for its `|atoms| + 1` and `cascade.nix` for its `maxDepth + 1`. This is
  # the third site and the last one that lacked it; what it replaces was a chosen `maxIter`, which
  # is the other thing.
  #
  # EQUALITY IS ANTISYMMETRY AT THE DECLARED ORDER, so there is no separate equality knob to supply
  # and no way to supply one. A convergence test unrelated to the ascent test is what lets a
  # fixed-point combinator return a value its own step does not fix: the answer is taken the moment
  # that test fires, whether or not the iteration reached a fixed point, and the free `eq` argument
  # this replaces made precisely that expressible.
  #
  # A QUOTIENT CARRIER IS ADMISSIBLE, and it is how a coarsened convergence keeps its technique.
  # `leq` may order a QUOTIENT of the value space rather than the raw values — key-set inclusion, a
  # projection's order — because the theorem's hypothesis constrains the DECLARED carrier and never
  # requires it be the raw value's equality. What converges is then the CLASS: raw values may still
  # churn inside one, and a consumer needing finer stability asks for a finer carrier. The price a
  # quotient pays is stating its height, which is where an unbounded coarsening is refused by name
  # instead of running to a cap. This is the reason both directions of `leq` are applied rather than
  # one `leq` and a structural `==`: a raw equality would never fire on a converged class, and the
  # two applications per iteration are what the quotient costs.
  #
  # WHAT IS NOT CHECKED, stated because a soundness gate that overclaims is worse than none: that
  # `leq` IS a partial order, and that `height` is large enough for the carrier it names. Both
  # quantify over the whole value set and no terminating predicate decides either. There is partial
  # cover in one direction only — a `leq` that holds too often admits a non-ascent, which then fails
  # to converge inside the declared height, so the height refusal is the ascent check's own control;
  # a `leq` that holds too rarely refuses a sound program, and nothing looks for those.

  # The reason a carrier is not one, or null. Total on any value: each arm establishes what the next
  # one reads. The reason NEVER RENDERS the carrier — an order is a function, and rendering a
  # function is itself an abort no caller can catch, which would answer an uncatchable termination
  # with another one while claiming to diagnose it.
  carrierDefect =
    c:
    if c == null then
      "declares no `carrier` — a circular attribute is well defined only over one, and its three terms are a bottom, an order and a bounded height (Söderberg & Hedin 2013 §4.1)"
    else if !builtins.isAttrs c then
      "declares a `carrier` that is a ${builtins.typeOf c} rather than a { bottom, leq, height } record"
    else if !(c ? bottom) then
      "declares a `carrier` with no `bottom` (the starting point of the fixed-point iteration)"
    else if !(c ? leq) then
      "declares a `carrier` with no `leq` (the order the step is required to ascend)"
    else if !(callable c.leq) then
      "declares a `carrier` whose `leq` cannot be applied (it is a ${builtins.typeOf c.leq})"
    else if !(c ? height) then
      "declares a `carrier` with no `height` (the lattice's bounded height, from which the iteration bound is derived)"
    else if !builtins.isInt c.height then
      "declares a `carrier` whose `height` is a ${builtins.typeOf c.height} rather than an integer"
    else if c.height < 0 then
      "declares a `carrier` whose `height` is ${toString c.height}, and a lattice has no negative height"
    else
      null;

  circular =
    {
      carrier ? null,
    }:
    f: self: id:
    let
      defect = carrierDefect carrier;
      inherit (carrier) leq height;
      go =
        n: prev:
        let
          next = f self id prev;
          ascends = leq prev next;
        in
        # The fixed point is the step whose result the declared order cannot tell from its input.
        if ascends && leq next prev then
          next
        else if !ascends then
          throw "gen-scope: circular attribute on '${id}' took a step its declared order does not ascend, at iteration ${toString n} — the step is not monotone on the declared carrier, so the iteration is not a Kleene ascent and no least fixed point is being computed"
        else if n >= height then
          # The step count is the one this run ACTUALLY took, never `height + 1` restated. A message
          # that recites the declaration says the same thing whatever the loop did, so it cannot
          # witness the bound it claims to derive — measured under a deliberately loosened bound, the
          # text was byte-identical while the loop ran fifty steps longer. Written this way the two
          # numbers agree only when the derivation holds, so a cell asserting the text asserts it.
          throw
            "gen-scope: circular attribute on '${id}' is still ascending after ${toString (n + 1)} steps, so the declared height of ${toString height} is exceeded — the bound is derived from the declaration, and what this refutes is the declaration rather than an iteration budget"
        else
          go (n + 1) next;
    in
    if defect != null then
      throw "gen-scope: circular attribute on '${id}' ${defect}"
    else
      go 0 carrier.bottom;

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
          self.get id (structural.edgePrefix + prelude.removePrefix "label:" traverse)
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
    self.get id (structural.edgePrefix + label);

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
