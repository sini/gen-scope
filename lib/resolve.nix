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
  # The answer is a SINGLE declaration. An import set contributed by more than one DISTINCT node is
  # an ambiguity (Neron §2.2, Duplicate Declarations) and refuses by name rather than being folded
  # together or chosen from by traversal order. Refusing is this library's single-answer contract,
  # not Neron's rule — the calculus deliberately identifies ambiguous resolutions rather than
  # requiring their absence (§2.2), and `queryAll` is that identify-all reading (Fig. 3 rule R).
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
          # Each candidate travels with the id of the node whose `dataFilter` produced it. Neron's
          # judgements conclude at a declaration OCCURRENCE (Fig. 3, `x^D_j`) and occurrence identity
          # is positional — §2.2, "all occurrences b_i denote the same name b at different positions"
          # — so the contributing node is the identity the predicate below is over. The recursion
          # needs no help: each recursive call knows its own `importId`, so a transitively-reached
          # candidate is attributed to the node that DECLARED it, never to the direct import it was
          # reached through.
          direct = prelude.optional (v != null) {
            node = importId;
            value = v;
          };
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
          contributions = prelude.concatMap (collectFromImport (_seen // { ${id} = true; })) unseenImports;
          contributors = prelude.unique (map (c: c.node) contributions);
        in
        # AMBIGUITY IS MORE THAN ONE DISTINCT DECLARATION OCCURRENCE, NOT MORE THAN ONE DERIVATION.
        # A node reached along several import routes — a repeated edge, a diamond — is ONE
        # declaration reached several ways, and the seen-imports machinery exists to make those
        # routes terminate (Neron §2.4) rather than to multiply the answer. Two distinct declaring
        # nodes are §2.2's Duplicate Declarations, and those refuse.
        #
        # Distinctness is deliberately NOT value equality. Comparing candidate values would force
        # them deeply, where the emptiness test below already forces each to WHNF and no further;
        # the ids cost nothing, being `importIds` the filters above have forced already. Value
        # equality would also refuse two nodes carrying the same function, which Nix compares as
        # unequal without erroring.
        if contributions == [ ] then
          null
        else if builtins.length contributors > 1 then
          throw "gen-scope: node '${id}' imports more than one declaration of the queried datum, from ${builtins.toJSON contributors}. That is an AMBIGUITY in the sense of Neron et al. 2015 (Fig. 3 rule (V); §2.2 Duplicate Declarations) — two declaration occurrences for one read. This query answers with a single declaration or REFUSES; it does not choose among them, and it does not fold them together. Declare the datum on '${id}' itself (a local declaration shadows imports at the default `localShadowsImport = true`), drop one of the competing imports, or read the whole set with `queryAll`, which identifies ALL the resolutions without shadowing (Neron rule R, and §2.2's own reading) and leaves the choice at the call site."
        else
          # One distinct contributor means every candidate carries the same value — `dataFilter` is a
          # pure function of the node — so this head is a projection out of a singleton equivalence
          # class, not a tie-break among rivals.
          (builtins.head contributions).value;
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
  # SIBLING ties break on `attrNames`, i.e. BYTEWISE CODEPOINT order, and a `derived-children`
  # node interleaves with its `children` siblings under the same rule. That tie-break is a
  # residue, not a law of attrsets — `childRecordsOf` merges the two child halves into ONE
  # attrset and the walk descends its `attrNames`. ROOTS are not tie-broken at all: `eval`
  # enters the walk at `scope.nodeOrder`, the declared vertex order `buildRoots` returns beside
  # the node set, so the top level answers in DECLARATION order. On a FLAT graph (every node a
  # root, no children) the walk is therefore the declared order and NOT the codepoint key order
  # `attrNames self.allNodes` gives; on a nested one the sibling residue shows inside each
  # subtree, and subtree contiguity is what the reader sees.
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

  # Parameterized attribute: a bare eta-expansion, NOT a per-parameter cache. Applying `f self id`
  # yields the closure `param: f self id param`, and that closure is the whole of what the
  # co-located `_eval`/`rootEval` cache (`lib/eval.nix`) memoizes — once per (node, attrName), same
  # as any other attribute. Applying the closure to a `param` is an ordinary Nix function call,
  # which Nix never memoizes, so every application recomputes the body: two demands for the SAME
  # (node, attrName, param) run `f` twice. Measured with a `builtins.trace` in `f`'s body, fired on
  # every application including a repeated identical one, against a control (a plain,
  # non-parameterized attribute read twice through the same public surface) that traces once.
  #
  # Sloane 2010 §3 and JastAdd are where a parameterized attribute IS cached per parameter — a memo
  # table keyed by the argument, so a repeated call with an already-seen argument is served rather
  # than recomputed. That per-parameter cache is what this function does not implement; the
  # citation names the design being fallen short of, not the one realized here. Closing that gap —
  # keying the co-located cache on `param` as well as on `(node, attrName)` — is open work.
  paramAttr =
    f: self: id: param:
    f self id param;

  # ── THE CIRCULAR ATTRIBUTE — A KIND-TAGGED DECLARATION, EVALUATED AT THE EVALUATOR ──
  #
  # THEORY. A circular attribute's value is the least fixed point of its equation, and that is
  # well defined only under conditions on the value domain: "Circular attributes are well-defined
  # as the least fixed-point solution to their equations, IF their semantic functions are monotonic
  # and yield values over a lattice of bounded height" (Söderberg & Hedin 2013 §2.4, printed 305),
  # restated at §4.1, printed 311, with the third term explicit — "a lattice of bounded height, that
  # the semantic function is monotonic, and that a BOTTOM VALUE is provided as the starting point of
  # the fixed-point iteration". Those terms are what `carrier` declares — plus a fourth, `quotient`,
  # which states whether `leq` orders a QUOTIENT of the value space rather than the raw values
  # (key-set inclusion, a projection's order). A quotient carrier is admissible per instance — what
  # converges is the CLASS, and the price a coarsening pays is stating its height — but it cannot
  # be a simultaneous member of a shared round, whose convergence needs antisymmetry; the term is
  # REQUIRED and TOTAL because an absent declaration would decide that soundness question silently.
  #
  # NONE OF THE TERMS IS DERIVABLE FROM `f`. The step arrives as an opaque caller-supplied function
  # over an open vocabulary, so nothing here can recover an order the caller did not state.
  # Declaring them is the only honest option.
  #
  # THIS COMBINATOR NO LONGER EVALUATES. It returns the DECLARATION — a kind-tagged record carrying
  # the kind, the carrier's terms and the step — and the evaluator reads it at demand time: JastAdd
  # declares a circular attribute WITH its lattice data at the declaration, and CIRCULAR-ATTR-EVAL
  # reads it there (Söderberg & Hedin 2013 §2.4, Figure 5). Sealed inside an applied closure, the
  # carrier was unreadable: the demand path could not decide admission at re-entry, could not
  # compute the composed iteration bound, and could not tell a circular attribute from an ordinary
  # one. The declaration's field set is exactly { kind, carrier, step } and the carrier's is exactly
  # { bottom, leq, height, quotient } — both capped: a term beyond the declared set is refused by
  # the evaluator rather than admitted as a refinement.
  #
  # VALIDATION MOVED WITH THE EVALUATION: an incomplete carrier is refused BY NAME at the
  # declaration's FIRST DEMAND (`lib/eval.nix`), `tryEval`-catchably — not here, where a throw at
  # declaration time would arrive before any evaluation a caller could catch, and not by Nix's
  # arity machinery, whose refusals carry no name of ours. The iteration itself — the per-instance
  # ascent, the shared round over an instance SCC, the derived bound `Σ hᵢ + 1` — lives with the
  # evaluator, which is the only surface that can see the instances a demand actually walks.
  circular =
    {
      carrier ? null,
    }:
    f: {
      kind = "circular";
      inherit carrier;
      step = f;
    };

  # Collection attribute combinator (Sloane 2010 §7).
  # Traversal uses COMPUTED attributes, not structural fields; the child direction reads the
  # accessor's composed child-record read (`self._childRecords`), so a traversal gathers over
  # spawned children exactly as the query surface enumerates them.
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
          builtins.attrNames (self._childRecords id)
        else if traverse == "siblings" then
          let
            p = (self.node id).parent;
          in
          if p == null then
            [ ]
          else
            builtins.filter (cid: cid != id) (builtins.attrNames (self._childRecords p))
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

  # Global collection (WARNING: forces full tree — Tier 2). Answers in MATERIALIZATION
  # order (`self.allNodeIds`), not the codepoint key order `attrNames self.allNodes` would
  # give — the same undeclared-order defect `queryReverse` had (see its ORDER comment
  # above): an attrset is a set, so enumerating it and discarding the walk that built it
  # loses a declared order to an incidental one. `allNodeIds` is the walk kept.
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
    ) self.allNodeIds;

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
