# Resolution primitives and named attribute constructors.
#
# Neron (2015) and van Antwerpen (2018) resolution semantics.
# Kiama-inspired vocabulary (Sloane et al., 2010) for attribute definitions.
#
# Key design: import edges are COMPUTED ATTRIBUTES (the `imports` attribute), not structural
# fields. This allows dynamic import resolution.
#
# The relation NAME is not written down here. It comes from `lib/traversal-names.nix`, the one
# binding this module and the structural classifier both read: a relation this resolver traverses
# must be reserved as structural, or a warm evaluation may serve it from a prior graph and answer
# over a stale import relation without saying so. Two agreeing literals would make that a
# coincidence; one binding makes it a property.
#
# The EDGE NAMESPACE is not written down here at all. Every edge read in this module — the walks
# and the one-hop reads alike — is a resolution, and the calculus's `targetsAt` is the one place
# that constructs an `edges-<label>` name, from the prefix `structural` owns and publishes. A caller
# assembling the name itself still escapes, since a predicate over attribute names has no access to
# a caller's literals; that residual is named at `interface.nix`'s facade note.
{
  prelude,
  calculus,
  key,
}:
let
  door = import ./door.nix { inherit prelude; };
  relations = import ./traversal-names.nix;

  # A one-hop edge read is the resolution `wf = l` under mode "reachable" (den-hoag-4or0a U2): the
  # targets of the edges labelled `l` that leave `id`, each once, in the edge list's declared order.
  # Mode "reachable" because the read answers TARGET SCOPES, and a scope's reachable set is
  # "reachable" by definition — not because edges form a set: the store keeps parallel identical
  # edges (distinct paths under "witnesses"), and they are one scope here. So it reads the marks at `id` exactly as every resolution does (ADR-0026), keys a store-context
  # label or target by its text, and refuses a malformed edge list by name. The letter is a WFL term
  # (`wfl.lit`), never parsed, so no character of a label is read as path-expression syntax. A label
  # that is not a string is refused here naming the site, which `wellFormed`'s alphabet refusal
  # would not.
  oneHop =
    site: label: self: id:
    if builtins.isString label then
      map (a: a.node)
        (calculus.resolve {
          wf = calculus.wellFormed {
            alphabet = [ label ];
            expression = calculus.wfl.lit label;
          };
          dataFilter = _: true;
        } self id).answers
    else
      throw "gen-scope.${site}: the label is a ${builtins.typeOf label}, not a letter (a string)";

  # `"ancestors"`: every scope strictly above `id`, nearest first.
  ancestorsWf = calculus.wellFormed {
    alphabet = [ "parent" ];
    expression = "parent parent*";
  };

  # Shadow: merge two declaration sets, inner shadows outer (Neron §5 Def. 1).
  shadow = inner: outer: inner // prelude.filterAttrs (k: _: !(inner ? ${k})) outer;

  # Inherited attribute: the first non-null up the parent chain, as the one calculus reads it —
  # `parent*` under mode "visible", one rank (`$ < parent`, so the nearest declaration shadows every
  # farther one), one DECLARED competition group, and `single`. The declared `group` is what keeps a
  # shadowed ancestor's datum unforced: `default = throw "set X"` on an ancestor, overridden below,
  # answers the override (den-hoag-gayc C1). A parent chain that returns to itself is
  # refused by name at the calculus's `parent` read (den-hoag-gayc D9), which is the refusal this
  # attribute always carried. Like every resolution it reads `marks` at each node it steps from.
  inheritWf = calculus.wellFormed {
    alphabet = [ "parent" ];
    expression = "parent*";
  };
  inheritOrder = calculus.labelOrder {
    alphabet = [ "parent" ];
    layers = [ [ "parent" ] ];
    endOfPath = -1;
  };
  inherit' =
    { resolve }:
    self: id:
    (calculus.resolve {
      wf = inheritWf;
      order = inheritOrder;
      mode = "visible";
      dataFilter = resolve;
      group = "inherited";
    } self id).single
      "inherited";

  # Inherited accumulator: the data along `parent*` from `id`, nearest first, one segment per scope.
  #
  # ★ THE CHAIN IS A RESOLUTION, NOT A HAND WALK (den-hoag-4or0a). It is the calculus's `parent*`
  # under mode "reachable", whose answers come in first-reach order — nearest first on a chain — at
  # a cost linear in the chain on both the list and the update axis (`ci/bench/resolve-folds.sh`).
  # So it inherits the calculus's whole contract: a boundary mark at a scope withholds every edge it
  # does not admit (ADR-0026), a parent chain that returns to itself is refused by name (D9), and a
  # store-context id is keyed by its text. A withheld edge ends the chain SILENTLY: the reason is the
  # same resolution's `withheld`, read through `resolve`. Every scope on the chain answers, an empty
  # one with `[ ]`, because `extract`'s value is normalised to a list before the calculus sees it.
  #
  # ★ `combine ? null` STATES THE ORDERED-LIST DISCIPLINE AS A VALUE, and the reason is that Nix
  # compares no two functions: a default spelled `a: b: a ++ b` is indistinguishable at runtime from
  # a caller passing that same expression, so the concatenation could never be recognised and taken
  # in one pass. `null` is what makes it recognisable. The VALUE is unchanged for every caller that
  # supplied nothing — a right fold of `++` over the segments and `concatLists` of them are the same
  # list, order included — and a caller who DOES supply a `combine` gets the identical right fold
  # the recursion gave, now over a chain that cost linear to walk.
  inheritAll =
    {
      extract,
      combine ? null,
    }:
    self: id:
    let
      contribOf =
        node:
        let
          local = extract node;
        in
        if local != null then (if builtins.isList local then local else [ local ]) else [ ];
      segments =
        map (a: a.value)
          (calculus.resolve {
            wf = inheritWf;
            mode = "reachable";
            dataFilter = contribOf;
          } self id).answers;
      n = builtins.length segments;
    in
    if combine == null then
      builtins.concatLists segments
    else
      # The caller's `combine` folded RIGHT down the chain, which is the association the recursion
      # had: `combine local (combine parent (combine grandparent …))`. Nix publishes no right fold,
      # so it is `foldl'` over the indices in reverse with the accumulator on the right.
      builtins.foldl' (acc: i: combine (builtins.elemAt segments i) acc) (builtins.elemAt segments (
        n - 1
      )) (builtins.genList (i: n - 2 - i) (n - 1));

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
  # Delegates the parent walk (and thus the calculus's marks and D9) to `inheritAll`, then folds out
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
    }:
    self: id:
    let
      all = inheritAll { inherit extract; } self id;
      # One index list, shared by every element's look-back. A per-element prefix would be the
      # Theta(n^2) allocation this replaces, so the prefix is expressed as the `j < i` guard below.
      idx = prelude.genList (i: i) (builtins.length all);
    in
    # First-occurrence dedup, INDEX-BASED, the shape `buildRoots`' `nodeOrder` ships: one pass
    # emitting each element no earlier element is equivalent to. The fold form it replaces re-copied
    # the kept list at every element (`acc ++ [ x ]`) and allocated Theta(n^2) to emit Theta(n);
    # this one allocates its output and one index list. `ci/bench/resolve-inherit-set.sh` holds it
    # to 1.05 per doubling and holds the prior fold, kept there as an arm, to exceeding the same
    # budget in the same run.
    #
    # ★ ONLY HALF OF `nodeOrder`'s REMEDY CARRIES OVER, and the half that does not is the reason
    # this is still quadratic in COMPARISONS. That constructor dedups vertex ids — STRINGS under
    # `==` — so it can record first positions in a `listToAttrs` and read them back in O(1). Here
    # the elements are arbitrary values and `eq` is a CALLER-SUPPLIED predicate, so there is no key
    # to index by and the scan is pairwise. That is the specified semantics rather than a residue:
    # the pairwise cost is `eq`'s, the way n(n-1)/2 edges are a clique's. Indexing it would mean
    # taking a key function in this signature, which is a different surface than the one documented.
    #
    # ★ SCANNING EVERY EARLIER ELEMENT AND SCANNING ONLY THE KEPT ONES SELECT THE SAME FIRSTS,
    # BECAUSE `eq` IS AN EQUIVALENCE. This is the set discipline stated above — an idempotent,
    # order-independent semilattice merge (Van Wyk 2010) — so equivalence is what `eq` already has
    # to be for the result to mean anything, and under transitivity a dropped element's class is
    # represented by the kept element it was dropped for. A caller passing a NON-transitive relation
    # would see this and the fold disagree, and would already have had no set.
    prelude.concatMap (
      i:
      let
        x = builtins.elemAt all i;
      in
      prelude.optional (!(builtins.any (j: j < i && eq (builtins.elemAt all j) x) idx)) x
    ) idx;

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
  #
  # ★ `combine ? null` STATES THE ORDERED-LIST DISCIPLINE AS A VALUE, for the reason given at
  # `inheritAll`: Nix compares no two functions, so a default spelled `a: b: a ++ b` is
  # indistinguishable from a caller passing that expression and the concatenation can never be
  # recognised. The default arm folded `++` over the per-target segments and re-copied the
  # accumulated list once per TARGET — a node's children, imports, ancestors or labelled edge set,
  # so the quantity grows with the graph rather than with anything an author writes down. A caller
  # supplying a `combine` still gets the left fold, unchanged and at the caller's own cost.
  collectionAttr =
    {
      traverse,
      extract,
      combine ? null,
      filter ? _: true,
    }:
    self: id:
    let
      targets =
        if builtins.isFunction traverse then
          traverse self id
        else if traverse == relations.imports then
          oneHop "collectionAttr" relations.imports self id
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
        # The two multi-step traversals are resolutions (den-hoag-4or0a), so each reads the marks, D9
        # and the text-keyed id exactly as `resolve` does; a withheld edge drops its scopes silently.
        else if traverse == "ancestors" then
          map (a: a.node)
            (calculus.resolve {
              wf = ancestorsWf;
              dataFilter = _: true;
            } self id).answers
        else if traverse == "neron" then
          # Every scope `neron.wf` reaches, once, at its `<p`-least path: the visibility order
          # `$ < imports < parent` IS the published self → imports → parent contract, and the sort is
          # stable, so imports keep their declaration order. The operator-less `genericClosure` keeps
          # each id's first occurrence in list order, compared by text — `reachable`'s own dedup.
          map (it: it.key) (
            builtins.genericClosure {
              startSet = map (w: { key = w.node; }) (
                builtins.sort (x: y: calculus.neron.order.pathPrecedes x.path y.path)
                  (calculus.resolve {
                    inherit (calculus.neron) wf;
                    mode = "witnesses";
                    dataFilter = _: true;
                  } self id).answers
              );
              operator = _: [ ];
            }
          )
        else if prelude.hasPrefix "label:" traverse then
          oneHop "collectionAttr" (prelude.removePrefix "label:" traverse) self id
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
    if combine == null then builtins.concatLists perTarget else builtins.foldl' combine [ ] perTarget;

  # Import-scoped collection: demand-driven (Neron §2.4, rule I).
  collectImports =
    extract: self: id:
    prelude.concatMap (importId: extract self importId) (
      oneHop "collectImports" relations.imports self id
    );

  # Global collection (WARNING: forces full tree — Tier 2). Answers in MATERIALIZATION
  # order (`self.allNodeIds`), not the codepoint key order `attrNames self.allNodes` would
  # give — the same undeclared-order defect the reverse walk had (see the ORDER comment at
  # `calculus.nix`'s converse): an attrset is a set, so enumerating it and discarding the walk that built it
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
    oneHop "followEdge" label self id;

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
    collectImports
    collectByType
    followEdge
    collectByLabel
    ;
  # THE DOORS (den-hoag-7gp66 P2, R7): options first, one closed set checked when `f opts` is formed,
  # then the operands, then the protocol tail (`self id`), which stays positional and last (OQ5).
  inherit' = door.options "inherit'" [ "resolve" ] inherit';
  # RETIRED BY THE ONE CALCULUS (den-hoag-gayc D16): each name is a tombstone naming its
  # replacement, so an un-migrated call is refused where it is written rather than answering.
  query = throw "gen-scope: `query` is retired. Use the one resolution calculus: `(resolve (neron // { mode = \"visible\"; dataFilter = f; group = \"k\"; }) self id).single \"k\"`. `transitiveImports = true` is `wf = wellFormed { alphabet = [ \"parent\" \"imports\" ]; expression = \"parent* imports*\"; }`, and the retired shadowing flags are a stated `order` (`labelOrder`). Every evaluation `resolve` reads declares `marks` (`_: _: [ ]` states none).";
  queryAll = throw "gen-scope: `queryAll` is retired. Use the one resolution calculus: `(resolve { inherit (neron) wf; mode = \"witnesses\"; dataFilter = f; } self id).answers`, one `{ node; value; path; state; }` per acyclic resolution path (a diamond answers twice). Every evaluation `resolve` reads declares `marks` (`_: _: [ ]` states none).";
  ambiguous = throw "gen-scope: `ambiguous` is retired. Use `length (unique (map (a: a.node) (resolve { inherit (neron) wf; mode = \"witnesses\"; dataFilter = f; } self id).answers)) > 1`: an ambiguity is more than one distinct declaring node, never one declaration reached along several paths. Every evaluation `resolve` reads declares `marks` (`_: _: [ ]` states none).";
  visibleFrom = throw "gen-scope: `visibleFrom` is retired. Use `(resolve (neron // { mode = \"visible\"; dataFilter = f; group = \"k\"; }) self id).single \"k\"`. Every evaluation `resolve` reads declares `marks` (`_: _: [ ]` states none).";
  queryReverse = throw "gen-scope: `queryReverse` is retired. Use the one resolution calculus over the converse: `map (a: a.value) (resolve { wf = wellFormed { alphabet = [ \"imports\" ]; expression = \"imports\"; }; mode = \"witnesses\"; direction = \"inbound\"; dataFilter = f; } self id).answers`; `transitive = true` is `expression = \"imports imports*\"`. One answer per acyclic reverse path, importers in `allNodeIds` order, so a node on two reverse paths answers twice. Every evaluation `resolve` reads declares `marks` (`_: _: [ ]` states none).";
  inheritAll = door.options "inheritAll" [ "extract" ] inheritAll;
  inheritSet = door.options "inheritSet" [ "extract" ] inheritSet;
  circular = door.options "circular" [ ] circular;
  # `traverse` before `extract`: the targets are chosen, then read — the order `collectByLabel label
  # extract` and `collectImports extract` already keep.
  collectionAttr = door.options "collectionAttr" [
    "traverse"
    "extract"
  ] collectionAttr;
  collect = door.options "collect" [ ] collect;
  subtypeOf = door.options "subtypeOf" [ ] subtypeOf;
  # `shadow { inner; outer; }` (R7 (b)): two declaration sets of one sort, and which shadows which is
  # the whole meaning, so each is named (Neron §5 Def. 1's own terms) rather than remembered by
  # position. The positional core stays the library's own.
  shadow = prelude.door {
    name = "gen-scope.shadow";
    required = [
      "inner"
      "outer"
    ];
    open = true;
  } (r: shadow r.inner r.outer);
}
