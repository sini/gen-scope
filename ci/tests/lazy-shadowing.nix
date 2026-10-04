# RESOLUTION STAYS LAZY IN DATA IT SHADOWS (den-hoag-gayc C1, owner-ruled 2026-09-30, arm (B);
# specs/2026-10-03-gen-scope-lazy-shadowing-spec.md in den-ag-design). Under a declared competition
# key, `group`, a nearer declaration shadows a farther one without forcing it. What must still throw
# (the ancestor that IS the answer, the strict data-reading key, the edge regression) is pinned by
# message in `ci/tests-error.nix`'s `lazy-shadowing`.
{ lib, genScope, ... }:
let
  S = genScope;
  F = import ./_fixtures/lazy-shadowing.nix { inherit lib genScope; };

  # ── THE RANDOM DIFFERENTIAL: `group = "k"` against `groupBy = _: "k"` on generated graphs ──
  # Every graph is a parent forest plus random `imports` and `edges-e` lists (cycles, self-loops and
  # duplicate targets admitted), every datum a plain string or absent, so the strict key never meets
  # a throw and the two keys must agree on every read: `answers`, `shadowed`, and `single "k"`, each
  # under `tryEval`, so an ambiguity refusal must agree as a refusal. The label order is random, ties
  # included, over the WF's own alphabet; walks without `parent` are sometimes inbound. A pure LCG
  # makes the population a fixed one, so the liveness figures below are exact.
  #
  # `cyclic = true` is the CYCLIC-PARENT ARM: `parent` may point anywhere, the node itself included,
  # so the two keys legitimately differ (the strict key decides D9 over whole chains, `group` over
  # what its selection read) and each `group` read is compared with a REFERENCE instead. The
  # reference walks a TWIN in which `parent` is an ordinary letter `up` (so no D9 applies) carrying
  # one more edge to a fresh sink per scope; a sink visit marks a visit whose `parent` edge is
  # admitted. A visit's class is examined iff no present candidate beats its word (the staged
  # selection never tries a lower-ranked symbol after a present one), so the read relation is
  # `from → parent` over the sink visits whose word minus the last letter is examined. The `group`
  # read must refuse iff that relation has a cycle, and otherwise answer as the twin does.
  differential =
    cyclic: n: seed:
    let
      inherit (builtins)
        genList
        elemAt
        length
        filter
        bitAnd
        foldl'
        tryEval
        deepSeq
        listToAttrs
        concatMap
        ;
      next = x: bitAnd (1103515245 * x + 12345) 2147483647;
      draws =
        k: x:
        (foldl'
          (
            acc: _:
            let
              y = next acc.x;
            in
            {
              x = y;
              xs = acc.xs ++ [ (y / 65536) ];
            }
          )
          {
            inherit x;
            xs = [ ];
          }
          (genList (i: i) k)
        ).xs;
      modn = r: m: r - (r / m) * m;
      pickL = r: l: elemAt l (modn r (length l));
      wfls = [
        {
          alphabet = [
            "parent"
            "imports"
          ];
          expressions = [
            "parent* imports?"
            "parent* imports*"
            "(parent|imports)*"
            "imports* parent*"
            "imports? parent*"
          ];
          closures = [
            "parent* imports?"
            "parent* imports*"
            "(parent|imports)*"
            "imports* parent*"
            "imports? parent*"
          ];
        }
        {
          alphabet = [
            "imports"
            "e"
          ];
          expressions = [
            "(imports|e)*"
            "imports* e?"
            "e imports*|imports"
            "(imports e)*"
            "e* imports*"
          ];
          closures = [
            "(imports|e)*"
            "imports* e?"
            "(e imports*)?|imports"
            "(imports e)* imports?"
            "e* imports*"
          ];
        }
        {
          alphabet = [
            "parent"
            "imports"
            "e"
          ];
          expressions = [
            "parent* (imports|e)*"
            "(parent|imports|e)*"
            "parent* imports? e?"
          ];
          closures = [
            "parent* (imports|e)*"
            "(parent|imports|e)*"
            "parent* imports? e?"
          ];
        }
      ];
      case =
        i:
        let
          xs = draws 64 (seed * 7919 + i * 104729 + 17);
          r = j: elemAt xs j;
          nn = 3 + modn (r 0) 3;
          ids = genList (k: "s${toString k}") nn;
          wfl = pickL (r 1) (if cyclic then filter (w: builtins.elem "parent" w.alphabet) wfls else wfls);
          L = wfl.alphabet;
          nL = length L;
          rankOfL = k: modn (r (3 + k)) nL;
          idx = l: foldl' (acc: k: if elemAt L k == l then k else acc) 0 (genList (k: k) nL);
          layers = filter (x: x != [ ]) (genList (rk: filter (l: rankOfL (idx l) == rk) L) nL);
          inbound = !(builtins.elem "parent" L) && modn (r 8) 2 == 1;
          base = 9;
          node = k: {
            id = "s${toString k}";
            type = "n";
            parent =
              if cyclic then
                (if modn (r (base + 6 * k)) 3 == 0 then null else "s${toString (modn (r (50 + k)) nn)}")
              else if k == 0 || modn (r (base + 6 * k)) 3 == 0 then
                null
              else
                "s${toString (modn (r (base + 6 * k)) k)}";
            decls = if modn (r (base + 6 * k + 1)) 2 == 0 then { v = "v-s${toString k}"; } else { };
          };
          nodes = listToAttrs (
            map (k: {
              name = "s${toString k}";
              value = node k;
            }) (genList (k: k) nn)
          );
          idOf = id: foldl' (acc: k: if "s${toString k}" == id then k else acc) 0 (genList (k: k) nn);
          tgts =
            k: off:
            genList (j: "s${toString (modn (r (base + 6 * k + off + 1 + j)) nn)}") (
              modn (r (base + 6 * k + off)) 3
            );
          # `plant` is the set of scopes whose edges, marks and `parent` field throw.
          evOf =
            plant:
            let
              spine = id: v: if plant ? ${id} then throw "SHADOWED-SPINE-FORCED" else v;
              nodes' = builtins.mapAttrs (id: nd: nd // { parent = spine id nd.parent; }) nodes;
            in
            S.eval { parseParent = id: nodes'.${id}.parent; }
              {
                children = _: _: { };
                imports = _: id: spine id (tgts (idOf id) 2);
                edges-e = _: id: spine id (tgts (idOf id) 3);
                marks = _: id: spine id [ ];
              }
              {
                nodes = nodes';
                nodeOrder = ids;
              };
          ev = evOf { };
          wfIx = modn (r 2) (length wfl.expressions);
          opts = {
            wf = S.wellFormed {
              alphabet = L;
              expression = elemAt wfl.expressions wfIx;
            };
            order = S.labelOrder {
              alphabet = L;
              inherit layers;
              endOfPath = modn (r 7) (nL + 2) - 1;
            };
            mode = "visible";
            dataFilter = nd: nd.decls.v or null;
          }
          // lib.optionalAttrs inbound { direction = "inbound"; };
          t = x: tryEval (deepSeq x x);
          read =
            o: s:
            let
              res = S.resolve o ev s;
            in
            {
              answers = t res.answers;
              shadowed = t res.shadowed;
              single = t (res.single "k");
            };
          # THE SPINE (U1 rework): every visit is enumerated by `witnesses` under the prefix closure
          # of `wf` (the same acyclic paths, every one an answer). A visit is SHADOWED when a visible
          # answer's word ŵ = u·$ leaves its word w at a position i < |w| on a symbol of lower rank:
          # the staged selection never tries w's rank there. A scope none of whose visits is needed
          # gets throwing edges, marks and `parent`, and the lazy read must not change.
          wordOf = p: map (step: step.label) p;
          rankOf = opts.order.rankOf;
          beats =
            u: w:
            let
              u' = u ++ [ "$" ];
              go =
                i:
                if i >= length w || i >= length u' then
                  false
                else if elemAt u' i == elemAt w i then
                  go (i + 1)
                else
                  rankOf (elemAt u' i) < rankOf (elemAt w i);
            in
            go 0;
          spineRow =
            s:
            let
              lazyOpts = opts // {
                group = "k";
              };
              clean = S.resolve lazyOpts ev s;
              winners = map (a: wordOf a.path) clean.answers;
              visits =
                (S.resolve {
                  wf = S.wellFormed {
                    alphabet = L;
                    expression = elemAt wfl.closures wfIx;
                  };
                  mode = "witnesses";
                  dataFilter = nd: nd.id;
                } ev s).answers;
              needed = listToAttrs (
                map (v: {
                  name = v.node;
                  value = true;
                }) (filter (v: !(builtins.any (u: beats u (wordOf v.path)) winners)) visits)
              );
              plant = listToAttrs (
                map (id: {
                  name = id;
                  value = true;
                }) (filter (id: !(needed ? ${id})) ids)
              );
              planted = S.resolve lazyOpts (evOf plant) s;
              lazyRead = res: {
                answers = t res.answers;
                single = t (res.single "k");
              };
              visitedPlant = builtins.any (v: plant ? ${v.node}) visits;
            in
            {
              inherit visitedPlant;
              agree = lazyRead clean == lazyRead planted;
              # The live control: the strict key reads every visit, so it meets a visited plant.
              strictForced = !(t ((S.resolve (opts // { groupBy = _: "k"; }) (evOf plant) s).single "k")).success;
            };
          # THE CYCLIC-PARENT ARM's reference (see the header).
          ren = l: if l == "parent" then "up" else l;
          renExpr = builtins.replaceStrings [ "parent" ] [ "up" ];
          Lt = map ren L;
          isSink = id: lib.hasPrefix "sink-" id;
          twin =
            S.eval { parseParent = _: null; }
              {
                children = _: _: { };
                imports = _: id: if isSink id then [ ] else tgts (idOf id) 2;
                edges-e = _: id: if isSink id then [ ] else tgts (idOf id) 3;
                edges-up =
                  _: id:
                  if isSink id then
                    [ ]
                  else
                    lib.optional (nodes.${id}.parent != null) nodes.${id}.parent ++ [ "sink-${id}" ];
                marks = _: _: [ ];
              }
              {
                nodes =
                  builtins.mapAttrs (_: nd: nd // { parent = null; }) nodes
                  // listToAttrs (
                    map (id: {
                      name = "sink-${id}";
                      value = {
                        id = "sink-${id}";
                        type = "n";
                        parent = null;
                        decls = { };
                      };
                    }) ids
                  );
                nodeOrder = ids ++ map (id: "sink-${id}") ids;
              };
          twinOrder = S.labelOrder {
            alphabet = Lt;
            layers = map (map ren) layers;
            endOfPath = modn (r 7) (nL + 2) - 1;
          };
          twinWf =
            expression:
            S.wellFormed {
              alphabet = Lt;
              inherit expression;
            };
          norm = res: {
            answers = t (
              map (a: {
                inherit (a) node value;
                word = map ren (wordOf a.path);
              }) res.answers
            );
            single = t (res.single "k");
          };
          cycRow =
            s:
            let
              witnesses =
                expression: dataFilter:
                (S.resolve {
                  wf = twinWf expression;
                  mode = "witnesses";
                  inherit dataFilter;
                } twin s).answers;
              presentWords = map (a: wordOf a.path) (
                witnesses (renExpr (elemAt wfl.expressions wfIx)) opts.dataFilter
              );
              beatsT =
                u: w:
                let
                  u' = u ++ [ "$" ];
                  go =
                    i:
                    if i >= length w || i >= length u' then
                      false
                    else if elemAt u' i == elemAt w i then
                      go (i + 1)
                    else
                      twinOrder.rankOf (elemAt u' i) < twinOrder.rankOf (elemAt w i);
                in
                go 0;
              examined = w: !(builtins.any (u: beatsT u w) presentWords);
              readFrom = map (z: (lib.last z.path).from) (
                filter (z: isSink z.node && examined (lib.init (wordOf z.path))) (
                  witnesses (renExpr (elemAt wfl.closures wfIx)) (nd: nd.id)
                )
              );
              readSet = listToAttrs (
                map (id: {
                  name = id;
                  value = true;
                }) (filter (id: nodes.${id}.parent != null) readFrom)
              );
              follow =
                id: k:
                if k == 0 then
                  true
                else if readSet ? ${nodes.${id}.parent} then
                  follow nodes.${id}.parent (k - 1)
                else
                  false;
              refCycle = builtins.any (id: follow id nn) (builtins.attrNames readSet);
              lazy = norm (S.resolve (opts // { group = "k"; }) ev s);
              ref = norm (
                S.resolve {
                  wf = twinWf (renExpr (elemAt wfl.expressions wfIx));
                  order = twinOrder;
                  mode = "visible";
                  inherit (opts) dataFilter;
                  group = "k";
                } twin s
              );
            in
            {
              inherit refCycle parentCyclic;
              agree = if refCycle then !lazy.answers.success && !lazy.single.success else lazy == ref;
              answered = lazy.answers.success && lazy.answers.value != [ ];
            };
          # Does the parent map itself carry a cycle (whether or not a selection reads it)?
          parentCyclic =
            let
              up =
                id: k:
                if k == 0 then
                  true
                else if nodes.${id}.parent == null then
                  false
                else
                  up nodes.${id}.parent (k - 1);
            in
            builtins.any (id: up id nn) ids;
        in
        if cyclic then
          { rows = map cycRow ids; }
        else
          {
            inherit inbound layers;
            rows = map (s: {
              strict = read (opts // { groupBy = _: "k"; }) s;
              lazy = read (opts // { group = "k"; }) s;
            }) ids;
            # The converse reads every scope's edges by construction (a node does not know its
            # importers), so only outbound walks are planted.
            spine = if inbound then [ ] else map spineRow ids;
          };
      cases = genList case n;
      rows = concatMap (c: c.rows) cases;
      count = p: length (filter p rows);
      spine = concatMap (c: c.spine) cases;
      spineCount = p: length (filter p spine);
    in
    if cyclic then
      {
        reads = length rows;
        mismatches = count (x: !x.agree);
        # Liveness: reads whose selection read a parent cycle (refused), reads over a graph whose
        # parent map has a cycle, and of those the reads that answer (a cycle the selection never
        # read, which must not refuse).
        refused = count (x: x.refCycle);
        onCyclicGraph = count (x: x.parentCyclic);
        answeredOnCyclicGraph = count (x: x.parentCyclic && !x.refCycle && x.answered);
      }
    else
      {
        reads = length rows;
        mismatches = count (x: x.strict != x.lazy);
        # Liveness: the population exercises what the selection decides.
        answered = count (x: x.strict.answers.success && x.strict.answers.value != [ ]);
        shadowedSome = count (x: x.strict.shadowed.success && x.strict.shadowed.value != [ ]);
        multiAnswer = count (x: x.strict.answers.success && length x.strict.answers.value > 1);
        ambiguityRefused = count (x: !x.strict.single.success);
        tiedLayers = length (filter (c: builtins.any (l: length l > 1) c.layers) cases);
        inbound = length (filter (c: c.inbound) cases);
        spineReads = length spine;
        spineMismatches = spineCount (x: !x.agree);
        # Liveness of the spine half: reads whose walk reaches a planted scope, and of those the reads
        # where the strict key, which forces every visit, throws (a live control must fire).
        spinePlantVisited = spineCount (x: x.visitedPlant);
        spineStrictForced = spineCount (x: x.visitedPlant && x.strictForced);
      };
in
{
  flake.tests.lazy-shadowing = {
    # L1–L3: the C1 fixture answers the nearer declaration, through `inherit'` and through
    # `resolve` under `group`, with one throwing ancestor and with two.
    test-C1-nearer-declaration-shadows-a-throwing-ancestor-unforced = {
      expr = {
        inheritShadow = F.inherit' F.shadowing;
        inheritDeep = F.inherit' F.deep;
        groupShadow = F.group F.shadowing;
        groupDeep = F.group F.deep;
      };
      expected = {
        inheritShadow = "va";
        inheritDeep = "va";
        groupShadow = "va";
        groupDeep = "va";
      };
    };

    # THE SPINE IS LAZY TOO (den-hoag-gayc U1 rework; ADR-0008 item 1): the shadowed scope `b`'s
    # computed `imports`, its marks, and its own `parent` field each throw, and a parent cycle sits
    # above it; nothing past `a`'s declaration is read (gen-scope main's `inherit'` answered "va" on
    # all four; U1 forced every reachable scope's edges). The strict twin is in `tests-error.nix`.
    test-U1-a-nearer-declaration-reads-no-shadowed-scope-s-edges = {
      expr = {
        imports = F.group F.edgeForcing;
        marks = F.group F.marksForcing;
        parent = F.group F.parentForcing;
        cycleAbove = F.group F.cycleAbove;
        inheritImports = F.inherit' F.edgeForcing;
        inheritParent = F.inherit' F.parentForcing;
        inheritCycleAbove = F.inherit' F.cycleAbove;
      };
      expected = {
        imports = "va";
        marks = "va";
        parent = "va";
        cycleAbove = "va";
        inheritImports = "va";
        inheritParent = "va";
        inheritCycleAbove = "va";
      };
    };

    # F2: gen-scope's own `config-cascade` example, unedited, over the C1 fixture (gen-scope main
    # answered 8080; a strict constant `groupBy` threw).
    test-C1-config-cascade-example-shadows-a-throwing-ancestor-unforced = {
      expr = F.cascade;
      expected = 8080;
    };

    # F1 / G5: an `order` that cannot rank a letter `wf` steps is refused at the door under either
    # key (the strict key once answered "vs" here and the lazy one refused, data-dependently); the
    # order over the whole alphabet answers under both.
    test-C1-G5-order-must-rank-every-wf-letter-under-either-key = {
      expr =
        let
          read =
            alphabet: key: (S.resolve (F.mismatchOpts alphabet // key) F.alphabetMismatch "s").single "k";
          ok = x: (builtins.tryEval (builtins.deepSeq x x)).success;
          short = [ "imports" ];
          full = [
            "imports"
            "e"
          ];
        in
        {
          shortGroup = ok (read short { group = "k"; });
          shortGroupBy = ok (read short { groupBy = _: "k"; });
          fullGroup = read full { group = "k"; };
          fullGroupBy = read full { groupBy = _: "k"; };
        };
      expected = {
        shortGroup = false;
        shortGroupBy = false;
        fullGroup = "vs";
        fullGroupBy = "vs";
      };
    };

    # P4: the gating differential. The suite's hand-written cells catch a selection that keeps only
    # the first symbol of a rank class in 2 cells; this population catches it on hundreds of reads.
    # Its spine half (U1 rework) plants throwing edges, marks and `parent` on every scope the
    # selection shadows, and the lazy read must not move; the strict key, the live control, throws.
    test-C1-group-agrees-with-groupBy-and-reads-no-shadowed-spine-on-generated-graphs = {
      expr = differential false 200 1;
      expected = {
        reads = 794;
        mismatches = 0;
        answered = 627;
        shadowedSome = 282;
        multiAnswer = 181;
        ambiguityRefused = 91;
        tiedLayers = 125;
        inbound = 32;
        spineReads = 666;
        spineMismatches = 0;
        spinePlantVisited = 136;
        spineStrictForced = 129;
      };
    };

    # K1: the CYCLIC-PARENT ARM of the differential (see its header). `group` decides D9 over the
    # `parent` fields its selection read, so it refuses exactly where the reference's read relation
    # has a cycle, whatever the rank order, and elsewhere answers as the D9-free twin does.
    test-D9-under-group-refuses-iff-the-parent-fields-read-cycle-on-generated-graphs = {
      expr = differential true 200 2;
      expected = {
        reads = 803;
        mismatches = 0;
        refused = 333;
        onCyclicGraph = 568;
        answeredOnCyclicGraph = 184;
      };
    };
  };
}
