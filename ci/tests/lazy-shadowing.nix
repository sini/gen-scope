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
  differential =
    n: seed:
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
        }
      ];
      case =
        i:
        let
          xs = draws 64 (seed * 7919 + i * 104729 + 17);
          r = j: elemAt xs j;
          nn = 3 + modn (r 0) 3;
          ids = genList (k: "s${toString k}") nn;
          wfl = pickL (r 1) wfls;
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
              if k == 0 || modn (r (base + 6 * k)) 3 == 0 then
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
          ev =
            S.eval { parseParent = id: nodes.${id}.parent; }
              {
                children = _: _: { };
                imports = _: id: tgts (idOf id) 2;
                edges-e = _: id: tgts (idOf id) 3;
                marks = _: _: [ ];
              }
              {
                inherit nodes;
                nodeOrder = ids;
              };
          opts = {
            wf = S.wellFormed {
              alphabet = L;
              expression = pickL (r 2) wfl.expressions;
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
          read =
            o: s:
            let
              res = S.resolve o ev s;
              t = x: tryEval (deepSeq x x);
            in
            {
              answers = t res.answers;
              shadowed = t res.shadowed;
              single = t (res.single "k");
            };
        in
        {
          inherit inbound layers;
          rows = map (s: {
            strict = read (opts // { groupBy = _: "k"; }) s;
            lazy = read (opts // { group = "k"; }) s;
          }) ids;
        };
      cases = genList case n;
      rows = concatMap (c: c.rows) cases;
      count = p: length (filter p rows);
    in
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
    test-C1-group-agrees-with-groupBy-on-generated-non-throwing-graphs = {
      expr = differential 200 1;
      expected = {
        reads = 794;
        mismatches = 0;
        answered = 627;
        shadowedSome = 282;
        multiAnswer = 181;
        ambiguityRefused = 91;
        tiedLayers = 125;
        inbound = 32;
      };
    };
  };
}
