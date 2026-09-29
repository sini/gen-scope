# THE ONE RESOLUTION CALCULUS (`lib/calculus.nix`, den-hoag-gayc U1b, U1c, U1d) — the gating cells.
#
# Every fixture is an EVALUATED scope: a node set lifted by `buildRoots`, each letter `l` read from
# an `edges-l` attribute, `imports` from the import relation, `parent` from the node record, and the
# boundary-mark floor from `marks`. The mode-law cells are the design's cycle-law fixtures
# (reports/den-hoag-gayc-cycle-law-v0, design-gate-v0), whose reference is gen-graph 0db4e737's
# opposite-law mode on the same graph: `reachable` is the walk law, `witnesses` the acyclic-path law.
#
# Refusal TEXT is pinned in `ci/tests-error.nix`'s `calculus-refusals`; here each refusal is shown
# catchable (`tryEval` false) beside an unplanted twin that answers.
{
  lib,
  genScope,
  genPreludeLib,
  ...
}:
let
  S = genScope;
  sorted = builtins.sort builtins.lessThan;
  throws = e: !(builtins.tryEval (builtins.deepSeq e true)).success;
  answers = e: (builtins.tryEval (builtins.deepSeq e true)).success;
  refusals = import ./_fixtures/calculus-refusals.nix { inherit lib genScope; };

  # A lifted scope. `edges.<l>.<from>` lists targets; `parents.<child>` names a parent; `marks` is
  # the floor, and `null` leaves the attribute undeclared.
  lift =
    {
      nodes,
      edges ? { },
      imports ? { },
      parents ? { },
      marks ? (_: _: [ ]),
      decls ? { },
      extra ? { },
    }:
    let
      roots = S.buildRoots {
        parentGraph = S.overlays (
          map (
            n:
            S.edge {
              from = n;
              to = parents.${n};
            }
          ) (builtins.attrNames parents)
          ++ map S.vertex nodes
        );
        inherit decls;
      };
    in
    S.eval
      {
        parseParent = id: (roots.nodes.${id} or { parent = null; }).parent;
      }
      (
        {
          children = _: _: { };
          imports = _: id: imports.${id} or [ ];
        }
        // lib.optionalAttrs (marks != null) { inherit marks; }
        // lib.mapAttrs' (l: m: lib.nameValuePair "edges-${l}" (_: id: m.${id} or [ ])) edges
        // extra
      )
      roots;

  wf = alphabet: expression: S.wellFormed { inherit alphabet expression; };
  ids = n: n.id;
  nodesOf = r: map (a: a.node) r.answers;
  run =
    mode: alphabet: expression: ev: from:
    S.resolve {
      wf = wf alphabet expression;
      dataFilter = ids;
      inherit mode;
    } ev from;
  both = alphabet: expression: ev: from: {
    reachable = nodesOf (run "reachable" alphabet expression ev from);
    witnesses = nodesOf (run "witnesses" alphabet expression ev from);
  };
  # A flat order over the listed letters, `$` first (gen-graph's `order.labels`, endOfPath = -1).
  flat =
    letters:
    S.labelOrder {
      alphabet = letters;
      layers = map (l: [ l ]) letters;
      endOfPath = -1;
    };
  visible =
    letters: expression: ev: from:
    S.resolve {
      wf = wf letters expression;
      dataFilter = ids;
      mode = "visible";
      order = flat letters;
      groupBy = _: "x";
    } ev from;
  wordsOf = map (a: map (s: s.label) a.path);

  # ── the cycle-law fixtures ──
  g0 = lift {
    nodes = [
      "s"
      "x"
    ];
    edges.b.s = [ "x" ];
  };
  g1 = lift {
    nodes = [
      "s"
      "x"
    ];
    edges = {
      a.s = [ "s" ];
      own.s = [ "x" ];
    };
  };
  g1b = lift {
    nodes = [
      "s"
      "t"
      "x"
    ];
    edges = {
      a = {
        s = [ "t" ];
        t = [ "s" ];
      };
      own.s = [ "x" ];
    };
  };
  g2 = lift {
    nodes = [
      "s"
      "t"
      "u"
      "xt"
      "xu"
    ];
    edges = {
      a.s = [ "s" ];
      b.s = [ "t" ];
      c.s = [ "u" ];
      own = {
        t = [ "xt" ];
        u = [ "xu" ];
      };
    };
  };
  g3 = lift {
    nodes = [
      "s"
      "x"
    ];
    edges = {
      a.s = [ "s" ];
      own.s = [ "x" ];
    };
  };
  # EN: Néron's policy on a cyclic import graph, with the real `parent` and `imports` letters.
  gN = lift {
    nodes = [
      "s"
      "m"
      "r"
      "xs"
      "xm"
      "xr"
    ];
    imports = {
      s = [ "m" ];
      m = [ "s" ];
    };
    parents.s = "r";
    edges.own = {
      s = [ "xs" ];
      m = [ "xm" ];
      r = [ "xr" ];
    };
  };
  keys = [
    "h0"
    "h1"
    "h2"
  ];
  peer = lift {
    nodes = keys;
    edges.peer = lib.genAttrs keys (_: keys);
  };
  t2 = lift {
    nodes = [
      "s"
      "t"
      "u"
    ];
    edges = {
      members.s = [ "t" ];
      contains.t = [
        "s"
        "u"
      ];
    };
  };
  t3 = lift {
    nodes = [
      "a"
      "b"
    ];
    edges.tacks = {
      a = [ "b" ];
      b = [ "a" ];
    };
  };
  ic = lift {
    nodes = [
      "a"
      "b"
    ];
    imports = {
      a = [ "b" ];
      b = [ "a" ];
    };
  };

  # ── C22's floor: grommet carries a mark admitting nothing ──
  c22nodes = [
    "grommet"
    "bodkin"
    "awl"
  ];
  c22 = lift {
    nodes = c22nodes;
    edges.peer = lib.genAttrs c22nodes (_: c22nodes);
    marks =
      _: id:
      if id == "grommet" then
        [
          {
            name = "batting";
            admits = _: false;
          }
        ]
      else
        [ ];
  };
  peerOf =
    extra: from:
    let
      r = S.resolve (
        {
          wf = wf [ "peer" ] "peer";
          dataFilter = ids;
        }
        // extra
      ) c22 from;
    in
    {
      answers = nodesOf r;
      withheld = map (w: {
        inherit (w) target marks;
      }) (r.withheld from);
    };
  batting = t: {
    target = t;
    marks = [ "batting" ];
  };

  # ── 6a: a gen-authored scope with and without its mark declaration ──
  sixA =
    marks:
    lift {
      nodes = [
        "c"
        "m"
      ];
      imports.c = [ "m" ];
      decls.m.x = "vm";
      inherit marks;
    };
  neronX =
    ev: from:
    (S.resolve (
      S.neron
      // {
        mode = "visible";
        dataFilter = n: n.decls.x or null;
        groupBy = _: "x";
      }
    ) ev from).single
      "x";

  # ── N3/D9: a revisit through `parent` on well-formed containment, and a real parent cycle ──
  n3 = lift {
    nodes = [
      "c"
      "m"
    ];
    parents.m = "c";
    imports.c = [ "m" ];
  };
  cyc = lift {
    nodes = [
      "a"
      "b"
    ];
    parents = {
      a = "b";
      b = "a";
    };
  };
  # D9's verdict is decided once per resolution; these pin WHERE it refuses. `rho`'s start is not on
  # the cycle, its chain enters one; `shutParents` withholds every `parent` edge, so no answer
  # reads one.
  rho = lift {
    nodes = [
      "t"
      "a"
      "b"
    ];
    parents = {
      t = "a";
      a = "b";
      b = "a";
    };
  };
  shutParents = lift {
    nodes = [
      "a"
      "b"
    ];
    parents = {
      a = "b";
      b = "a";
    };
    marks = _: _: [
      {
        name = "shut";
        admits = l: l != "parent";
      }
    ];
  };

  # ── the neron = query grid (gate v1 grid2): every 3-node scope — acyclic parent map, import
  # subsets, declaration flags — read by the retired `query` (frozen in
  # `_fixtures/retired-resolution.nix`) and by `neron` + visible + `single` ──
  retired = import ./_fixtures/retired-resolution.nix { prelude = genPreludeLib; };
  ns = [
    "c"
    "p"
    "m"
  ];
  others = n: builtins.filter (x: x != n) ns;
  subsets =
    l:
    if l == [ ] then
      [ [ ] ]
    else
      let
        r = subsets (builtins.tail l);
      in
      r ++ map (s: [ (builtins.head l) ] ++ s) r;
  choices = n: [ null ] ++ others n;
  pmaps = builtins.concatMap (
    pc:
    builtins.concatMap (
      pp:
      map (pm: {
        c = pc;
        p = pp;
        m = pm;
      }) (choices "m")
    ) (choices "p")
  ) (choices "c");
  acyclic =
    pm:
    let
      up =
        n: k:
        if k > 3 then
          false
        else if pm.${n} == null then
          true
        else
          up pm.${n} (k + 1);
    in
    builtins.all (n: up n 0) ns;
  imaps = builtins.concatMap (
    ic:
    builtins.concatMap (
      ip:
      map (im: {
        c = ic;
        p = ip;
        m = im;
      }) (subsets (others "m"))
    ) (subsets (others "p"))
  ) (subsets (others "c"));
  dmaps =
    builtins.concatMap
      (
        dc:
        builtins.concatMap
          (
            dp:
            map
              (dm: {
                c = dc;
                p = dp;
                m = dm;
              })
              [
                true
                false
              ]
          )
          [
            true
            false
          ]
      )
      [
        true
        false
      ];
  gridRow =
    lsi: pm: im: dm:
    let
      ev = lift {
        nodes = ns;
        parents = lib.filterAttrs (_: p: p != null) pm;
        imports = im;
        decls = lib.genAttrs ns (n: if dm.${n} then { x = "v${n}"; } else { });
      };
      f = n: n.decls.x or null;
      order =
        if lsi then
          S.neron.order
        else
          S.labelOrder {
            alphabet = [
              "parent"
              "imports"
            ];
            layers = [
              [ "imports" ]
              [ ]
              [ "parent" ]
            ];
            endOfPath = 1;
          };
      verdict = r: if r.success then (if r.value == null then "null" else r.value) else "AMBIG";
      try = e: builtins.tryEval (builtins.deepSeq e e);
    in
    {
      today = verdict (
        try (
          retired.query {
            dataFilter = f;
            localShadowsImport = lsi;
          } ev "c"
        )
      );
      preset = verdict (
        try (
          (S.resolve (
            S.neron
            // {
              mode = "visible";
              inherit order;
              dataFilter = f;
              groupBy = _: "x";
            }
          ) ev "c").single
            "x"
        )
      );
    };
  grid =
    lsi:
    builtins.concatMap (pm: builtins.concatMap (im: map (dm: gridRow lsi pm im dm) dmaps) imaps) (
      builtins.filter acyclic pmaps
    );
  gridRead =
    lsi:
    let
      rows = grid lsi;
    in
    {
      shapes = builtins.length rows;
      flips = builtins.length (builtins.filter (r: r.today != r.preset) rows);
      vc = builtins.length (builtins.filter (r: r.today == "vc") rows);
    };

  # ── U1c: the retired surfaces against their replacements, over the same grid ──
  neronWf =
    transitive:
    if transitive then
      wf [
        "parent"
        "imports"
      ] "parent* imports*"
    else
      S.neron.wf;
  witnessesOf =
    transitive: f: ev: from:
    (S.resolve {
      wf = neronWf transitive;
      mode = "witnesses";
      dataFilter = f;
    } ev from).answers;
  # D10: the retiring `ambiguous` over DISTINCT ORIGINS — one declaration reached several ways is one.
  ambiguousD10 =
    transitive: f: ev: from:
    builtins.length (lib.unique (map (a: a.node) (witnessesOf transitive f ev from))) > 1;
  # How many times each value occurs, so two answer lists compare as multisets.
  tally = builtins.foldl' (acc: v: acc // { ${v} = (acc.${v} or 0) + 1; }) { };
  within = a: b: builtins.all (v: (b.${v} or 0) >= a.${v}) (builtins.attrNames a);
  ambRow =
    transitive: pm: im: dm:
    let
      ev = lift {
        nodes = ns;
        parents = lib.filterAttrs (_: p: p != null) pm;
        imports = im;
        decls = lib.genAttrs ns (n: if dm.${n} then { x = "v${n}"; } else { });
      };
      f = n: n.decls.x or null;
      o = {
        dataFilter = f;
        transitiveImports = transitive;
      };
      wit = witnessesOf transitive f ev "c";
    in
    {
      today = retired.ambiguous o ev "c";
      distinct = ambiguousD10 transitive f ev "c";
      count = builtins.length wit > 1;
      all = tally (retired.queryAll o ev "c");
      wit = tally (map (a: a.value) wit);
    };
  ambRead =
    transitive:
    let
      rows = builtins.concatMap (
        pm: builtins.concatMap (im: map (dm: ambRow transitive pm im dm) dmaps) imaps
      ) (builtins.filter acyclic pmaps);
      n = pred: builtins.length (builtins.filter pred rows);
      differ = r: r.all != r.wit;
    in
    {
      shapes = builtins.length rows;
      distinct = {
        trueToFalse = n (r: r.today && !r.distinct);
        falseToTrue = n (r: !r.today && r.distinct);
      };
      # The control: the witness-COUNT reading, which the gate measured flipping both ways.
      count = {
        trueToFalse = n (r: r.today && !r.count);
        falseToTrue = n (r: !r.today && r.count);
      };
      queryAllVersusWitnesses = {
        differ = n differ;
        moreInQueryAll = n (r: differ r && within r.wit r.all);
        moreInWitnesses = n (r: differ r && within r.all r.wit);
        mixed = n (r: differ r && !(within r.wit r.all) && !(within r.all r.wit));
      };
    };
  # `inherit'` read from every node of every acyclic parent map under every declaration pattern.
  inheritRead =
    let
      rows = builtins.concatMap (
        pm:
        builtins.concatMap (
          dm:
          let
            ev = lift {
              nodes = ns;
              parents = lib.filterAttrs (_: p: p != null) pm;
              decls = lib.genAttrs ns (n: if dm.${n} then { x = "v${n}"; } else { });
            };
            f = n: n.decls.x or null;
          in
          map (from: {
            today = retired."inherit'" { resolve = f; } ev from;
            now = S."inherit'" { } f ev from;
          }) ns
        ) dmaps
      ) (builtins.filter acyclic pmaps);
    in
    {
      reads = builtins.length rows;
      flips = builtins.length (builtins.filter (r: r.today != r.now) rows);
      # The control: both answer kinds occur, so an `inherit'` reading one constant cannot read 0.
      nulls = builtins.length (builtins.filter (r: r.now == null) rows);
      answered = builtins.length (builtins.filter (r: r.now != null) rows);
    };
  # T4, T6 and the N2 diamond: one scope each, read by the replacement and by the retired surface.
  x = n: n.decls.x or null;
  valuesOf = map (a: a.value);
  t4 =
    withImport:
    lift {
      nodes = [
        "c"
        "p"
      ];
      parents.c = "p";
      imports = lib.optionalAttrs withImport { p = [ "c" ]; };
      decls = {
        c.x = "vc";
        p.x = "vp";
      };
    };
  t6 = lift {
    nodes = [
      "c"
      "m1"
      "m2"
    ];
    imports = {
      c = [ "m1" ];
      m1 = [ "m2" ];
    };
    decls = {
      m1.x = "v1";
      m2.x = "v2";
    };
  };
  diamond = lift {
    nodes = [
      "c"
      "p"
      "m"
    ];
    parents.c = "p";
    imports = {
      c = [ "m" ];
      p = [ "m" ];
    };
    decls.m.x = "vm";
  };
  # The flag fixture: `child` imports `provider` (x = "imported") and sits under `parent`
  # (x = "inherited").
  flags = lift {
    nodes = [
      "child"
      "parent"
      "provider"
    ];
    parents.child = "parent";
    imports.child = [ "provider" ];
    decls = {
      parent.x = "inherited";
      provider.x = "imported";
    };
  };
  visibleUnder =
    order: ev: from:
    (S.resolve (
      S.neron
      // {
        mode = "visible";
        inherit order;
        dataFilter = x;
        groupBy = _: "x";
      }
    ) ev from).single
      "x";

  # ── warm freshness: a prior whose every route and whose floor answer values a cold run never
  # produces; a decision naming every structural attribute the calculus reads as reusable ──
  # a —imports→ b, a —tack→ c, b's parent c (withheld by b's mark), c's parent d. The prior holds
  # none of it: no import, no tack, no mark, no parents — so a served route loses a node, and a
  # served floor admits b's parent edge.
  warmNodes = [
    "a"
    "b"
    "c"
    "d"
  ];
  warmScope = parents: {
    nodes = lib.genAttrs warmNodes (id: {
      inherit id;
      parent = parents.${id} or null;
      decls = { };
      type = "t";
    });
    nodeOrder = warmNodes;
  };
  current = warmScope {
    b = "c";
    c = "d";
  };
  warmAttrs = {
    children = _: _: { };
    imports = _: id: if id == "a" then [ "b" ] else [ ];
    "edges-tack" = _: id: if id == "a" then [ "c" ] else [ ];
    marks =
      _: id:
      if id == "b" then
        [
          {
            name = "shut";
            admits = _: false;
          }
        ]
      else
        [ ];
  };
  warmPrior = S.eval { } (
    warmAttrs
    // {
      imports = _: _: [ ];
      "edges-tack" = _: _: [ ];
      marks = _: _: [ ];
    }
  ) (warmScope { });
  warmOf =
    names:
    S.evalWarm { } {
      scope = current;
      attributes = warmAttrs;
      prior = warmPrior;
      decision = S.mkDecision {
        isClean = _: true;
        reusable = _: names;
      };
    };
  warmCold = S.eval { } warmAttrs current;
  warmRead =
    ev:
    let
      r = S.resolve {
        wf = wf [
          "imports"
          "tack"
          "parent"
        ] "(imports | tack | parent)*";
        dataFilter = ids;
      } ev "a";
    in
    {
      answers = nodesOf r;
      withheld = r.withheld "b";
    };

  # ── U1d: the converse ──
  # The spec's O3 fixture: importers a —→ t, b —→ t, c —→ a, c —→ b (c reaches t along two reverse
  # paths), and a cycle t —→ c.
  reverseScope =
    marks:
    lift {
      nodes = [
        "t"
        "a"
        "b"
        "c"
      ];
      imports = {
        a = [ "t" ];
        b = [ "t" ];
        c = [
          "a"
          "b"
        ];
        t = [ "c" ];
      };
      decls = {
        t.x = "t";
        a.x = "a";
        b.x = "b";
        c.x = "c";
      };
      inherit marks;
    };
  inbound =
    mode: alphabet: expression: ev: from:
    S.resolve {
      wf = wf alphabet expression;
      dataFilter = x;
      inherit mode;
      direction = "inbound";
    } ev from;
  shut =
    who: _: id:
    if id == who then
      [
        {
          name = "shut";
          admits = _: false;
        }
      ]
    else
      [ ];
  converseRead =
    ev: at:
    let
      r = inbound "witnesses" [ "imports" ] "imports imports*" ev "t";
    in
    {
      answers = valuesOf r.answers;
      withheld = r.withheld at;
    };
  # `tack` edges a —→ t and b —→ t twice: a converse source is enumerated once.
  tacks = lift {
    nodes = [
      "t"
      "a"
      "b"
    ];
    edges.tack = {
      a = [ "t" ];
      b = [
        "t"
        "t"
      ];
    };
    decls = {
      a.x = "a";
      b.x = "b";
    };
  };

  # A scope whose one edge attribute throws a named error of its own.
  throwing = lift {
    nodes = [ "a" ];
    extra."edges-boom" = _: _: throw "planted: the edge read's own refusal";
  };
  quiet = lift {
    nodes = [ "a" ];
    edges.boom = { };
  };

  # The 4ok8y chain shape, `seq [ lit a, star acc ]` nested 5,000 deep, built by the published
  # constructors; keyed by the engine the calculus reads.
  regex = import ../../lib/regex.nix { prelude = genPreludeLib; };
  structural = import ../../lib/structural.nix { prelude = genPreludeLib; };
  chain =
    k:
    builtins.foldl' (
      acc: _:
      S.wfl.seq [
        (S.wfl.lit "a")
        (S.wfl.star acc)
      ]
    ) (S.wfl.lit "a") (builtins.genList (i: i) k);
in
{
  flake.tests.calculus = {
    # ── mode law (Q4 = S): reachable is the walk, witnesses the acyclic paths ──
    test-E1-self-loop = {
      expr = both [ "a" "own" ] "a own" g1 "s";
      expected = {
        reachable = [ "x" ];
        witnesses = [ ];
      };
    };
    test-E1b-two-cycle = {
      expr = both [ "a" "own" ] "a a own" g1b "s";
      expected = {
        reachable = [ "x" ];
        witnesses = [ ];
      };
    };
    test-T1-hub-peer-with-self-edge = {
      expr = both [ "peer" ] "peer" peer "h0";
      expected = {
        reachable = keys;
        witnesses = [
          "h1"
          "h2"
        ];
      };
    };
    test-T2-members-contains-star = {
      expr = both [ "members" "contains" ] "members contains*" t2 "s";
      expected = {
        reachable = [
          "s"
          "t"
          "u"
        ];
        witnesses = [
          "t"
          "u"
        ];
      };
    };
    test-T3-tacks-plus = {
      expr = both [ "tacks" ] "tacks+" t3 "a";
      expected = {
        reachable = [
          "a"
          "b"
        ];
        witnesses = [ "b" ];
      };
    };
    test-E2-visible-is-the-acyclic-reading = {
      expr = nodesOf (visible [ "a" "b" "c" "own" ] "b own | a c own" g2 "s");
      expected = [ "xt" ];
    };
    test-E3-visible-a-star-own-terminates = {
      expr = wordsOf (visible [ "a" "own" ] "a* own" g3 "s").answers;
      expected = [ [ "own" ] ];
    };
    # Controls: where the two laws agree, both modes answer the same.
    test-control-E0-acyclic = {
      expr = both [ "b" ] "b" g0 "s";
      expected = {
        reachable = [ "x" ];
        witnesses = [ "x" ];
      };
    };
    test-control-E1-own-only = {
      expr = both [ "a" "own" ] "own" g1 "s";
      expected = {
        reachable = [ "x" ];
        witnesses = [ "x" ];
      };
    };
    test-control-EN-neron-on-a-cyclic-import-graph = {
      expr =
        let
          r = both [ "parent" "imports" "own" ] "parent* imports* own" gN "s";
        in
        r // { witnesses = sorted r.witnesses; };
      expected = {
        reachable = [
          "xm"
          "xr"
          "xs"
        ];
        witnesses = [
          "xm"
          "xr"
          "xs"
        ];
      };
    };
    test-control-imports-star-on-a-two-cycle = {
      expr = both [ "imports" ] "imports*" ic "a";
      expected = {
        reachable = [
          "a"
          "b"
        ];
        witnesses = [
          "a"
          "b"
        ];
      };
    };

    # ── N1/D1: the floor is read in every resolution ──
    test-C22-floor-grommet-withholds-every-edge = {
      expr = peerOf { } "grommet";
      expected = {
        answers = [ ];
        withheld = map batting c22nodes;
      };
    };
    test-C22-floor-bodkin-answers-all-three = {
      expr = peerOf { } "bodkin";
      expected = {
        answers = sorted c22nodes;
        withheld = [ ];
      };
    };
    # ── D2: `bound` only narrows ──
    test-D2-bound-narrows-bodkin-to-nothing = {
      expr = peerOf {
        bound = _: [
          {
            name = "narrow";
            admits = _: false;
          }
        ];
      } "bodkin";
      expected = {
        answers = [ ];
        withheld = map (t: {
          target = t;
          marks = [ "narrow" ];
        }) c22nodes;
      };
    };
    test-D2-bound-cannot-widen-grommet = {
      expr = peerOf {
        bound = _: [
          {
            name = "wide";
            admits = _: true;
          }
        ];
      } "grommet";
      expected = {
        answers = [ ];
        withheld = map batting c22nodes;
      };
    };

    # ── 6a: a gen-authored scope with no mark declaration is refused; `_: _: [ ]` answers ──
    test-6a-no-marks-is-refused-catchably = {
      expr = throws (neronX (sixA null) "c");
      expected = true;
    };
    test-6a-marks-declared-none-answers = {
      expr = neronX (sixA (_: _: [ ])) "c";
      expected = "vm";
    };

    # ── D6: the mark attribute is structural and out of the edge projection ──
    test-D6-marks-is-structural-and-not-projected = {
      expr = {
        structural = S.structural structural.markAttribute;
        projected = structural.projected structural.markAttribute;
        edges = c22.structuralEdges "grommet";
        findings = c22.projectionFindings "grommet";
      };
      expected = {
        structural = true;
        projected = false;
        edges = c22nodes;
        findings = [ ];
      };
    };

    # ── N4/D7: a letter's attribute is read; an undeclared one is refused ──
    test-N4-a-declared-letter-reads-its-edges = {
      expr = nodesOf (run "reachable" [ "tacks" ] "tacks*" t3 "a");
      expected = [
        "a"
        "b"
      ];
    };
    test-N4-an-undeclared-letter-is-refused-catchably = {
      expr = throws (run "reachable" [ "l1" ] "l1" t3 "a");
      expected = true;
    };

    # ── N5/D8: the calculus's reserved letters are refused as lifted labels ──
    test-N5-reserved-letters-refused-at-the-lift = {
      expr =
        map
          (
            label:
            throws
              (S.buildRoots {
                parentGraph = S.vertices [
                  "a"
                  "b"
                ];
                edgeGraphs = [
                  {
                    inherit label;
                    graph = S.edge {
                      from = "a";
                      to = "b";
                    };
                  }
                ];
              }).nodes.a.decls.__edges
          )
          [
            "imports"
            "parent"
            "I"
            "peer"
          ];
      expected = [
        true
        true
        true
        false
      ];
    };

    # ── N3/D9: a parent revisit on well-formed containment is NR-Cons's drop; a real cycle refuses ──
    test-N3-parent-revisit-on-well-formed-containment = {
      expr = {
        reachable = nodesOf (run "reachable" [ "imports" "parent" ] "(imports | parent)*" n3 "c");
        paths = wordsOf (run "witnesses" [ "imports" "parent" ] "(imports | parent)*" n3 "c").answers;
      };
      expected = {
        reachable = [
          "c"
          "m"
        ];
        paths = [
          [ ]
          [ "imports" ]
        ];
      };
    };
    test-N3-a-parent-cycle-is-refused-catchably = {
      expr = throws (run "reachable" [ "parent" ] "parent*" cyc "a");
      expected = true;
    };
    test-D9-refused-where-a-read-meets-the-cycle = {
      expr = {
        rhoReachable = throws (run "reachable" [ "parent" ] "parent*" rho "t");
        rhoWitnesses = throws (run "witnesses" [ "parent" ] "parent*" rho "t");
        shutAnswers = nodesOf (run "witnesses" [ "parent" ] "parent*" shutParents "a");
        shutWithheld = throws ((run "witnesses" [ "parent" ] "parent*" shutParents "a").withheld "a");
      };
      expected = {
        rhoReachable = true;
        rhoWitnesses = true;
        shutAnswers = [ "a" ];
        shutWithheld = true;
      };
    };

    # ── P1: the preset constructs over the plain alphabet ──
    test-P1-neron-constructs-over-a-plain-list = {
      expr = {
        wf = S.neron.wf.alphabet;
        order = S.neron.order.alphabet;
        layers = S.neron.order.layers;
      };
      expected = {
        wf = [
          "parent"
          "imports"
        ];
        order = [
          "parent"
          "imports"
        ];
        layers = [
          [ "imports" ]
          [ "parent" ]
        ];
      };
    };

    # ── neron = query over every 3-node scope; the lsi = false row via the middle rank ──
    # The control is the distribution: `vc` answers differ between the two rows, so a comparison
    # blind to the order could not read 0 flips on both.
    test-neron-agrees-with-query-over-the-grid = {
      expr = {
        default = gridRead true;
        localDoesNotShadowImport = gridRead false;
      };
      expected = {
        default = {
          shapes = 8192;
          flips = 0;
          vc = 4096;
        };
        localDoesNotShadowImport = {
          shapes = 8192;
          flips = 0;
          vc = 2304;
        };
      };
    };

    # ── U1c (den-hoag-gayc §3a): the intended answer changes, each against the retired surface ──

    # T4: c —P→ p —I→ c. The acyclic-path law drops the return to c; `queryAll` counted it again.
    test-U1c-T4-witnesses-drop-the-revisit = {
      expr = {
        witnesses = valuesOf (witnessesOf false x (t4 true) "c");
        retired = retired.queryAll { dataFilter = x; } (t4 true) "c";
        retiredWithoutTheImport = retired.queryAll { dataFilter = x; } (t4 false) "c";
      };
      expected = {
        witnesses = [
          "vc"
          "vp"
        ];
        retired = [
          "vc"
          "vp"
          "vc"
        ];
        retiredWithoutTheImport = [
          "vc"
          "vp"
        ];
      };
    };

    # T6: c —I→ m1 —I→ m2, transitive. The nearer declaration shadows the farther (`$ < imports`);
    # `query` refused the pair as an AMBIGUITY.
    test-U1c-T6-visible-takes-the-nearer-import = {
      expr = {
        visible =
          (S.resolve {
            wf = neronWf true;
            mode = "visible";
            inherit (S.neron) order;
            dataFilter = x;
            groupBy = _: "x";
          } t6 "c").single
            "x";
        retiredRefuses = throws (
          retired.query {
            dataFilter = x;
            transitiveImports = true;
          } t6 "c"
        );
        retiredAll = retired.queryAll {
          dataFilter = x;
          transitiveImports = true;
        } t6 "c";
      };
      expected = {
        visible = "v1";
        retiredRefuses = true;
        retiredAll = [
          "v1"
          "v2"
        ];
      };
    };

    # N2: c's parent is p, both import m. NR-Cons admits c·I·m and c·P·p·I·m; `queryAll`'s parent
    # recursion seeded `_seen` with c's imports and skipped the second.
    test-U1c-N2-the-diamond-answers-twice = {
      expr = {
        witnesses = valuesOf (witnessesOf false x diamond "c");
        retired = retired.queryAll { dataFilter = x; } diamond "c";
      };
      expected = {
        witnesses = [
          "vm"
          "vm"
        ];
        retired = [ "vm" ];
      };
    };

    # N2/D10 over the grid: distinct origins flip only true → false (one declaration reached several
    # ways); the witness-count reading, the control, flips both ways. The queryAll/witnesses split
    # is the gate's class count.
    test-U1c-N2-D10-ambiguous-over-distinct-origins = {
      expr = {
        nonTransitive = ambRead false;
        transitive = builtins.removeAttrs (ambRead true) [ "queryAllVersusWitnesses" ];
      };
      expected = {
        nonTransitive = {
          shapes = 8192;
          distinct = {
            trueToFalse = 768;
            falseToTrue = 0;
          };
          count = {
            trueToFalse = 368;
            falseToTrue = 96;
          };
          queryAllVersusWitnesses = {
            differ = 1590;
            moreInQueryAll = 1078;
            moreInWitnesses = 358;
            mixed = 154;
          };
        };
        transitive = {
          shapes = 8192;
          distinct = {
            trueToFalse = 1064;
            falseToTrue = 0;
          };
          count = {
            trueToFalse = 376;
            falseToTrue = 48;
          };
        };
      };
    };

    # The retired flags as stated orders: `imports` before `parent` answers the import; one rank for
    # both is I ∥ P, and `single` refuses the two origins. The retired `importShadowsParent = false`
    # was inert and answered the import regardless.
    test-U1c-flags-become-stated-orders = {
      expr = {
        importsFirst = visibleUnder S.neron.order flags "child";
        oneRank = throws (
          visibleUnder (S.labelOrder {
            alphabet = [
              "parent"
              "imports"
            ];
            layers = [
              [
                "imports"
                "parent"
              ]
            ];
            endOfPath = -1;
          }) flags "child"
        );
        retiredIspInert = retired.query {
          dataFilter = x;
          importShadowsParent = false;
        } flags "child";
      };
      expected = {
        importsFirst = "imported";
        oneRank = true;
        retiredIspInert = "imported";
      };
    };

    # `inherit'` over `resolve`: parity with the retired walk from every node of the grid's parent
    # maps, and a real parent cycle refused by name (D9).
    test-U1c-inherit-over-resolve-parity-and-cycle = {
      expr = inheritRead // {
        cycleRefused = throws (S."inherit'" { } x cyc "a");
        retiredCycleRefused = throws (retired."inherit'" { resolve = x; } cyc "a");
      };
      expected = {
        reads = 384;
        flips = 0;
        nulls = 138;
        answered = 246;
        cycleRefused = true;
        retiredCycleRefused = true;
      };
    };

    # ── U1d (den-hoag-gayc; ADR-0024 `direction`): the converse ──
    # O3: the retired `queryReverse`'s counting contract IS (NR-Cons) witnesses over the converse,
    # order included — read against the frozen reference on the spec's own fixture.
    test-U1d-O3-witnesses-over-the-converse-are-queryReverse = {
      expr =
        let
          ev = reverseScope (_: _: [ ]);
        in
        {
          order = ev.allNodeIds;
          direct = valuesOf (inbound "witnesses" [ "imports" ] "imports" ev "t").answers;
          transitive = valuesOf (inbound "witnesses" [ "imports" ] "imports imports*" ev "t").answers;
          retiredDirect = retired.queryReverse { dataFilter = x; } ev "t";
          retiredTransitive = retired.queryReverse {
            dataFilter = x;
            transitive = true;
          } ev "t";
          reachable = nodesOf (inbound "reachable" [ "imports" ] "imports*" ev "t");
        };
      expected = {
        order = [
          "t"
          "a"
          "b"
          "c"
        ];
        direct = [
          "a"
          "b"
        ];
        transitive = [
          "a"
          "c"
          "b"
          "c"
        ];
        retiredDirect = [
          "a"
          "b"
        ];
        retiredTransitive = [
          "a"
          "c"
          "b"
          "c"
        ];
        reachable = [
          "a"
          "b"
          "c"
          "t"
        ];
      };
    };
    # The marks are applied to the AUTHORED graph before the converse is taken. `c` shut: its
    # authored edges c —→ a and c —→ b are withheld, so `c` is never reached. `t` shut: its one
    # authored edge t —→ c is withheld, and the importers of `t` are reached as if unmarked — a
    # reading of the marks at the transposed source would shut every step out of `t` instead.
    test-U1d-marks-read-at-the-authored-source = {
      expr = {
        cShut = converseRead (reverseScope (shut "c")) "c";
        tShut = converseRead (reverseScope (shut "t")) "t";
      };
      expected = {
        cShut = {
          answers = [
            "a"
            "b"
          ];
          withheld =
            map
              (t: {
                label = "imports";
                target = t;
                marks = [ "shut" ];
              })
              [
                "a"
                "b"
              ];
        };
        tShut = {
          answers = [
            "a"
            "c"
            "b"
            "c"
          ];
          withheld = [
            {
              label = "imports";
              target = "c";
              marks = [ "shut" ];
            }
          ];
        };
      };
    };
    # `edges-l` has a converse as `imports` does; a letter the evaluation does not declare is
    # refused inbound as outbound (row 20).
    test-U1d-an-edge-letter-has-a-converse = {
      expr = {
        tack = valuesOf (inbound "witnesses" [ "tack" ] "tack" tacks "t").answers;
        undeclared = throws (inbound "reachable" [ "l1" ] "l1" tacks "t");
      };
      expected = {
        tack = [
          "a"
          "b"
        ];
        undeclared = true;
      };
    };
    # Containment's converse is `children`, a different relation: `parent` is refused in an inbound
    # alphabet, catchably, and the same alphabet walked outbound answers.
    test-U1d-parent-is-refused-in-an-inbound-alphabet = {
      expr = {
        inbound = throws (inbound "reachable" [ "parent" "imports" ] "parent* imports?" flags "child");
        outbound = nodesOf (run "reachable" [ "parent" "imports" ] "parent* imports?" flags "child");
      };
      expected = {
        inbound = true;
        outbound = [
          "child"
          "parent"
          "provider"
        ];
      };
    };

    # ── row 18: an edge read's own refusal propagates; the walk never catches it ──
    test-row18-an-edge-reads-refusal-propagates = {
      expr = {
        refused = throws (run "reachable" [ "boom" ] "boom" throwing "a");
        # The unplanted twin: the same read over an attribute that answers.
        twin = nodesOf (run "reachable" [ "boom" ] "boom?" quiet "a");
      };
      expected = {
        refused = true;
        twin = [ "a" ];
      };
    };

    # ── warm freshness: every route and the floor are recomputed, warm = cold ──
    test-warm-resolution-equals-cold = {
      expr = {
        warm = warmRead (warmOf [
          "imports"
          "edges-tack"
          "marks"
        ]);
        cold = warmRead warmCold;
      };
      expected =
        let
          read = {
            answers = warmNodes;
            withheld = [
              {
                label = "parent";
                target = "c";
                marks = [ "shut" ];
              }
            ];
          };
        in
        {
          warm = read;
          cold = read;
        };
    };

    # ── the refusal table: every plant refused catchably, every unplanted twin answers ──
    test-every-refusal-row-is-catchable-beside-an-answering-twin = {
      expr = builtins.mapAttrs (_: r: {
        plant = throws r.plant;
        twin = answers r.twin;
      }) refusals;
      expected = builtins.mapAttrs (_: _: {
        plant = true;
        twin = true;
      }) refusals;
    };

    # ── the constructor chain keys under H1 at 5,000 levels ──
    test-constructor-chain-5000-keys = {
      expr = builtins.stringLength (regex.stateKey (chain 5000));
      expected = 64;
    };

    # ── the engine is unpublished; the syntax is ──
    test-engine-unpublished-syntax-published = {
      expr = {
        engine = builtins.filter (n: S ? ${n}) [
          "deriv"
          "nullable"
          "stateKey"
          "parse"
          "parseWith"
          "markAttribute"
          "projected"
        ];
        syntax = builtins.attrNames S.wfl;
      };
      expected = {
        engine = [ ];
        syntax = [
          "alt"
          "any"
          "lit"
          "opt"
          "plus"
          "seq"
          "star"
        ];
      };
    };
  };
}
