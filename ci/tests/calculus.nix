# THE ONE RESOLUTION CALCULUS (`lib/calculus.nix`, den-hoag-gayc U1b) — the gating cells.
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

  # ── the neron = query grid (gate v1 grid2): every 3-node scope — acyclic parent map, import
  # subsets, declaration flags — read by today's `query` and by `neron` + visible + `single` ──
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
      today = verdict (try (S.query { localShadowsImport = lsi; } f ev "c"));
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
        structural = S.structural S.markAttribute;
        projected = S.projected S.markAttribute;
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
