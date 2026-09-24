# THE `nta` CHANNEL — Vogt, Swierstra & Kuiper 1989 Def. 3.14's recursive NTA, beside `spawns`.
#
# The value half of the Unit 1 acceptance cells (den-hoag-n6dh7 spec §3a, U1-a … U1-m, and the gate's
# K1–K3 and P-e); every refusal's MESSAGE is asserted in `tests-error.nix`'s `nta-refusals`, and the
# cycle price (U1-h) and the memo count (U1-i) are process exits in `tests-process.nix`. The fixture
# is shared: `_fixtures/nta.nix`.
{ genScope, ... }:
let
  fx = import ./_fixtures/nta.nix { inherit genScope; };
  inherit (genScope)
    mkKind
    mkKinds
    mintNtaId
    decodeNta
    ;
  ntaIds = ev: builtins.filter (i: decodeNta i != null) ev.allNodeIds;
  # Sorted: siblings enumerate in the codepoint order of their minted identifiers, which is not the
  # order of their keys.
  keysOf = ev: builtins.sort builtins.lessThan (map (i: (decodeNta i).key) (ntaIds ev));
  fails = v: !(builtins.tryEval (builtins.deepSeq v v)).success;

  # U1-k: one child per address into the host's COMPUTED definitions.
  addressed =
    at: def:
    fx.rawRun (
      _: _: {
        g.k = [
          {
            attr = "computed";
            inherit def at;
          }
        ];
      }
    );
  valueAt = at: def: (builtins.head ((addressed at def).node fx.child).decls.seed).value;

  u1d = fx.famRun;
in
{
  flake.tests.nta = {
    # ── U1-a · the surface ──
    test-U1a-a-kind-declaring-an-nta-registers = {
      expr = (mkKinds [ fx.tree ]).kinds.tree.nta ? sub;
      expected = true;
    };
    # `nta` adds no `below` entry: the self-`below` refusal stays the only same-kind door, and it
    # stays shut.
    test-U1a-nta-adds-no-below-entry = {
      expr = fx.tree.below;
      expected = [ ];
    };

    # ── U1-b · same-kind growth ──
    test-U1b-children-are-of-the-hosts-own-kind = {
      expr = map (i: (fx.threeLevels.node i).type) fx.threeLevels.allNodeIds;
      expected = [
        "tree"
        "tree"
        "tree"
        "tree"
      ];
    };
    test-U1b-allNodeIds-includes-the-nta-children = {
      expr = fx.threeLevels.allNodeIds;
      expected =
        let
          c1 = mintNtaId "r" "sub" "g" "k";
          c2 = mintNtaId c1 "sub" "g" "k";
        in
        [
          "r"
          c1
          c2
          (mintNtaId c2 "sub" "g" "k")
        ];
    };
    test-U1b-the-child-is-parented-on-its-host = {
      expr = (fx.threeLevels.node (mintNtaId "r" "sub" "g" "k")).parent;
      expected = "r";
    };

    # ── U1-c · a value-dependent key set moves with the value ──
    test-U1c-selector-alpha-beta = {
      expr = keysOf (
        fx.pickWith [
          "alpha"
          "beta"
        ]
      );
      expected = [
        "alpha"
        "beta"
      ];
    };
    test-U1c-selector-gamma = {
      expr = keysOf (fx.pickWith [ "gamma" ]);
      expected = [ "gamma" ];
    };

    # ── U1-d · interleaved families: group `second`'s key is group `first`'s child's value ──
    test-U1d-grouped-shape = {
      expr = builtins.mapAttrs (_: builtins.attrNames) (u1d.get "r" "nta-children").fam;
      expected = {
        first = [ "seed" ];
        second = [ "from-seed" ];
      };
    };
    test-U1d-the-second-family-child-resolves-by-id = {
      expr = u1d.get (mintNtaId "r" "fam" "second" "from-seed") "label";
      expected = "x";
    };
    test-U1d-both-families-enumerate = {
      expr = builtins.length (ntaIds u1d);
      expected = 2;
    };

    # ── U1-g · the identifier ──
    test-U1g-a-split-across-the-separator-is-two-identifiers = {
      expr = [
        (mintNtaId "h" "n" "a:1" "b" == mintNtaId "h" "n" "a" "1:b")
        (mintNtaId "h" "n" "a/b" "c" == mintNtaId "h" "n" "a" "b/c")
        (mintNtaId "h" "n1" "" "k" == mintNtaId "h" "n" "1" "k")
      ];
      expected = [
        false
        false
        false
      ];
    };
    test-U1g-decode-round-trips = {
      expr =
        let
          tuples = [
            {
              host = "r";
              name = "sub";
              group = "g";
              key = "k";
            }
            {
              host = mintNtaId "r" "sub" "g" "k";
              name = "n:4:";
              group = "";
              key = "12:x";
            }
          ];
        in
        map (t: decodeNta (mintNtaId t.host t.name t.group t.key) == t) tuples;
      expected = [
        true
        true
      ];
    };
    test-U1g-decode-answers-null-off-the-encoders-image = {
      expr = map decodeNta [
        "r"
        "a@b"
        "nta:"
        "nta:01:r3:sub1:g1:k"
        "nta:1:r3:sub1:g1:kX"
        "nta:9:r3:sub1:g1:k"
      ];
      expected = [
        null
        null
        null
        null
        null
        null
      ];
    };
    # The identifier is a function of the coordinates and never of the seed: two runs whose data
    # differ under the same shape mint the same identifiers.
    test-U1g-a-seed-change-leaves-the-identifiers-unmoved = {
      expr = (fx.treeWith { s.s = { }; }).allNodeIds == (fx.treeWith { s.s.z = 1; }).allNodeIds;
      expected = true;
    };
    test-U1g-control-a-shape-change-moves-them = {
      expr = (fx.treeWith { s.s = { }; }).allNodeIds == (fx.treeWith { s = { }; }).allNodeIds;
      expected = false;
    };

    # ── U1-i · the carriage is structural: a warm run never serves `nta-children` stale ──
    test-U1i-a-warm-run-reusing-nta-children-answers-the-current-key-set = {
      expr =
        let
          prior = fx.pickWith [
            "alpha"
            "beta"
          ];
          warm = genScope.evalWarm {
            scope = fx.pickScope [ "gamma" ];
            attributes = fx.attributes;
            inherit prior;
            decision = genScope.mkDecision {
              isClean = _: true;
              reusable = _: [ "nta-children" ];
            };
          };
        in
        builtins.attrNames (warm.get "r" "nta-children").hosts.hosts;
      expected = [ "gamma" ];
    };
    test-U1i-nta-children-is-structural = {
      expr = genScope.structural "nta-children";
      expected = true;
    };

    # ── U1-k · an address admits a sub-value of an EVALUATED definition ──
    test-U1k-data-function-computed-and-index-definitions = {
      expr = [
        (valueAt [ "value" "s" ] 0).x
        (valueAt [ "value" "s" ] 1).x
        (valueAt [ "value" "s" ] 2).x
        (valueAt [ "value" "l" 0 ] 3).x
      ];
      expected = [
        1
        2
        4
        5
      ];
    };
    # K3 — a PRESENT path whose value is null is found, not refused as absent.
    test-K3-a-present-null-is-admitted = {
      expr = valueAt [ "value" "s" ] 4;
      expected = null;
    };
    test-K3-control-an-absent-path-is-refused = {
      expr = fails (valueAt [ "value" "t" ] 4);
      expected = true;
    };
    # The seed keeps its address beside its value, so the definition it came from is reachable.
    test-P-c-the-seed-element-keeps-its-address = {
      expr = (builtins.head ((addressed [ "value" "s" ] 0).node fx.child).decls.seed).address;
      expected = {
        attr = "computed";
        def = 0;
        at = [
          "value"
          "s"
        ];
      };
    };

    # ── U1-l · a constant seed is refused; each refusal is catchable ──
    test-U1l-every-seed-refusal-is-catchable = {
      expr = map (s: fails (fx.seedOfChild (fx.seeded s))) [
        { x = 7; }
        [ { x = 7; } ]
        [
          {
            attr = "defs";
            def = "0";
            at = [ "s" ];
          }
        ]
        [ (fx.addr 0 [ ]) ]
        [ (fx.addr 0 [ "absent" ]) ]
      ];
      expected = [
        true
        true
        true
        true
        true
      ];
    };
    test-U1l-control-a-well-formed-address-is-admitted = {
      expr = map (e: e.value) (fx.seedOfChild (fx.seeded [ (fx.addr 0 [ "s" ]) ]));
      expected = [ { } ];
    };

    # ── U1-m · each step descends; well-founded data terminates ──
    test-U1m-three-levels-of-data-give-four-tree-nodes = {
      expr = builtins.length fx.threeLevels.allNodeIds;
      expected = 4;
    };

    # ── P-e · enumeration forces no seed ──
    test-Pe-a-child-with-a-malformed-seed-is-still-enumerated = {
      expr = builtins.elem fx.child (fx.seeded { x = 7; }).allNodeIds;
      expected = true;
    };

    # ── K1 · `decls` stays an attribute set, so the published `subtypeOf` answers over a child ──
    test-K1-subtypeOf-over-an-nta-child-answers = {
      expr =
        let
          c = mintNtaId "r" "sub" "g" "k";
        in
        [
          (genScope.subtypeOf { } fx.threeLevels c c)
          (genScope.subtypeOf { } fx.threeLevels "r" c)
        ];
      expected = [
        true
        false
      ];
    };

    # ── K2 · the debug evaluator resolves an `nta` child by id before `parseParent` ──
    test-K2-evalDebug-resolves-an-nta-child-by-id = {
      expr =
        let
          c = mintNtaId "r" "sub" "g" "k";
          dbg = genScope.evalDebug {
            scope = fx.scopeOf (mkKinds [ fx.tree ]) (fx.root "tree" { defs = [ { s.s = { }; } ]; });
            attributes = fx.attributes;
            inherit (genScope) parseParent;
          };
        in
        [
          (dbg.node c).id
          (builtins.length (dbg.get c "defs"))
        ];
      expected = [
        (mintNtaId "r" "sub" "g" "k")
        1
      ];
    };

    # ── the projection reads the flattened carriage ──
    test-structuralEdges-reach-the-nta-child = {
      expr = fx.threeLevels.structuralEdges "r";
      expected = [ (mintNtaId "r" "sub" "g" "k") ];
    };
    test-projectionFindings-are-empty-over-the-nta-carriage = {
      expr = fx.threeLevels.projectionFindings "r";
      expected = [ ];
    };
  };
}
