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
          c1 = mintNtaId {
            host = "r";
            name = "sub";
            group = "g";
            key = "k";
          };
          c2 = mintNtaId {
            host = c1;
            name = "sub";
            group = "g";
            key = "k";
          };
        in
        [
          "r"
          c1
          c2
          (mintNtaId {
            host = c2;
            name = "sub";
            group = "g";
            key = "k";
          })
        ];
    };
    test-U1b-the-child-is-parented-on-its-host = {
      expr =
        (fx.threeLevels.node (mintNtaId {
          host = "r";
          name = "sub";
          group = "g";
          key = "k";
        })).parent;
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
      expr = u1d.get (mintNtaId {
        host = "r";
        name = "fam";
        group = "second";
        key = "from-seed";
      }) "label";
      expected = "x";
    };
    test-U1d-both-families-enumerate = {
      expr = builtins.length (ntaIds u1d);
      expected = 2;
    };

    # ── U1-g · the identifier ──
    test-U1g-a-split-across-the-separator-is-two-identifiers = {
      expr = [
        (
          mintNtaId {
            host = "h";
            name = "n";
            group = "a:1";
            key = "b";
          } == mintNtaId {
            host = "h";
            name = "n";
            group = "a";
            key = "1:b";
          }
        )
        (
          mintNtaId {
            host = "h";
            name = "n";
            group = "a/b";
            key = "c";
          } == mintNtaId {
            host = "h";
            name = "n";
            group = "a";
            key = "b/c";
          }
        )
        (
          mintNtaId {
            host = "h";
            name = "n1";
            group = "";
            key = "k";
          } == mintNtaId {
            host = "h";
            name = "n";
            group = "1";
            key = "k";
          }
        )
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
              host = mintNtaId {
                host = "r";
                name = "sub";
                group = "g";
                key = "k";
              };
              name = "n:4:";
              group = "";
              key = "12:x";
            }
          ];
        in
        map (
          t:
          decodeNta (mintNtaId {
            host = t.host;
            name = t.name;
            group = t.group;
            key = t.key;
          }) == t
        ) tuples;
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
          warm = genScope.evalWarm { } {
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
          c = mintNtaId {
            host = "r";
            name = "sub";
            group = "g";
            key = "k";
          };
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
          c = mintNtaId {
            host = "r";
            name = "sub";
            group = "g";
            key = "k";
          };
          dbg = genScope.evalDebug {
            inherit (genScope) parseParent;
          } fx.attributes (fx.scopeOf (mkKinds [ fx.tree ]) (fx.root "tree" { defs = [ { s.s = { }; } ]; }));
        in
        [
          (dbg.node c).id
          (builtins.length (dbg.get c "defs"))
        ];
      expected = [
        (mintNtaId {
          host = "r";
          name = "sub";
          group = "g";
          key = "k";
        })
        1
      ];
    };

    # ── the projection reads the flattened carriage ──
    test-structuralEdges-reach-the-nta-child = {
      expr = fx.threeLevels.structuralEdges "r";
      expected = [
        (mintNtaId {
          host = "r";
          name = "sub";
          group = "g";
          key = "k";
        })
      ];
    };
    test-projectionFindings-are-empty-over-the-nta-carriage = {
      expr = fx.threeLevels.projectionFindings "r";
      expected = [ ];
    };

    # ── U2.0 · a host reads its own children through `getNta` (den-hoag-n6dh7 Unit 2.0) ──
    # The read goes through the host's own product and the child's record; the refusals are
    # `tests-error.nix`'s `nta-getNta-refusals`, and one evaluation per node is U2.0-c in
    # `tests-process.nix`.
    test-U20-a-host-reads-its-childs-attribute = {
      expr =
        (fx.nestWith genScope.eval { readB = self: _: self.getNta "sub" "g" "b" "v"; }).get "r"
          "readB";
      expected = 2;
    };
    # Depth 2: the child is itself a host and reads its grandchild inside its own body.
    test-U20-a-child-reads-its-grandchild = {
      expr =
        (fx.nestWith genScope.eval {
          readK = self: _: self.getNta "sub" "g" "k" "v";
          readAK = self: _: self.getNta "sub" "g" "a" "readK";
        }).get
          "r"
          "readAK";
      expected = 3;
    };
    # The record read and the read by identifier answer one value.
    test-U20-the-record-read-agrees-with-the-read-by-id = {
      expr =
        let
          ev = fx.nestWith genScope.eval { readB = self: _: self.getNta "sub" "g" "b" "v"; };
        in
        [
          (ev.get "r" "readB")
          (ev.get (mintNtaId {
            host = "r";
            name = "sub";
            group = "g";
            key = "b";
          }) "v")
        ];
      expected = [
        2
        2
      ];
    };
    # The debug evaluator's reader carries it too.
    test-U20-evalDebug-reads-through-getNta = {
      expr =
        (fx.nestWith genScope.evalDebug { readB = self: _: self.getNta "sub" "g" "b" "v"; }).get "r"
          "readB";
      expected = 2;
    };
    # Both evaluators' `getNta` agree, at both depths measured above: the debug accessor's route
    # (item 4) is a different implementation of the same property, not a different value.
    test-U20-evalDebug-agrees-with-eval-on-getNta = {
      expr =
        let
          extra = {
            readB = self: _: self.getNta "sub" "g" "b" "v";
            readK = self: _: self.getNta "sub" "g" "k" "v";
            readAK = self: _: self.getNta "sub" "g" "a" "readK";
          };
        in
        [
          ((fx.nestWith genScope.eval extra).get "r" "readB")
          ((fx.nestWith genScope.evalDebug extra).get "r" "readB")
          ((fx.nestWith genScope.eval extra).get "r" "readAK")
          ((fx.nestWith genScope.evalDebug extra).get "r" "readAK")
        ];
      expected = [
        2
        2
        3
        3
      ];
    };
    # Inside an open round the co-located cache refuses by its lifetime rule, so the read runs the
    # guarded per-attribute evaluator: a circular step demanding a body that reads through
    # `getNta` converges on the child's value.
    test-U20-getNta-answers-inside-an-open-round = {
      expr =
        (fx.nestWith genScope.eval {
          readB = self: _: self.getNta "sub" "g" "b" "v";
          ring =
            genScope.circular
              {
                carrier = {
                  bottom = 0;
                  leq = a: b: a <= b;
                  height = 3;
                  quotient = false;
                };
              }
              (
                self: id: _:
                self.get id "readB"
              );
        }).get
          "r"
          "ring";
      expected = 2;
    };

    # ── U2.0′ · a child reads its HOST's equation at its own coordinates (den-hoag-n6dh7 U2.0′) ──
    # `self.getHostAt a` on an `nta` child's reader answers `(host's a).${name}.${group}.${key}`. One
    # parity cell per entry path — through the host's `getNta`, and by the child's identifier — each
    # at depth 1 and at depth 2 (the host is itself an `nta` child), `eval` against `evalDebug`. The
    # refusals are `tests-error.nix`'s `nta-getHostAt-refusals`; one evaluation of the host
    # attribute is U2.0-f in `tests-process.nix`.
    test-U20p-evalDebug-agrees-with-eval-through-getNta =
      let
        extra = {
          inherit (fx) pos;
          hp = self: _: self.getHostAt "pos";
          readB = self: _: self.getNta "sub" "g" "b" "hp";
          readK = self: _: self.getNta "sub" "g" "k" "hp";
          readAK = self: _: self.getNta "sub" "g" "a" "readK";
        };
        reads = ev: [
          (ev.get "r" "readB")
          (ev.get "r" "readAK")
        ];
      in
      {
        expr = [
          (reads (fx.nestWith genScope.eval extra))
          (reads (fx.nestWith genScope.evalDebug extra))
        ];
        expected = [
          [
            "r/b"
            "${
              mintNtaId {
                host = "r";
                name = "sub";
                group = "g";
                key = "a";
              }
            }/k"
          ]
          [
            "r/b"
            "${
              mintNtaId {
                host = "r";
                name = "sub";
                group = "g";
                key = "a";
              }
            }/k"
          ]
        ];
      };
    test-U20p-evalDebug-agrees-with-eval-by-id =
      let
        extra = {
          inherit (fx) pos;
          hp = self: _: self.getHostAt "pos";
        };
        reads = ev: [
          (ev.get (mintNtaId {
            host = "r";
            name = "sub";
            group = "g";
            key = "b";
          }) "hp")
          (ev.get (mintNtaId {
            host = (
              mintNtaId {
                host = "r";
                name = "sub";
                group = "g";
                key = "a";
              }
            );
            name = "sub";
            group = "g";
            key = "k";
          }) "hp")
        ];
      in
      {
        expr = [
          (reads (fx.nestWith genScope.eval extra))
          (reads (fx.nestWith genScope.evalDebug extra))
        ];
        expected = [
          [
            "r/b"
            "${
              mintNtaId {
                host = "r";
                name = "sub";
                group = "g";
                key = "a";
              }
            }/k"
          ]
          [
            "r/b"
            "${
              mintNtaId {
                host = "r";
                name = "sub";
                group = "g";
                key = "a";
              }
            }/k"
          ]
        ];
      };
  };
}
