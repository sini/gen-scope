# Neron (2015) and van Antwerpen (2018) resolution semantics tests.
# Covers: specificity ordering, well-formedness (P*I*), transitive imports,
# custom edge labels, scoped relations, subtypeOf, ambiguity detection.
{ lib, genScope, ... }:
let
  # Helper: build the scope record from the constructor
  mkRoots = args: genScope.buildRoots args;

  # Attributes that wire __edges.I as computed imports, and state no boundary mark (the calculus
  # reads `marks` in every resolution; `[ ]` is the declaration of none).
  withImports =
    extra:
    {
      imports = _self: id: (_self.node id).decls.__edges.I or [ ];
      children = _self: _id: { };
      marks = _: _: [ ];
    }
    // extra;

  # The retired `query` and `ambiguous`, read through the one calculus (den-hoag-gayc U1c). Néron's
  # D < I < P is `neron` under mode "visible" with one competition group; `transitiveImports` is
  # the WFL `parent* imports*`; a retired shadowing flag is a stated `order`. An ambiguity is more
  # than one DISTINCT declaring node among the witnesses (D10).
  transitiveWf = genScope.wellFormed {
    alphabet = [
      "parent"
      "imports"
    ];
    expression = "parent* imports*";
  };
  visibleOf =
    {
      wf ? genScope.neron.wf,
      order ? genScope.neron.order,
    }:
    dataFilter: self: id:
    (genScope.resolve {
      inherit wf order dataFilter;
      mode = "visible";
      groupBy = _: "x";
    } self id).single
      "x";
  ambiguous =
    dataFilter: self: id:
    builtins.length (
      lib.unique (
        map (a: a.node)
          (genScope.resolve {
            inherit (genScope.neron) wf;
            inherit dataFilter;
            mode = "witnesses";
          } self id).answers
      )
    ) > 1;
  # An order over the Néron alphabet, `$` ranked by `endOfPath`.
  orderOf =
    layers: endOfPath:
    genScope.labelOrder {
      alphabet = [
        "parent"
        "imports"
      ];
      inherit layers endOfPath;
    };

  # A refusal here is a named `throw`, so `tryEval` observes it and the suite REPORTS rather than
  # dying — the property that separates this idiom from the anonymous attribute-missing abort.
  # `deepSeq` is what makes the observation reach a refusal that sits inside a value rather than at
  # it: an attrset answer survives WHNF with its refusing field unforced.
  didRefuse = e: !(builtins.tryEval (builtins.deepSeq e null)).success;
  resolves = e: (builtins.tryEval (builtins.deepSeq e null)).success;
in
{
  # === Specificity ordering (Neron 2015 §2.5, Fig. 2) ===

  flake.tests.specificity = {
    # D < I < P: local shadows import
    test-local-shadows-import = {
      expr =
        let
          roots = mkRoots {
            importGraph = genScope.edge {
              from = "consumer";
              to = "provider";
            };
            decls = {
              consumer = {
                x = "local";
              };
              provider = {
                x = "imported";
              };
            };
          };
          attributes = withImports { };
          result = genScope.eval { } attributes roots;
        in
        visibleOf { } (n: n.decls.x or null) result "consumer";
      expected = "local";
    };

    # D < I < P: import shadows parent
    test-import-shadows-parent = {
      expr =
        let
          roots = mkRoots {
            parentGraph = genScope.edge {
              from = "child";
              to = "parent";
            };
            importGraph = genScope.edge {
              from = "child";
              to = "provider";
            };
            decls = {
              parent = {
                x = "inherited";
              };
              provider = {
                x = "imported";
              };
              child = { };
            };
          };
          attributes = withImports { };
          result = genScope.eval { } attributes roots;
        in
        visibleOf { } (n: n.decls.x or null) result "child";
      expected = "imported";
    };

    # The retired `importShadowsParent = false` as the order its name states: `imports` and `parent`
    # share one rank (I ∥ P), so the import and the inherited value are two origins and `single`
    # refuses the AMBIGUITY. The retired flag was inert here and answered "imported" (den-hoag-gayc
    # U1c flag cells); `imports` before `parent` is `neron`, the cell above.
    test-import-does-not-shadow-parent = {
      expr = didRefuse (
        let
          roots = mkRoots {
            parentGraph = genScope.edge {
              from = "child";
              to = "parent";
            };
            importGraph = genScope.edge {
              from = "child";
              to = "provider";
            };
            decls = {
              parent = {
                x = "inherited";
              };
              provider = {
                x = "imported";
              };
              child = { };
            };
          };
          attributes = withImports { };
          result = genScope.eval { } attributes roots;
        in
        visibleOf {
          order = orderOf [
            [
              "imports"
              "parent"
            ]
          ] (-1);
        } (n: n.decls.x or null) result "child"
      );
      expected = true;
    };

    # Override: localShadowsImport = false — local no longer takes priority,
    # so resolve skips the "local wins" branch and finds import instead.
    test-local-does-not-shadow-import = {
      expr =
        let
          roots = mkRoots {
            importGraph = genScope.edge {
              from = "consumer";
              to = "provider";
            };
            decls = {
              consumer = {
                x = "local";
              };
              provider = {
                x = "imported";
              };
            };
          };
          attributes = withImports { };
          result = genScope.eval { } attributes roots;
        in
        visibleOf {
          order = orderOf [
            [ "imports" ]
            [ ]
            [ "parent" ]
          ] 1;
        } (n: n.decls.x or null) result "consumer";
      # With localShadowsImport = false: import is checked before local in priority
      expected = "imported";
    };

    # No local, no import: parent provides
    test-parent-provides-when-no-local-or-import = {
      expr =
        let
          roots = mkRoots {
            parentGraph = genScope.edge {
              from = "child";
              to = "parent";
            };
            decls = {
              parent = {
                x = "from-parent";
              };
              child = { };
            };
          };
          attributes = withImports { };
          result = genScope.eval { } attributes roots;
        in
        visibleOf { } (n: n.decls.x or null) result "child";
      expected = "from-parent";
    };
  };

  # === Well-formedness and transitive imports (Neron 2015 §2.4) ===

  flake.tests.wf-policy = {
    # Transitive imports: A imports B, B imports C. A can see C's decls.
    test-transitive-imports = {
      expr =
        let
          roots = mkRoots {
            importGraph = genScope.overlays [
              (genScope.edge {
                from = "a";
                to = "b";
              })
              (genScope.edge {
                from = "b";
                to = "c";
              })
            ];
            decls = {
              a = { };
              b = { };
              c = {
                value = "deep";
              };
            };
          };
          attributes = withImports { };
          result = genScope.eval { } attributes roots;
        in
        visibleOf { wf = transitiveWf; } (n: n.decls.value or null) result "a";
      expected = "deep";
    };

    # Non-transitive (default): A imports B, B imports C. A cannot see C.
    test-non-transitive-default = {
      expr =
        let
          roots = mkRoots {
            importGraph = genScope.overlays [
              (genScope.edge {
                from = "a";
                to = "b";
              })
              (genScope.edge {
                from = "b";
                to = "c";
              })
            ];
            decls = {
              a = { };
              b = { };
              c = {
                value = "deep";
              };
            };
          };
          attributes = withImports { };
          result = genScope.eval { } attributes roots;
        in
        visibleOf { } (n: n.decls.value or null) result "a";
      expected = null; # not reachable without transitive
    };

    # Import cycle prevention: A imports B, B imports A. No infinite loop.
    test-import-cycle-terminates = {
      expr =
        let
          roots = mkRoots {
            importGraph = genScope.overlays [
              (genScope.edge {
                from = "a";
                to = "b";
              })
              (genScope.edge {
                from = "b";
                to = "a";
              })
            ];
            decls = {
              a = {
                x = "from-a";
              };
              b = {
                y = "from-b";
              };
            };
          };
          attributes = withImports { };
          result = genScope.eval { } attributes roots;
        in
        visibleOf { } (n: n.decls.y or null) result "a";
      expected = "from-b";
    };

    # P*I* well-formedness: after following import, cannot follow parent of imported scope
    test-wf-import-does-not-inherit-from-imported-parent = {
      expr =
        let
          roots = mkRoots {
            parentGraph = genScope.edge {
              from = "provider";
              to = "provider-parent";
            };
            importGraph = genScope.edge {
              from = "consumer";
              to = "provider";
            };
            decls = {
              consumer = { };
              provider = { };
              provider-parent = {
                secret = "should-not-see";
              };
            };
          };
          attributes = withImports { };
          result = genScope.eval { } attributes roots;
          # consumer imports provider; provider's PARENT has "secret"
          # Under P*I* WF: once you follow I edge, you don't follow P from there
          # the default `neron` WFL (`parent* imports?`) does NOT walk provider's parent
        in
        visibleOf { } (n: n.decls.secret or null) result "consumer";
      expected = null;
    };
  };

  # === Ambiguity detection (van Antwerpen 2018 §2.3) ===

  flake.tests.ambiguity = {
    # Two imports provide the same declaration — ambiguous
    test-ambiguous-two-providers = {
      expr =
        let
          roots = mkRoots {
            importGraph = genScope.overlays [
              (genScope.edge {
                from = "consumer";
                to = "providerA";
              })
              (genScope.edge {
                from = "consumer";
                to = "providerB";
              })
            ];
            decls = {
              consumer = { };
              providerA = {
                x = 1;
              };
              providerB = {
                x = 2;
              };
            };
          };
          attributes = withImports { };
          result = genScope.eval { } attributes roots;
        in
        ambiguous (n: n.decls.x or null) result "consumer";
      expected = true;
    };

    # Single provider — not ambiguous
    test-not-ambiguous-single-provider = {
      expr =
        let
          roots = mkRoots {
            importGraph = genScope.edge {
              from = "consumer";
              to = "provider";
            };
            decls = {
              consumer = { };
              provider = {
                x = 1;
              };
            };
          };
          attributes = withImports { };
          result = genScope.eval { } attributes roots;
        in
        ambiguous (n: n.decls.x or null) result "consumer";
      expected = false;
    };

    # Local declaration resolves ambiguity (shadows both imports)
    test-local-resolves-ambiguity = {
      expr =
        let
          roots = mkRoots {
            importGraph = genScope.overlays [
              (genScope.edge {
                from = "consumer";
                to = "providerA";
              })
              (genScope.edge {
                from = "consumer";
                to = "providerB";
              })
            ];
            decls = {
              consumer = {
                x = "local";
              };
              providerA = {
                x = 1;
              };
              providerB = {
                x = 2;
              };
            };
          };
          attributes = withImports { };
          result = genScope.eval { } attributes roots;
          # With local shadowing, the local declaration is visible — ambiguity in imports is moot
        in
        visibleOf { } (n: n.decls.x or null) result "consumer";
      expected = "local";
    };

    # ── A multi-candidate import set REFUSES BY NAME (Neron §2.2, Duplicate Declarations) ──
    #
    # `single` answers with ONE declaration and refuses a minimal set holding two distinct origins.
    # The retired `query` once disposed of a larger candidate set itself, dispatching on the runtime
    # type of the first candidate: an attrset arm folded every candidate together into a value that
    # existed at no node, a list arm took the head and dropped the rest. Neither came back.
    #
    # ★★ THE REFUSAL CELLS AND THE IDENTICAL-EDGE CELLS ARE ONE INSTRUMENT AND ARE READ TOGETHER.
    # The refusals alone pass under a predicate spelled over candidate-list LENGTH; the
    # identical-edge cells alone pass under a construction that never refuses at all. Only the pair
    # pins the predicate where it belongs — on DISTINCT CONTRIBUTING NODES. Both are written in
    # both type arms, because the two disposal arms they retire were different code paths and a
    # cell in one arm says nothing about the other.

    test-two-distinct-declarations-refuse-list-arm = {
      expr = didRefuse (
        let
          roots = mkRoots {
            importGraph = genScope.overlays [
              (genScope.edge {
                from = "consumer";
                to = "providerA";
              })
              (genScope.edge {
                from = "consumer";
                to = "providerB";
              })
            ];
            decls = {
              consumer = { };
              providerA = {
                x = [ "a" ];
              };
              providerB = {
                x = [ "b" ];
              };
            };
          };
          result = genScope.eval { } (withImports { }) roots;
        in
        visibleOf { } (n: n.decls.x or null) result "consumer"
      );
      expected = true;
    };

    test-two-distinct-declarations-refuse-attrset-arm = {
      expr = didRefuse (
        let
          roots = mkRoots {
            importGraph = genScope.overlays [
              (genScope.edge {
                from = "consumer";
                to = "providerA";
              })
              (genScope.edge {
                from = "consumer";
                to = "providerB";
              })
            ];
            decls = {
              consumer = { };
              providerA = {
                x = {
                  a = 1;
                };
              };
              providerB = {
                x = {
                  b = 2;
                };
              };
            };
          };
          result = genScope.eval { } (withImports { }) roots;
        in
        visibleOf { } (n: n.decls.x or null) result "consumer"
      );
      expected = true;
    };

    # ★ Occurrence identity is POSITIONAL, and takes no account of what a declaration denotes
    # (Neron §2.2, "all occurrences b_i denote the same name b at different positions"). Two nodes
    # carrying equal values are still two occurrences. This is also why the predicate is not
    # spelled as value equality: that spelling would force candidate values deeply, where this one
    # reads ids the import filters have forced already.
    test-two-distinct-declarations-of-equal-value-still-refuse = {
      expr = didRefuse (
        let
          roots = mkRoots {
            importGraph = genScope.overlays [
              (genScope.edge {
                from = "consumer";
                to = "providerA";
              })
              (genScope.edge {
                from = "consumer";
                to = "providerB";
              })
            ];
            decls = {
              consumer = { };
              providerA = {
                x = [ "same" ];
              };
              providerB = {
                x = [ "same" ];
              };
            };
          };
          result = genScope.eval { } (withImports { }) roots;
        in
        visibleOf { } (n: n.decls.x or null) result "consumer"
      );
      expected = true;
    };

    # ★ THE CONTROL THAT PINS THE PREDICATE. One node reached along three identical edges is ONE
    # declaration reached three ways — three derivations of one judgement, not three declarations.
    # The `imports` relation is a multiset and does not deduplicate its edges, so this shape really
    # does deliver three candidates to the disposal; a length predicate would refuse it. It is a
    # live shape, not a hypothetical: nix-config's `dev` environment carries three identical
    # env:dev → env:prod edges.
    test-control-one-node-three-identical-edges-resolves-list-arm = {
      expr =
        let
          roots = mkRoots {
            importGraph = genScope.overlays [
              (genScope.edge {
                from = "consumer";
                to = "provider";
              })
              (genScope.edge {
                from = "consumer";
                to = "provider";
              })
              (genScope.edge {
                from = "consumer";
                to = "provider";
              })
            ];
            decls = {
              consumer = { };
              provider = {
                x = [ "p" ];
              };
            };
          };
          result = genScope.eval { } (withImports { }) roots;
        in
        visibleOf { } (n: n.decls.x or null) result "consumer";
      expected = [ "p" ];
    };

    test-control-one-node-three-identical-edges-resolves-attrset-arm = {
      expr =
        let
          roots = mkRoots {
            importGraph = genScope.overlays [
              (genScope.edge {
                from = "consumer";
                to = "provider";
              })
              (genScope.edge {
                from = "consumer";
                to = "provider";
              })
              (genScope.edge {
                from = "consumer";
                to = "provider";
              })
            ];
            decls = {
              consumer = { };
              provider = {
                x = {
                  p = 1;
                };
              };
            };
          };
          result = genScope.eval { } (withImports { }) roots;
        in
        visibleOf { } (n: n.decls.x or null) result "consumer";
      expected = {
        p = 1;
      };
    };

    # ★ THE PREMISE OF THE CELL ABOVE, ASSERTED RATHER THAN ASSUMED. If the graph layer ever begins
    # deduplicating import edges, the three-identical-edge cells stop delivering three candidates
    # and pass for a reason that has nothing to do with the predicate they exist to pin. This cell
    # reds when that happens.
    test-control-identical-import-edges-are-not-deduplicated = {
      expr =
        (mkRoots {
          importGraph = genScope.overlays [
            (genScope.edge {
              from = "consumer";
              to = "provider";
            })
            (genScope.edge {
              from = "consumer";
              to = "provider";
            })
            (genScope.edge {
              from = "consumer";
              to = "provider";
            })
          ];
          decls = {
            consumer = { };
            provider = {
              x = [ "p" ];
            };
          };
        }).nodes.consumer.decls.__edges.I;
      expected = [
        "provider"
        "provider"
        "provider"
      ];
    };

    # ── Diamonds and reconvergence: one declaration reached by several ROUTES ──
    #
    # Acyclic resolution paths (NR-Cons: a path never re-enters a scope it has already visited) make
    # repeated routes TERMINATE; they do not multiply the answer. Each route is its own witness, but
    # a witness carries the node that DECLARED it and never the direct import it was reached
    # through, so both diamond routes name the same origin and `single` sees one.

    test-control-a-diamond-reaching-one-declaration-resolves-list-arm = {
      expr =
        let
          roots = mkRoots {
            importGraph = genScope.overlays [
              (genScope.edge {
                from = "r";
                to = "B";
              })
              (genScope.edge {
                from = "r";
                to = "C";
              })
              (genScope.edge {
                from = "B";
                to = "D";
              })
              (genScope.edge {
                from = "C";
                to = "D";
              })
            ];
            decls = {
              r = { };
              B = { };
              C = { };
              D = {
                x = [ "d" ];
              };
            };
          };
          result = genScope.eval { } (withImports { }) roots;
        in
        visibleOf { wf = transitiveWf; } (n: n.decls.x or null) result "r";
      expected = [ "d" ];
    };

    test-control-a-diamond-reaching-one-declaration-resolves-attrset-arm = {
      expr =
        let
          roots = mkRoots {
            importGraph = genScope.overlays [
              (genScope.edge {
                from = "r";
                to = "B";
              })
              (genScope.edge {
                from = "r";
                to = "C";
              })
              (genScope.edge {
                from = "B";
                to = "D";
              })
              (genScope.edge {
                from = "C";
                to = "D";
              })
            ];
            decls = {
              r = { };
              B = { };
              C = { };
              D = {
                x = {
                  d = 1;
                };
              };
            };
          };
          result = genScope.eval { } (withImports { }) roots;
        in
        visibleOf { wf = transitiveWf; } (n: n.decls.x or null) result "r";
      expected = {
        d = 1;
      };
    };

    # ★ THIS IS WHAT MAKES THE TWO DIAMOND CELLS MEAN SOMETHING. Declare on BOTH routes at the same
    # depth and it refuses — so their non-refusal is the two routes collapsing onto one occurrence,
    # and not a fixture that failed to form two routes in the first place. A declarer on ONE route
    # only is nearer than `D` and shadows it (`$ < imports`, den-hoag-gayc T6); the retired `query`
    # refused that shape too, counting `B` and `D` as rivals.
    test-a-diamond-with-declarers-on-both-routes-refuses = {
      expr =
        let
          read =
            decls:
            visibleOf { wf = transitiveWf; } (n: n.decls.x or null) (genScope.eval { } (withImports { })
              (mkRoots {
                importGraph = genScope.overlays [
                  (genScope.edge {
                    from = "r";
                    to = "B";
                  })
                  (genScope.edge {
                    from = "r";
                    to = "C";
                  })
                  (genScope.edge {
                    from = "B";
                    to = "D";
                  })
                  (genScope.edge {
                    from = "C";
                    to = "D";
                  })
                ];
                inherit decls;
              })
            ) "r";
        in
        {
          bothRoutes = didRefuse (read {
            r = { };
            B.x = [ "b" ];
            C.x = [ "c" ];
            D.x = [ "d" ];
          });
          oneRoute = read {
            r = { };
            B.x = [ "b" ];
            C = { };
            D.x = [ "d" ];
          };
        };
      expected = {
        bothRoutes = true;
        oneRoute = [ "b" ];
      };
    };

    # Reconvergence rather than a diamond: `r` imports A directly AND reaches it through B.
    test-control-a-reconvergent-import-pair-reaching-one-declaration-resolves = {
      expr =
        let
          roots = mkRoots {
            importGraph = genScope.overlays [
              (genScope.edge {
                from = "r";
                to = "A";
              })
              (genScope.edge {
                from = "r";
                to = "B";
              })
              (genScope.edge {
                from = "B";
                to = "A";
              })
            ];
            decls = {
              r = { };
              A = {
                x = [ "a" ];
              };
              B = { };
            };
          };
          result = genScope.eval { } (withImports { }) roots;
        in
        visibleOf { wf = transitiveWf; } (n: n.decls.x or null) result "r";
      expected = [ "a" ];
    };

    # The degenerate route: one chain, one declarer. It shares the transitive machinery with the
    # cells above and refuses nothing, so a construction that refused on route count rather than on
    # declarer count would still have to pass this one.
    test-control-a-single-transitive-chain-resolves = {
      expr =
        let
          roots = mkRoots {
            importGraph = genScope.overlays [
              (genScope.edge {
                from = "r";
                to = "B";
              })
              (genScope.edge {
                from = "B";
                to = "D";
              })
            ];
            decls = {
              r = { };
              B = { };
              D = {
                x = [ "d" ];
              };
            };
          };
          result = genScope.eval { } (withImports { }) roots;
        in
        visibleOf { wf = transitiveWf; } (n: n.decls.x or null) result "r";
      expected = [ "d" ];
    };

    # ★ CATCHABILITY, AND ITS LIVE CONTROL IN THE SAME CELL. The refusal is a `throw`, so a caller
    # can hold it; and the single-declaration read on the same instrument still succeeds, so the
    # `false` above is the refusal firing rather than the instrument reporting failure at
    # everything. Spelled as `abort` or `assert`, the first field would escape `tryEval` and take
    # the suite down instead of failing this cell.
    test-control-the-refusal-is-catchable-and-a-single-declaration-still-reads = {
      expr =
        let
          mkResult =
            decls:
            genScope.eval { } (withImports { }) (mkRoots {
              importGraph = genScope.overlays [
                (genScope.edge {
                  from = "consumer";
                  to = "providerA";
                })
                (genScope.edge {
                  from = "consumer";
                  to = "providerB";
                })
              ];
              inherit decls;
            });
          read = decls: visibleOf { } (n: n.decls.x or null) (mkResult decls) "consumer";
        in
        {
          ambiguous = resolves (read {
            consumer = { };
            providerA = {
              x = [ "a" ];
            };
            providerB = {
              x = [ "b" ];
            };
          });
          single = resolves (read {
            consumer = { };
            providerA = {
              x = [ "a" ];
            };
            providerB = { };
          });
        };
      expected = {
        ambiguous = false;
        single = true;
      };
    };
  };

  # === Custom edge labels (van Antwerpen 2018 §2.1) ===

  flake.tests.custom-edges = {
    # followEdge traverses a custom label
    test-follow-custom-edge = {
      expr =
        let
          roots = mkRoots {
            edgeGraphs = [
              {
                label = "R";
                graph = genScope.edge {
                  from = "record";
                  to = "extension";
                };
              }
            ];
            decls = {
              record = {
                base = true;
              };
              extension = {
                extra = true;
              };
            };
          };
          attributes = {
            imports = _self: _id: [ ];
            marks = _self: _id: [ ];
            children = _self: _id: { };
            "edges-R" = self: id: (self.node id).decls.__edges.R or [ ];
          };
          result = genScope.eval { } attributes roots;
        in
        genScope.followEdge "R" result "record";
      expected = [ "extension" ];
    };

    # collectByLabel gathers data from custom edge targets
    test-collect-by-label = {
      expr =
        let
          roots = mkRoots {
            edgeGraphs = [
              {
                label = "R";
                graph = genScope.overlays [
                  (genScope.edge {
                    from = "base";
                    to = "ext1";
                  })
                  (genScope.edge {
                    from = "base";
                    to = "ext2";
                  })
                ];
              }
            ];
            decls = {
              base = { };
              ext1 = {
                field = "a";
              };
              ext2 = {
                field = "b";
              };
            };
          };
          attributes = {
            imports = _self: _id: [ ];
            marks = _self: _id: [ ];
            children = _self: _id: { };
            "edges-R" = self: id: (self.node id).decls.__edges.R or [ ];
          };
          result = genScope.eval { } attributes roots;
        in
        builtins.sort builtins.lessThan (
          genScope.collectByLabel "R" (
            self: id:
            let
              f = (self.node id).decls.field or null;
            in
            if f != null then [ f ] else [ ]
          ) result "base"
        );
      expected = [
        "a"
        "b"
      ];
    };

    # Multiple custom labels on same node
    test-multiple-custom-labels = {
      expr =
        let
          roots = mkRoots {
            edgeGraphs = [
              {
                label = "R";
                graph = genScope.edge {
                  from = "a";
                  to = "b";
                };
              }
              {
                label = "E";
                graph = genScope.edge {
                  from = "a";
                  to = "c";
                };
              }
            ];
            decls = {
              a = { };
              b = { };
              c = { };
            };
          };
          attributes = {
            imports = _self: _id: [ ];
            marks = _self: _id: [ ];
            children = _self: _id: { };
            "edges-R" = self: id: (self.node id).decls.__edges.R or [ ];
            "edges-E" = self: id: (self.node id).decls.__edges.E or [ ];
          };
          result = genScope.eval { } attributes roots;
        in
        {
          r = genScope.followEdge "R" result "a";
          e = genScope.followEdge "E" result "a";
        };
      expected = {
        r = [ "b" ];
        e = [ "c" ];
      };
    };
  };

  # === subtypeOf (van Antwerpen 2018 §2.3) ===

  flake.tests.subtype = {
    # A's decls are a subset of B's — A subtypes B
    test-subtype-subset = {
      expr =
        let
          roots = mkRoots {
            decls = {
              partial = {
                x = 1;
                y = 2;
              };
              full = {
                x = 1;
                y = 2;
                z = 3;
              };
            };
          };
          attributes = {
            imports = _self: _id: [ ];
            children = _self: _id: { };
          };
          result = genScope.eval { } attributes roots;
        in
        genScope.subtypeOf { } result "partial" "full";
      expected = true;
    };

    # A has a field B doesn't — not a subtype
    test-not-subtype-extra-field = {
      expr =
        let
          roots = mkRoots {
            decls = {
              extra = {
                x = 1;
                y = 2;
                z = 3;
              };
              base = {
                x = 1;
                y = 2;
              };
            };
          };
          attributes = {
            imports = _self: _id: [ ];
            children = _self: _id: { };
          };
          result = genScope.eval { } attributes roots;
        in
        genScope.subtypeOf { } result "extra" "base";
      expected = false;
    };

    # Custom equality check
    test-subtype-custom-eq = {
      expr =
        let
          roots = mkRoots {
            decls = {
              a = {
                x = 1;
              };
              b = {
                x = 2;
              };
            };
          };
          attributes = {
            imports = _self: _id: [ ];
            children = _self: _id: { };
          };
          result = genScope.eval { } attributes roots;
          # eq ignores values — only checks field existence
        in
        genScope.subtypeOf {
          eq =
            _k: _a: _b:
            true;
        } result "a" "b";
      expected = true;
    };

    # Empty decls subtypes everything
    test-empty-subtypes-all = {
      expr =
        let
          roots = mkRoots {
            decls = {
              empty = { };
              full = {
                x = 1;
                y = 2;
              };
            };
          };
          attributes = {
            imports = _self: _id: [ ];
            children = _self: _id: { };
          };
          result = genScope.eval { } attributes roots;
        in
        genScope.subtypeOf { } result "empty" "full";
      expected = true;
    };
  };

  # === Scoped relations as computed attributes ===

  flake.tests.relations = {
    # In the HOAG model, scoped relations are computed attributes.
    # A node can have multiple "namespaces" — each is a separate attribute.
    test-scoped-relations-via-attributes = {
      expr =
        let
          roots = mkRoots {
            decls = {
              module-a = {
                __relations = {
                  types = {
                    Int = "int";
                  };
                  values = {
                    x = 1;
                  };
                };
              };
            };
          };
          attributes = {
            imports = _self: _id: [ ];
            children = _self: _id: { };
            types = self: id: (self.node id).decls.__relations.types or { };
            values = self: id: (self.node id).decls.__relations.values or { };
          };
          result = genScope.eval { } attributes roots;
        in
        {
          types = result.get "module-a" "types";
          values = result.get "module-a" "values";
        };
      expected = {
        types = {
          Int = "int";
        };
        values = {
          x = 1;
        };
      };
    };

    # Relations inherited through parent chain
    test-relations-inherited = {
      expr =
        let
          roots = mkRoots {
            parentGraph = genScope.edge {
              from = "inner";
              to = "outer";
            };
            decls = {
              outer = {
                __relations = {
                  types = {
                    Int = "int";
                    Bool = "bool";
                  };
                };
              };
              inner = {
                __relations = {
                  types = {
                    String = "string";
                  };
                };
              };
            };
          };
          attributes = {
            imports = _self: _id: [ ];
            children = _self: _id: { };
            marks = _: _: [ ];
            types = self: id: (self.node id).decls.__relations.types or { };
            all-types = genScope.inherit' { } (
              n:
              let
                t = n.decls.__relations.types or null;
              in
              t
            );
          };
          result = genScope.eval { } attributes roots;
        in
        {
          # inner's own types
          inner-own = result.get "inner" "types";
          # inherited: first non-null in parent chain (inner has types, so returns inner's)
          inner-inherited = result.get "inner" "all-types";
          # outer's types
          outer-types = result.get "outer" "all-types";
        };
      expected = {
        inner-own = {
          String = "string";
        };
        inner-inherited = {
          String = "string";
        };
        outer-types = {
          Int = "int";
          Bool = "bool";
        };
      };
    };
  };
}
