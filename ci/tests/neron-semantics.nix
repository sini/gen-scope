# Neron (2015) and van Antwerpen (2018) resolution semantics tests.
# Covers: specificity ordering, well-formedness (P*I*), transitive imports,
# custom edge labels, scoped relations, subtypeOf, ambiguity detection.
{ lib, genScope, ... }:
let
  # Helper: build the scope record from the constructor
  mkRoots = args: genScope.buildRoots args;

  # Attributes that wire __edges.I as computed imports
  withImports =
    extra:
    {
      imports = _self: id: (_self.node id).decls.__edges.I or [ ];
      children = _self: _id: { };
    }
    // extra;

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
            importGraph = genScope.edge "consumer" "provider";
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
          result = genScope.eval {
            scope = roots;
            inherit attributes;
          };
        in
        genScope.query { dataFilter = n: n.decls.x or null; } result "consumer";
      expected = "local";
    };

    # D < I < P: import shadows parent
    test-import-shadows-parent = {
      expr =
        let
          roots = mkRoots {
            parentGraph = genScope.edge "child" "parent";
            importGraph = genScope.edge "child" "provider";
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
          result = genScope.eval {
            scope = roots;
            inherit attributes;
          };
        in
        genScope.query { dataFilter = n: n.decls.x or null; } result "child";
      expected = "imported";
    };

    # Override: importShadowsParent = false
    test-import-does-not-shadow-parent = {
      expr =
        let
          roots = mkRoots {
            parentGraph = genScope.edge "child" "parent";
            importGraph = genScope.edge "child" "provider";
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
          result = genScope.eval {
            scope = roots;
            inherit attributes;
          };
        in
        genScope.query {
          dataFilter = n: n.decls.x or null;
          importShadowsParent = false;
        } result "child";
      # When import doesn't shadow parent, local is still null, import is found
      # but doesn't shadow, so we check inherited — "inherited" wins
      expected = "imported"; # import found first (before parent walk)
    };

    # Override: localShadowsImport = false — local no longer takes priority,
    # so resolve skips the "local wins" branch and finds import instead.
    test-local-does-not-shadow-import = {
      expr =
        let
          roots = mkRoots {
            importGraph = genScope.edge "consumer" "provider";
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
          result = genScope.eval {
            scope = roots;
            inherit attributes;
          };
        in
        genScope.query {
          dataFilter = n: n.decls.x or null;
          localShadowsImport = false;
        } result "consumer";
      # With localShadowsImport = false: import is checked before local in priority
      expected = "imported";
    };

    # No local, no import: parent provides
    test-parent-provides-when-no-local-or-import = {
      expr =
        let
          roots = mkRoots {
            parentGraph = genScope.edge "child" "parent";
            decls = {
              parent = {
                x = "from-parent";
              };
              child = { };
            };
          };
          attributes = withImports { };
          result = genScope.eval {
            scope = roots;
            inherit attributes;
          };
        in
        genScope.query { dataFilter = n: n.decls.x or null; } result "child";
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
              (genScope.edge "a" "b")
              (genScope.edge "b" "c")
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
          result = genScope.eval {
            scope = roots;
            inherit attributes;
          };
        in
        genScope.query {
          dataFilter = n: n.decls.value or null;
          transitiveImports = true;
        } result "a";
      expected = "deep";
    };

    # Non-transitive (default): A imports B, B imports C. A cannot see C.
    test-non-transitive-default = {
      expr =
        let
          roots = mkRoots {
            importGraph = genScope.overlays [
              (genScope.edge "a" "b")
              (genScope.edge "b" "c")
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
          result = genScope.eval {
            scope = roots;
            inherit attributes;
          };
        in
        genScope.query {
          dataFilter = n: n.decls.value or null;
        } result "a";
      expected = null; # not reachable without transitive
    };

    # Import cycle prevention: A imports B, B imports A. No infinite loop.
    test-import-cycle-terminates = {
      expr =
        let
          roots = mkRoots {
            importGraph = genScope.overlays [
              (genScope.edge "a" "b")
              (genScope.edge "b" "a")
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
          result = genScope.eval {
            scope = roots;
            inherit attributes;
          };
        in
        genScope.query { dataFilter = n: n.decls.y or null; } result "a";
      expected = "from-b";
    };

    # P*I* well-formedness: after following import, cannot follow parent of imported scope
    test-wf-import-does-not-inherit-from-imported-parent = {
      expr =
        let
          roots = mkRoots {
            parentGraph = genScope.edge "provider" "provider-parent";
            importGraph = genScope.edge "consumer" "provider";
            decls = {
              consumer = { };
              provider = { };
              provider-parent = {
                secret = "should-not-see";
              };
            };
          };
          attributes = withImports { };
          result = genScope.eval {
            scope = roots;
            inherit attributes;
          };
          # consumer imports provider; provider's PARENT has "secret"
          # Under P*I* WF: once you follow I edge, you don't follow P from there
          # query with default settings does NOT walk provider's parent
        in
        genScope.query { dataFilter = n: n.decls.secret or null; } result "consumer";
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
              (genScope.edge "consumer" "providerA")
              (genScope.edge "consumer" "providerB")
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
          result = genScope.eval {
            scope = roots;
            inherit attributes;
          };
        in
        genScope.ambiguous { dataFilter = n: n.decls.x or null; } result "consumer";
      expected = true;
    };

    # Single provider — not ambiguous
    test-not-ambiguous-single-provider = {
      expr =
        let
          roots = mkRoots {
            importGraph = genScope.edge "consumer" "provider";
            decls = {
              consumer = { };
              provider = {
                x = 1;
              };
            };
          };
          attributes = withImports { };
          result = genScope.eval {
            scope = roots;
            inherit attributes;
          };
        in
        genScope.ambiguous { dataFilter = n: n.decls.x or null; } result "consumer";
      expected = false;
    };

    # Local declaration resolves ambiguity (shadows both imports)
    test-local-resolves-ambiguity = {
      expr =
        let
          roots = mkRoots {
            importGraph = genScope.overlays [
              (genScope.edge "consumer" "providerA")
              (genScope.edge "consumer" "providerB")
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
          result = genScope.eval {
            scope = roots;
            inherit attributes;
          };
          # With local shadowing, query returns local — ambiguity in imports is moot
        in
        genScope.query { dataFilter = n: n.decls.x or null; } result "consumer";
      expected = "local";
    };

    # ── A multi-candidate import set REFUSES BY NAME (Neron §2.2, Duplicate Declarations) ──
    #
    # `query` answers with a SINGLE declaration. It used to dispose of a larger candidate set
    # itself, dispatching on the runtime type of the first candidate: an attrset arm folded every
    # candidate together into a value that existed at no node, a list arm took the head and dropped
    # the rest. Both are gone.
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
              (genScope.edge "consumer" "providerA")
              (genScope.edge "consumer" "providerB")
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
          result = genScope.eval {
            scope = roots;
            attributes = withImports { };
          };
        in
        genScope.query { dataFilter = n: n.decls.x or null; } result "consumer"
      );
      expected = true;
    };

    test-two-distinct-declarations-refuse-attrset-arm = {
      expr = didRefuse (
        let
          roots = mkRoots {
            importGraph = genScope.overlays [
              (genScope.edge "consumer" "providerA")
              (genScope.edge "consumer" "providerB")
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
          result = genScope.eval {
            scope = roots;
            attributes = withImports { };
          };
        in
        genScope.query { dataFilter = n: n.decls.x or null; } result "consumer"
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
              (genScope.edge "consumer" "providerA")
              (genScope.edge "consumer" "providerB")
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
          result = genScope.eval {
            scope = roots;
            attributes = withImports { };
          };
        in
        genScope.query { dataFilter = n: n.decls.x or null; } result "consumer"
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
              (genScope.edge "consumer" "provider")
              (genScope.edge "consumer" "provider")
              (genScope.edge "consumer" "provider")
            ];
            decls = {
              consumer = { };
              provider = {
                x = [ "p" ];
              };
            };
          };
          result = genScope.eval {
            scope = roots;
            attributes = withImports { };
          };
        in
        genScope.query { dataFilter = n: n.decls.x or null; } result "consumer";
      expected = [ "p" ];
    };

    test-control-one-node-three-identical-edges-resolves-attrset-arm = {
      expr =
        let
          roots = mkRoots {
            importGraph = genScope.overlays [
              (genScope.edge "consumer" "provider")
              (genScope.edge "consumer" "provider")
              (genScope.edge "consumer" "provider")
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
          result = genScope.eval {
            scope = roots;
            attributes = withImports { };
          };
        in
        genScope.query { dataFilter = n: n.decls.x or null; } result "consumer";
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
            (genScope.edge "consumer" "provider")
            (genScope.edge "consumer" "provider")
            (genScope.edge "consumer" "provider")
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
    # The seen-imports machinery exists to make repeated routes TERMINATE (Neron §2.4, rule X), not
    # to multiply the answer. Attribution is what makes these resolve, and it is correct by
    # construction rather than by luck: the recursion maps the collector over the NEXT node's
    # imports, so a transitively-reached candidate carries the id of the node that DECLARED it and
    # never that of the direct import it was reached through. Both diamond routes therefore tag the
    # same declarer.

    test-control-a-diamond-reaching-one-declaration-resolves-list-arm = {
      expr =
        let
          roots = mkRoots {
            importGraph = genScope.overlays [
              (genScope.edge "r" "B")
              (genScope.edge "r" "C")
              (genScope.edge "B" "D")
              (genScope.edge "C" "D")
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
          result = genScope.eval {
            scope = roots;
            attributes = withImports { };
          };
        in
        genScope.query {
          dataFilter = n: n.decls.x or null;
          transitiveImports = true;
        } result "r";
      expected = [ "d" ];
    };

    test-control-a-diamond-reaching-one-declaration-resolves-attrset-arm = {
      expr =
        let
          roots = mkRoots {
            importGraph = genScope.overlays [
              (genScope.edge "r" "B")
              (genScope.edge "r" "C")
              (genScope.edge "B" "D")
              (genScope.edge "C" "D")
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
          result = genScope.eval {
            scope = roots;
            attributes = withImports { };
          };
        in
        genScope.query {
          dataFilter = n: n.decls.x or null;
          transitiveImports = true;
        } result "r";
      expected = {
        d = 1;
      };
    };

    # ★ THIS IS WHAT MAKES THE TWO DIAMOND CELLS MEAN SOMETHING. Add a second DECLARER on one route
    # of the same fixture and it refuses — so their non-refusal is the two routes collapsing onto
    # one occurrence, and not a fixture that failed to form two routes in the first place.
    test-a-diamond-with-a-second-declarer-on-one-route-refuses = {
      expr = didRefuse (
        let
          roots = mkRoots {
            importGraph = genScope.overlays [
              (genScope.edge "r" "B")
              (genScope.edge "r" "C")
              (genScope.edge "B" "D")
              (genScope.edge "C" "D")
            ];
            decls = {
              r = { };
              B = {
                x = [ "b" ];
              };
              C = { };
              D = {
                x = [ "d" ];
              };
            };
          };
          result = genScope.eval {
            scope = roots;
            attributes = withImports { };
          };
        in
        genScope.query {
          dataFilter = n: n.decls.x or null;
          transitiveImports = true;
        } result "r"
      );
      expected = true;
    };

    # Reconvergence rather than a diamond: `r` imports A directly AND reaches it through B.
    test-control-a-reconvergent-import-pair-reaching-one-declaration-resolves = {
      expr =
        let
          roots = mkRoots {
            importGraph = genScope.overlays [
              (genScope.edge "r" "A")
              (genScope.edge "r" "B")
              (genScope.edge "B" "A")
            ];
            decls = {
              r = { };
              A = {
                x = [ "a" ];
              };
              B = { };
            };
          };
          result = genScope.eval {
            scope = roots;
            attributes = withImports { };
          };
        in
        genScope.query {
          dataFilter = n: n.decls.x or null;
          transitiveImports = true;
        } result "r";
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
              (genScope.edge "r" "B")
              (genScope.edge "B" "D")
            ];
            decls = {
              r = { };
              B = { };
              D = {
                x = [ "d" ];
              };
            };
          };
          result = genScope.eval {
            scope = roots;
            attributes = withImports { };
          };
        in
        genScope.query {
          dataFilter = n: n.decls.x or null;
          transitiveImports = true;
        } result "r";
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
            genScope.eval {
              scope = mkRoots {
                importGraph = genScope.overlays [
                  (genScope.edge "consumer" "providerA")
                  (genScope.edge "consumer" "providerB")
                ];
                inherit decls;
              };
              attributes = withImports { };
            };
          read = decls: genScope.query { dataFilter = n: n.decls.x or null; } (mkResult decls) "consumer";
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
                graph = genScope.edge "record" "extension";
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
            children = _self: _id: { };
            "edges-R" = self: id: (self.node id).decls.__edges.R or [ ];
          };
          result = genScope.eval {
            scope = roots;
            inherit attributes;
          };
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
                  (genScope.edge "base" "ext1")
                  (genScope.edge "base" "ext2")
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
            children = _self: _id: { };
            "edges-R" = self: id: (self.node id).decls.__edges.R or [ ];
          };
          result = genScope.eval {
            scope = roots;
            inherit attributes;
          };
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
                graph = genScope.edge "a" "b";
              }
              {
                label = "E";
                graph = genScope.edge "a" "c";
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
            children = _self: _id: { };
            "edges-R" = self: id: (self.node id).decls.__edges.R or [ ];
            "edges-E" = self: id: (self.node id).decls.__edges.E or [ ];
          };
          result = genScope.eval {
            scope = roots;
            inherit attributes;
          };
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
          result = genScope.eval {
            scope = roots;
            inherit attributes;
          };
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
          result = genScope.eval {
            scope = roots;
            inherit attributes;
          };
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
          result = genScope.eval {
            scope = roots;
            inherit attributes;
          };
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
          result = genScope.eval {
            scope = roots;
            inherit attributes;
          };
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
          result = genScope.eval {
            scope = roots;
            inherit attributes;
          };
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
            parentGraph = genScope.edge "inner" "outer";
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
            types = self: id: (self.node id).decls.__relations.types or { };
            all-types = genScope.inherit' {
              resolve =
                n:
                let
                  t = n.decls.__relations.types or null;
                in
                t;
            };
          };
          result = genScope.eval {
            scope = roots;
            inherit attributes;
          };
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
