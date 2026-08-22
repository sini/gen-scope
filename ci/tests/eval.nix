{ lib, genScope, ... }:
let
  # A FLAT kind vocabulary: names, and no order between them, so no kind expands into another.
  # These fixtures declare types and never spawn, which is exactly what an empty `below` says.
  flatKinds = names: genScope.mkKinds (map (name: genScope.mkKind { inherit name; }) names);

  # Minimal graph: two roots, a and b
  roots = genScope.buildRoots {
    kinds = flatKinds [
      "host"
      "user"
    ];
    parentGraph = genScope.edge "child" "parent";
    importGraph = genScope.empty;
    decls = {
      parent = {
        x = 1;
        y = 2;
      };
      child = {
        x = 10;
      };
    };
    types = {
      parent = "host";
      child = "user";
    };
  };

  result = genScope.eval {
    scope = roots;
    attributes = {
      children =
        self: id:
        let
          node = self.node id;
        in
        lib.filterAttrs (_: n: n.parent == id) roots.nodes;
      imports = self: id: [ ];
      greeting = self: id: "hello-${id}";
      declX = self: id: (self.node id).decls.x or 0;
    };
    parseParent =
      id:
      let
        node = roots.nodes.${id} or null;
      in
      if node != null then node.parent else null;
  };

  # Single root, no children
  singleRoots = genScope.buildRoots {
    kinds = flatKinds [ "host" ];
    parentGraph = genScope.vertex "solo";
    importGraph = genScope.empty;
    decls = {
      solo = {
        val = 42;
      };
    };
    types = {
      solo = "host";
    };
  };

  singleResult = genScope.eval {
    scope = singleRoots;
    attributes = {
      children = self: id: { };
      imports = self: id: [ ];
      value = self: id: (self.node id).decls.val or 0;
    };
  };
in
{
  flake.tests."eval" = {
    test-node-returns-root = {
      expr = (result.node "parent").id;
      expected = "parent";
    };

    test-node-returns-child = {
      expr = (result.node "child").id;
      expected = "child";
    };

    test-node-type = {
      expr = (result.node "parent").type;
      expected = "host";
    };

    test-node-decls = {
      expr = (result.node "parent").decls.x;
      expected = 1;
    };

    test-get-custom-attr = {
      expr = result.get "parent" "greeting";
      expected = "hello-parent";
    };

    test-get-custom-attr-child = {
      expr = result.get "child" "greeting";
      expected = "hello-child";
    };

    test-get-declX-parent = {
      expr = result.get "parent" "declX";
      expected = 1;
    };

    test-get-declX-child = {
      expr = result.get "child" "declX";
      expected = 10;
    };

    test-children-of-parent = {
      expr = builtins.attrNames (result.get "parent" "children");
      expected = [ "child" ];
    };

    test-children-of-child = {
      expr = builtins.attrNames (result.get "child" "children");
      expected = [ ];
    };

    test-allNodes-keys = {
      expr = builtins.sort builtins.lessThan (builtins.attrNames result.allNodes);
      expected = [
        "child"
        "parent"
      ];
    };

    # `allNodeIds` is `allNodes`' key set in MATERIALIZATION order. Here the walk reaches
    # `child` twice — once as a root in its own right, once by descending from `parent` —
    # and the repeat is dropped first-occurrence-wins, the same rule `listToAttrs` applies
    # when it builds `allNodes`. `buildRoots` makes every vertex a root, so this repeat is
    # the ordinary case rather than a contrived one.
    test-allNodeIds-dedups-repeat-visit = {
      expr = result.allNodeIds;
      expected = [
        "child"
        "parent"
      ];
    };

    # The set invariant that lets a consumer swap one enumeration for the other.
    test-allNodeIds-is-allNodes-key-set = {
      expr = builtins.sort builtins.lessThan result.allNodeIds == builtins.attrNames result.allNodes;
      expected = true;
    };

    test-single-root-allNodeIds = {
      expr = singleResult.allNodeIds;
      expected = [ "solo" ];
    };

    test-single-root-value = {
      expr = singleResult.get "solo" "value";
      expected = 42;
    };

    test-single-root-allNodes = {
      expr = builtins.attrNames singleResult.allNodes;
      expected = [ "solo" ];
    };

    test-unknown-attr-throws = {
      expr = builtins.tryEval (result.get "parent" "nonexistent");
      expected = {
        success = false;
        value = false;
      };
    };

    test-unreachable-node-throws = {
      expr = builtins.tryEval (result.node "ghost");
      expected = {
        success = false;
        value = false;
      };
    };

    # --- Tier 2 selective materialization ---

    test-subtreeOf = {
      expr =
        let
          roots = {
            "env:prod" = {
              id = "env:prod";
              type = "env";
              parent = null;
              decls = {
                hosts = [ "web" ];
              };
            };
            "env:dev" = {
              id = "env:dev";
              type = "env";
              parent = null;
              decls = {
                hosts = [ "dev-1" ];
              };
            };
          };
          attributes = {
            children =
              self: id:
              let
                n = self.node id;
              in
              lib.listToAttrs (
                map (h: {
                  name = "host:${h}@${id}";
                  value = {
                    id = "host:${h}@${id}";
                    type = "host";
                    parent = id;
                    decls = { };
                  };
                }) (n.decls.hosts or [ ])
              );
          };
          parseParent =
            id:
            let
              parts = lib.splitString "@" id;
            in
            if builtins.length parts > 1 then lib.concatStringsSep "@" (lib.drop 1 parts) else null;
          result = genScope.eval {
            scope = {
              nodes = roots;
              # A hand-built scope states its own order at the site.
              nodeOrder = builtins.attrNames roots;
            };
            inherit attributes parseParent;
          };
        in
        builtins.sort builtins.lessThan (builtins.attrNames (result.subtreeOf "env:prod"));
      expected = [
        "env:prod"
        "host:web@env:prod"
      ];
    };

    test-nodesOfType = {
      expr =
        let
          roots = {
            "env:prod" = {
              id = "env:prod";
              type = "env";
              parent = null;
              decls = {
                hosts = [
                  "web"
                  "db"
                ];
              };
            };
          };
          attributes = {
            children =
              self: id:
              let
                n = self.node id;
              in
              lib.listToAttrs (
                map (h: {
                  name = "host:${h}@${id}";
                  value = {
                    id = "host:${h}@${id}";
                    type = "host";
                    parent = id;
                    decls = { };
                  };
                }) (n.decls.hosts or [ ])
              );
          };
          parseParent =
            id:
            let
              parts = lib.splitString "@" id;
            in
            if builtins.length parts > 1 then lib.concatStringsSep "@" (lib.drop 1 parts) else null;
          result = genScope.eval {
            scope = {
              nodes = roots;
              # A hand-built scope states its own order at the site.
              nodeOrder = builtins.attrNames roots;
            };
            inherit attributes parseParent;
          };
        in
        builtins.sort builtins.lessThan (builtins.attrNames (result.nodesOfType "host"));
      expected = [
        "host:db@env:prod"
        "host:web@env:prod"
      ];
    };

    test-allNodesWhere = {
      expr =
        let
          roots = {
            "env:prod" = {
              id = "env:prod";
              type = "env";
              parent = null;
              decls = {
                hosts = [ "web" ];
                secure = true;
              };
            };
            "env:dev" = {
              id = "env:dev";
              type = "env";
              parent = null;
              decls = {
                hosts = [ "dev-1" ];
                secure = false;
              };
            };
          };
          attributes = {
            children =
              self: id:
              let
                n = self.node id;
              in
              lib.listToAttrs (
                map (h: {
                  name = "host:${h}@${id}";
                  value = {
                    id = "host:${h}@${id}";
                    type = "host";
                    parent = id;
                    decls = {
                      secure = n.decls.secure or false;
                    };
                  };
                }) (n.decls.hosts or [ ])
              );
          };
          parseParent =
            id:
            let
              parts = lib.splitString "@" id;
            in
            if builtins.length parts > 1 then lib.concatStringsSep "@" (lib.drop 1 parts) else null;
          result = genScope.eval {
            scope = {
              nodes = roots;
              # A hand-built scope states its own order at the site.
              nodeOrder = builtins.attrNames roots;
            };
            inherit attributes parseParent;
          };
        in
        builtins.sort builtins.lessThan (
          builtins.attrNames (result.allNodesWhere (n: n.decls.secure or false))
        );
      expected = [
        "env:prod"
        "host:web@env:prod"
      ];
    };
  };

  # appended inside the same `{ ... }` the module returns, as a sibling of flake.tests."eval"
  #
  # The prior is an EVALUATION, not a result map: every "cached" value below is produced by a
  # second `eval` over the same program, read through its accessor. Membership in a snapshot is
  # gone — what an attribute may be reused for is now the decision's `reusable`.
  flake.tests."eval-warm" =
    let
      mkRoots =
        decls:
        let
          nodes = lib.mapAttrs (id: d: {
            inherit id;
            type = "t";
            parent = null;
            decls = d;
          }) decls;
        in
        {
          inherit nodes;
          # A hand-built scope has no constructor to carry an order, so it states one here.
          nodeOrder = builtins.attrNames nodes;
        };
      poison = {
        children = self: id: { };
        boom = self: id: throw "boom-${id}";
        val = self: id: (self.node id).decls.v or 0;
      };
      # The same program, evaluated with attribute functions that answer with the prior values.
      priorOf =
        roots: attributes:
        genScope.eval {
          scope = roots;
          inherit attributes;
        };
      allClean =
        names:
        genScope.mkDecision {
          isClean = _: true;
          reusable = _: names;
        };
      nRoots = mkRoots {
        n = {
          v = 5;
        };
      };
    in
    {
      # clean + named reusable ⇒ served from the prior, fn NEVER forced (poison doesn't throw)
      test-warm-serves-clean-no-force = {
        expr =
          (genScope.evalWarm {
            scope = nRoots;
            attributes = poison;
            prior = priorOf nRoots (poison // { boom = self: id: "cached"; });
            decision = allClean [ "boom" ];
          }).get
            "n"
            "boom";
        expected = "cached";
      };
      # dirty ⇒ recompute ⇒ poison fn runs ⇒ throws
      test-dirty-recomputes = {
        expr =
          (builtins.tryEval (
            (genScope.evalWarm {
              scope = nRoots;
              attributes = poison;
              prior = priorOf nRoots (poison // { boom = self: id: "cached"; });
              decision = genScope.mkDecision {
                isClean = _: false;
                reusable = _: [ "boom" ];
              };
            }).get
              "n"
              "boom"
          )).success;
        expected = false;
      };
      # clean but the decision does not name the attribute ⇒ falls through to fn ⇒ throws
      test-warm-missing-attr-falls-through = {
        expr =
          (builtins.tryEval (
            (genScope.evalWarm {
              scope = nRoots;
              attributes = poison;
              prior = priorOf nRoots (poison // { boom = self: id: "cached"; });
              decision = allClean [ ];
            }).get
              "n"
              "boom"
          )).success;
        expected = false;
      };
      # the prior's value is served verbatim (not the fresh computation)
      test-warm-serves-prior-value = {
        expr =
          (genScope.evalWarm {
            scope = nRoots;
            attributes = poison;
            prior = priorOf nRoots (poison // { val = self: id: 99; });
            decision = allClean [ "val" ];
          }).get
            "n"
            "val";
        expected = 99;
      };
      # a dirty node reads a clean dep's REUSED value
      test-dirty-reads-clean-dep = {
        expr =
          let
            abRoots = mkRoots {
              a = {
                base = 10;
              };
              b = {
                base = 0;
              };
            };
            attrs = {
              children = self: id: { };
              val = self: id: if id == "b" then (self.get "a" "val") + 1 else (self.node id).decls.base;
            };
          in
          (genScope.evalWarm {
            scope = abRoots;
            attributes = attrs;
            prior = priorOf abRoots (attrs // { val = self: id: 99; });
            decision = genScope.mkDecision {
              isClean = id: id == "a";
              reusable = _: [ "val" ];
            };
          }).get
            "b"
            "val";
        expected = 100;
      };
      # children NEVER reused (stale prior children ignored; fresh structure used) — the
      # decision names a structural attribute and the always-recompute branch answers first
      test-children-always-recomputed = {
        expr =
          let
            pRoots = mkRoots { p = { }; };
            attrs = {
              children =
                self: id:
                if id == "p" then
                  {
                    c = {
                      id = "c";
                      type = "t";
                      parent = "p";
                      decls = { };
                    };
                  }
                else
                  { };
              label = self: id: "fresh-${id}";
            };
            w = genScope.evalWarm {
              scope = pRoots;
              attributes = attrs;
              prior = priorOf pRoots (
                attrs
                // {
                  children =
                    self: id:
                    if id == "p" then
                      {
                        BOGUS = {
                          id = "BOGUS";
                          type = "t";
                          parent = "p";
                          decls = { };
                        };
                      }
                    else
                      { };
                }
              );
              decision = allClean [ "children" ];
            };
          in
          builtins.attrNames (w.get "p" "children");
        expected = [ "c" ];
      };
      # THE IMPORT RELATION IS NEVER SERVED FROM A PRIOR — AND THE CONTROL THAT ARMS THE READING.
      #
      # One construction, run twice over a graph whose import relation CHANGED between passes:
      # the prior answers `n -> old`, the current program answers `n -> new`, and the decision
      # calls the node clean and names the relation reusable. That decision is the plane
      # behaviour that makes a stale serve possible at all, so it is supplied rather than
      # avoided.
      #
      # The two arms differ in ONE thing, the NAME the relation is declared under.
      #
      #   `imports`    — the name the resolver traverses, reserved through the traversal binding
      #                  the classifier reads. The always-recompute branch answers first and the
      #                  reading is the CURRENT relation.
      #   `my-imports` — the same relation, same prior, same decision, under a name outside the
      #                  reserved namespace. It classifies resolutional, the prior is served, and
      #                  the evaluation answers over a STALE IMPORT RELATION: complete,
      #                  well-typed, wrong, and silent.
      #
      # The second arm is what makes the first a reading. A fixture that never reuses anything
      # passes the first arm for a reason that has nothing to do with the partition, and a guard
      # never observed failing is not armed. This is also the residual `structural`'s stated
      # domain names: a relation the substrate cannot recognise by name is a relation it cannot
      # protect.
      test-the-import-relation-is-recomputed-and-the-stale-serve-is-live = {
        expr =
          let
            iRoots = mkRoots {
              n = { };
              old = { };
              new = { };
            };
            attrsUnder = relName: {
              children = self: id: { };
              ${relName} = self: id: if id == "n" then [ "new" ] else [ ];
            };
            priorUnder = relName: {
              children = self: id: { };
              ${relName} = self: id: if id == "n" then [ "old" ] else [ ];
            };
            readUnder =
              relName:
              (genScope.evalWarm {
                scope = iRoots;
                attributes = attrsUnder relName;
                prior = priorOf iRoots (priorUnder relName);
                decision = allClean [ relName ];
              }).get
                "n"
                relName;
          in
          {
            reserved = readUnder "imports";
            seeded = readUnder "my-imports";
          };
        expected = {
          reserved = [ "new" ];
          seeded = [ "old" ];
        };
      };
      # a dirty GRANDCHILD is reachable through freshly-recomputed children
      test-dirty-grandchild-reachable = {
        expr =
          let
            pRoots = mkRoots { p = { }; };
            attrs = {
              children =
                self: id:
                if id == "p" then
                  {
                    c = {
                      id = "c";
                      type = "t";
                      parent = "p";
                      decls = { };
                    };
                  }
                else if id == "c" then
                  {
                    g = {
                      id = "g";
                      type = "t";
                      parent = "c";
                      decls = { };
                    };
                  }
                else
                  { };
              label = self: id: "fresh-${id}";
            };
            w = genScope.evalWarm {
              scope = pRoots;
              attributes = attrs;
              prior = priorOf pRoots (attrs // { label = self: id: "stale-${id}"; });
              decision = genScope.mkDecision {
                isClean = id: id != "g"; # g dirty, p/c clean
                reusable = _: [ "label" ];
              };
            };
          in
          w.get "g" "label";
        expected = "fresh-g"; # g recomputed (dirty) AND reachable (children recomputed, never reused)
      };
      # per-(node,attr) granularity: clean node, attr a reused / attr b recomputed
      test-mixed-warm-cold = {
        expr =
          let
            nnRoots = mkRoots { n = { }; };
            attrs = {
              children = self: id: { };
              a = self: id: "fresh-a";
              b = self: id: "fresh-b";
            };
            w = genScope.evalWarm {
              scope = nnRoots;
              attributes = attrs;
              prior = priorOf nnRoots (
                attrs
                // {
                  a = self: id: "cached-a";
                  b = self: id: "cached-b";
                }
              );
              decision = allClean [ "a" ]; # names a, not b
            };
          in
          [
            (w.get "n" "a")
            (w.get "n" "b")
          ];
        expected = [
          "cached-a"
          "fresh-b"
        ];
      };
      # evalWarm under the COLD decision == eval. The cold case is the same code path with the
      # decision saying nothing is clean, not a second one.
      test-evalWarm-cold-decision-equals-eval = {
        expr =
          let
            r = mkRoots {
              n = {
                v = 7;
              };
            };
          in
          (genScope.evalWarm {
            scope = r;
            attributes = poison;
            prior = null;
            decision = genScope.coldDecision;
          }).get
            "n"
            "val";
        expected =
          (genScope.eval {
            scope = mkRoots {
              n = {
                v = 7;
              };
            };
            attributes = poison;
          }).get
            "n"
            "val";
      };
    };
}
