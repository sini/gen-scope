{ lib, genScope, ... }:
let
  # Minimal graph: two roots, a and b
  roots = genScope.buildNodes {
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
    inherit roots;
    attributes = {
      children =
        self: id:
        let
          node = self.node id;
        in
        lib.filterAttrs (_: n: n.parent == id) roots;
      imports = self: id: [ ];
      greeting = self: id: "hello-${id}";
      declX = self: id: (self.node id).decls.x or 0;
    };
    parseParent =
      id:
      let
        node = roots.${id} or null;
      in
      if node != null then node.parent else null;
  };

  # Single root, no children
  singleRoots = genScope.buildNodes {
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
    roots = singleRoots;
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
    # when it builds `allNodes`. `buildNodes` makes every vertex a root, so this repeat is
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
          result = genScope.eval { inherit roots attributes parseParent; };
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
          result = genScope.eval { inherit roots attributes parseParent; };
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
          result = genScope.eval { inherit roots attributes parseParent; };
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
  flake.tests."eval-warm" =
    let
      mkRoots =
        decls:
        lib.mapAttrs (id: d: {
          inherit id;
          type = "t";
          parent = null;
          decls = d;
        }) decls;
      poison = {
        children = self: id: { };
        boom = self: id: throw "boom-${id}";
        val = self: id: (self.node id).decls.v or 0;
      };
    in
    {
      # clean + prior present ⇒ warm-served, fn NEVER forced (poison doesn't throw)
      test-warm-serves-clean-no-force = {
        expr =
          (genScope.evalWarm {
            roots = mkRoots {
              n = {
                v = 5;
              };
            };
            attributes = poison;
            priorResults = {
              n = {
                boom = "cached";
              };
            };
            isClean = _: true;
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
              roots = mkRoots {
                n = {
                  v = 5;
                };
              };
              attributes = poison;
              priorResults = {
                n = {
                  boom = "cached";
                };
              };
              isClean = _: false;
            }).get
              "n"
              "boom"
          )).success;
        expected = false;
      };
      # clean but attr absent from priorResults ⇒ falls through to fn ⇒ throws
      test-warm-missing-attr-falls-through = {
        expr =
          (builtins.tryEval (
            (genScope.evalWarm {
              roots = mkRoots {
                n = {
                  v = 5;
                };
              };
              attributes = poison;
              priorResults = {
                n = { };
              };
              isClean = _: true;
            }).get
              "n"
              "boom"
          )).success;
        expected = false;
      };
      # warm value is served verbatim (not the fresh computation)
      test-warm-serves-prior-value = {
        expr =
          (genScope.evalWarm {
            roots = mkRoots {
              n = {
                v = 5;
              };
            };
            attributes = poison;
            priorResults = {
              n = {
                val = 99;
              };
            };
            isClean = _: true;
          }).get
            "n"
            "val";
        expected = 99;
      };
      # a dirty node reads a clean dep's WARM value
      test-dirty-reads-clean-dep = {
        expr =
          (genScope.evalWarm {
            roots = mkRoots {
              a = {
                base = 10;
              };
              b = {
                base = 0;
              };
            };
            attributes = {
              children = self: id: { };
              val = self: id: if id == "b" then (self.get "a" "val") + 1 else (self.node id).decls.base;
            };
            priorResults = {
              a = {
                val = 99;
              };
            };
            isClean = id: id == "a";
          }).get
            "b"
            "val";
        expected = 100;
      };
      # children NEVER warm-served (stale prior children ignored; fresh structure used)
      test-children-always-recomputed = {
        expr =
          let
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
              roots = mkRoots { p = { }; };
              attributes = attrs;
              priorResults = {
                p = {
                  children = {
                    BOGUS = { };
                  };
                };
              };
              isClean = _: true;
            };
          in
          builtins.attrNames (w.get "p" "children");
        expected = [ "c" ];
      };
      # a dirty GRANDCHILD is reachable through freshly-recomputed children
      test-dirty-grandchild-reachable = {
        expr =
          let
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
              roots = mkRoots { p = { }; };
              attributes = attrs;
              priorResults = {
                g = {
                  label = "stale-g";
                };
              };
              isClean = id: id != "g"; # g dirty, p/c clean
            };
          in
          w.get "g" "label";
        expected = "fresh-g"; # g recomputed (dirty) AND reachable (children recomputed, never warm)
      };
      # per-(node,attr) granularity: clean node, attr a warm / attr b cold
      test-mixed-warm-cold = {
        expr =
          let
            w = genScope.evalWarm {
              roots = mkRoots { n = { }; };
              attributes = {
                children = self: id: { };
                a = self: id: "fresh-a";
                b = self: id: "fresh-b";
              };
              priorResults = {
                n = {
                  a = "cached-a";
                };
              }; # has a, not b
              isClean = _: true;
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
      # evalWarm with warm-off defaults == eval
      test-evalWarm-defaults-equal-eval = {
        expr =
          (genScope.evalWarm {
            roots = mkRoots {
              n = {
                v = 7;
              };
            };
            attributes = poison;
            priorResults = { };
            isClean = _: false;
          }).get
            "n"
            "val";
        expected =
          (genScope.eval {
            roots = mkRoots {
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

  flake.tests."recorded-deps" = {
    test-recordedDeps-declared = {
      expr = genScope.recordedDeps { declaredEdges = id: if id == "b" then [ "a" ] else [ ]; } "b";
      expected = [ "a" ];
    };
    test-recordedDeps-empty = {
      expr = genScope.recordedDeps { declaredEdges = _: [ ]; } "x";
      expected = [ ];
    };
  };
}
