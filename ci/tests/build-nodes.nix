{ lib, genScope, ... }:
let
  # Basic build
  basic = genScope.buildRoots {
    parentGraph = genScope.edge "child" "parent";
    importGraph = genScope.edge "child" "lib";
    decls = {
      parent = {
        x = 1;
      };
      child = {
        y = 2;
      };
      lib = {
        z = 3;
      };
    };
    types = {
      parent = "host";
      child = "user";
      lib = "library";
    };
  };

  # No edges (vertices declared via parentGraph)
  noEdges = genScope.buildRoots {
    parentGraph = genScope.vertices [
      "a"
      "b"
    ];
    importGraph = genScope.empty;
    decls = {
      a = {
        val = 1;
      };
      b = {
        val = 2;
      };
    };
    types = {
      a = "x";
    };
  };

  # ── THE RESERVED-LABEL FIXTURE ──
  # One shape, four readings: both privileged relations are supplied EXPLICITLY, so a caller label
  # that reached them would be observable as a changed `parent` or a changed `I` edge set rather than
  # as an absence. `collide` varies only the label the caller offers.
  collide =
    label:
    genScope.buildRoots {
      parentGraph = genScope.edge "a" "root";
      importGraph = genScope.edge "a" "lib1";
      edgeGraphs = [
        {
          label = label;
          graph = genScope.edge "a" "HIJACKED";
        }
      ];
    };

  # Multiple import edges
  multiImport = genScope.buildRoots {
    parentGraph = genScope.empty;
    importGraph = genScope.overlays [
      (genScope.edge "a" "b")
      (genScope.edge "a" "c")
    ];
    decls = {
      a = { };
      b = { };
      c = { };
    };
    types = { };
  };
in
{
  flake.tests."build-nodes" = {
    test-output-has-all-vertices = {
      expr = builtins.sort builtins.lessThan (builtins.attrNames basic.nodes);
      expected = [
        "child"
        "lib"
        "parent"
      ];
    };

    test-node-shape-id = {
      expr = basic.nodes.parent.id;
      expected = "parent";
    };

    test-node-shape-type = {
      expr = basic.nodes.parent.type;
      expected = "host";
    };

    test-node-shape-parent = {
      expr = basic.nodes.child.parent;
      expected = "parent";
    };

    test-node-shape-null-parent = {
      expr = basic.nodes.parent.parent;
      expected = null;
    };

    test-node-decls-present = {
      expr = basic.nodes.parent.decls.x;
      expected = 1;
    };

    test-edges-I-populated = {
      expr = basic.nodes.child.decls.__edges.I;
      expected = [ "lib" ];
    };

    test-edges-I-empty-for-root = {
      expr = basic.nodes.parent.decls.__edges.I or [ ];
      expected = [ ];
    };

    test-type-null-when-unset = {
      expr = noEdges.nodes.b.type;
      expected = null;
    };

    test-no-parent-when-no-P-edge = {
      expr = noEdges.nodes.a.parent;
      expected = null;
    };

    test-multiple-imports = {
      expr = builtins.sort builtins.lessThan multiImport.nodes.a.decls.__edges.I;
      expected = [
        "b"
        "c"
      ];
    };

    test-multiple-parent-edges-strict-throws = {
      # strict=true (default): P partial function violation throws eagerly
      expr =
        !(builtins.tryEval (
          genScope.buildRoots {
            parentGraph = genScope.overlays [
              (genScope.edge "x" "a")
              (genScope.edge "x" "b")
            ];
          }
        )).success;
      expected = true;
    };

    test-multiple-parent-edges-lazy-deferred = {
      # strict=false: throws only when conflicting node's parent is accessed
      expr =
        let
          nodes = genScope.buildRoots {
            strict = false;
            parentGraph = genScope.overlays [
              (genScope.edge "x" "a")
              (genScope.edge "x" "b")
            ];
          };
        in
        (builtins.tryEval (builtins.attrNames nodes.nodes)).success;
      expected = true;
    };

    test-decls-default-empty = {
      expr = builtins.removeAttrs basic.nodes.lib.decls [ "__edges" ];
      expected = {
        z = 3;
      };
    };

    # ── THE RESERVED LABELS ──
    # `P` and `I` name the constructor's own relations, and the caller's `edgeGraphs` merges LAST, so
    # a caller offering either one used to replace the argument it passed in the same call with no
    # diagnostic. The refusal is asserted here as a BOOLEAN and its text in `../tests-error.nix`,
    # where `expectedError` can read what it says: `tryEval` discards a throw's message.
    #
    # The two control cells are the other half of these two. A refusal cell alone passes over a
    # construction that refuses everything, and a fixture whose privileged relations never reached the
    # node would show no hijack to refuse: `M` is an ordinary caller label carrying the SAME edge, and
    # it leaves `parent` and the `I` set exactly as the arguments declared them.
    test-control-an-ordinary-label-leaves-parent-alone = {
      expr = (collide "M").nodes.a.parent;
      expected = "root";
    };

    test-control-an-ordinary-label-leaves-the-I-edges-alone = {
      expr = (collide "M").nodes.a.decls.__edges.I;
      expected = [ "lib1" ];
    };

    test-reserved-label-P-is-refused = {
      expr = !(builtins.tryEval (collide "P")).success;
      expected = true;
    };

    test-reserved-label-I-is-refused = {
      expr = !(builtins.tryEval (collide "I")).success;
      expected = true;
    };

    test-custom-edge-graphs =
      let
        custom = genScope.buildRoots {
          parentGraph = genScope.empty;
          importGraph = genScope.empty;
          edgeGraphs = [
            {
              label = "D";
              graph = genScope.edge "a" "b";
            }
          ];
          decls = {
            a = { };
            b = { };
          };
          types = { };
        };
      in
      {
        expr = custom.nodes.a.decls.__edges.D;
        expected = [ "b" ];
      };
  };
}
