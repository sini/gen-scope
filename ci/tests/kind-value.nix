# A KIND CARRIES ITS KIND VALUE, AND EVERY NODE OF THAT KIND CARRIES IT (den-hoag-l0y, arm (B′)).
# The refusals are message cells in `ci/tests-error.nix`'s `kind-value-refusals`; these are the
# admitting half over the same fixtures.
#
# The kind values here are SHAPE fixtures: records carrying gen-schema's tagged sum
# (`kind`, `__mint.minted`) without having been minted. That is the whole of what gen-scope reads —
# it takes no gen-schema input and its door asks `__mint ? minted` and stops — so a minted value
# and this fixture cross the door identically. The minted value's behaviour at `sel.kind` is
# gen-select's to test.
{ genScope, ... }:
let
  S = genScope;
  valueOf = name: mark: {
    kind = name;
    __mint.minted = mark;
  };
  hostA = valueOf "host" "host:a";
  leafV = valueOf "leaf" "leaf:l";

  scopeWith =
    kinds:
    S.buildRoots {
      parentGraph = S.vertex "a";
      types.a = "host";
      inherit kinds;
    };
  declared = scopeWith (S.mkKinds [ (S.mkKind { kindValue = hostA; } "host") ]);
  bare = scopeWith (S.mkKinds [ (S.mkKind { } "host") ]);
  kindless = S.buildRoots { parentGraph = S.vertex "a"; };

  # A `//`-merged registry whose two records under `host` carry the SAME value: coherent.
  plain = S.mkKinds [
    (S.mkKind { } "host")
    (S.mkKind { below = [ "host" ]; } "leaf")
  ];
  withValue = r: v: r // { kindValue = v; };
  mergedCoherent = {
    kinds = {
      host = withValue plain.kinds.host hostA;
      leaf = plain.kinds.leaf // {
        belowKinds.host = withValue plain.kinds.host hostA;
      };
    };
  };

  # Hand-built records crossing the eval door: coherent with the registry, omitting the field, and
  # carrying a value in a scope whose registry declares none.
  handBuilt =
    kinds: node:
    (S.eval { } { children = _self: _id: { }; } {
      inherit kinds;
      nodeOrder = [ "a" ];
      nodes.a = {
        id = "a";
        type = "host";
        parent = null;
        decls = { };
      }
      // node;
    }).allNodeIds;
  valuedReg = S.mkKinds [ (S.mkKind { kindValue = hostA; } "host") ];
  bareReg = S.mkKinds [ (S.mkKind { } "host") ];

  # `host` spawns `leaf` children; both kinds declare a value.
  spawnScope = S.buildRoots {
    parentGraph = S.vertex "a";
    types.a = "host";
    kinds = S.mkKinds [
      (S.mkKind { kindValue = leafV; } "leaf")
      (S.mkKind {
        below = [ "leaf" ];
        kindValue = hostA;
        spawns.leaf = _self: id: {
          sprout = {
            id = "sprout";
            parent = id;
            decls = { };
          };
        };
      } "host")
    ];
  };
  sprout =
    (S.eval { } {
      children = _self: _id: { };
    } spawnScope).get
      "a"
      "derived-children";
in
{
  flake.tests.kind-value = {
    # c7: a scope with no kinds keeps the node record it always had, field for field.
    test-c7-a-kindless-node-carries-no-kind-value = {
      expr = builtins.attrNames kindless.nodes.a;
      expected = [
        "decls"
        "id"
        "parent"
        "type"
      ];
    };
    # c13: and so does a kinded scope whose kinds declare no value — the per-scope choice.
    test-c13-a-kinded-scope-declaring-no-value-keeps-the-record = {
      expr = builtins.attrNames bare.nodes.a;
      expected = [
        "decls"
        "id"
        "parent"
        "type"
      ];
    };
    # The node carries its kind's value itself — the same reference, read by its mark.
    test-a-node-carries-its-kinds-value = {
      expr = declared.nodes.a.kindValue.__mint.minted;
      expected = "host:a";
    };
    test-a-kind-carries-the-value-it-declared = {
      expr = declared.kinds.kinds.host.kindValue.__mint.minted;
      expected = "host:a";
    };
    # c11b: a merge whose records under one name carry one value is admitted.
    test-c11b-a-coherent-merged-registry-is-admitted = {
      expr =
        builtins.attrNames
          (S.buildRoots {
            types.a = "host";
            kinds = mergedCoherent;
          }).nodes;
      expected = [ "a" ];
    };
    # C2's admitting half: a hand-built node carrying its kind's own value, one omitting the field
    # (kind-blind, refused by name at `sel.kind`), and one carrying a value in a scope whose registry
    # declares none (the node's own declaration, authoritative there).
    test-C2-a-hand-built-node-carrying-its-kinds-value-is-admitted = {
      expr = handBuilt valuedReg { kindValue = hostA; };
      expected = [ "a" ];
    };
    test-C2-a-hand-built-node-omitting-the-value-is-admitted = {
      expr = handBuilt valuedReg { };
      expected = [ "a" ];
    };
    test-C2-a-node-carried-value-in-a-scope-declaring-none-is-admitted = {
      expr = handBuilt bareReg { kindValue = hostA; };
      expected = [ "a" ];
    };
    # c14: a spawned child carries its PRODUCED kind's value, stamped with its `type`.
    test-c14-a-spawned-child-carries-its-kinds-value = {
      expr = {
        inherit (sprout.sprout) type;
        mark = sprout.sprout.kindValue.__mint.minted;
      };
      expected = {
        type = "leaf";
        mark = "leaf:l";
      };
    };
  };
}
