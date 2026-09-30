# THE SPAWNED KEY'S CONTRACT: CATCHABILITY, AND THE WELL-FORMED CONTROL.
#
# The refusal MESSAGES for a spawn key colliding with an already-registered node (flavor B) or
# with a sibling spawn on the same host (flavor C) live in `tests-error.nix`'s
# `spawn-key-collision-refusals` group, per this suite's own split (a throwing cell cannot live
# under `flake.tests`, which the batch asserter forces unconditionally). This file pins two things
# that group cannot: that both refusals are CATCHABLE (`tryEval`, ADR-0025's "named, not a bare
# interpreter error" bar — row17's own idiom) rather than an uncatchable abort, and that a
# WELL-FORMED, non-colliding spawn still mints — the live positive control, same fixture shape,
# same run.
{ genScope, ... }:
let
  succeeds = e: (builtins.tryEval (builtins.deepSeq e null)).success;

  # `plantRegistered`/`plantSibling` pick which collision (if either) the fixture plants, so the
  # control and both refusal arms are one construction read three ways rather than three drifting
  # copies of it.
  mkFixture =
    {
      plantRegistered ? false,
      plantSibling ? false,
    }:
    let
      childKey = if plantRegistered then "b" else "warp";
      secondKey = if plantSibling then childKey else "weft";
    in
    genScope.eval { }
      {
        children = _self: _id: { };
      }
      (
        genScope.buildRoots {
          parentGraph = genScope.overlay (genScope.vertex "a") (genScope.vertex "b");
          types.a = "host";
          types.b = "leafOne";
          decls.a = { };
          decls.b = { };
          kinds = genScope.mkKinds [
            (genScope.mkKind { } "leafOne")
            (genScope.mkKind { } "leafTwo")
            (genScope.mkKind {
              below = [
                "leafOne"
                "leafTwo"
              ];
              spawns.leafOne = _self: id: {
                ${childKey} = {
                  id = childKey;
                  parent = id;
                  decls = { };
                };
              };
              spawns.leafTwo = _self: id: {
                ${secondKey} = {
                  id = secondKey;
                  parent = id;
                  decls = { };
                };
              };
            } "host")
          ];
        }
      );

  control = mkFixture { };
  plantedRegistered = mkFixture { plantRegistered = true; };
  plantedSibling = mkFixture { plantSibling = true; };

  # The child's `id` against its key: omitted, it is stamped from the key; disagreeing, refused.
  mkIdFixture =
    child:
    genScope.eval { }
      {
        children = _self: _id: { };
      }
      (
        genScope.buildRoots {
          parentGraph = genScope.vertex "a";
          types.a = "host";
          decls.a = { };
          kinds = genScope.mkKinds [
            (genScope.mkKind { } "leaf")
            (genScope.mkKind {
              below = [ "leaf" ];
              spawns.leaf = _self: _id: { warp = child; };
            } "host")
          ];
        }
      );
  idless = mkIdFixture { decls.v = 1; };
  mismatched = mkIdFixture {
    id = "weft";
    decls = { };
  };
in
{
  flake.tests."spawn-key-contract" = {
    # ── THE LIVE POSITIVE CONTROL: neither collision planted, both spawns still mint ──
    test-control-two-non-colliding-spawns-both-mint = {
      expr = builtins.sort builtins.lessThan control.allNodeIds;
      expected = [
        "a"
        "b"
        "warp"
        "weft"
      ];
    };

    # ── O2: flavor (B)'s refusal is catchable, not an uncatchable abort ──
    test-a-registered-id-collision-is-catchable = {
      expr = succeeds plantedRegistered.allNodeIds;
      expected = false;
    };

    # ── O3's catchability: flavor (C)'s refusal is catchable, not an uncatchable abort ──
    test-a-sibling-spawn-collision-is-catchable = {
      expr = succeeds plantedSibling.allNodeIds;
      expected = false;
    };

    # ── the key IS the identity: an id-less child is admitted under it ──
    test-an-idless-spawned-child-is-stamped-with-its-key = {
      expr = {
        ids = builtins.sort builtins.lessThan idless.allNodeIds;
        inherit (idless.node "warp") id parent type;
        v = (idless.node "warp").decls.v;
      };
      expected = {
        ids = [
          "a"
          "warp"
        ];
        id = "warp";
        parent = "a";
        type = "leaf";
        v = 1;
      };
    };

    # ── an id disagreeing with its key is refused catchably (message: tests-error.nix) ──
    test-a-spawned-id-disagreeing-with-its-key-is-catchable = {
      expr = succeeds mismatched.allNodeIds;
      expected = false;
    };
  };
}
