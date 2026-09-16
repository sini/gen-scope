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
    genScope.eval {
      scope = genScope.buildRoots {
        parentGraph = genScope.overlay (genScope.vertex "a") (genScope.vertex "b");
        types.a = "host";
        types.b = "leafOne";
        decls.a = { };
        decls.b = { };
        kinds = genScope.mkKinds [
          (genScope.mkKind { name = "leafOne"; })
          (genScope.mkKind { name = "leafTwo"; })
          (genScope.mkKind {
            name = "host";
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
          })
        ];
      };
      attributes.children = _self: _id: { };
    };

  control = mkFixture { };
  plantedRegistered = mkFixture { plantRegistered = true; };
  plantedSibling = mkFixture { plantSibling = true; };
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
  };
}
