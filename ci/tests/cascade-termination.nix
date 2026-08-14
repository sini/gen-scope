# The cascade quiesces, and what it refuses on the way down. A `below` relation of depth d resolves
# in exactly d+1 strata with each kind resolving only in its own; and the refusal chain that guards
# intake guards EMISSION too, from the emitting claim's own call site.
#
# THEORY: the descending-measure termination argument — Abiteboul, Beeri, Wong. The measure is the
# registry's `depth`, the round bound is `maxDepth + 1`, and it is a THEOREM about that measure
# rather than a cap the loop carries.
#
# ★ THE TWO EMISSION-PATH REFUSAL CELLS CLOSE A MEASURED HOLE, and the measurement is the reason
# they are here rather than assumed covered. `validate` is shared by intake and emission
# (`lib/cascade.nix:671`), but it is CALLED TWICE — once at intake (`:756`) and once per emitted
# sub-claim (`:805`). Deleting the emission call outright left the whole suite green before these
# cells existed: the intake cells only ever exercise the first call site, and the below-membership
# cells beside them refuse at `:811`, AFTER `validate` has returned, on a sub-claim that is
# well-formed. So nothing reached `:805`'s own arms. These two do.
#
# ★ THE RESERVED-KEY EMISSION IS HAND-BUILT, and it has to be. `mkClaim` refuses a shadowing
# payload where the author writes it, so a fixture built with the constructor would refuse INSIDE
# the resolver and report this cell as covered when the emission arm was never entered — the same
# reason `cascade-claims.nix`'s own reserved-key cell uses a hand-built record.
#
# ★ WHAT THESE CELLS DO NOT DISCHARGE: the driver's own termination oracle. When the stratification
# is extracted into a named driver, its oracle quantifies the theorem over several depths and
# equates the result's `strata` field with the schedule's length. No such field exists on this
# result (`attrNames` gives resources, trace, unrun, wiring), and these cells read one chain at one
# depth. They guard the property on the construction that exists today; they are not the stronger
# statement that supersedes them.
{ lib, genScope, ... }:
let
  inherit (genScope)
    mkKind
    mkKinds
    mkClaim
    resolveClaims
    ;

  didThrow = e: !(builtins.tryEval (builtins.deepSeq e null)).success;
  succeeds = e: (builtins.tryEval (builtins.deepSeq e null)).success;

  entry = name: {
    id_hash = "id-${name}";
    inherit name;
  };
  subj = entry "s";

  # ── deep chain l4 → l3 → … → l0, each composite emitting one sub-claim a level down ──
  chainKinds = mkKinds (
    [
      (mkKind {
        name = "l0";
        resolve = _: _: { };
      })
    ]
    ++
      map
        (
          n:
          mkKind {
            name = "l${toString n}";
            below = [ "l${toString (n - 1)}" ];
            resolve = c: _: {
              claims = [
                (mkClaim {
                  kind = "l${toString (n - 1)}";
                  subject = c.subject;
                })
              ];
            };
          }
        )
        [
          1
          2
          3
          4
        ]
  );

  chainRes = resolveClaims {
    kinds = chainKinds;
    claims = [
      (mkClaim {
        kind = "l4";
        subject = subj;
      })
    ];
  };

  # ── an emitted sub-claim that is malformed: the emission call site's own arms ──
  emitBadKinds =
    badClaim:
    mkKinds [
      (mkKind {
        name = "b";
        resolve = _: _: { };
      })
      (mkKind {
        name = "a";
        below = [ "b" ];
        resolve = _: _: { claims = [ badClaim ]; };
      })
    ];
  runEmit =
    badClaim:
    resolveClaims {
      kinds = emitBadKinds badClaim;
      claims = [
        (mkClaim {
          kind = "a";
          subject = subj;
        })
      ];
    };

  # The reserved-key emission, hand-built for the reason in the header.
  handBuiltReservedEmission = {
    _type = "gen-scope/claim";
    kind = "b";
    subject = subj;
    _reserved = [ "_path" ];
  };
in
{
  flake.tests.cascade-termination = {
    # Each kind resolves only in its stratum: every trace claim's stratum equals its kind depth.
    test-chain-strata-descending = {
      expr = map (c: c.stratum) chainRes.trace.claims;
      expected = [
        4
        3
        2
        1
        0
      ];
    };
    # maxDepth+1 = 5 distinct strata, one claim each — the cascade quiesced (no error).
    test-chain-quiesces-count = {
      expr = builtins.length chainRes.trace.claims;
      expected = 5;
    };
    # Every parent chain reaches the root: l0's path is [0,0,0,0,0].
    test-chain-deepest-path = {
      expr = (lib.last chainRes.trace.claims).path;
      expected = [
        0
        0
        0
        0
        0
      ];
    };

    # ── emission-stage refusals, reached at the emitting claim's own call site ──
    test-emit-subject-without-id-refused = {
      expr = didThrow (
        runEmit (mkClaim {
          kind = "b";
          subject = {
            name = "no-id";
          };
        })
      );
      expected = true;
    };
    test-emit-reserved-key-refused = {
      expr = didThrow (runEmit handBuiltReservedEmission);
      expected = true;
    };

    # ── ARMING ──
    # A well-formed emission through the same two kinds must RESOLVE, or the two cells above are
    # satisfied by a construction that refuses every emission there is.
    test-control-a-well-formed-emission-resolves = {
      expr = succeeds (
        runEmit (mkClaim {
          kind = "b";
          subject = subj;
        })
      );
      expected = true;
    };
    # The chain cells rest on the fixture's depth, and the two ways of saying it are one apart:
    # FIVE levels `l0`…`l4`, `maxDepth` FOUR, so `maxDepth + 1 = 5` strata. Both numbers are
    # asserted here because either one alone reads as the other's off-by-one, and the theorem's
    # antecedent is the depth while the count cell's expected value is the level count.
    test-control-the-chain-fixture-is-five-levels-of-max-depth-four = {
      expr = {
        maxDepth = chainKinds.maxDepth;
        levels = builtins.length (builtins.attrNames chainKinds.depth);
      };
      expected = {
        maxDepth = 4;
        levels = 5;
      };
    };
  };
}
