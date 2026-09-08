# THE BOUNDED-ASCENT DRIVER'S OWN ORACLE — the three things the driver does that its caller cannot
# do for it, and the one thing it deliberately does NOT do.
#
# ★ WHY THE FIXTURES ARE INTEGERS AND NOT LATTICES. The driver is parameterized by the caller's seed,
# round and quiescence test and knows nothing else about a value, so a fixture built out of a lattice
# would test the lattice. A member here is a name and an integer; the only questions asked of it are
# the three functions the caller supplies to answer them.
#
# ★ WHAT IS NOT A CELL HERE, AND WHY. `lib/ascent.nix` claims NO termination theorem — neither that
# the caller's step ascends a chain that ends, nor that the caller's bound is long enough to reach
# it — so there is nothing here to quantify over depths the way `stratify.nix`'s suite does. The
# third cell below is the observable form of that abstention: the driver meets a bound it cannot
# settle within and RETURNS.
#
# ★ AND THE PER-MEMBER PREDICATE'S OWN CONTROL IS A MEASURED FACT RATHER THAN A FOURTH CELL, because
# it is a claim about a fixture this suite does not otherwise run. The second cell's fixture, with
# its per-member `settledBy` replaced by `prev == next` for BOTH members and everything else
# identical, settles at `rounds = 3` instead of 2 — so the mod-2 predicate is what buys round 2, and
# a driver that asked one whole-record question would read 3 here.
{ genScope, ... }:
let
  inherit (genScope) ascend;

  # `x mod 2` written in the two builtins that exist for it: integer division truncates, so
  # `x - (x / 2) * 2` is the remainder for the non-negative values this fixture uses.
  parity = x: x - (x / 2) * 2;

  # Fixture 2, held as a function of the settlement test alone, so the cell and the control in the
  # header above differ in EXACTLY that argument and in nothing else.
  #
  # `a` is driven to 7 in one round and stays there. `b` sits at its seed 1 for the first round and
  # moves to 3 in the second — a genuine move, which `==` would refuse to call quiescent. Under `b`'s
  # OWN mod-2 predicate 1 and 3 are equal, so the round that moves it is also the round that settles
  # it, and `a`'s `==` is satisfied in the same round.
  movingUnderItsOwnEq = settledBy: {
    members = [
      "a"
      "b"
    ];
    bottomOf = m: if m == "a" then 0 else 1;
    advance = v: {
      a = 7;
      b = if v.a == 0 then 1 else 3;
    };
    inherit settledBy;
    bound = [
      1
      2
      3
      4
    ];
  };
in
{
  flake.tests.ascent = {
    # ── THE SEED IS THE CALLER'S, PER MEMBER ──
    # `bound` is empty, so no round runs and the result is the seed alone. `advance` is a throw: it
    # must never fire, and if the driver ever ran a round on an empty bound this cell would abort
    # rather than fail — which is the sharper signal of the two, since the batch asserter forces
    # every `expr` unconditionally. `settled` is `false` here and that is not a defect: nothing has
    # been shown to be a fixed point, and the driver reports what it knows rather than what would be
    # convenient.
    test-the-seed-is-each-members-own-bottom = {
      expr = ascend {
        members = [
          "a"
          "b"
        ];
        bottomOf = m: if m == "a" then 0 else 100;
        advance = _: throw "gen-scope: ascent fixture — advance fired on an empty bound";
        settledBy =
          _: a: b:
          a == b;
        bound = [ ];
      };
      expected = {
        values = {
          a = 0;
          b = 100;
        };
        settled = false;
        rounds = 0;
      };
    };

    # ── SETTLEMENT IS QUANTIFIED OVER MEMBERS AND ANSWERED PER MEMBER ──
    # `rounds = 2` is the load-bearing figure. See the header: the identical fixture under one
    # whole-record equality reads 3, so this cell distinguishes a driver that asks each member its
    # own question from one that asks a single question about the record.
    test-settlement-reads-each-members-own-predicate = {
      expr = ascend (
        movingUnderItsOwnEq (
          m: prev: next:
          if m == "b" then parity prev == parity next else prev == next
        )
      );
      expected = {
        values = {
          a = 7;
          b = 3;
        };
        settled = true;
        rounds = 2;
      };
    };

    # ── AN EXHAUSTED BOUND IS A FACT ON THE RESULT, NOT A REFUSAL ──
    # ★ THIS IS THE CELL "THROWS NOWHERE" RESTS ON. The step strictly increments and can never
    # satisfy `==`, so the walk uses every element of the bound and stops with the member still
    # moving. What comes back is the iterate it reached and `settled = false`; a driver that raised
    # the divergence itself would abort this cell instead of failing it, and would have taken a
    # refusal that belongs to whoever declared the bound and knows what it was declared to mean.
    test-an-exhausted-bound-returns-unsettled-rather-than-throwing = {
      expr = ascend {
        members = [ "x" ];
        bottomOf = _: 0;
        advance = v: {
          x = v.x + 1;
        };
        settledBy =
          _: prev: next:
          prev == next;
        bound = [
          1
          2
          3
          4
          5
        ];
      };
      expected = {
        values = {
          x = 5;
        };
        settled = false;
        rounds = 5;
      };
    };
  };
}
