# THE STRATIFICATION DRIVER'S OWN ORACLE — the termination theorem quantified over depths, and the
# global order of what comes back.
#
# THEORY: the descending-measure termination argument. A relation of depth d has a stratum universe
# of exactly d + 1 members, every edge strictly decreases the measure, and the loop visits each
# member once — so the run's length is a fact about the measure rather than a budget. The cells
# below read the result's own `strata` field against the schedule it was given at four depths, which
# is the statement `cascade-termination.nix` names as the one it does not discharge: that suite
# reads one chain at one depth against a result carrying no such field.
#
# ★ WHY THE FIXTURES ARE INTEGERS AND NOT CLAIMS. The driver is parameterized by the instance's
# stratum assignment and knows nothing else about an item, so a fixture built out of the cascade's
# kinds would test the cascade. An item here is a stratum and an index; the only questions asked of
# it are the two functions the caller supplies to answer them.
#
# ★ WHAT IS NOT A CELL HERE, AND WHERE IT IS INSTEAD. The forcing discipline's negative control —
# the same loop with its accumulator left unforced — ends the evaluation rather than producing a
# value, so `tryEval` holds it and no `didThrow` cell can observe it. It is an exit-code arm in
# `ci/bench/stratify-forcing.sh`, beside the forced arm on the same input in the same invocation.
{ genScope, ... }:
let
  inherit (genScope) stratify;

  inherit (builtins)
    concatMap
    genList
    length
    map
    ;

  item = stratum: index: { inherit stratum index; };

  # The descending schedule of a depth-d relation: [ d, d-1, … 0 ]. Descending because an edge runs
  # from a larger measure to a smaller one, so the larger stratum must finish first.
  descending = d: genList (n: d - n) (d + 1);

  stratumOf = i: i.stratum;
  within = a: b: a.index < b.index;
  describe = i: "item ${toString i.index} at stratum ${toString i.stratum}";

  # One item at depth d emitting a single successor exactly one stratum lower — the shape a `below`
  # edge has once the measure IS the stratum. Each stratum reports the strata it settled, so the
  # result's `settled` list is the run's own account of which strata ran and in what order.
  chainOn =
    depth: schedule:
    stratify {
      inherit
        schedule
        stratumOf
        within
        describe
        ;
      seed = [ (item depth 0) ];
      advance =
        { stratum, items }:
        {
          settled = map (i: i.stratum) items;
          emitted = concatMap (i: if i.stratum == 0 then [ ] else [ (item (i.stratum - 1) i.index) ]) items;
        };
    };

  chain = d: chainOn d (descending d);

  # The same chain, seeded at the same depth, under a schedule one stratum short: [ d, d-1, … 1 ].
  # The last emission is then into a stratum the schedule never names.
  shortChain = d: chainOn d (genList (n: d - n) d);

  # Three strata whose items arrive out of order and out of stratum, so that neither the seed's
  # order nor the schedule's alone accounts for what comes back.
  scrambled = [
    (item 1 2)
    (item 0 0)
    (item 2 1)
    (item 1 0)
    (item 2 0)
    (item 1 1)
  ];
in
{
  flake.tests.stratify = {
    # ── THE TERMINATION THEOREM, QUANTIFIED OVER DEPTHS ──
    # `strata` is read against the schedule's own length at each depth: a driver that stopped early
    # would report a smaller one, and a driver that reported the length without walking it would
    # settle fewer.
    test-a-depth-d-relation-completes-in-exactly-d-plus-one-strata = {
      expr =
        map
          (
            d:
            let
              result = chain d;
            in
            {
              inherit (result) strata;
              settledCount = length result.settled;
              scheduleLength = length (descending d);
            }
          )
          [
            0
            1
            7
            40
          ];
      expected = [
        {
          strata = 1;
          settledCount = 1;
          scheduleLength = 1;
        }
        {
          strata = 2;
          settledCount = 2;
          scheduleLength = 2;
        }
        {
          strata = 8;
          settledCount = 8;
          scheduleLength = 8;
        }
        {
          strata = 41;
          settledCount = 41;
          scheduleLength = 41;
        }
      ];
    };

    # The counts above are satisfied by a run that settled the right number of items in the wrong
    # order, or that settled one stratum twice and another never. These pin the contents against
    # literals, which is also what pins `descending` itself for the cell below it.
    test-every-stratum-settles-its-own-item-in-descending-schedule-order = {
      expr = {
        d0 = (chain 0).settled;
        d1 = (chain 1).settled;
        d7 = (chain 7).settled;
      };
      expected = {
        d0 = [ 0 ];
        d1 = [
          1
          0
        ];
        d7 = [
          7
          6
          5
          4
          3
          2
          1
          0
        ];
      };
    };
    # At forty the claim is stated as the identity it is — the settled order IS the schedule order,
    # one contribution per stratum — rather than as forty-one literals. The three literal cases
    # above are what establish that `descending` spells what its name says.
    test-the-forty-deep-chain-settles-every-stratum-exactly-once = {
      expr = (chain 40).settled;
      expected = descending 40;
    };

    # ── THE ARMING, AND WITHOUT IT THE THREE CELLS ABOVE READ THE FIXTURE RATHER THAN THE DRIVER ──
    # One stratum removed from the schedule, everything else identical: the run must be one stratum
    # shorter, and the emission into the missing stratum must come back as a leftover rather than
    # vanishing or refusing.
    test-control-a-schedule-one-stratum-short-settles-fewer-and-leaves-the-rest-unrun = {
      expr =
        let
          result = shortChain 7;
        in
        {
          inherit (result) strata settled;
          unrunStrata = map (i: i.stratum) result.unrun;
        };
      expected = {
        strata = 7;
        settled = [
          7
          6
          5
          4
          3
          2
          1
        ];
        unrunStrata = [ 0 ];
      };
    };

    # ── THE GLOBAL ORDER IS A COMPOSITION OF TWO ORDERS ──
    # Stratum-major in schedule order, `within` inside. The seed is scrambled on both axes, so a
    # driver that preserved the seed's order, or that sorted globally, disagrees here.
    test-settled-is-stratum-major-with-the-within-order-inside = {
      expr =
        (stratify {
          schedule = [
            2
            1
            0
          ];
          inherit stratumOf within describe;
          seed = scrambled;
          advance =
            { stratum, items }:
            {
              settled = map (i: "${toString i.stratum}.${toString i.index}") items;
              emitted = [ ];
            };
        }).settled;
      expected = [
        "2.0"
        "2.1"
        "1.0"
        "1.1"
        "1.2"
        "0.0"
      ];
    };
  };
}
