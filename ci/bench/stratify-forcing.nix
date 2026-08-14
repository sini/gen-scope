# THE DRIVER'S PER-ROUND FORCING AS EXIT-CODE ARMS — one construction per arm, read by
# `stratify-forcing.sh`.
#
# WHY THIS CANNOT BE A SUITE CELL. An accumulator field written every round and read in none is a
# thunk chain as long as the loop, and forcing it at the end spends C stack per link until the
# evaluation ENDS. That ending is not a throw: `tryEval` holds `throw` and `assert` and nothing
# else, so `didThrow` never returns a boolean for a suite to compare and there is no arm of
# `nix-unit` that can host the cell — the runner itself is what stops. What can be read is the
# evaluator's own exit code, which is what this pair reads.
#
# ★ THE UNFORCED ARM IS THE DRIVER'S OWN LOOP WITH ONE CHARACTER CHANGED. `unforcedRun` below is
# `lib/stratify.nix`'s walk with the same step body, the same accumulator and the same bound; the
# only difference is that it hands `iterateBounded` a strict function that forces nothing. A
# control that differed in any other way would be measuring that difference. It is built here to be
# measured and is never used.
#
# ★ AND WHICH FIELD IS THE ONE THAT CHAINS, SAID PLAINLY, because "unforced" is a property of the
# loop and not of every field in it. `pending` is read by the step's own control flow and `items` is
# read by the round's selection, so both are forced by use no matter what the strict function does.
# `settled` is written every round and read by nobody until the end — the field the discipline
# exists for, and the one whose chain the forced arm never builds.
#
# ★ AND THE SHORT ARMS ARE THE CONTROL ON THE CONTROL. At a round count below the measured
# boundary the unforced construction RETURNS, and returns the same value as the forced one — so the
# abort at the long count is the chain and not a broken fixture. Measured on this machine (`ulimit
# -s` 8192): the unforced chain returns at 57000 rounds and ends the evaluation at 60000, so the
# long arms run at 100000 with the boundary between them and the short arms at 1000. The boundary
# is a property of the stack the evaluator was given, not a constant of the language; the sweep
# reports what it saw rather than asserting a depth.
#
# ★ `plain-throw-wrapped` IS THE CONTROL ON THE INSTRUMENT ITSELF. If the `tryEval` idiom were
# broken, every wrapped arm would report an escape and the table would read as a discovery. That
# arm is an ordinary named refusal wrapped the same way, and it must be CAUGHT.
#
# It imports `lib/stratify.nix` and `lib/least-model.nix` DIRECTLY, with the prelude and nothing
# else. That is not a shortcut around the library's entry point: the driver takes `{ prelude,
# forceFields }` and the forcing is what `lib/default.nix` hands it, so a bench file that had to
# reach for the graph to build a driver would be reporting that the driver is not the standalone
# thing it claims to be.
{
  arm ? "forced",
}:
let
  lock = builtins.fromJSON (builtins.readFile ../../flake.lock);
  fetch =
    name:
    let
      node = lock.nodes.${name}.locked;
    in
    builtins.fetchTree {
      inherit (node)
        type
        owner
        repo
        rev
        narHash
        ;
    };
  prelude = import "${fetch "gen-prelude"}/lib";
  inherit (import ../../lib/least-model.nix { inherit prelude; }) forceFields;
  inherit (import ../../lib/stratify.nix { inherit prelude forceFields; }) stratify;

  inherit (prelude)
    filter
    head
    iterateBounded
    length
    sort
    tail
    ;

  # ── THE FIXTURE, ONE SHAPE FOR BOTH CONSTRUCTIONS ──
  # A schedule of n strata whose only item sits in the last one. Every round therefore does the
  # same trivial work and the accumulator is written every round and read in none, which is the
  # shape being measured; the single settled item is what makes the returned value say that the
  # walk reached the end rather than that it produced nothing.
  args = n: {
    schedule = builtins.genList (i: i) n;
    stratumOf = i: i.stratum;
    within = a: b: a.index < b.index;
    seed = [
      {
        stratum = n - 1;
        index = 0;
      }
    ];
    advance =
      { stratum, items }:
      {
        settled = builtins.map (i: i.index) items;
        emitted = [ ];
      };
    describe = i: "item ${toString i.index} at stratum ${toString i.stratum}";
  };

  readout = result: {
    inherit (result) strata;
    settled = length result.settled;
  };

  # ── THE UNFORCED CONSTRUCTION, VERBATIM IN SHAPE FROM THE DRIVER ──
  unforcedRun =
    {
      schedule,
      stratumOf,
      within,
      seed,
      advance,
      describe,
    }:
    let
      step =
        st:
        let
          stratum = head st.pending;
          items = sort within (filter (i: stratumOf i == stratum) st.items);
          round = advance { inherit stratum items; };
        in
        {
          pending = tail st.pending;
          items = st.items ++ round.emitted;
          settled = st.settled ++ round.settled;
        };

      final = iterateBounded (_: null) step {
        pending = schedule;
        items = seed;
        settled = [ ];
      } schedule;
    in
    {
      inherit (final) settled;
      strata = length schedule;
    };

  # True when the wrapper HELD a thrown value — which is what a working `tryEval` reports on a
  # refusal, and what no `tryEval` can report on an evaluation that ended.
  held = e: !(builtins.tryEval (builtins.deepSeq e null)).success;

  long = 100000;
  short = 1000;

  arms = {
    forced = readout (stratify (args long));
    unforced = readout (unforcedRun (args long));
    unforced-wrapped = held (readout (unforcedRun (args long)));

    forced-small = readout (stratify (args short));
    unforced-small = readout (unforcedRun (args short));

    plain-throw-wrapped = held (throw "gen-scope.stratify-forcing: the instrument's own control");
  };
in
arms.${arm}
