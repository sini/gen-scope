# THE MINTING INSTANCE'S OWN PER-ROUND FORCING AS EXIT-CODE ARMS — one construction per arm, read by
# `mint-forcing.sh`.
#
# WHY THIS CANNOT BE A SUITE CELL. The frozen set is written every round and read only when a mint
# needs it, so without a per-round force it is a chain of attribute-set updates as long as the
# schedule, and forcing it at the end spends C stack per link until the evaluation ENDS. That ending
# is not a throw: `tryEval` holds `throw` and `assert` and nothing else, so `didThrow` never returns a
# boolean for a suite to compare and there is no arm of `nix-unit` that can host the cell — the runner
# itself is what stops. What can be read is the evaluator's own exit code, which is what this pair
# reads.
#
# ★ THE FORCED ARM IS THE SHIPPED ENTRY AND NOT A COPY OF IT. `mintStrata` is called through the
# library's own door, so the row that must return is the construction that ships. Only the UNFORCED
# arm is a reproduction, and it differs from `lib/mint.nix`'s accumulation in two places rather than
# one. (1) It hands `iterateBounded` a strict function that forces nothing — the difference this file
# exists to measure. (2) It stops at the accumulation and never runs the driver, the merge or the
# incidence, because those are downstream of the field being measured. The second difference is stated
# rather than removed because it is CONSERVATIVE in the direction that matters: the omitted work is
# work the shipped entry does and this arm does not, so the arm is handicapped toward returning and it
# ends the evaluation anyway.
#
# ★ AND WHICH FIELD IS THE ONE THAT CHAINS, SAID PLAINLY, because "unforced" is a property of the loop
# and not of every field in it. `pending` is read by the step's own control flow, so it is forced by
# use no matter what the strict function does. `frozen` and `byStratum` are written every round and
# read by nobody until a mint or the driver asks — the fields the discipline exists for, and the ones
# whose chain the forced arm never builds. The readout below reads `frozen`, because a readout that
# never forces the accumulated field would let both arms return and measure nothing.
#
# ★ THE FIXTURE MINTS ONE NODE FROM `n` PASSES, AND THAT SHAPE IS DELIBERATE. Every emitter names the
# same identifier with the same kind and no relata, so each round adds a single key to a set that
# stays one key wide: the round's own work is constant and the only thing growing with `n` is the
# update chain. A fixture whose frozen set grew a key per round would measure the cost of copying an
# attribute set instead.
#
# ★ AND THE SHORT ARMS ARE THE CONTROL ON THE CONTROL. At a round count below the measured boundary
# the unforced construction RETURNS, and returns the same value as the forced one — so the abort at
# the long count is the chain and not a broken fixture. Measured on this machine: the unforced chain
# returns at 8000 rounds and ends the evaluation at 12000, so the long arms run at 20000 with the
# boundary between them and the short arms at 1000. The boundary is a property of the stack the
# evaluator was given, not a constant of the language; the sweep reports what it saw rather than
# asserting a depth.
#
# ★ `plain-throw-wrapped` IS THE CONTROL ON THE INSTRUMENT ITSELF. If the `tryEval` idiom were broken,
# every wrapped arm would report an escape and the table would read as a discovery. That arm is an
# ordinary named refusal wrapped the same way, and it must be CAUGHT.
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
  graph = import "${fetch "gen-graph"}/lib" { inherit prelude; };
  schema = import "${fetch "gen-schema"}/lib" {
    inherit prelude;
    merge = import "${fetch "gen-merge"}/lib" { inherit prelude; };
    algebra = import "${fetch "gen-algebra"}/lib";
  };
  inherit (import ../../lib { inherit prelude graph schema; }) mintStrata;
  inherit (import ../../lib/least-model.nix { inherit prelude; }) forceFields;

  inherit (prelude)
    attrNames
    filter
    head
    iterateBounded
    length
    listToAttrs
    map
    nameValuePair
    sort
    tail
    ;

  # ── THE FIXTURE, ONE SHAPE FOR BOTH CONSTRUCTIONS ──
  emittersOf =
    n:
    builtins.genList (i: {
      pass = i;
      identifier = "dup";
      kind = "widget";
      relata = { };
      content = { };
      site = "site-dup";
    }) n;

  args = n: {
    emitters = emittersOf n;
    kinds = {
      widget = { };
    };
  };

  # ── THE UNFORCED CONSTRUCTION, VERBATIM IN SHAPE FROM THE ACCUMULATION ──
  unforcedRun =
    { emitters, kinds }:
    let
      schedule = sort (a: b: a < b) (prelude.unique (map (e: e.pass) emitters));
      within =
        a: b: if a.identifier != b.identifier then a.identifier < b.identifier else a.site < b.site;
      itemsAt = stratum: sort within (filter (e: e.pass == stratum) emitters);
      mintOne =
        frozen: e:
        let
          valueOf =
            label:
            if label == "identifier" then
              e.identifier
            else
              let
                relatum = e.relata.${label};
              in
              frozen.${relatum} or (throw "mint-forcing: unresolved '${relatum}'");
        in
        {
          inherit (e)
            identifier
            kind
            relata
            content
            site
            ;
          identity = schema.hashIdentity e.kind ([ "identifier" ] ++ attrNames e.relata) valueOf;
        };
      accumulate =
        acc:
        let
          stratum = head acc.pending;
          settled = map (mintOne acc.frozen) (itemsAt stratum);
        in
        {
          pending = tail acc.pending;
          frozen = acc.frozen // listToAttrs (map (r: nameValuePair r.identifier r.identity) settled);
          byStratum = acc.byStratum // {
            ${toString stratum} = settled;
          };
        };
      final = iterateBounded (_: null) accumulate {
        pending = schedule;
        frozen = { };
        byStratum = { };
      } schedule;
    in
    {
      nodes = length (attrNames final.frozen);
      strata = length schedule;
    };

  readout = result: {
    nodes = length (attrNames result.nodes);
    inherit (result) strata;
  };

  # True when the wrapper HELD a thrown value — which is what a working `tryEval` reports on a
  # refusal, and what no `tryEval` can report on an evaluation that ended.
  held = e: !(builtins.tryEval (builtins.deepSeq e null)).success;

  long = 20000;
  short = 1000;

  arms = {
    forced = readout (mintStrata (args long));
    unforced = unforcedRun (args long);
    unforced-wrapped = held (unforcedRun (args long));

    forced-small = readout (mintStrata (args short));
    unforced-small = unforcedRun (args short);

    plain-throw-wrapped = held (throw "gen-scope.mint-forcing: the instrument's own control");
  };
in
arms.${arm}
