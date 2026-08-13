# `wiringFor`'s two arms — the shipped indexed scan, and the list walk it replaced — over ONE
# resolution, plus the ordering control the suite cannot host.
#
# WHY THIS IS NOT A TEST. Both of the walk's failures are ABORTS rather than throws: past the
# evaluator's call-depth guard it reports `max-call-depth exceeded`, and past a RAISED guard it
# reaches the C stack and reports `stack overflow` with no guard in front of it. Neither is a
# value, so `tryEval` holds neither and no `didThrow` cell can observe either. The only instrument
# that reads an abort is the EXIT CODE of a separate evaluation. The `walkTry` arm below is that
# demonstration, run as a cell rather than asserted in prose.
#
# ── THE COMPARISON IS THE INSTRUMENT, SO THE CONTROL IS THE REAL CONSTRUCTION ──
# `walkWiringFor` below is the retiring library's `walk`, transcribed, with only the trace field's
# rename applied. It is not a strawman written to fail: the `agree` arm runs both arms over the
# same resolution at a size both survive and asserts they return the SAME LIST, element for
# element. A control that computed something else would abort for reasons that say nothing about
# the construction under test.
#
# ── TWO SIGNATURES, NOT ONE, AND A SWEEP ARMED FOR ONE MISSES THE OTHER ──
# The walk chains through a FUNCTION APPLICATION — it calls itself on the tail — so its descent
# exhausts the call-depth guard first. Raising that guard does not make the walk flat; it moves
# the failure to the mechanism with no guard in front of it. Both readings are taken over the same
# arm at the same size, and what differs is the evaluator setting.
#
# ── THE ORDERING CONTROL, WHICH IS ABOUT THE FIXTURE AND NOT ABOUT AN ABORT ──
# `wiringFor` exists to publish global schedule order across kinds; the construction worth ruling
# out is one that reads the per-kind lists in kind order. `globalOrder` and `byKindOrder` compute
# both answers over the SAME k8s fixture the suite uses. If they agreed, the suite's order cell
# would be green under either construction and would be pinning nothing — so the sweep reports
# both and the shell arm calls agreement INVALID.
#
# RUN (per cell — the sweep is the shell script):
#   nix-instantiate --eval --strict --json \
#     --arg n 20000 --argstr arm walk ./ci/bench/wiring-scan.nix
{
  n ? 2000,
  arm ? "scan",
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
  s = import ../../lib { inherit prelude graph; };

  inherit (builtins)
    elemAt
    genList
    head
    tail
    ;
  inherit (prelude)
    attrNames
    concatMap
    foldl'
    groupBy
    map
    mapAttrs
    ;

  # ── the synthetic resolution: one subject, `n` wiring emissions, three kinds round-robin ──
  # Built from ONE flat list and then projected the two ways the run publishes it, so the two
  # views are aligned by construction exactly as a real resolution's are. Three kinds rather than
  # one because a single-kind trace makes the walk's per-kind counter a constant and would exercise
  # neither construction's grouping.
  id = "id-swept-subject";
  subject = {
    id_hash = id;
  };
  kindOf = i: "k${toString (i - (i / 3) * 3)}";
  flat = genList (i: {
    kind = kindOf i;
    claim = [ i ];
    wiring = {
      v = i;
    };
  }) n;
  resolution = {
    wiring.${id} = {
      inherit subject;
      byKind = mapAttrs (_: es: map (e: e.wiring) es) (groupBy (e: e.kind) flat);
    };
    trace.wiring.${id} = map (e: { inherit (e) kind claim; }) flat;
  };

  # ── the negative control: the retiring library's `walk`, transcribed ──
  # One evaluator frame per trace entry, and a whole-record copy of the per-kind counter beside it.
  walkWiringFor =
    res: subj:
    let
      sid = subj.id_hash;
      traceEntries = res.trace.wiring.${sid} or [ ];
      byKind = (res.wiring.${sid} or { byKind = { }; }).byKind;
      walk =
        counts: entries:
        if entries == [ ] then
          [ ]
        else
          let
            e = head entries;
            c = counts.${e.kind} or 0;
          in
          [
            {
              inherit (e) kind claim;
              wiring = elemAt byKind.${e.kind} c;
            }
          ]
          ++ walk (
            counts
            // {
              ${e.kind} = c + 1;
            }
          ) (tail entries);
    in
    walk { } traceEntries;

  # Forces every element of a result and returns a single number, so an arm's reading is small and
  # a partially-forced list cannot be mistaken for a completed one.
  checksum = entries: foldl' (a: e: a + e.wiring.v) 0 entries;

  # ── the ordering control, over the suite's own fixture ──
  k8s = import ../tests/_fixtures/k8s.nix { genScope = s; };
  sonarrGlobal = map (e: e.kind) (s.wiringFor k8s.resolution k8s.apps.sonarr);
  sonarrByKind =
    let
      bk = k8s.resolution.wiring.${k8s.apps.sonarr.id_hash}.byKind;
    in
    concatMap (k: map (_: k) bk.${k}) (attrNames bk);
in
if arm == "scan" then
  checksum (s.wiringFor resolution subject)
else if arm == "walk" then
  checksum (walkWiringFor resolution subject)
else if arm == "agree" then
  s.wiringFor resolution subject == walkWiringFor resolution subject
else if arm == "walkTry" then
  # The uncatchability cell: the same walk, wrapped. A `false` here would mean `tryEval` contained
  # the abort and would refute the reason this file is an exit-code instrument rather than a suite.
  (builtins.tryEval (builtins.deepSeq (walkWiringFor resolution subject) null)).success
else if arm == "catchControl" then
  # The catcher's own control, so an abort reading is never confused with a broken evaluation.
  (builtins.tryEval (builtins.deepSeq (throw "control") null)).success
else if arm == "globalOrder" then
  sonarrGlobal
else if arm == "byKindOrder" then
  sonarrByKind
else if arm == "orderDiffers" then
  sonarrGlobal != sonarrByKind
else
  throw "gen-scope/wiring-scan: unknown arm '${arm}'"
