# The consumer read over one subject's published wiring, and the two constructions it retired,
# over ONE resolution — plus the ill-formed inputs those constructions could not refuse, and the
# ordering control the suite cannot host.
#
# WHY THIS IS NOT A TEST. Every failure this file measures is an ABORT rather than a throw. The
# walk past the evaluator's call-depth guard reports `max-call-depth exceeded`, and past a RAISED
# guard reaches the C stack and reports `stack overflow` with no guard in front of it; the
# ill-formed-input arms report a missing attribute, an out-of-range `elemAt` or a type error at a
# list position. None of those is a value, so `tryEval` holds none of them and no `didThrow` cell
# can observe one. The only instrument that reads an abort is the EXIT CODE of a separate
# evaluation, and each arm below is one.
#
# ── WHAT SHIPS IS A FIELD READ, AND THE TWO CONSTRUCTIONS BELOW IT ARE CONTROLS ──
# `resolveClaims` publishes `wiring.<id>.entries`: the subject's emissions in global schedule
# order, values included. Reading them is an attribute lookup. `retiredWiringFor` is the indexed
# scan that used to rebuild that list from the two lossy views, and `walkWiringFor` is the list
# walk the scan itself replaced — both transcribed here verbatim, because a claim that the shipped
# read costs less and refuses more says nothing unless what it replaced is running in the same
# sweep.
#
# ── THE CONTROLS ARE CHECKED FOR FAITHFULNESS BEFORE THEY ARE TRUSTED ──
# `agree` runs all three arms over the same resolution at a size all three survive and compares the
# lists element for element. A control that computed something else would abort for reasons that
# say nothing about the construction under test, so a false `agree` invalidates the sweep rather
# than being reported as a difference.
#
# ── TWO ABORT SIGNATURES FOR THE WALK, NOT ONE, AND A SWEEP ARMED FOR ONE MISSES THE OTHER ──
# The walk chains through a FUNCTION APPLICATION — it calls itself on the tail — so its descent
# exhausts the call-depth guard first. Raising that guard does not make the walk flat; it moves the
# failure to the mechanism with no guard in front of it. Both readings are taken over the same arm
# at the same size, and what differs is the evaluator setting.
#
# ── THE ILL-FORMED-INPUT ARMS, AND WHAT RETIREMENT DID TO THEM ──
# The scan read TWO published views and paired them positionally, so every way those views could
# disagree — a trace naming a kind `byKind` lacks, a `byKind` list shorter than the trace's per-kind
# count, a trace entry with no `kind`, a trace that is not a list, a wiring record with no `byKind`,
# a subject with no `id_hash` — reached the evaluator instead of a refusal. Those inputs are built
# below and handed to the transcribed constructions, where they still abort. What changed is that
# there is no longer a library function to hand them to: `surfaceGone` reads that off the shipped
# library in the same run, because an absence is not something the aborting arms can show.
#
# ── HOW THE PUBLISHED FIELD IS READ, WHICH IS THE ONE THING RETIREMENT MOVED OUTWARD ──
# The record is total — a key for every subject a claim was about — so the two reflexive reads are
# the two broken ones, and both are arms here rather than assertions: `bareRead` aborts on a subject
# no claim named, `erasingRead` answers the same empty list for that subject and for one the run
# registered and left unwired, and `safeRead` keeps them apart.
#
# ── THE ORDERING ARM IS NOT ABOUT AN ABORT ──
# The field publishes global schedule order across kinds; the construction worth ruling out is one
# that reads the per-kind lists in kind order. `globalOrder` and `byKindOrder` compute both answers
# over the SAME k8s fixture the suite uses. If they agreed, the suite's order cell would be green
# under either construction and would be pinning nothing — so the sweep reports both and the shell
# arm calls agreement INVALID.
#
# RUN (per cell — the sweep is the shell script):
#   nix-instantiate --eval --strict --json \
#     --arg n 20000 --argstr arm walk ./ci/bench/wiring-scan.nix
{
  n ? 2000,
  arm ? "read",
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
  # The identity authority the library injects into its minting module. Built on the prelude this
  # file derives rather than on the one inside gen-schema's own lock, which is the same simplification
  # the root shim states and is inert here: the authority's closure is `builtins`-only.
  schema = import "${fetch "gen-schema"}/lib" {
    inherit prelude;
    merge = import "${fetch "gen-merge"}/lib" { inherit prelude; };
    algebra = import "${fetch "gen-algebra"}/lib";
  };
  s = import ../../lib { inherit prelude graph schema; };

  inherit (builtins)
    elemAt
    genList
    head
    length
    tail
    ;
  inherit (prelude)
    attrNames
    concatMap
    foldl'
    groupBy
    imap0
    listToAttrs
    map
    mapAttrs
    nameValuePair
    range
    unique
    ;

  # ── the synthetic resolution: one subject, `n` wiring emissions, three kinds round-robin ──
  # Built from ONE flat list and then published the three ways a run publishes it, so the views are
  # aligned by construction exactly as a real resolution's are. Three kinds rather than one because
  # a single-kind trace makes the walk's per-kind counter a constant and would exercise neither
  # retired construction's grouping.
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
      entries = flat;
    };
    trace.wiring.${id} = map (e: { inherit (e) kind claim; }) flat;
  };

  # ── what ships: the read, in the form a consumer is told to write ──
  # Registration is decided before anything is projected, so a subject the run never registered is
  # a `registered = false` answer rather than an abort.
  safeRead =
    res: subj:
    let
      sid = subj.id_hash;
    in
    if res.wiring ? ${sid} then
      {
        registered = true;
        inherit (res.wiring.${sid}) entries;
      }
    else
      { registered = false; };
  readEntries = res: subj: (safeRead res subj).entries;

  # ── the first negative control: the retired indexed scan, transcribed ──
  # Two published views, paired by rank. Every ill-formed-input arm in this file is an input on
  # which the two views disagree, or a malformed value standing in for one.
  retiredWiringFor =
    res: subj:
    let
      sid = subj.id_hash;
      traceEntries = res.trace.wiring.${sid} or [ ];
      byKind = (res.wiring.${sid} or { byKind = { }; }).byKind;
      positionsByKind = groupBy (i: (elemAt traceEntries i).kind) (range 0 (length traceEntries - 1));
      rankAt = listToAttrs (
        concatMap (k: imap0 (rank: i: nameValuePair (toString i) rank) positionsByKind.${k}) (
          attrNames positionsByKind
        )
      );
    in
    imap0 (i: e: {
      inherit (e) kind claim;
      wiring = elemAt byKind.${e.kind} rankAt.${toString i};
    }) traceEntries;

  # The retired splice over the retired scan. It is not merely "inherits both": laziness reaches
  # `attrNames` on the first drawn value before a later entry's out-of-range `elemAt`, so on one
  # input it aborts with a DIFFERENT message than the scan does, and an instrument that swept only
  # the scan would never read that path.
  retiredSpliceWiring =
    {
      resolution,
      subject,
      combine ? s.folds.one,
    }:
    let
      vals = map (x: x.wiring) (retiredWiringFor resolution subject);
      allKeys = unique (concatMap attrNames vals);
      keyVal = k: combine k (concatMap (e: if e ? ${k} then [ e.${k} ] else [ ]) vals);
    in
    listToAttrs (map (k: nameValuePair k (keyVal k)) allKeys);

  # ── the second negative control: the list walk the scan itself replaced ──
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

  # The same discipline where the result's shape is the caller's rather than this file's: the
  # ill-formed arms below are hand-built and carry no `v`, so they are forced whole and report only
  # that they returned. An arm that aborts prints nothing and is read off the exit code.
  forced = x: builtins.deepSeq x "returned";

  # ── the ill-formed inputs the retired constructions could not refuse ──
  handSubject = {
    id_hash = "h1";
    name = "hand";
  };
  # trace names a kind `byKind` lacks
  resMissingKind = {
    trace.wiring."h1" = [
      {
        kind = "b";
        claim = "p";
      }
    ];
    wiring."h1".byKind.a = [ 1 ];
  };
  # `byKind.<k>` SHORTER than the trace's per-kind count
  resShortList = {
    trace.wiring."h1" = [
      {
        kind = "a";
        claim = "p";
      }
      {
        kind = "a";
        claim = "q";
      }
    ];
    wiring."h1".byKind.a = [ 1 ];
  };
  # a wiring record for the subject that carries no `byKind` at all
  resNoByKind = {
    trace.wiring."h1" = [
      {
        kind = "a";
        claim = "p";
      }
    ];
    wiring."h1" = { };
  };
  # a trace entry with no `kind` field
  resNoKindField = {
    trace.wiring."h1" = [ { claim = "p"; } ];
    wiring."h1".byKind.a = [ 1 ];
  };
  # `trace.wiring.<id>` is not a list
  resTraceNotList = {
    trace.wiring."h1" = {
      a = 1;
    };
    wiring."h1".byKind.a = [ 1 ];
  };
  # the domain's good half: a hand-built resolution that IS aligned
  resAligned = {
    trace.wiring."h1" = [
      {
        kind = "a";
        claim = "p";
      }
    ];
    wiring."h1".byKind.a = [ { port = 1; } ];
  };

  # ── the read arms, over a run that registers a subject and wires nothing ──
  # The k8s fixture cannot host this: every claim subject there is wired, so a subject drawn from it
  # is FOREIGN to the run rather than unwired, and the two arms would measure one case twice.
  unwiredRun = s.resolveClaims {
    kinds = s.mkKinds [
      (s.mkKind {
        name = "noWire";
        resolve = c: _ctx: {
          resources.${c.subject.name} = {
            ok = true;
          };
        };
      })
    ];
    claims = [
      (s.mkClaim {
        kind = "noWire";
        subject = {
          id_hash = "id-q";
          name = "q";
        };
      })
    ];
  };
  unwiredSubject = {
    id_hash = "id-q";
  };
  neverClaimedSubject = {
    id_hash = "id-never-claimed";
  };
  erasingRead = res: subj: (res.wiring.${subj.id_hash} or { entries = [ ]; }).entries;

  # ── the ordering control, over the suite's own fixture ──
  k8s = import ../tests/_fixtures/k8s.nix { genScope = s; };
  sonarrGlobal = map (e: e.kind) (readEntries k8s.resolution k8s.apps.sonarr);
  sonarrByKind =
    let
      bk = k8s.resolution.wiring.${k8s.apps.sonarr.id_hash}.byKind;
    in
    concatMap (k: map (_: k) bk.${k}) (attrNames bk);

  arms = {
    # ── cost: what ships, against the two constructions it retired ──
    read = checksum (readEntries resolution subject);
    scan = checksum (retiredWiringFor resolution subject);
    walk = checksum (walkWiringFor resolution subject);
    # the controls are the real constructions, checked before they are trusted
    agree =
      let
        r0 = readEntries resolution subject;
      in
      r0 == retiredWiringFor resolution subject && r0 == walkWiringFor resolution subject;
    # The uncatchability cell: the walk, wrapped. A `true` here would mean `tryEval` contained the
    # abort and would refute the reason this file is an exit-code instrument rather than a suite.
    walkTry = (builtins.tryEval (builtins.deepSeq (walkWiringFor resolution subject) null)).success;
    # The catcher's own control, so an abort reading is never confused with a broken evaluation.
    catchControl = (builtins.tryEval (builtins.deepSeq (throw "control") null)).success;

    # ── the retirement itself, read off the shipped library ──
    # The aborting arms below show what the retired constructions do with ill-formed input. Only
    # this arm shows that no such input can reach the library any more, because an absence is not
    # something an abort can demonstrate.
    surfaceGone = !(s ? wiringFor) && !(s ? spliceWiring);

    # ── the nine ill-formed inputs, through the transcribed constructions ──
    missingKind = forced (retiredWiringFor resMissingKind handSubject);
    shortList = forced (retiredWiringFor resShortList handSubject);
    noByKind = forced (retiredWiringFor resNoByKind handSubject);
    noKindField = forced (retiredWiringFor resNoKindField handSubject);
    traceNotList = forced (retiredWiringFor resTraceNotList handSubject);
    noIdHash = forced (retiredWiringFor resAligned { name = "no-hash"; });
    spliceMissingKind = forced (retiredSpliceWiring {
      resolution = resMissingKind;
      subject = handSubject;
    });
    spliceShortList = forced (retiredSpliceWiring {
      resolution = resShortList;
      subject = handSubject;
    });
    spliceNoIdHash = forced (retiredSpliceWiring {
      resolution = resAligned;
      subject = {
        name = "no-hash";
      };
    });
    # The aligned half of that same hand-built domain, so the nine readings above are a statement
    # about misalignment rather than about hand-built resolutions.
    handAligned = forced (retiredWiringFor resAligned handSubject);

    # ── the three consumer reads: two reflexive, both broken ──
    safeReadUnwired = safeRead unwiredRun unwiredSubject;
    safeReadNeverClaimed = safeRead unwiredRun neverClaimedSubject;
    erasingReadUnwired = length (erasingRead unwiredRun unwiredSubject);
    erasingReadNeverClaimed = length (erasingRead unwiredRun neverClaimedSubject);
    bareReadNeverClaimed = length unwiredRun.wiring.${neverClaimedSubject.id_hash}.entries;

    # ── the ordering control ──
    globalOrder = sonarrGlobal;
    byKindOrder = sonarrByKind;
    orderDiffers = sonarrGlobal != sonarrByKind;
  };
in
arms.${arm} or (throw "gen-scope/wiring-scan: unknown arm '${arm}'")
