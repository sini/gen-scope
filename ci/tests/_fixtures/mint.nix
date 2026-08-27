# THE MINTING FIXTURES — the handles, the substituted drivers, the emitter fixtures and the two
# refusal texts, shared by the two suites that read them.
#
# NOT A SUITE. It sits under `_fixtures/` because the tree importer ignores any path containing
# `/_`, so this file is reached only by the suites that import it and never as a flake module.
#
# ★ WHY THESE LIVE IN ONE PLACE. The cells that read them are split across two outputs by the shape
# of their assertion rather than by their subject: a cell whose subject is a refusal MESSAGE cannot
# live under `flake.tests`, because the batch asserter behind `checks.default` quantifies over that
# option and forces every `expr` unconditionally, so a throwing one crashes the gate instead of
# failing a cell. The subject is the same minting run either way. Duplicating the fixtures across
# the two files would make the split a fork: the refusal TEXTS below are the specification of those
# bytes, and a specification with two copies has two answers the moment one of them is edited.
#
# ★★ WHAT THIS FILE COMMITS TO THAT THE RULES DO NOT FIX, stated here rather than left for a reader
# to reverse-engineer out of the fixtures. The entry's `Args`/`Result` records, the module's formals,
# the driver's `Args`/`Result` and `advance`'s two-field per-stratum record are all specified
# surfaces and the cells assert them directly. THREE THINGS ARE NOT, and the fixtures fix them by
# construction because executable cells cannot avoid it:
#
#   1. THE EMITTER RECORD. An emitter must declare its own pass, the identifier of the node it
#      mints, that node's kind, its labelled relata, its content contribution and a site
#      description — the last because a conflicting-contribution refusal names both emitters' sites.
#      `mkEmitter` below is the one place that shape appears.
#   2. THE KIND STRATUM'S SHAPE. It arrives as an already-evaluated value and the entry holds no
#      handle with which to re-open a kind's option set, so the cells assert what the entry does
#      NOT expose rather than what a kind contains; `kindStratum` is a placeholder value.
#   3. THE REFUSAL TEXTS. Both refusals are required to name specific coordinates but neither text
#      is fixed anywhere, so the literals below ARE the specification of those bytes.
#
# `unrun` AS A PASS-THROUGH is NOT among them, and the distinction matters because six cells rest on
# it. The entry returns a list EQUAL to the one its driver returned — it does not filter it, re-type
# it or substitute a constant for it. That identity is a ruled property of the entry rather than an
# assumption these fixtures make, which is what makes reading a substituted driver's report back
# through the field a specified channel and not a trick.
{
  lib,
  genScope,
  genPreludeLib,
  genGraph,
}:
let
  # ── THE HANDLES ──
  #
  # `mint` is the published entry: the authority is injected by the library and is not a formal a
  # caller fills, so a cell that wants a predictable identity in a refusal message cannot reach it
  # here. `mintModule` is the module before injection, and substituting one of its formals is how a
  # cell observes what the minting instance hands its driver.
  mint = genScope.mintStrata;
  mintModule = import ../../../lib/mint.nix;

  # A substituted authority. Identity minting is `gen-schema`'s and stays there; what a cell needs
  # is a total function of the same arity whose output it can write down, so that a refusal naming
  # an identity has a text a cell can anchor.
  stubIdentity =
    kind: _labels: _valueOf:
    "${kind}:stub";

  # The module under a chosen driver. Everything the minting instance computes before the driver
  # runs — the schedule, the seed, the per-stratum step — is visible only here, because the entry's
  # own result reports the schedule's LENGTH and never the schedule.
  withDriver =
    stratify:
    (mintModule {
      prelude = genPreludeLib;
      graph = genGraph;
      hashIdentity = stubIdentity;
      inherit stratify;
    }).mintStrata;

  mintUnderStubIdentity = withDriver genScope.stratify;

  # ── THE SPY DRIVER ──
  #
  # A driver that reports rather than runs. It returns a well-formed driver result, so the entry's
  # own post-processing succeeds, and it carries what the cell wants to read out through `unrun` —
  # the one result field the specified surface carries through from the driver rather than deriving.
  # `unrun` is empty by theorem in a real run and no behaviour rests on a consumer reading it, which
  # is what leaves it free to carry a readout here; the pass-through it depends on is a ruled
  # property of the entry rather than an assumption made at this end.
  spy = report: args: {
    settled = [ ];
    strata = builtins.length args.schedule;
    unrun = report args;
  };

  # A stratum's items, as the driver would hand them to `advance`: the seed filtered by the
  # instance's own stratum assignment, ordered by the instance's own within-stratum order. Both come
  # out of the captured arguments, so nothing about the instance is assumed.
  #
  # ★★ APPLYING `advance` OUTSIDE THE FOLD IS SAFE, AND THE REASON IS WHO OWNS THE FROZEN SET. The
  # driver walks the schedule; the frozen set is accumulated by the MINTING INSTANCE'S OWN fold over
  # that same schedule. It cannot be otherwise: the per-stratum record a driver hands an instance is
  # `{ stratum, items }` and carries no frozen-set channel, so there is no construction in which the
  # driver builds the set. `advance` reads its stratum's output out of that accumulation, which is
  # why a spy that reports instead of walking leaves the earlier-strata set fully populated rather
  # than empty, and why no unresolved-relatum refusal becomes reachable by taking this path. The
  # fixtures applied through `advanceAt` below are relatum-free — a property they happen to have,
  # not a constraint this path imposes.
  itemsAt = args: s: builtins.sort args.within (builtins.filter (i: args.stratumOf i == s) args.seed);
  advanceAt =
    args: s:
    args.advance {
      stratum = s;
      items = itemsAt args s;
    };

  scheduleSpy = withDriver (spy (args: args.schedule));
  emittedSpy = withDriver (spy (args: map (s: (advanceAt args s).emitted) args.schedule));
  settledSpy = withDriver (spy (args: map (s: (advanceAt args s).settled != [ ]) args.schedule));
  advanceFormalsSpy = withDriver (
    spy (args: builtins.attrNames (builtins.functionArgs args.advance))
  );

  # The arming for the emptiness theorem: a driver that drops the LAST declared stratum from the
  # schedule it was given. Items assigned to that stratum are then outside the schedule, which is
  # the only construction under which a run can report leftovers — and it must REPORT them rather
  # than throw, because leftovers are a fact a caller reads, not a refusal.
  #
  # ★★ THE LAST RATHER THAN THE FIRST, AND THE CHOICE IS LOAD-BEARING. Relata resolve against
  # STRICTLY EARLIER strata, so dropping the HEAD unsettles everything the surviving strata depend
  # on and the variant refuses by name — at exactly the assertion that demands it not throw, which
  # would make a refusal read as a discharged arming. Dropping the tail leaves every surviving
  # stratum's predecessors intact and leaves the highest declared pass as the leftover.
  mintShortSchedule = withDriver (
    args: genScope.stratify (args // { schedule = lib.init args.schedule; })
  );

  # ── THE FIXTURES ──
  mkEmitter =
    {
      pass,
      identifier,
      kind ? "widget",
      relata ? { },
      content ? { },
      site ? "site-${identifier}",
    }:
    {
      inherit
        pass
        identifier
        kind
        relata
        content
        site
        ;
    };

  # The schema stratum, already evaluated before the entry is called. Its contents are not this
  # suite's subject; that it arrives as a value with no handle in the result is.
  kindStratum = {
    widget = { };
    store = { };
    service = { };
  };

  withKinds = emitters: {
    inherit emitters;
    kinds = kindStratum;
  };

  # Declared passes {0,3,3,7}: duplicated and non-contiguous, so a schedule that deduplicates and a
  # schedule that enumerates a range are told apart by the same fixture.
  base = mkEmitter {
    pass = 0;
    identifier = "base";
  };
  midA = mkEmitter {
    pass = 3;
    identifier = "mid-a";
    relata.under = "base";
  };
  midB = mkEmitter {
    pass = 3;
    identifier = "mid-b";
    relata.under = "base";
  };
  top = mkEmitter {
    pass = 7;
    identifier = "top";
    relata.under = "mid-a";
  };
  fixtureSchedule = withKinds [
    base
    midA
    midB
    top
  ];

  # The same three declared passes {0,3,7} with NO relata anywhere, for the two cells that apply
  # `advance` directly, one stratum at a time, outside any fold. Nothing resolves, so these cells
  # read the per-stratum step's shape with no resolution behaviour in the frame at all. The schedule
  # it derives is the same length as the fixture above, so the shapes the two cells assert are
  # unchanged by the substitution.
  unrelated =
    pass: identifier:
    mkEmitter {
      inherit pass identifier;
    };
  fixtureUnrelated = withKinds [
    (unrelated 0 "free-a")
    (unrelated 3 "free-b")
    (unrelated 7 "free-c")
  ];

  # Declared passes {0,7}. A contiguous range over the same declaration would run eight strata.
  fixtureSparse = withKinds [
    base
    (mkEmitter {
      pass = 7;
      identifier = "top";
      relata.under = "base";
    })
  ];

  # The admitted case. Two nodes settle at pass 0; the pass-1 binding names both of them by
  # identifier and both resolve. Without it three refusals would be equally satisfied by a resolver
  # that refuses everything.
  db = mkEmitter {
    pass = 0;
    identifier = "db";
    kind = "store";
  };
  web = mkEmitter {
    pass = 0;
    identifier = "web";
    kind = "store";
  };
  app = mkEmitter {
    pass = 1;
    identifier = "app";
    kind = "service";
    relata = {
      backing = "db";
      fronting = "web";
    };
  };
  fixtureAdmitted = withKinds [
    db
    web
    app
  ];

  # The same binding with its two relatum VALUES exchanged between the two labels. The label set is
  # unchanged, so a result that cannot tell them apart is a result in which the labels are decorative.
  appSwapped = mkEmitter {
    pass = 1;
    identifier = "app";
    kind = "service";
    relata = {
      backing = "web";
      fronting = "db";
    };
  };
  fixtureSwapped = withKinds [
    db
    web
    appSwapped
  ];

  # A later pass naming an identity already frozen. The freeze is over MEMBERSHIP, so the map's
  # values may be revisited: the later emission contributes content and does not re-mint. The two
  # emissions carry DIFFERENT keys, which is the case the rules settle; what a later pass may do to
  # a key an earlier one already carries is open (see the note on the cross-pass cell).
  fixtureCrossPass = withKinds [
    (mkEmitter {
      pass = 0;
      identifier = "svc";
      kind = "service";
      content.port = 80;
    })
    (mkEmitter {
      pass = 2;
      identifier = "svc";
      kind = "service";
      content.host = "h";
    })
  ];

  # Two emitters, one pass, one identity. Within a pass there is no order, so the only outcomes an
  # unordered fold may have are agreement and refusal — which is what buys confluence without
  # inventing a within-pass position (ADR-0022).
  collapseA = mkEmitter {
    pass = 1;
    identifier = "dup";
    content.port = 80;
    site = "site-a";
  };
  collapseB = mkEmitter {
    pass = 1;
    identifier = "dup";
    content.port = 80;
    site = "site-b";
  };
  conflictA = collapseA;
  conflictB = mkEmitter {
    pass = 1;
    identifier = "dup";
    content.port = 8080;
    site = "site-b";
  };

  # A second conflicting pair, on a different key and different sites. Two refusals differing only
  # in their coordinates are what say the message reports the construction rather than a constant.
  conflictOtherA = mkEmitter {
    pass = 1;
    identifier = "dup";
    content.host = "left";
    site = "site-x";
  };
  conflictOtherB = mkEmitter {
    pass = 1;
    identifier = "dup";
    content.host = "right";
    site = "site-y";
  };

  # ── THE SILENT-DROP PAIR (den-hoag-mintone-silent-drop-1wjov) ──
  # `wellFormedEmitter` carries exactly the six fields an emitter has; `smuggledFieldEmitter` is that
  # same record plus one `mintOne` never reads, standing for a kind-option contribution smuggled onto
  # an emitter. `mkEmitter`'s own formals are closed the same way `mintOne`'s now are, so the surplus
  # has to arrive by `//` after construction — going through the builder would refuse it a layer too
  # early to exercise what this pair is for.
  wellFormedEmitter = mkEmitter {
    pass = 0;
    identifier = "carrier";
    kind = "widget";
    content.tag = "well-formed";
  };
  smuggledFieldEmitter = wellFormedEmitter // {
    kindOption = "sneaky";
  };

  # ── THE TWO REFUSAL TEXTS ──
  #
  # They are different in kind and must be distinguishable, or a cell asserting one passes on the
  # other: the first is a RESOLUTION failure at mint time, the second a MERGE failure after minting
  # has already succeeded.
  unresolvedRelatum =
    identifier: label: kind: pass:
    "gen-scope.mintStrata: unresolved relatum '${identifier}' (label '${label}', minting kind '${kind}', pass ${toString pass})";
  conflictingContribution =
    key: leftSite: rightSite:
    "gen-scope.mintStrata: conflicting contributions to identity 'widget:stub' at key '${key}' (${leftSite}, ${rightSite})";
in
{
  inherit
    mint
    mintModule
    mintUnderStubIdentity
    mintShortSchedule
    scheduleSpy
    emittedSpy
    settledSpy
    advanceFormalsSpy
    mkEmitter
    withKinds
    fixtureSchedule
    fixtureUnrelated
    fixtureSparse
    fixtureAdmitted
    fixtureSwapped
    fixtureCrossPass
    db
    web
    app
    collapseA
    collapseB
    wellFormedEmitter
    smuggledFieldEmitter
    conflictA
    conflictB
    conflictOtherA
    conflictOtherB
    unresolvedRelatum
    conflictingContribution
    ;
}
