# THE THIRD TEST OUTPUT — cells for a minting entry that does not exist yet, and why they need an
# output of their own.
#
# These cells assert the frozen-set semantics of a staged minting run: an identifier is the scope
# graph's vertex name and not the identity (ADR-0016 ruling 5), a pass resolves relata only against
# identities settled by STRICTLY EARLIER passes, and a cycle is inexpressible because it would
# require a pass to see its own output (ADR-0016 ruling 7). The entry they call is not built. Every
# cell that reaches it is therefore RED at this revision, and that is the point: the cells are
# written against a specified surface rather than against running code, so the code that lands next
# is derived against them instead of the other way round.
#
# ★ WHY A THIRD OUTPUT RATHER THAN CELLS IN `./tests`. Red cells under `testModules` turn
# `nix-unit --flake ./ci#tests` red at HEAD for every consumer until the entry lands, and
# `checks.default`'s batch asserter quantifies over `flake.tests` and forces every `expr`
# unconditionally — the same reason `tests-error.nix` exists. A red suite is also where a real
# regression hides: nobody can tell the intended red from a new one. Hosting them here keeps the
# shipped suites honest while these stay live on the nix-unit path:
#
#   nix-unit --flake ./ci#tests          # the shipped suites
#   nix-unit --flake ./ci#testsError     # shipped cells whose subject is an error message
#   nix-unit --flake ./ci#testsPending   # these — red until the minting entry exists
#
# ★★ A DECLARED-BUT-EMPTY OUTPUT REPORTS `0/0 successful` AND EXITS 0. An exit code alone therefore
# discharges nothing about this output in either direction, and the collected cell count is reported
# and reconciled against the declared set at every run of it.
#
# ★★ THE RED MUST BE FOR THE RIGHT REASON, so the suite carries cells that PASS at this revision:
# the two formals-instrument controls, the pattern-discrimination cell, and the library-reachability
# control assert facts true of `gen-scope` as it stands and are independent of the absent entry. A
# suite in which nothing can pass is a suite whose red says nothing.
#
# ★★★ WHAT THIS FILE COMMITS TO THAT THE RULES DO NOT FIX, stated here rather than left for a reader
# to reverse-engineer out of the fixtures. The entry's `Args`/`Result` records, the module's formals,
# the driver's `Args`/`Result` and `advance`'s two-field per-stratum record are all specified
# surfaces and the cells assert them directly. THREE THINGS ARE NOT, and the cells fix them by
# construction because executable cells cannot avoid it:
#
#   1. THE EMITTER RECORD. An emitter must declare its own pass, the identifier of the node it
#      mints, that node's kind, its labelled relata, its content contribution and a site
#      description — the last because a conflicting-contribution refusal names both emitters' sites.
#      `mkEmitter` below is the one place that shape appears.
#   2. THE KIND STRATUM'S SHAPE. It arrives as an already-evaluated value and the entry holds no
#      handle with which to re-open a kind's option set, so these cells assert what the entry does
#      NOT expose rather than what a kind contains; `kindStratum` is a placeholder value.
#   3. THE REFUSAL TEXTS. Both refusals are required to name specific coordinates but neither text
#      is fixed anywhere, so the literals below ARE the specification of those bytes.
#
# ★ MESSAGE PATTERNS ARE ANCHORED AND MACHINE-ESCAPED. `expectedError.msg` is regex-SEARCHED, not
# whole-matched, so a pattern naming a prefix passes against a message that says something else
# after it. `exactly` escapes the literal and anchors both ends, which is the same idiom the
# error-message suite uses and for the same reason: a hand-written pattern is one forgotten
# backslash away from a metacharacter matching something it was never meant to spell.
{
  lib,
  genScope,
  genPreludeLib,
  genGraph,
  ...
}:
let
  # The message, pinned to the byte. `escapeRegex` is the prelude's own and its metacharacter set is
  # byte-identical to nixpkgs', so what is anchored below is the text as written above it.
  exactly = msg: "^" + genPreludeLib.escapeRegex msg + "$";

  # ── THE HANDLES ──
  #
  # `mint` is the published entry: the authority is injected by the library and is not a formal a
  # caller fills, so a cell that wants a predictable identity in a refusal message cannot reach it
  # here. `mintModule` is the module before injection, and substituting one of its formals is how a
  # cell observes what the minting instance hands its driver. Both are absent at this revision; the
  # bindings are lazy, so their absence fails the cells that force them and leaves the rest alone.
  mint = genScope.mintStrata;
  mintModule = import ../lib/mint.nix;

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
  # the one result field that is a pass-through list. `unrun` is empty by theorem in a real run and
  # is not a live channel any behaviour rests on, which is exactly what makes it usable as one here.
  spy = report: args: {
    settled = [ ];
    strata = builtins.length args.schedule;
    unrun = report args;
  };

  # A stratum's items, as the driver would hand them to `advance`: the seed filtered by the
  # instance's own stratum assignment, ordered by the instance's own within-stratum order. Both come
  # out of the captured arguments, so nothing about the instance is assumed.
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

  # The arming for the emptiness theorem: a driver that drops the first declared stratum from the
  # schedule it was given. Items assigned to that stratum are then outside the schedule, which is
  # the only construction under which a run can report leftovers — and it must REPORT them rather
  # than throw, because leftovers are a fact a caller reads, not a refusal.
  mintShortSchedule = withDriver (
    args: genScope.stratify (args // { schedule = builtins.tail args.schedule; })
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
  # values may be revisited: the later emission contributes content and does not re-mint.
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
  # Same type as `flake.tests` and `flake.testsError`, because it is the same kind of thing read by
  # the same runner — only the revision at which the cells are expected to pass differs.
  options.flake.testsPending = lib.mkOption {
    type = lib.types.lazyAttrsOf (lib.types.lazyAttrsOf lib.types.raw);
    default = { };
    description = "Test suites whose subject is NOT BUILT YET: { suite.test = { expr; expected | expectedError; }; }. Read by `nix-unit --flake ./ci#testsPending`, which is red until the subject lands. Outside `flake.tests` so the shipped suites stay green, and outside `flake.testsError` so a pending cell is never mistaken for a shipped one.";
  };

  config.flake.testsPending.minting = {
    # ── CONTROLS THAT PASS AT THIS REVISION ──
    # Without them the suite's red is indistinguishable from a suite that cannot evaluate at all.
    test-control-the-library-is-reachable-and-a-shipped-entry-is-live = {
      expr = {
        mkClaim = builtins.isFunction genScope.mkClaim;
        resolveClaims = builtins.isFunction genScope.resolveClaims;
      };
      expected = {
        mkClaim = true;
        resolveClaims = true;
      };
    };
    test-control-an-extra-formal-is-visible-to-the-formals-instrument = {
      expr = builtins.attrNames (
        builtins.functionArgs (
          {
            emitters,
            kinds,
            frozen,
          }:
          null
        )
      );
      expected = [
        "emitters"
        "frozen"
        "kinds"
      ];
    };
    test-control-an-extra-per-stratum-field-is-visible-to-the-formals-instrument = {
      expr = builtins.attrNames (
        builtins.functionArgs (
          {
            stratum,
            items,
            frozen,
          }:
          null
        )
      );
      expected = [
        "frozen"
        "items"
        "stratum"
      ];
    };

    # ── THE TWO REFUSALS ARE DISCRIMINATED ──
    # Asserted against EACH OTHER rather than merely both non-empty. Both patterns are anchored at
    # both ends, so `match`'s whole-match and the runner's search agree on them; a pattern that
    # matched the other message would make the refusal cells interchangeable.
    test-the-two-refusal-patterns-do-not-match-each-others-message = {
      expr =
        let
          unresolved = unresolvedRelatum "db" "backing" "service" 0;
          conflict = conflictingContribution "port" "site-a" "site-b";
        in
        {
          unresolvedPatternOnConflict = builtins.match (exactly unresolved) conflict != null;
          conflictPatternOnUnresolved = builtins.match (exactly conflict) unresolved != null;
          eachPatternMatchesItsOwn =
            builtins.match (exactly unresolved) unresolved != null
            && builtins.match (exactly conflict) conflict != null;
        };
      expected = {
        unresolvedPatternOnConflict = false;
        conflictPatternOnUnresolved = false;
        eachPatternMatchesItsOwn = true;
      };
    };

    # ── THE ENTRY'S ARGUMENT RECORD ──
    test-entry-argument-record-is-exactly-emitters-and-kinds = {
      expr = builtins.attrNames (builtins.functionArgs mint);
      expected = [
        "emitters"
        "kinds"
      ];
    };
    # The authority is injected by the library and never supplied by a caller: a caller-supplied
    # minter makes one minting authority a convention rather than a fact (ADR-0016 ruling 5). A
    # caller-supplied frozen set is refused on the neighbouring ground — a forgeable frozen set is a
    # rule authors must obey rather than a construction — and a stratum-0 seed would be that set
    # under another name.
    test-entry-formals-admit-neither-the-authority-nor-a-frozen-set = {
      expr = builtins.filter (n: builtins.functionArgs mint ? ${n}) [
        "hashIdentity"
        "frozen"
        "frozenSet"
        "seed"
      ];
      expected = [ ];
    };
    test-entry-formals-answer-present-for-the-two-declared-fields = {
      expr = builtins.filter (n: builtins.functionArgs mint ? ${n}) [
        "emitters"
        "kinds"
      ];
      expected = [
        "emitters"
        "kinds"
      ];
    };
    test-module-formals-carry-the-authority-and-the-driver = {
      expr = builtins.attrNames (builtins.functionArgs mintModule);
      expected = [
        "graph"
        "hashIdentity"
        "prelude"
        "stratify"
      ];
    };

    # ── THE RESULT RECORD, AND THE KIND STRATUM'S ABSENCE FROM IT ──
    # The remedy for a late kind-option contribution is a SHAPE, so its oracle is structural: the
    # entry does not participate in the fixpoint that produces kind options, and the observable form
    # of that is a result carrying no handle through which one could be re-opened. Asserting a throw
    # instead would be vacuous — under this construction there is nothing to throw.
    test-result-record-is-exactly-nodes-edges-strata-and-unrun = {
      expr = builtins.attrNames (mint fixtureAdmitted);
      expected = [
        "edges"
        "nodes"
        "strata"
        "unrun"
      ];
    };
    test-kind-stratum-is-an-argument-with-no-handle-in-the-result = {
      expr = {
        isAnArgument = builtins.functionArgs mint ? kinds;
        reopenableFromTheResult = mint fixtureAdmitted ? kinds;
      };
      expected = {
        isAnArgument = true;
        reopenableFromTheResult = false;
      };
    };

    # ── THE SCHEDULE IS THE DECLARED INDICES, ASCENDING, DEDUPLICATED ──
    # Not a range and not a topological sort. Ascending because pass N's predecessors are passes
    # 0..N-1. Deriving it from the declared set is what removes the cost of the empty strata a range
    # would run, without introducing a limit anywhere.
    test-schedule-is-the-distinct-declared-passes-ascending = {
      expr = (scheduleSpy fixtureSchedule).unrun;
      expected = [
        0
        3
        7
      ];
    };
    test-strata-is-the-schedule-length = {
      expr = (mint fixtureSchedule).strata;
      expected = 3;
    };
    test-a-sparse-declaration-does-not-become-a-contiguous-range = {
      expr = (scheduleSpy fixtureSparse).unrun;
      expected = [
        0
        7
      ];
    };
    test-a-sparse-declaration-runs-two-strata-not-eight = {
      expr = (mint fixtureSparse).strata;
      expected = 2;
    };

    # ── THE SCHEDULE IS IMMUTABLE BECAUSE NOTHING IS EMITTED INTO IT ──
    # A stratum does not produce emitters. What varies per stratum is what each emitter mints; which
    # emitters exist is fixed before the first stratum runs. If a stratum could emit an emitter
    # carrying a fresh declared pass, the schedule computed at the start would be incomplete and the
    # boundedness of the run would be delivering silence rather than a theorem.
    test-advance-emits-nothing-at-every-stratum = {
      expr = (emittedSpy fixtureSchedule).unrun;
      expected = [
        [ ]
        [ ]
        [ ]
      ];
    };
    # Without this the cell above passes on an `advance` that returns nothing at all.
    test-control-settled-is-non-empty-at-the-same-strata = {
      expr = (settledSpy fixtureSchedule).unrun;
      expected = [
        true
        true
        true
      ];
    };

    # ── NO VIEW OF IN-FLIGHT STATE ──
    # The per-stratum record is the driver's and gains no third field here. A user-visible "is X
    # minted yet?" during a pass would make the answer depend on evaluation order inside the pass,
    # which is what the unordered within-pass fold is constructed to avoid.
    test-advance-record-is-exactly-stratum-and-items = {
      expr = (advanceFormalsSpy fixtureSchedule).unrun;
      expected = [
        "items"
        "stratum"
      ];
    };

    # ── EMPTINESS OF THE LEFTOVER SET IS A THEOREM, NOT AN OBSERVATION ──
    # The schedule is DERIVED FROM the declared passes, so no emitter's pass can fall outside it.
    test-nothing-is-left-unrun-on-any-fixture = {
      expr = map (f: (mint f).unrun) [
        fixtureAdmitted
        fixtureSchedule
        fixtureCrossPass
      ];
      expected = [
        [ ]
        [ ]
        [ ]
      ];
    };
    # The arming, and without it the cell above is satisfied by a run that drops items silently: a
    # driver whose schedule omits one declared stratum must REPORT the leftovers and must not throw.
    test-armed-a-schedule-omitting-driver-reports-leftovers-without-throwing = {
      expr =
        let
          attempt = builtins.tryEval (
            let
              u = (mintShortSchedule fixtureSchedule).unrun;
            in
            builtins.deepSeq u u
          );
        in
        {
          inherit (attempt) success;
          leftoversReported = attempt.success && builtins.length attempt.value > 0;
        };
      expected = {
        success = true;
        leftoversReported = true;
      };
    };

    # ── THE ADMITTED CASE, AND LABELLED INCIDENCE ──
    # One node plus one edge per relatum, each edge carrying the relation's label for that relatum —
    # the same label that keyed the identity. The label set is one vocabulary shared between
    # identity and traversal, which is what makes choosing a label choosing a traversal token
    # (ADR-0024 as amended).
    test-a-resolving-relatum-is-admitted = {
      expr = builtins.attrNames (mint fixtureAdmitted).nodes;
      expected = [
        "app"
        "db"
        "web"
      ];
    };
    test-one-node-and-one-labelled-edge-per-relatum = {
      expr =
        let
          r = mint fixtureAdmitted;
          sorted = builtins.sort (a: b: a < b);
        in
        {
          nodes = builtins.length (builtins.attrNames r.nodes);
          edges = builtins.length r.edges;
          labels = sorted (map (e: e.label) r.edges);
          froms = sorted (genPreludeLib.unique (map (e: e.from) r.edges));
          tos = sorted (map (e: e.to) r.edges);
        };
      expected = {
        nodes = 3;
        edges = 2;
        labels = [
          "backing"
          "fronting"
        ];
        froms = [ "app" ];
        tos = [
          "db"
          "web"
        ];
      };
    };
    # The label set is a SET: a permuted expectation must still pass, so the cell above is not
    # secretly asserting an emission order.
    test-the-label-set-survives-a-permuted-expectation = {
      expr =
        let
          declared = [
            "fronting"
            "backing"
          ];
          found = map (e: e.label) (mint fixtureAdmitted).edges;
          sorted = builtins.sort (a: b: a < b);
        in
        sorted found == sorted declared;
      expected = true;
    };
    # And a CHANGED label set must not: without this the set comparison above is satisfied by any
    # two-element result.
    test-a-changed-label-set-is-visible-to-the-same-comparison = {
      expr =
        let
          changed = [
            "backing"
            "adjacent"
          ];
          found = map (e: e.label) (mint fixtureAdmitted).edges;
          sorted = builtins.sort (a: b: a < b);
        in
        sorted found == sorted changed;
      expected = false;
    };

    # ── CROSS-PASS CONTRIBUTION ──
    # A later pass naming an identity already in the frozen set contributes content. It never
    # re-mints and it never refuses at minting: two emitters never yield two nodes.
    test-a-later-pass-contributes-content-without-a-second-node = {
      expr =
        let
          r = mint fixtureCrossPass;
        in
        {
          nodes = builtins.attrNames r.nodes;
          content = r.nodes.svc.content;
        };
      expected = {
        nodes = [ "svc" ];
        content = {
          host = "h";
          port = 80;
        };
      };
    };

    # ── WITHIN ONE PASS, IDENTICAL CONTRIBUTIONS COLLAPSE ──
    test-same-pass-identical-contributions-collapse = {
      expr =
        let
          r = mint (withKinds [
            collapseA
            collapseB
          ]);
        in
        {
          nodes = builtins.attrNames r.nodes;
          content = r.nodes.dup.content;
        };
      expected = {
        nodes = [ "dup" ];
        content.port = 80;
      };
    };

    # ── PERMUTATION, ARM 1a: EMITTER PRESENTATION ORDER ──
    # Pass assignment is declared by the emitter and the contribution order IS pass order, so the
    # schedule is invariant under presentation order and so is everything downstream of it. Compared
    # through `toJSON` because that is byte identity rather than structural equality, and because a
    # result carrying a function would fail the comparison instead of silently satisfying it.
    test-arm-1a-emitter-presentation-order-is-byte-identical = {
      expr =
        builtins.toJSON (mint fixtureAdmitted) == builtins.toJSON (
          mint (withKinds [
            app
            web
            db
          ])
        );
      expected = true;
    };
    # The arming: exchanging the two relatum VALUES between the two labels leaves the label set and
    # the emitter list identical and must still produce a different result.
    test-control-arm-1a-swapped-relatum-values-differ = {
      expr = builtins.toJSON (mint fixtureAdmitted) == builtins.toJSON (mint fixtureSwapped);
      expected = false;
    };

    # ── PERMUTATION, ARM 1b: ORDER WITHIN ONE PASS ──
    test-arm-1b-within-pass-order-is-byte-identical = {
      expr =
        builtins.toJSON (
          mint (withKinds [
            collapseA
            collapseB
          ])
        ) == builtins.toJSON (
          mint (withKinds [
            collapseB
            collapseA
          ])
        );
      expected = true;
    };
  };

  # Cells whose subject is a refusal MESSAGE. `tryEval` returns `{ success, value }` and discards the
  # text, so a suite of booleans is equally satisfied by a construction with one refusal in it.
  config.flake.testsPending.minting-refusals = {
    # ── ONE REFUSAL, THREE REACHABLE CAUSES, EACH BY ITS OWN TEXT ──
    # The three differ only in why the lookup misses, which is why they land on one mechanism; each
    # message names the relatum, the label, the kind being minted and the emitting pass, so the three
    # texts are distinct and no cell can pass on another's construction.
    #
    # A same-pass relatum: the node is not in the frozen set, because the set is accumulated from
    # STRICTLY EARLIER strata only. Merging two adjacent strata turns an earlier-pass relatum into a
    # same-pass one and turns success into refusal with no conflicting contribution anywhere — which
    # is meaning being stratification-dependent by construction (ADR-0016 ruling 7).
    test-a-same-pass-relatum-refuses-by-name = {
      expr = mint (withKinds [
        (mkEmitter {
          pass = 0;
          identifier = "db";
          kind = "store";
        })
        (mkEmitter {
          pass = 0;
          identifier = "app";
          kind = "service";
          relata.backing = "db";
        })
      ]);
      expectedError = {
        type = "ThrownError";
        msg = exactly (unresolvedRelatum "db" "backing" "service" 0);
      };
    };
    # The root as a relatum: the root has an identifier by declaration and NO identity (ADR-0016
    # ruling 5). Resolution is identifier-to-identity, so there is nothing for it to resolve to.
    test-the-root-as-a-relatum-refuses-by-name = {
      expr = mint (withKinds [
        db
        (mkEmitter {
          pass = 1;
          identifier = "app";
          kind = "service";
          relata.scope = "root";
        })
      ]);
      expectedError = {
        type = "ThrownError";
        msg = exactly (unresolvedRelatum "root" "scope" "service" 1);
      };
    };
    # A nonexistent identifier: no entry.
    test-a-nonexistent-identifier-refuses-by-name = {
      expr = mint (withKinds [
        db
        (mkEmitter {
          pass = 1;
          identifier = "app";
          kind = "service";
          relata.backing = "nosuchnode";
        })
      ]);
      expectedError = {
        type = "ThrownError";
        msg = exactly (unresolvedRelatum "nosuchnode" "backing" "service" 1);
      };
    };

    # ── WITHIN ONE PASS, CONFLICTING CONTRIBUTIONS REFUSE BY NAME ──
    # Refusal at content merge, exactly as nixpkgs refuses two conflicting definitions of one option.
    # It names the identity, the conflicting key and both emitters' sites, and it reads through a
    # substituted authority so the identity in the message is a text a cell can anchor.
    test-conflicting-same-pass-contributions-refuse-by-name = {
      expr = mintUnderStubIdentity (withKinds [
        conflictOtherA
        conflictOtherB
      ]);
      expectedError = {
        type = "ThrownError";
        msg = exactly (conflictingContribution "host" "site-x" "site-y");
      };
    };

    # ── PERMUTATION, ARM 1b: THE REFUSAL SET MOVES WITH ORDER OR IT DOES NOT ──
    # A permutation cell that compares only successful output passes on a construction whose REFUSAL
    # set moves with order. These two anchor the same literal on the two orders, so a refusal that
    # named its sites in emitter order would fail one of them.
    test-arm-1b-refusal-is-identical-under-within-pass-order-a = {
      expr = mintUnderStubIdentity (withKinds [
        conflictA
        conflictB
      ]);
      expectedError = {
        type = "ThrownError";
        msg = exactly (conflictingContribution "port" "site-a" "site-b");
      };
    };
    test-arm-1b-refusal-is-identical-under-within-pass-order-b = {
      expr = mintUnderStubIdentity (withKinds [
        conflictB
        conflictA
      ]);
      expectedError = {
        type = "ThrownError";
        msg = exactly (conflictingContribution "port" "site-a" "site-b");
      };
    };
  };
}
