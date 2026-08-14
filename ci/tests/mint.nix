# THE MINTING ENTRY'S ORACLE — the staged run's frozen-set semantics, asserted on the entry the
# library publishes.
#
# These cells assert that an identifier is the scope graph's vertex name and not the identity
# (ADR-0016 ruling 5), that a pass resolves relata only against identities settled by STRICTLY
# EARLIER passes, and that a cycle is inexpressible because it would require a pass to see its own
# output (ADR-0016 ruling 7).
#
# ★ THEY ARE WRITTEN AGAINST A SPECIFIED SURFACE AND AGAINST NO IMPLEMENTATION, which is what lets
# the implementation be derived against them rather than the other way round — and it is only worth
# anything if the cells that pass are, to the byte, the cells that were written before the subject
# existed. A suite whose assertions are adjusted to what the code turned out to do reports a
# property it no longer tests.
#
# ★★ THE CELLS WHOSE SUBJECT IS A REFUSAL MESSAGE ARE NOT HERE. `tryEval` returns
# `{ success, value }` and discards the text, so a suite of booleans is equally satisfied by a
# construction with one refusal in it; `expectedError` is the assertion for that, and a cell with a
# throwing `expr` crashes `checks.default`'s batch asserter rather than failing. They live in
# `ci/tests-error.nix` as the `minting-refusals` suite, on the fixtures this file also reads.
#
# The handles, the substituted drivers, the emitter fixtures and the two refusal texts are in
# `_fixtures/mint.nix`, shared with that suite so the refusal texts have one definition.
{
  lib,
  genScope,
  genPreludeLib,
  genGraph,
  ...
}:
let
  fixtures = import ./_fixtures/mint.nix {
    inherit
      lib
      genScope
      genPreludeLib
      genGraph
      ;
  };
  inherit (fixtures)
    mint
    mintModule
    mintShortSchedule
    scheduleSpy
    emittedSpy
    settledSpy
    advanceFormalsSpy
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
    unresolvedRelatum
    conflictingContribution
    ;

  # The message, pinned to the byte. `escapeRegex` is the prelude's own, and it escapes every
  # metacharacter that occurs in the refusal literals — measured over them, the live set is `.`, `(`
  # and `)`. The prelude's escape set and nixpkgs' are NOT identical: they disagree on `]`, which
  # the prelude escapes and nixpkgs leaves bare. No literal there contains one, so the disagreement
  # cannot reach these patterns; a literal that grows one should be re-measured rather than assumed.
  exactly = msg: "^" + genPreludeLib.escapeRegex msg + "$";
in
{
  flake.tests.minting = {
    # ── THE INSTRUMENT CONTROLS ──
    # The library-reachability cell says the suite is evaluating something rather than agreeing with
    # itself; the two formals cells say `functionArgs` can SEE a field, without which every absence
    # asserted below is one a blind instrument would report identically.
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
      expr = (emittedSpy fixtureUnrelated).unrun;
      expected = [
        [ ]
        [ ]
        [ ]
      ];
    };
    # Without this the cell above passes on an `advance` that returns nothing at all.
    test-control-settled-is-non-empty-at-the-same-strata = {
      expr = (settledSpy fixtureUnrelated).unrun;
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
    # A later pass naming an identity already in the frozen set contributes content: the freeze is
    # over MEMBERSHIP, so the map's values may be revisited, and two emitters never yield two nodes.
    # It never re-mints, and on this fixture — whose two emissions carry DIFFERENT keys — it does
    # not refuse.
    #
    # ★ WHAT IS FORECLOSED IS REFUSAL AT MINTING, AND ONLY THAT. Two emitters never yield two nodes
    # and minting never fails on this input (ADR-0016), which is what the cell below reads. Refusal
    # at content MERGE is NOT foreclosed, and the case where a later pass DISAGREES on a key an
    # earlier pass already settled is not ruled at all — the ADR routes it to the substrate's
    # general content rule and leaves that premise open. The library refuses there, and marks the
    # refusal a PROPOSAL pending that rule. No cell in this suite or in `minting-refusals` exercises
    # the case, in either direction, so whichever way it is ruled the suite is untouched. Read as a
    # flat "a later pass never refuses", the paragraph above would settle by comment a question the
    # law has deliberately left open.
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
}
