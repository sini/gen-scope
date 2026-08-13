# The fold vocabulary: what each fold is defined over, what it refuses when it is handed something
# else, and WHEN an aggregate is allowed to run at all.
#
# ★ THE REFUSAL CELLS HERE PIN REACHABILITY, NOT MESSAGES. `tryEval` reports that a refusal fired
# and discards what it said, so no cell in this file can tell one refusal from another. What each
# refusal SAYS is asserted in `../tests-error.nix`, where `expectedError` can read the text.
#
# ★★ AND THE REFUSAL CELLS HERE CANNOT SEE THE FAILURE THEY REPLACED. The preconditions replaced
# evaluator failures — `toJSON` on a value containing a function, `attrNames` on a function — and
# `tryEval` holds neither, so a cell asserting the OLD behaviour would end the runner rather than
# report it. That measurement is `../bench/folds-guard.sh`, which reads exit codes and runs the
# unguarded constructions as live controls beside the guarded ones. Two cells below reach the part
# of the old behaviour that IS observable from inside a suite — the input on which the unguarded
# comparison used to RETURN — and the split is stated so this file is not read as more than it is.
#
# ★★ WHAT THESE CELLS ASSERT IS THE PRECONDITION, AND NOT THAT SUCH FRAGMENTS ARE UNWRITABLE. A
# resolver may still return a function-bearing fragment; what changed is that a fold defined over
# comparable values now says so by name instead of ending the evaluation. Making such a fragment
# INEXPRESSIBLE is a different construction — plain-data conformance of what a resolver may hand
# back — and it is a change to the cascade's contract that is not made here. A cell reading as
# "function-valued fragments cannot exist" would be claiming that construction's property for a
# check an author can still omit.
#
# ── WHEN AN AGGREGATE MAY RUN ──
# The second suite is about the cascade rather than the vocabulary: a fold answers about the fact
# set it is handed, so what makes its answer mean anything is that the set was CLOSED when it ran.
# THEORY: Apt, Blair & Walker (1988), "Towards a Theory of Declarative Knowledge", in Minker (ed.),
# pp. 89–148 — the standard model is built stratum by stratum, `M_i = T_{P_i}↑ω(M_{i-1})` (printed
# p. 108), each stratum reaching its own fixed point before the next begins; that completeness, and
# not a restriction on what a stratum may read, is what aggregation demands of stratification
# (strictly-lower indexing is their rule for the NEGATIVE case, §"Stratified Programs", Definition 3,
# printed p. 96, and this cascade has no negation in it).
#
# The cells measure the difference that guarantee makes: the same fold, the same fixture, folded
# over the closed fact set and over the prefix of it that existed before the higher stratum
# contributed. If those two agreed, the guarantee would be buying nothing and the cells would be
# reporting a property no construction could violate.
{
  genScope,
  ...
}:
let
  inherit (genScope)
    mkKind
    mkKinds
    mkClaim
    resolveClaims
    folds
    ;

  didThrow = e: !(builtins.tryEval (builtins.deepSeq e null)).success;
  succeeds = e: (builtins.tryEval (builtins.deepSeq e null)).success;

  # ── THE COMPARISON WITHOUT ITS PRECONDITION ──
  # Built here to be measured and never used: `same`'s comparison arm alone, which is the only part
  # of the unguarded construction the cells below reach. Its other arm — the mismatch diagnostic —
  # ends the evaluation on these inputs and is measured by the exit-code sweep instead.
  unguardedSame =
    key: vs:
    if builtins.all (v: v == builtins.head vs) vs then
      builtins.head vs
    else
      throw "unguarded.same: conflicting values for key '${key}'";

  # Two fragments carrying functions, as DISTINCT values: nothing is shared between two literals.
  fnA = {
    gen = _: "a";
  };
  fnB = {
    gen = _: "b";
  };
  # ONE fragment, listed twice — the same value slot on both sides of the comparison, which is the
  # only way `==` reports agreement between function-bearing values.
  shared =
    let
      v = {
        gen = _: "a";
      };
    in
    [
      v
      v
    ];
  # ── THE SCAN'S STOPPING RULE, AS THREE PAIRS THAT VARY BOTH OF ITS TERMS ──
  # The evaluator's shortcut is a CONJUNCTION — the derivation marker AND an `outPath` — so a
  # fixture set that holds either term fixed cannot observe the other, and would report a stopping
  # rule that admits fragments the comparison decides by their interiors. All three pairs below are
  # DISTINCT values carrying DIFFERENT functions inside, so nothing here can be explained by one
  # value slot being compared with itself:
  #
  #   drvA/drvA2      marker + path  ⇒ the evaluator agrees by path; the scan must NOT descend
  #   markerOnly1/2   marker, no path ⇒ compared field by field, and `toJSON` aborts on them
  #   bareA/bareA2    path, no marker ⇒ compared field by field
  #
  # The last two are the fragments the scan must ENTER, and each is a shape a stop written on one
  # term alone would have skipped.
  drvA = {
    type = "derivation";
    outPath = "/nix/store/aaaa";
    passthru = _: "one";
  };
  drvA2 = {
    type = "derivation";
    outPath = "/nix/store/aaaa";
    passthru = _: "two";
  };
  drvB = {
    type = "derivation";
    outPath = "/nix/store/bbbb";
    passthru = _: "three";
  };
  bareA = {
    outPath = "/nix/store/aaaa";
    passthru = _: "one";
  };
  bareA2 = {
    outPath = "/nix/store/aaaa";
    passthru = _: "two";
  };
  markerOnly1 = {
    type = "derivation";
    passthru = _: "one";
  };
  markerOnly2 = {
    type = "derivation";
    passthru = _: "two";
  };

  # Every fold in the vocabulary, in one list, so a key-type cell reports WHICH member regressed
  # rather than that something did.
  everyFold = [
    folds.same
    folds.one
    folds.list
    folds.mergeAttrs
    (folds.byKey { a = folds.same; })
  ];

  # ── THE TWO-STRATUM FIXTURE ──
  # `leaf` (depth 0) aggregates its fragments per group; `top` (depth 1) resolves earlier and emits
  # a claim INTO one of those groups. So the leaf stratum's fact set is not complete until the top
  # stratum has finished, and a fold that ran before it would be folding a prefix.
  aggKinds =
    {
      fold,
      group ? "g",
      tag ? "from-emission",
    }:
    mkKinds [
      (mkKind {
        name = "leaf";
        dedupKey = c: c.group;
        inherit fold;
        resolve = c: _: { resources.${c.group} = c.tag; };
      })
      (mkKind {
        name = "top";
        below = [ "leaf" ];
        resolve = c: _: {
          claims = [
            (mkClaim {
              kind = "leaf";
              inherit (c) subject;
              inherit group tag;
            })
          ];
        };
      })
    ];

  subjA = {
    id_hash = "id-a";
    name = "a-subject";
  };
  subjB = {
    id_hash = "id-b";
    name = "b-subject";
  };

  leafRoot = mkClaim {
    kind = "leaf";
    subject = subjA;
    group = "g";
    tag = "from-intake";
  };
  topRoot = mkClaim {
    kind = "top";
    subject = subjB;
  };

  # The run as the cascade schedules it: the fold sees the leaf stratum's fact set CLOSED.
  closed =
    spec:
    resolveClaims {
      kinds = aggKinds spec;
      claims = [
        leafRoot
        topRoot
      ];
    };
  # The same fold over the same registry, folding the fact set as it stood BEFORE the higher
  # stratum contributed. Nothing about the fold changes — only when it is allowed to answer.
  early =
    spec:
    resolveClaims {
      kinds = aggKinds spec;
      claims = [ leafRoot ];
    };

  listSpec = {
    fold = folds.list;
  };
  # A variant whose emission lands in a DIFFERENT group: the later stratum still runs, still emits,
  # and contributes nothing to the group under test. Without this row the disagreement below reads
  # as "these two runs differ", which they would whatever the fold did.
  disjointSpec = {
    fold = folds.list;
    group = "h";
  };
  # The sharp form: under `same`, the prefix does not merely give a different answer — it gives a
  # confident one, and the conflict exists only once the fact set is complete.
  sameSpec = {
    fold = folds.same;
    tag = "from-emission";
  };
in
{
  flake.tests.folds = {
    # ── THE MODULE IS A VALUE ALGEBRA, AND ITS ARGUMENT LIST IS THE EVIDENCE ──
    test-module-takes-the-prelude-and-nothing-else = {
      expr = builtins.attrNames (builtins.functionArgs (import ../../lib/folds.nix));
      expected = [ "prelude" ];
    };
    # The same predicate over a module that takes more, in the same run: without it, an empty or
    # constant answer would satisfy the cell above.
    test-the-cascade-module-takes-more = {
      expr = builtins.attrNames (builtins.functionArgs (import ../../lib/cascade.nix));
      expected = [
        "graph"
        "prelude"
      ];
    };

    # ── `same`: THE COMPARISON'S PRECONDITION ──
    test-same-refuses-a-function-bearing-fragment = {
      expr = didThrow (
        folds.same "k" [
          fnA
          fnB
        ]
      );
      expected = true;
    };
    # The input the unguarded comparison ANSWERED, and the answer was the caller's value sharing
    # rather than anything about the fragments.
    test-same-refuses-one-value-slot-listed-twice = {
      expr = didThrow (folds.same "k" shared);
      expected = true;
    };
    # LIVE CONTROL for the cell above, same run: without the precondition this input returns.
    test-the-unguarded-comparison-returns-on-the-pointer-accident = {
      expr = succeeds (unguardedSame "k" shared);
      expected = true;
    };
    test-the-unguarded-comparison-answers-with-the-shared-fragment = {
      expr = builtins.typeOf (unguardedSame "k" shared);
      expected = "set";
    };

    # ── AND IT REFUSES NOTHING ELSE ──
    test-same-returns-on-agreeing-plain-fragments = {
      expr = folds.same "k" [
        { a = 1; }
        { a = 1; }
      ];
      expected = {
        a = 1;
      };
    };
    # The conflict arm stays reachable behind the precondition: the guard dominates the diagnostic
    # for fragments it refuses, and leaves it in place for the fragments it admits.
    test-same-still-refuses-a-plain-conflict = {
      expr = didThrow (
        folds.same "k" [
          1
          2
        ]
      );
      expected = true;
    };
    # ── WHERE THE SCAN STOPS, ON TWO DISTINCT VALUES RATHER THAN ONE COMPARED WITH ITSELF ──
    # Green only if BOTH halves hold: the scan did not descend into a marked derivation (or the
    # function inside would be refused), and the comparison agreed on two values whose interiors
    # differ (which only the evaluator's `outPath` rule can produce). A singleton fragment could
    # report neither — it agrees with itself by pointer identity whatever the rule is.
    test-two-derivations-with-one-store-path-agree = {
      expr =
        (folds.same "k" [
          drvA
          drvA2
        ]).outPath;
      expected = "/nix/store/aaaa";
    };
    # ★ THE SAME PAIR WITHOUT THE MARKER IS REFUSED, because the evaluator's shortcut is narrower
    # than its rendering: an unmarked carrier is compared field by field, functions included. That
    # this cell and the one above disagree IS the stopping rule. Which refusal fires is asserted in
    # `../tests-error.nix` — a fold that let this pair through would ALSO throw here, reporting a
    # conflict between two fragments that render identically, so `didThrow` cannot tell them apart.
    test-a-store-path-without-the-derivation-marker-is-refused = {
      expr = didThrow (
        folds.same "k" [
          bareA
          bareA2
        ]
      );
      expected = true;
    };
    # ★ THE MARKER WITHOUT A PATH IS THE OTHER HALF OF THE CONJUNCTION, and this cell is the one
    # that fails LOUDEST when the stop is written on one term: a stop testing the marker alone
    # skips these, hands them to a comparison their functions decide, and then to a `toJSON` that
    # ABORTS — so this cell does not go red, it takes the runner's cell down with it (☢️). That is
    # the same uncatchable failure the fold's whole precondition exists to remove.
    test-a-derivation-marker-without-a-store-path-is-refused = {
      expr = didThrow (
        folds.same "k" [
          markerOnly1
          markerOnly2
        ]
      );
      expected = true;
    };
    # Two marked derivations with DIFFERENT paths still conflict: where the scan stops decides what
    # is compared, not whether anything is.
    test-two-derivations-with-different-store-paths-conflict = {
      expr = didThrow (
        folds.same "k" [
          drvA
          drvB
        ]
      );
      expected = true;
    };

    # ── THE KEY IS AN ARGUMENT THE VOCABULARY DECIDES, AT EVERY MEMBER ──
    test-every-fold-refuses-a-non-string-key = {
      expr = builtins.map (f: didThrow (f 42 [ { a = 1; } ])) everyFold;
      expected = [
        true
        true
        true
        true
        true
      ];
    };
    # CONTROL, same run, same folds, same fragments: with a string key every one of them returns.
    # Without it the row above is satisfied by a vocabulary that refuses this fragment list outright.
    test-every-fold-accepts-a-string-key = {
      expr = builtins.map (f: succeeds (f "k" [ { a = 1; } ])) everyFold;
      expected = [
        true
        true
        true
        true
        true
      ];
    };
    # The key is decided before the fragments are, so it is refused where the fragments would have
    # folded cleanly, where they would have conflicted, and where there are none at all.
    test-a-non-string-key-is-refused-where-the-fragments-would-conflict = {
      expr = didThrow (
        folds.same 42 [
          1
          2
        ]
      );
      expected = true;
    };
    test-a-non-string-key-is-refused-on-an-empty-fragment-list = {
      expr = didThrow (folds.same 42 [ ]);
      expected = true;
    };

    # ── THE FRAGMENT-SHAPE PRECONDITIONS ──
    test-mergeattrs-refuses-a-fragment-that-is-not-an-attribute-set = {
      expr = didThrow (
        folds.mergeAttrs "k" [
          { a = 1; }
          (_: "not a fragment")
        ]
      );
      expected = true;
    };
    test-mergeattrs-returns-on-attribute-set-fragments = {
      expr = folds.mergeAttrs "k" [
        { a = 1; }
        { b = 2; }
      ];
      expected = {
        a = 1;
        b = 2;
      };
    };
    test-bykey-refuses-a-fragment-that-is-not-an-attribute-set = {
      expr = didThrow (folds.byKey { gen = folds.same; } "k" [ (_: "not a fragment") ]);
      expected = true;
    };
    test-bykey-returns-on-attribute-set-fragments = {
      expr = folds.byKey { gen = folds.same; } "k" [
        { gen = "hex"; }
        { gen = "hex"; }
      ];
      expected = {
        gen = "hex";
      };
    };
  };

  # ── STRATUM-LOCAL AGGREGATION: THE FOLD RUNS ON A CLOSED FACT SET ──
  flake.tests.stratum-aggregation = {
    # The fold's contributors span BOTH strata: the intake claim and the one the higher stratum
    # emitted, in schedule order.
    test-fold-sees-the-later-emission = {
      expr = (closed listSpec).resources.leaf.g;
      expected = [
        "from-intake"
        "from-emission"
      ];
    };
    # And the second contributor really is a child of the higher stratum's claim — a path of
    # `[1 0]` is an emission of the claim at intake index 1, not something present at intake.
    test-the-second-contributor-is-an-emission = {
      expr = (closed listSpec).trace.resources.leaf.g.claims;
      expected = [
        [ 0 ]
        [
          1
          0
        ]
      ];
    };

    # ── THE EARLY-FOLD VARIANT, AND IT MUST DISAGREE ──
    test-the-early-fold-answers-about-the-prefix = {
      expr = (early listSpec).resources.leaf.g;
      expected = [ "from-intake" ];
    };
    test-the-early-fold-disagrees-with-the-complete-fact-set = {
      expr = (early listSpec).resources.leaf.g != (closed listSpec).resources.leaf.g;
      expected = true;
    };
    # The other direction, so the disagreement is attributable to the emission and not to the
    # variant: when the later stratum contributes to a different group, the two agree.
    test-the-early-fold-agrees-when-the-later-stratum-contributes-elsewhere = {
      expr = (early disjointSpec).resources.leaf.g == (closed disjointSpec).resources.leaf.g;
      expected = true;
    };

    # ── AND THE PREFIX ANSWER IS NOT MERELY DIFFERENT ──
    # Under `same`, folding the prefix RETURNS: one fragment, no disagreement to find. The conflict
    # is a fact about the complete set, and only the complete set can report it.
    test-the-early-fold-returns-where-the-complete-set-refuses = {
      expr = succeeds (early sameSpec).resources.leaf.g;
      expected = true;
    };
    test-the-complete-fact-set-refuses-the-conflict = {
      expr = didThrow (closed sameSpec).resources.leaf.g;
      expected = true;
    };
  };
}
