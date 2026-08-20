# THE INTERPRETATION PARAMETER — a prior pass's verdicts entering as an INTERPRETATION.
#
# The parameter exists because `solve` took ONE argument and a program is rules over atoms: a fact
# encodes TRUE, omission encodes FALSE, and UNDEFINED had no encoding at all. A consumer that
# manufactured rules to say the third value made a zero-stable-model program acquire one at the
# boundary. The repair is to give the value a channel, not to make the encoding cleverer.
#
# ★★★ WHAT THIS SUITE IS REALLY FOR: THE PARITY. `U` reaches OVERESTIMATE stages only, and it
# enters BEFORE the fixpoint rather than after it. Both halves are load-bearing, each has its own
# failure mode, and each failure mode is INVISIBLE ON THE WRONG SUBJECT. So every seeded defect
# below is run on a subject where it is observable, and the pairing is asserted rather than assumed.
#
# ★★ THE REFERENCE CONSTRUCTION IS A TEST-ONLY INSTRUMENT AND IS BARRED FROM THE PRODUCTION PATH.
# `mkAlternating` below assembles an alternating fixpoint whose SEEDING IS A PARAMETER, out of the
# library's own published `reduct` and `leastModel` — it re-implements no reduct and no least
# fixpoint. Its purpose is to let a defect be BUILT and then shown to be caught; a seeded defect
# that cannot be built is a control nobody has run. **It is a differential instrument, never a
# second production copy of the semantics** — two copies agree only for as long as someone keeps
# them in step, which is `least-model.nix`'s own stated reason for routing through one door.
#
# ★ AND THE INSTRUMENT HAS ITS OWN CONTROL, WHICH IS THE FIRST CELL BELOW. Assembled with the
# CORRECT seeding it must agree with the shipped `wellFoundedModel` on every fixture. Without that,
# a "defect fires" result could just as easily be the reference construction being wrong about
# something else.
{
  genScope,
  genPreludeLib,
  ...
}:
let
  prelude = genPreludeLib;

  inherit (genScope)
    mkProgram
    reduct
    leastModel
    forceFields
    ;

  program = rules: mkProgram { inherit rules; };

  # The shipped surface, under an interpretation given as the parameter's own list form.
  shipped =
    rules: interpretation:
    genScope.wellFoundedModel {
      program = program rules;
      inherit interpretation;
    };

  carry = verdict: atoms: map (atom: { inherit atom verdict; }) atoms;
  undef = carry "undefined";
  true' = carry "true";

  # ── THE REFERENCE CONSTRUCTION, SEEDING PARAMETERISED ──
  # `seedOnce` / `seedTwice` / `seedPossible` each choose a starting set from `T` and `U`;
  # `afterTwice` and `afterOver` are post-hoc hooks, which is how the two STRUCTURAL defects
  # (pinning, and revision 1's union-after-the-fixpoint) are expressible at all.
  mkAlternating =
    {
      seedOnce,
      seedTwice,
      seedPossible,
      afterTwice ? (_U: x: x),
      afterOver ? (_U: x: x),
    }:
    {
      rules,
      T,
      U,
    }:
    let
      p = program rules;
      tSet = prelude.genAttrs T (_: true);
      uSet = prelude.genAttrs U (_: true);
      stage =
        seed: guess:
        (leastModel {
          program = reduct p guess;
          inherit seed;
        }).derived;
      base = p.atoms ++ prelude.filter (a: !(prelude.elem a p.atoms)) (T ++ U);
      step =
        acc:
        if acc.done then
          acc
        else
          let
            once = afterOver uSet (stage (seedOnce tSet uSet) acc.w);
            twice = afterTwice uSet (stage (seedTwice tSet uSet) once);
          in
          {
            w = twice;
            done = twice == acc.w;
            rounds = acc.rounds + 1;
          };
      final = prelude.iterateBounded forceFields step {
        w = { };
        done = false;
        rounds = 0;
      } (base ++ [ null ]);
      trueSet = final.w;
      possible = afterOver uSet (stage (seedPossible tSet uSet) trueSet);
    in
    {
      inherit base;
      verdict =
        atom:
        if trueSet ? ${atom} then
          "true"
        else if possible ? ${atom} then
          "undefined"
        else
          "false";
      trueAtoms = prelude.filter (a: trueSet ? ${a}) base;
      undefinedAtoms = prelude.filter (a: possible ? ${a} && !(trueSet ? ${a})) base;
      falseAtoms = prelude.filter (a: !(possible ? ${a})) base;
    };

  union = u: x: x // u;

  # `x \ u`, written out because the prelude publishes no attrset difference.
  without = u: x: prelude.genAttrs (prelude.filter (a: !(u ? ${a})) (prelude.attrNames x)) (_: true);

  # THE CORRECT CONSTRUCTION: T seeds both, U seeds the overestimate only, both before the fixpoint.
  correct = mkAlternating {
    seedOnce = t: u: t // u;
    seedTwice = t: _u: t;
    seedPossible = t: u: t // u;
  };

  # DEFECT 1 — THE MIRROR: `U` reaches the UNDERESTIMATE as well. Pins atoms this pass settles.
  mirror = mkAlternating {
    seedOnce = t: u: t // u;
    seedTwice = t: u: t // u;
    seedPossible = t: u: t // u;
  };

  # DEFECT 2 — PINNING: the underestimate has `U` SUBTRACTED from it after the fact.
  pinning = mkAlternating {
    seedOnce = t: u: t // u;
    seedTwice = t: _u: t;
    seedPossible = t: u: t // u;
    afterTwice = u: x: without u x;
  };

  # DEFECT 3 — OMIT-T: the OVERESTIMATE is seeded with `U` alone, losing the carried-true atoms.
  omitT = mkAlternating {
    seedOnce = _t: u: u;
    seedTwice = t: _u: t;
    seedPossible = _t: u: u;
  };

  # DEFECT 4 — REVISION 1's: `U` unioned in AFTER the fixpoint instead of seeding it.
  unionAfter = mkAlternating {
    seedOnce = t: _u: t;
    seedTwice = t: _u: t;
    seedPossible = t: _u: t;
    afterOver = u: x: union u x;
  };

  # ── THE FOUR SUBJECTS, AND EACH DEFECT IS OBSERVABLE ON SOME AND NOT OTHERS ──
  derivedSubject = {
    rules = [
      {
        head = "x";
        pos = [ "f" ];
      }
      { head = "f"; }
    ];
    T = [ ];
    U = [ "x" ];
  };
  pureCarrySubject = {
    rules = [ ];
    T = [ ];
    U = [ "x" ];
  };
  positiveReaderSubject = {
    rules = [
      {
        head = "s";
        pos = [ "x" ];
      }
    ];
    T = [ ];
    U = [ "x" ];
  };
  negativeReaderSubject = {
    rules = [
      {
        head = "r";
        neg = [ "x" ];
      }
    ];
    T = [ ];
    U = [ "x" ];
  };

  subjects = [
    derivedSubject
    pureCarrySubject
    positiveReaderSubject
    negativeReaderSubject
  ];

  interpretationOf = s: undef s.U ++ true' s.T;

  # The two accounts read pointwise over the same base, which is the only well-defined comparison:
  # the enumerations are lists over possibly different domains.
  agreesWithShipped =
    s:
    let
      r = correct s;
      m = shipped s.rules (interpretationOf s);
    in
    prelude.all (a: r.verdict a == m.verdict a) r.base;

  verdictUnder =
    construction: s: atom:
    (construction s).verdict atom;
in
{
  flake.tests.interpretation = {
    # ══ THE INSTRUMENT'S OWN CONTROL ══
    # The reference construction, seeded CORRECTLY, agrees with the shipped one on every subject.
    # Without this cell a "defect fires" reading below could be the reference being wrong about
    # something else entirely.
    test-control-the-reference-construction-agrees-with-the-shipped-one = {
      expr = map agreesWithShipped subjects;
      expected = [
        true
        true
        true
        true
      ];
    };

    # ══ THE SHIPPED SEMANTICS, ON THE FIVE HAND-DERIVED CASES ══
    test-a-pure-carry-is-undefined-even-though-no-rule-mentions-it = {
      expr = (shipped [ ] (undef [ "x" ])).verdict "x";
      expected = "undefined";
    };

    # The extended base: a carried atom the program never mentions is REPORTED, not merely
    # answerable. If the base did not extend, this list would be empty and the cell above would
    # still pass on `verdict`'s totality alone.
    test-the-base-extends-to-carry-only-atoms = {
      expr = (shipped [ ] (undef [ "x" ])).undefinedAtoms;
      expected = [ "x" ];
    };

    test-a-carry-does-not-pin-an-atom-this-pass-derives = {
      expr = (shipped derivedSubject.rules (undef [ "x" ])).verdict "x";
      expected = "true";
    };

    # ★ O4's FIRST SUBJECT: undefinedness propagates through a POSITIVE body. This is the exact
    # answer revision 1's construction got wrong.
    test-undefinedness-propagates-through-a-positive-body = {
      expr = (shipped positiveReaderSubject.rules (undef [ "x" ])).verdict "s";
      expected = "undefined";
    };

    # ★ O4's SECOND SUBJECT: and through negation.
    test-undefinedness-propagates-through-negation = {
      expr = (shipped negativeReaderSubject.rules (undef [ "x" ])).verdict "r";
      expected = "undefined";
    };

    # FALSE is inert: it asks for the answer the model gives anyway, so a negative reader of a
    # FALSE-carried atom is TRUE rather than undefined.
    test-a-false-carry-is-inert = {
      expr = (shipped negativeReaderSubject.rules (carry "false" [ "x" ])).verdict "r";
      expected = "true";
    };

    # A TRUE carry is an external fact and DELETES rules through the reduct — it does not merely
    # add. Asserted because the opposite was claimed and struck.
    test-a-true-carry-removes-a-derivation-through-the-reduct = {
      expr =
        (shipped [
          {
            head = "q";
            neg = [ "p" ];
          }
        ] (true' [ "p" ])).verdict
          "q";
      expected = "false";
    };

    test-control-the-same-program-without-the-true-carry-derives-it = {
      expr =
        (shipped
          [
            {
              head = "q";
              neg = [ "p" ];
            }
          ]
          [ ]
        ).verdict
          "q";
      expected = "true";
    };

    # ══ O4's SEEDED DEFECT: REVISION 1's UNION-AFTER-THE-FIXPOINT ══
    # It silences the POSITIVE reader while leaving the negative one undefined — the exact
    # asymmetry that rejected revision 1, and the arm that proves this oracle discriminates.
    test-control-the-union-after-the-fixpoint-defect-silences-the-positive-reader = {
      expr = {
        positive = verdictUnder unionAfter positiveReaderSubject "s";
        negative = verdictUnder unionAfter negativeReaderSubject "r";
      };
      expected = {
        positive = "false";
        negative = "undefined";
      };
    };

    # And the correct construction differs from it on exactly that subject, which is what makes
    # the cell above a control rather than a curiosity.
    test-control-the-correct-construction-differs-there = {
      expr = {
        positive = verdictUnder correct positiveReaderSubject "s";
        negative = verdictUnder correct negativeReaderSubject "r";
      };
      expected = {
        positive = "undefined";
        negative = "undefined";
      };
    };

    # ══ R§3.5's FOUR-SUBJECT TABLE: THE MIRROR DEFECT IS DEAD ON THE DERIVED SUBJECT ══
    # `U` reaching the underestimate is INVISIBLE on an atom the program derives — it is in the
    # underestimate anyway — and fires on all three underived subjects. The whole row is asserted,
    # because the point is the PAIRING and not any one cell.
    test-control-the-mirror-defect-is-dead-on-a-derived-subject-and-fires-on-the-others = {
      expr = {
        derived = verdictUnder mirror derivedSubject "x";
        pureCarry = verdictUnder mirror pureCarrySubject "x";
        positiveReader = verdictUnder mirror positiveReaderSubject "s";
        negativeReader = verdictUnder mirror negativeReaderSubject "r";
      };
      expected = {
        # identical to the correct build ⇒ a control placed here could never fire
        derived = "true";
        pureCarry = "true";
        positiveReader = "true";
        negativeReader = "false";
      };
    };

    # The correct build's answers on the same four, so the difference is legible in one place.
    test-control-the-correct-build-on-the-same-four-subjects = {
      expr = {
        derived = verdictUnder correct derivedSubject "x";
        pureCarry = verdictUnder correct pureCarrySubject "x";
        positiveReader = verdictUnder correct positiveReaderSubject "s";
        negativeReader = verdictUnder correct negativeReaderSubject "r";
      };
      expected = {
        derived = "true";
        pureCarry = "undefined";
        positiveReader = "undefined";
        negativeReader = "undefined";
      };
    };

    # ══ THE PINNING DEFECT IS THE COMPLEMENT: it fires on the DERIVED subject and is dead on the
    # pure carry — so the two defects have two catchers and neither covers the other.
    test-control-the-pinning-defect-fires-on-the-derived-subject-and-is-dead-on-the-pure-carry = {
      expr = {
        derived = verdictUnder pinning derivedSubject "x";
        pureCarry = verdictUnder pinning pureCarrySubject "x";
      };
      expected = {
        derived = "undefined";
        pureCarry = "undefined";
      };
    };

    # ══ O12: THE THREE VERDICTS PARTITION THE BASE ══
    # Asserted as a PARTITION and not as three memberships — three membership checks cannot see a
    # double membership, which is exactly what the omit-T defect produces.
    test-the-three-verdicts-partition-the-extended-base = {
      expr =
        let
          m = shipped [
            {
              head = "s";
              pos = [ "x" ];
            }
            {
              head = "r";
              neg = [ "x" ];
            }
          ] (undef [ "x" ] ++ true' [ "a" ]);
          all' = m.trueAtoms ++ m.undefinedAtoms ++ m.falseAtoms;
        in
        {
          covers = prelude.sort (a: b: a < b) all';
          noDuplicates = prelude.length all' == prelude.length (prelude.unique all');
        };
      expected = {
        covers = [
          "a"
          "r"
          "s"
          "x"
        ];
        noDuplicates = true;
      };
    };

    # ★ O12's SEEDED DEFECT IS DERIVED, BECAUSE THE OBVIOUS CANDIDATE IS DEAD. Seeding BOTH
    # operators alike (the mirror defect) leaves the construction a genuine alternating fixpoint of
    # one augmented program, so containment holds by leastness and the partition survives. What
    # breaks it is omitting `T` from the OVERESTIMATE's starting set: on the empty program with `a`
    # carried TRUE it yields `W⁺ = {a}` and `possible = { }`, putting `a` in trueAtoms AND
    # falseAtoms.
    test-control-the-omit-T-defect-breaks-the-partition = {
      expr =
        let
          s = {
            rules = [ ];
            T = [ "a" ];
            U = [ ];
          };
          r = omitT s;
          all' = r.trueAtoms ++ r.undefinedAtoms ++ r.falseAtoms;
        in
        {
          inherit (r) trueAtoms falseAtoms;
          doubleMembership = prelude.length all' != prelude.length (prelude.unique all');
        };
      expected = {
        trueAtoms = [ "a" ];
        falseAtoms = [ "a" ];
        doubleMembership = true;
      };
    };

    # And the correct build partitions the same subject, so the cell above is a defect and not a
    # property of the fixture.
    test-control-the-correct-build-partitions-that-same-subject = {
      expr =
        let
          r = correct {
            rules = [ ];
            T = [ "a" ];
            U = [ ];
          };
        in
        {
          inherit (r) trueAtoms falseAtoms undefinedAtoms;
        };
      expected = {
        trueAtoms = [ "a" ];
        falseAtoms = [ ];
        undefinedAtoms = [ ];
      };
    };

    # ★ AND THE OMIT-T DEFECT IS INVISIBLE TO A POINTWISE VERDICT COMPARISON, which is why the
    # partition needs its own cell: `verdict` tests the true set first, so the atom still answers
    # "true" while the enumerations have stopped partitioning.
    test-control-the-omit-T-defect-is-invisible-pointwise = {
      expr = verdictUnder omitT {
        rules = [ ];
        T = [ "a" ];
        U = [ ];
      } "a";
      expected = "true";
    };

    # ══ THE EMPTY INTERPRETATION REPRODUCES THE UN-INTERPRETED SEMANTICS ══
    # With `U = ∅` the two operators coincide, so the construction is the ordinary alternating
    # fixpoint and Van Gelder 1993's Theorem 7.8 applies to it exactly. Nothing that already had a
    # meaning acquires a different one.
    test-an-empty-interpretation-reproduces-the-negative-cycle = {
      expr =
        let
          m =
            shipped
              [
                {
                  head = "a";
                  neg = [ "b" ];
                }
                {
                  head = "b";
                  neg = [ "a" ];
                }
              ]
              [ ];
        in
        {
          inherit (m) trueAtoms undefinedAtoms falseAtoms;
        };
      expected = {
        trueAtoms = [ ];
        undefinedAtoms = [
          "a"
          "b"
        ];
        falseAtoms = [ ];
      };
    };

    # ══ R§4.7's EMPTY-PROGRAM BOUNDARY ══
    # An empty program with a non-empty interpretation has verdicts to report, which is what makes
    # this case meaningful where before it was degenerate.
    test-an-empty-program-with-a-non-empty-interpretation-reports-and-stamps = {
      expr =
        let
          r = genScope.solve {
            program = mkProgram { rules = [ ]; };
            interpretation = undef [ "x" ] ++ true' [ "y" ];
          };
        in
        {
          inherit (r)
            trueAtoms
            undefinedAtoms
            falseAtoms
            condensationDepth
            ;
          stamped = r.provenance != [ ];
        };
      expected = {
        trueAtoms = [ "y" ];
        undefinedAtoms = [ "x" ];
        falseAtoms = [ ];
        condensationDepth = 0;
        stamped = false;
      };
    };

    # ══ O11: THE INTERFACE REFUSES WHAT IT SAYS IT REFUSES ══
    # Each is asserted as a boolean here; the MESSAGES — which is where "names the atom and both
    # verdicts" lives — are in ci/tests-error.nix.
    test-an-inconsistent-interpretation-is-refused = {
      expr =
        (builtins.tryEval (
          builtins.deepSeq
            (shipped
              [ ]
              [
                {
                  atom = "x";
                  verdict = "true";
                }
                {
                  atom = "x";
                  verdict = "false";
                }
              ]
            ).trueAtoms
            true
        )).success;
      expected = false;
    };

    # A repeated atom under the SAME verdict is the same SET of literals, so it is deduplicated
    # rather than refused — a set has no duplicates and there is nothing inconsistent about writing
    # one twice. This is the control that keeps the refusal from being "any repeat".
    test-control-a-repeated-atom-under-one-verdict-is-not-inconsistent = {
      expr =
        (shipped
          [ ]
          [
            {
              atom = "x";
              verdict = "undefined";
            }
            {
              atom = "x";
              verdict = "undefined";
            }
          ]
        ).undefinedAtoms;
      expected = [ "x" ];
    };

    test-a-carried-atom-with-no-verdict-is-refused = {
      expr =
        (builtins.tryEval (builtins.deepSeq (shipped [ ] [ { atom = "x"; } ]).trueAtoms true)).success;
      expected = false;
    };

    test-an-unknown-field-on-an-entry-is-refused = {
      expr =
        (builtins.tryEval (
          builtins.deepSeq
            (shipped
              [ ]
              [
                {
                  atom = "x";
                  verdict = "true";
                  why = "no";
                }
              ]
            ).trueAtoms
            true
        )).success;
      expected = false;
    };

    test-a-verdict-outside-the-vocabulary-is-refused = {
      expr =
        (builtins.tryEval (
          builtins.deepSeq
            (shipped
              [ ]
              [
                {
                  atom = "x";
                  verdict = "maybe";
                }
              ]
            ).trueAtoms
            true
        )).success;
      expected = false;
    };

    # ★ THE LIVE CONTROL for all four refusals above: a well-formed interpretation over the same
    # entry point does NOT refuse. Without it every refusal cell passes against a constructor that
    # refuses everything.
    test-control-a-well-formed-interpretation-is-not-refused = {
      expr =
        (builtins.tryEval (
          builtins.deepSeq
            (shipped
              [ ]
              [
                {
                  atom = "x";
                  verdict = "true";
                }
              ]
            ).trueAtoms
            true
        )).success;
      expected = true;
    };

    # The verdict vocabulary the entries are checked against is the library's own binding, so a
    # widening fails here rather than passing silently.
    test-the-interpretation-vocabulary-is-the-published-verdict-vocabulary = {
      expr = genScope.verdictNames;
      expected = [
        "true"
        "undefined"
        "false"
      ];
    };

    # `Pos(I)` is published because it is what the interpreted stability criterion's augmented
    # program is a function of. VGRS Definition 5.1's own name.
    test-Pos-projects-the-carried-true-atoms-in-first-occurrence-order = {
      expr = genScope.Pos (
        undef [ "u1" ]
        ++ true' [
          "t1"
          "t2"
        ]
        ++ carry "false" [ "f1" ]
      );
      expected = [
        "t1"
        "t2"
      ];
    };
  };
}
