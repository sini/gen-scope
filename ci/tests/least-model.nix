# The least model of a definite program, its two arms, and the routing between them.
#
# THE ARMS AGREE ON THE ANSWER AND DIFFER IN WHAT THEY CAN EXPRESS. The unary arm is a C-level
# closure and cannot see the accumulated set, so it cannot decide a conjunctive body and refuses
# one BY NAME rather than answering a different program. The round arm expresses every program.
# The door routes on the program's own body arity and never on a caller's request, so a caller
# cannot select the engine that cannot express their program.
#
# ★ THE REFUSAL CELL CARRIES ITS LIVE CONTROL. A cell asserting only that something threw passes
# against an arm that throws on everything; the unary fixture beside it is what says the arm
# answers when it can.
{ genScope, ... }:
let
  # a → b → c, unary throughout.
  unary = genScope.mkProgram {
    rules = [
      { head = "a"; }
      {
        head = "b";
        pos = [ "a" ];
      }
      {
        head = "c";
        pos = [ "b" ];
      }
    ];
  };
  # The same derived set, reached through a binary body.
  conjunctive = genScope.mkProgram {
    rules = [
      { head = "a"; }
      { head = "b"; }
      {
        head = "c";
        pos = [
          "a"
          "b"
        ];
      }
      {
        head = "d";
        pos = [
          "c"
          "unsupported"
        ];
      }
    ];
  };
  derivedOf = m: builtins.attrNames m.derived;

  # The door and both arms take a STARTING SET, and these cells are about the un-seeded case, so
  # the empty seed is written ONCE here rather than at every call. The seeded case has its own
  # suite (ci/tests/interpretation.nix), where the seed is the subject rather than a constant.
  lmDoor =
    program:
    genScope.leastModel {
      inherit program;
      seed = { };
    };
  lmUnary =
    program:
    genScope.leastModelUnary {
      inherit program;
      seed = { };
    };
  lmRounds =
    program:
    genScope.leastModelRounds {
      inherit program;
      seed = { };
    };

  # ── THE SEEDED FIXTURE, WHERE THE SEED IS THE SUBJECT ──
  # `q :- a.` is the smallest program whose answer MOVES with the starting set, so a seed that is
  # admitted is visibly admitted rather than merely not refused. `atoms = [ "q" "a" ]`, which is
  # what makes `offbase` below off-base.
  seedable = genScope.mkProgram {
    rules = [
      {
        head = "q";
        pos = [ "a" ];
      }
    ];
  };
  seededUnary =
    seed:
    genScope.leastModelUnary {
      program = seedable;
      inherit seed;
    };
  seededRounds =
    seed:
    genScope.leastModelRounds {
      program = seedable;
      inherit seed;
    };
in
{
  flake.tests."engine-least-model" = {
    test-unary-arm-derives-the-closure = {
      expr = derivedOf (lmUnary unary);
      expected = [
        "a"
        "b"
        "c"
      ];
    };
    test-round-arm-derives-the-same-set = {
      expr = derivedOf (lmRounds unary);
      expected = [
        "a"
        "b"
        "c"
      ];
    };
    # An atom whose body has an underivable conjunct is not derived — the fixpoint's own answer,
    # and the control that says the round arm is deciding bodies rather than collecting heads.
    test-round-arm-leaves-an-unsatisfied-body-underived = {
      expr = derivedOf (lmRounds conjunctive);
      expected = [
        "a"
        "b"
        "c"
      ];
    };
    # One round per derivation step, plus the round that observes no atom was added.
    test-round-count-is-the-derivation-depth-plus-the-detection-round = {
      expr = (lmRounds unary).work;
      expected = {
        arm = "conjunctive";
        rounds = 4;
      };
    };
    # The round count is ABSENT on the closure arm rather than zero: `genericClosure` keeps its
    # done-set outside the evaluator, so the work it does appears in none of the counters, and a
    # zero would read as "no work".
    test-closure-arm-reports-no-round-count = {
      expr = (lmUnary unary).work;
      expected = {
        arm = "unary";
      };
    };
    test-both-arms-report-convergence = {
      expr = [
        (lmUnary unary).converged
        (lmRounds unary).converged
      ];
      expected = [
        true
        true
      ];
    };

    # ── ROUTING, AND THE REFUSAL IT KEEPS UNREACHABLE ──
    test-the-door-routes-on-the-program = {
      expr = [
        (genScope.armFor unary)
        (genScope.armFor conjunctive)
      ];
      expected = [
        "unary"
        "conjunctive"
      ];
    };
    test-arm-names-are-a-closed-enumeration = {
      expr = genScope.armNames;
      expected = [
        "unary"
        "conjunctive"
      ];
    };
    test-the-door-answers-with-the-arm-it-routed-to = {
      expr = [
        (lmDoor unary).work.arm
        (lmDoor conjunctive).work.arm
      ];
      expected = [
        "unary"
        "conjunctive"
      ];
    };
    # A conjunctive program bound to the unary arm by name hits its refusal. The door never
    # routes one here, so this fires only where a caller asserted a property their program does
    # not have.
    test-the-unary-arm-refuses-conjunctive-input = {
      expr = builtins.tryEval (builtins.deepSeq (lmUnary conjunctive) true);
      expected = {
        success = false;
        value = false;
      };
    };
    # ★ THE LIVE CONTROL. Without it every cell above would pass against an arm that refuses
    # everything.
    test-the-unary-arm-answers-unary-input = {
      expr = builtins.tryEval (builtins.deepSeq (lmUnary unary) true);
      expected = {
        success = true;
        value = true;
      };
    };

    # ── THE STARTING SET'S CARRIER ──
    # WHICH message each refusal carries is in `ci/tests-error.nix`, group `least-model-refusals`;
    # these three cells hold the properties `tryEval` can see — that a non-set is refused
    # CATCHABLY, that the canonical set is still admitted, and that the guard is a membership
    # question rather than a containment one.
    #
    # A non-set seed used to be an evaluator type error (`expected a set but found a list`), which
    # `tryEval` does not contain: this cell could not be EVALUATED before the guard, so it crashed
    # the batch asserter behind `checks.default` rather than failing. What it holds is that the
    # refusal is now in-language and a caller can recover from one.
    test-a-seed-that-is-not-a-set-is-refused-CATCHABLY = {
      expr = builtins.tryEval (builtins.deepSeq (seededUnary [ "a" ]) true);
      expected = {
        success = false;
        value = false;
      };
    };
    # ★ THE LIVE CONTROL. Every refusal cell above and in `tests-error.nix` is equally satisfied by
    # a guard that refuses EVERYTHING; this is what says the door still opens, on both arms and on
    # both the empty and the non-empty canonical seed.
    test-the-seed-guard-admits-the-canonical-set = {
      expr = builtins.tryEval (
        builtins.deepSeq [
          (seededUnary { })
          (seededUnary { a = true; })
          (seededRounds { })
          (seededRounds { a = true; })
        ] true
      );
      expected = {
        success = true;
        value = true;
      };
    };
    # THE GUARD IS A MEMBERSHIP QUESTION, NOT A CONTAINMENT ONE. `seed ⊆ program.atoms` would be the
    # obvious over-narrow reading and it breaks this library's own caller: `wellFoundedModel` seeds
    # atoms the program never mentions, carrying `parsed.undef` into a base extended past
    # `program.atoms`. `tests/interpretation.nix`'s `test-the-base-extends-to-carry-only-atoms` is
    # the end-to-end half of this; this cell is the arm-level one.
    test-a-seed-atom-outside-the-program-base-stays-admitted = {
      expr = [
        (seededUnary { offbase = true; }).derived
        (seededRounds { offbase = true; }).derived
      ];
      expected = [
        { offbase = true; }
        { offbase = true; }
      ];
    };

    # ── THE FORCING DISCIPLINE, AS A VALUE ──
    # It is derived from the accumulator's own fields, so a field added later is forced without
    # the discipline being re-applied. What it returns is not the point — that it has visited
    # every field is, and the cell below pins that it is total over a record rather than over a
    # list of names someone maintains.
    test-force-fields-visits-every-field = {
      expr = builtins.tryEval (
        genScope.forceFields {
          a = 1;
          b = "two";
          c = [ 3 ];
        }
      );
      expected = {
        success = true;
        value = null;
      };
    };
    # A field that cannot be forced is REACHED — which is the property under test, since the
    # failure this discipline exists to prevent is a field nothing ever touches.
    test-force-fields-reaches-a-field-no-control-flow-reads = {
      expr = builtins.tryEval (
        genScope.forceFields {
          read = 1;
          unread = throw "reached";
        }
      );
      expected = {
        success = false;
        value = false;
      };
    };
  };
}
