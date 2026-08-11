# The least Herbrand model of a DEFINITE program — `lfp T_P` — in two constructions behind one
# routing door.
#
# THEORY. van Emden & Kowalski 1976 give the immediate-consequence operator `T_P` and its least
# fixpoint as the meaning of a definite (negation-free) program; Apt, Blair & Walker 1988 build
# the stratified iteration on top of it. This surface computes only that least fixpoint. Negation
# never reaches here: the alternating fixpoint hands this door a REDUCT, which is definite by
# construction, so every rule below has a purely positive body.
#
# ── ITERATIVE ENCODINGS ONLY, AND WHY IT IS A CONSTRUCTION RATHER THAN A STYLE ──
# A loop written as a self-applying lambda costs one evaluator frame per iteration — Nix does not
# reuse the frame of a call in tail position — so a per-atom recursion's descent depth IS its
# iteration count, and past the call-depth guard it aborts. That abort is NOT a throw: `tryEval`
# does not contain it, so no in-language assertion can observe one and no caller can recover from
# one. Both arms below are therefore flat: one is a C-level closure and the other a C-level fold.
#
# ── THE ROUND BOUND IS A THEOREM, NOT A CAP ──
# `T_P` is monotone and the iteration from ∅ is increasing, so every round that is not the last
# adds at least one atom to a set bounded by the Herbrand base. At most `|atoms|` rounds can be
# productive, and one further round observes that none was. `|atoms| + 1` is therefore the number
# of steps the recursion would itself have taken — a fact about the fixpoint, not a budget on
# what a caller may express, and nothing here refuses a program for reaching it. A cap would be
# the other thing: a number chosen to bound cost, which turns cost into correctness.
#
# ── THE TWO ARMS ARE COMPLEMENTARY, AND THE ROUTING IS ON THE PROGRAM ──
# The unary arm is depth-immune and cannot express a conjunctive body; the round arm expresses
# every program and pays a round loop for it. Measured at equal answer on unary input, the round
# loop costs 16.9× the closure at 258 rounds and the factor widens with depth — which is the
# price of conjunctivity, paid only where a program actually is conjunctive. So the door routes
# on the program's own body arity and never on a caller's request.
{ prelude }:
let
  # THE FORCING DISCIPLINE, WRITTEN SO IT CANNOT GO PARTIAL. `foldl'` forces its accumulator to
  # weak head normal form, which for a record is the record and not its fields — so a field
  # written every round and read in none accumulates one update thunk per round, and forcing that
  # chain at the end spends stack per link and aborts. The measured shapes of that failure are
  # two, not one: where the chain passes through a call it exhausts the call-depth guard, and
  # where it is pure operator it goes straight to the C stack with no guard in front of it. An
  # engine armed for one signature misses the other.
  #
  # A PARTIAL FIX IS INDISTINGUISHABLE FROM NO FIX, so the forcing is derived from the
  # accumulator's OWN fields rather than from a list of names maintained beside it: a field added
  # later is forced without anyone re-applying the discipline, and a strict read of one field by
  # the loop's control flow — which does force that field, and only that field — cannot be
  # mistaken for coverage of the rest.
  forceFields = acc: prelude.foldl' (a: v: builtins.seq v a) null (prelude.attrValues acc);

  # ── ARM: THE CLOSURE ──
  # `builtins.genericClosure` is a C-level worklist: it holds its done-set outside the evaluator,
  # so it carries no accumulator, spends no frame per step and has no round to force. Its
  # operator sees ONE item and never the accumulated set, and that is exactly why it cannot
  # decide a conjunctive body — "is every conjunct derived" is a question about the set.
  #
  # IT REFUSES CONJUNCTIVE INPUT BY NAME rather than answering a different program. The door
  # never routes one here, so this refusal is reachable only by a caller binding the arm
  # directly — which is the case it exists for: a caller who has bound the arm by name has
  # asserted a property of their program, and the refusal is where that assertion is checked.
  leastModelUnary =
    program:
    let
      conjunctive = builtins.filter (r: prelude.length r.pos > 1) program.rules;
      offender = prelude.head conjunctive;
      facts = prelude.concatMap (r: prelude.optional (r.pos == [ ]) r.head) program.rules;
      # body atom → the heads one step derives from it.
      index = prelude.mapAttrs (_: rs: map (r: r.head) rs) (
        builtins.groupBy (r: prelude.head r.pos) (
          builtins.filter (r: prelude.length r.pos == 1) program.rules
        )
      );
      closure = builtins.genericClosure {
        startSet = map (atom: { key = atom; }) facts;
        operator = item: map (atom: { key = atom; }) (index.${item.key} or [ ]);
      };
    in
    if conjunctive != [ ] then
      throw "gen-scope: leastModelUnary is unary-only: the rule for '${offender.head}' has a positive body of arity ${toString (prelude.length offender.pos)}"
    else
      {
        derived = prelude.genAttrs (map (item: item.key) closure) (_: true);
        # `genericClosure` runs to closure or not at all; there is no partial state it could
        # return. The flag is carried on both arms so a consumer reads one shape.
        converged = true;
        # The round count is NOT observable on this arm and is absent rather than zero:
        # `genericClosure` keeps its done-set in C++, so the work it does appears in none of the
        # evaluator's counters. A zero here would read as "no work", which is a different claim.
        work = {
          arm = "unary";
        };
      };

  # ── ARM: THE ROUND LOOP ──
  # One `T_P` application per round over a flat fold. General conjunctive bodies: `prelude.all`
  # over the body short-circuits at the first unsatisfied conjunct, which is why body arity is
  # not where this arm's cost lives — the cost is on the round axis, and a round is a step of
  # derivation depth.
  leastModelRounds =
    program:
    let
      # One round per atom plus the detection round — the theorem's own bound, above.
      roundBound = program.atoms ++ [ null ];
      step =
        acc:
        if acc.done then
          acc
        else
          let
            fired = prelude.concatMap (
              r: prelude.optional (prelude.all (atom: acc.derived ? ${atom}) r.pos) r.head
            ) program.rules;
            newly = builtins.filter (atom: !(acc.derived ? ${atom})) fired;
          in
          {
            derived = acc.derived // prelude.genAttrs newly (_: true);
            # The fixpoint test reads what the round PRODUCED, not the size of what it holds:
            # `T_P` is monotone from ∅, so a round that adds nothing is the fixpoint.
            done = newly == [ ];
            rounds = acc.rounds + 1;
          };
      final = prelude.iterateBounded forceFields step {
        derived = { };
        done = false;
        rounds = 0;
      } roundBound;
    in
    {
      inherit (final) derived;
      # An unconverged result is INVALID, never merely slow, and it is visible on the value
      # rather than inferable from a cost. Under the bound above it is unreachable; carrying it
      # is what makes that an observation instead of an assumption.
      converged = final.done;
      work = {
        arm = "conjunctive";
        inherit (final) rounds;
      };
    };

  # ── THE DOOR ──
  # The routing decision is ONE function of the program, and everything that needs to know which
  # arm answered reads it rather than re-deriving it — a second derivation is a second place the
  # decision lives, and two of them agree only for as long as someone keeps them in step.
  armFor = program: if program.unaryBodies then "unary" else "conjunctive";

  # The delegation is an identity rather than a wrapper, so an arm bound by name is the same
  # function the door would have chosen.
  leastModel =
    program: if armFor program == "unary" then leastModelUnary program else leastModelRounds program;

  # The arm names, as data, so a cell reads a closed enumeration rather than two string literals.
  armNames = [
    "unary"
    "conjunctive"
  ];
in
{
  inherit
    forceFields
    armFor
    armNames
    leastModel
    leastModelUnary
    leastModelRounds
    ;
}
