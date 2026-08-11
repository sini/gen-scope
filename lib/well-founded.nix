# The well-founded partial model, by Van Gelder's alternating fixpoint.
#
# THEORY. Van Gelder, Ross & Schlipf 1991 define the well-founded model of a program with
# negation; Van Gelder 1993 gives the construction computed here. For a guess `J` of what is
# true, the Gelfond–Lifschitz reduct `P/J` deletes every rule with a negative literal in `J` and
# deletes the negative literals from the rest, leaving a DEFINITE program; `S(J) = lfp T_{P/J}`.
# `S` is ANTIMONOTONE — a larger guess deletes more rules and leaves a smaller model — so `S²` is
# MONOTONE, and
#
#   W⁺ = lfp(S²) from ∅        is the set of TRUE atoms
#   S(W⁺)                      is the set of atoms TRUE-OR-UNDEFINED
#
# which partitions the Herbrand base into three: true, undefined, false. The third value is the
# reason the construction exists. A cycle through a negative edge has no meaning under the
# stratified semantics — Apt, Blair & Walker 1988 admit positive cycles and leave that shape
# without one — and the well-founded model gives it UNDEFINED, which is a NAMED verdict and not
# a gap where an answer should be. On locally stratified programs the model is total and equal to
# the perfect model, so nothing that already had a meaning acquires a different one.
#
# ORDER-INDEPENDENCE IS A THEOREM HERE, NOT A DISCIPLINE. The model is a function of the rules;
# the fixpoint mentions no arrival, no iteration index and no evaluation order, so a construction
# that fires once and records itself as fired is not something this engine forbids — it is
# something it cannot express, because there is nowhere in the semantics for "already fired" to
# be said.
#
# THE OUTER LOOP IS THE SAME SHAPE AS THE INNER ONE and carries the same two obligations: it is
# a flat fold rather than a recursion, and every field of its accumulator is forced each round.
# One of its fields is read by no control flow at all, which is precisely the shape that chains.
{ prelude }:
let
  leastModelLib = import ./least-model.nix { inherit prelude; };

  # The Gelfond–Lifschitz reduct. Rules with a negative literal in the guess are DELETED; the
  # survivors keep their positive bodies and lose their negative ones. What comes out is a
  # definite program, which is the only thing the least-model door ever sees.
  #
  # `unaryBodies` is CARRIED, not recomputed, and that is sound rather than a saving: reduction
  # deletes rules and deletes negative literals, so no surviving rule's positive body is longer
  # than it was in the program the figure was computed on.
  reduct = program: guess: {
    inherit (program) atoms unaryBodies;
    rules = prelude.concatMap (
      rule:
      prelude.optional (!(prelude.any (atom: guess ? ${atom}) rule.neg)) {
        inherit (rule) head pos;
        neg = [ ];
      }
    ) program.rules;
  };

  # `S(J)`, with the inner convergence flag carried out rather than discarded — an inner loop
  # that did not reach its fixpoint invalidates the outer round that consumed it, and a result
  # that cannot say so is a result whose validity has to be assumed.
  underestimate = program: guess: leastModelLib.leastModel (reduct program guess);

  wellFoundedModel =
    program:
    let
      # `S²` is monotone and the iteration from ∅ is increasing over subsets of a base of
      # `|atoms|` atoms, so the same theorem bounds this loop as bounds the inner one: at most
      # one productive round per atom, plus the round that observes none was.
      roundBound = program.atoms ++ [ null ];
      step =
        acc:
        if acc.done then
          acc
        else
          let
            once = underestimate program acc.w;
            twice = underestimate program once.derived;
          in
          {
            w = twice.derived;
            # Increasing under `S²`, so equality IS the fixpoint.
            done = twice.derived == acc.w;
            rounds = acc.rounds + 1;
            # ★ THE FIELD NO CONTROL FLOW READS, kept deliberately. A strict read of `done`
            # forces `done` and reaches nothing else, so this counter is exactly the shape that
            # accumulates one thunk per round and aborts on a chain no caller can catch. It is
            # here because the engine genuinely needs it — an inner loop that did not converge
            # makes its outer round invalid — and it is safe because the forcing is derived from
            # the accumulator rather than from a list of the fields somebody remembered.
            innerConverged = acc.innerConverged && once.converged && twice.converged;
          };
      final = prelude.iterateBounded leastModelLib.forceFields step {
        w = { };
        done = false;
        rounds = 0;
        innerConverged = true;
      } roundBound;

      trueSet = final.w;
      # `S(W⁺)`: true or undefined. The complement of this set is false.
      possible = (underestimate program trueSet).derived;

      # The three verdicts are emitted in the program's DECLARATION ORDER rather than in the
      # codepoint order an attribute-set walk would give, because that order is the one the
      # ordered fold over contributions is defined against and a set that arrives sorted by name
      # has already lost it.
      select = pred: builtins.filter pred program.atoms;
    in
    {
      trueAtoms = select (atom: trueSet ? ${atom});
      undefinedAtoms = select (atom: possible ? ${atom} && !(trueSet ? ${atom}));
      falseAtoms = select (atom: !(possible ? ${atom}));

      # TOTAL ON EVERY STRING, and the totality is the point. An atom no rule mentions is FALSE
      # — no rule can derive it, so it is outside `S(W⁺)` — and this says so rather than
      # answering with an absence the caller has to interpret. UNDEFINED is a value the function
      # returns, never a silence it falls into.
      verdict =
        atom:
        if trueSet ? ${atom} then
          "true"
        else if possible ? ${atom} then
          "undefined"
        else
          "false";

      outerRounds = final.rounds;
      # Both halves, because they fail independently: the outer alternation may not have reached
      # its fixpoint, or an inner least-model round may not have reached its own.
      converged = final.done && final.innerConverged;
      # Read from the one routing function rather than re-derived here, and it is a property of
      # the PROGRAM: every reduct of it routes the same way, which is what the discriminator
      # being the positive body arity buys.
      arm = leastModelLib.armFor program;
    };

  # The vocabulary, as data, so a widening fails a cell rather than passing silently — and so
  # the third value has a name a consumer can bind rather than a string it has to know.
  verdictNames = [
    "true"
    "undefined"
    "false"
  ];
in
{
  inherit
    reduct
    wellFoundedModel
    verdictNames
    ;
}
