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
#
# ══ THE INTERPRETATION PARAMETER ══
#
# A prior pass's verdicts enter HERE, as an INTERPRETATION, never as re-encoded rules. Van Gelder,
# Ross & Schlipf 1991 Definition 2.4: "Given a program P, a partial interpretation I is a
# CONSISTENT SET OF LITERALS whose atoms are in the Herbrand base of P." ⇒ the object is the held
# primary's own, and so is the consistency requirement the constructor refuses on.
#
# ★★ THE THREE VALUES ARE THREE DIFFERENT KINDS OF THING, AND COLLAPSING THEM IS THE DEFECT THIS
# PARAMETER EXISTS TO REMOVE.
#
#   TRUE       an EXTERNAL FACT. It enters as the starting set of BOTH operators below, so every
#              `lfp T_{P/J}` is taken above it. ★ It does NOT merely add: a TRUE carry makes
#              `not p` false, so the reduct DELETES every rule whose negative body mentions `p` —
#              on `P = { q :- not p }` with `p` true, `q` goes from true to FALSE. What it cannot
#              do is CONTRADICT the program: a general logic program contains no construction that
#              asserts falsity, and a rule with a false body is satisfied rather than violated.
#
#   FALSE      INERT, and that is a decision with a ground rather than an omission. `verdict` is
#              already total — an atom no rule can derive is FALSE by the model rather than absent
#              from it — so a FALSE carry asks for the answer the model gives anyway, and the only
#              way to make it operative is to let it SUPPRESS a derivation this pass's rules
#              justify, which is pinning. The channel is total and required, so nothing is silent;
#              the value adds no constraint, so nothing is overridden.
#
#   UNDEFINED  a SUSPENSION OF FALSITY. VGRS Definition 4.1 makes UNDEFINED an ABSENCE — "neither q
#              nor its complement is in I" — so it cannot be seeded as information and carried
#              forward; a monotone sequence of partial interpretations only ever ADDS literals. So
#              what a carried UNDEFINED means is stated at the construction that MANUFACTURES
#              falsity: VGRS Definition 3.1 makes `A ⊆ H` unfounded with respect to `I` when every
#              rule with head `p ∈ A` has a witness of unusability, and an atom NO RULE HEADS
#              satisfies it vacuously, so it enters the greatest unfounded set and becomes FALSE.
#              ⇒ A CARRIED-UNDEFINED ATOM IS ONE WHOSE SUPPORT LIES OUTSIDE THIS PROGRAM, AND IT
#              ENTERS BY BEING EXEMPT FROM THE UNFOUNDED SET — neither derivable nor unfounded,
#              which is Definition 4.1's "neither q nor its complement is in I" exactly.
#
# ── THE TWO SEEDED OPERATORS, AND THE PARITY IS THE WHOLE DESIGN ──
# Writing `T` for the carried-true atoms and `U` for the carried-undefined ones:
#
#   S_T  (J) = lfp_{⊇T}     T_{P/J}      the UNDERESTIMATE operator
#   S^U_T(J) = lfp_{⊇T ∪ U} T_{P/J}      the OVERESTIMATE operator
#
#   once = S^U_T(w)      twice = S_T(once)      possible = S^U_T(W⁺)
#
# ★★★ `U` REACHES OVERESTIMATE STAGES ONLY, AND IT ENTERS BEFORE THE FIXPOINT RATHER THAN AFTER
# IT. Both halves of that sentence are load-bearing and each has its own failure mode:
#
#   TOO LATE — unioning `U` in AFTER the fixpoint silences POSITIVE readers. On `P = { s :- x }`
#              with `x` carried UNDEFINED the union form gives `possible = {x}` and `s` FALSE,
#              where the unfounded-set account gives `s` UNDEFINED: `s`'s only rule has a subgoal
#              that is not false, so `s` is not unfounded. Carried undefinedness would have
#              propagated through negation only and never through a positive body.
#
#   TOO WIDE — letting `U` reach the UNDERESTIMATE pins atoms this pass settles: the carried atom
#              lands in `W⁺` and comes back TRUE. ★ Invisible on an atom the program DERIVES (it is
#              in the underestimate anyway), which is why a suite must arm it on an UNDERIVED
#              subject — a control names a defect AND a subject, and the pair has to be checked.
#
# ── THE HERBRAND BASE EXTENDS, AND `program.nix`'s HEADER IS AMENDED TO SAY SO ──
# A carried atom need not be mentioned by this pass's program at all — the pure-carry case — so the
# model is computed and reported over `program.atoms ∪ dom(interpretation)`: program atoms first in
# declaration order, then interpretation atoms not already present, in the interpretation's own
# order. `verdict` is unchanged and stays total on every string.
#
# ★ WHAT THIS CONSTRUCTION IS NOT. With `U ≠ ∅` the two operators belong to two DIFFERENT augmented
# programs — `S^U_T` is the `S` of `P ∪ facts(T ∪ U)` and `S_T` is that of `P ∪ facts(T)` — while
# the alternating transformation composes ONE program's operator with itself. So this is `A_Q` for
# no program `Q`, and Van Gelder 1993's Theorem 7.8 ("The alternating fixpoint model is IDENTICAL
# to the well-founded partial model") does NOT apply to it. That the unfounded-set account above
# and the alternating account here define the same object is an INTERPRETED ANALOGUE, CLAIMED AND
# NOT PROVED. It has a differential oracle rather than a proof, and the oracle is the honest form.
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

  # ── THE INTERPRETATION, PARSED AND REFUSED BEFORE ANYTHING IS COMPUTED OVER IT ──
  # The entries are validated by an EXPLICIT walk rather than by a destructuring pattern, and that
  # is a diagnostic decision: a pattern refuses uncatchably and cannot say WHICH element of a list
  # was malformed, where these refusals name the atom, the position and the offending value.
  #
  # ★ EVERY REFUSAL HERE IS THE PRIMARY'S REQUIREMENT, NOT A VALIDATION CONVENTION. Admitting a
  # violation would mean the engine computed over something VGRS Definition 2.4 does not quantify
  # over, so its theorems would not be about the result.
  interpretationVocabulary = [
    "true"
    "undefined"
    "false"
  ];

  parseInterpretation =
    entries:
    let
      positions = prelude.genList (i: i) (prelude.length entries);
      checked = map (
        i:
        let
          e = prelude.elemAt entries i;
          keys = prelude.attrNames e;
        in
        if !(e ? atom) then
          throw "gen-scope: interpretation entry ${toString i} has no 'atom' field — an interpretation is a list of { atom, verdict }"
        else if !(e ? verdict) then
          throw "gen-scope: the carried atom '${e.atom}' has no verdict, and a carried atom with no verdict is REFUSED rather than defaulted — 'absent means false' is the exact substitution this parameter exists to prevent"
        else if
          keys != [
            "atom"
            "verdict"
          ]
        then
          throw "gen-scope: the interpretation entry for '${e.atom}' carries the unknown field(s) ${
            prelude.concatMapStringsSep ", " (k: "'${k}'") (
              prelude.filter (k: k != "atom" && k != "verdict") keys
            )
          } — an entry is { atom, verdict } and nothing else"
        else if !(prelude.elem e.verdict interpretationVocabulary) then
          throw "gen-scope: the carried atom '${e.atom}' has verdict '${e.verdict}', which is not one of ${
            prelude.concatMapStringsSep ", " (v: "'${v}'") interpretationVocabulary
          }"
        else
          e
      ) positions;

      # VGRS Definition 2.4 makes a partial interpretation a CONSISTENT set of literals. One atom
      # under two verdicts is therefore not an interpretation at all. A repeated atom under the
      # SAME verdict is the same set and is deduplicated first-occurrence rather than refused —
      # a set has no duplicates, so there is nothing inconsistent about writing one twice.
      byAtom = builtins.groupBy (e: e.atom) checked;
      verdictsOf = atom: prelude.unique (map (e: e.verdict) byAtom.${atom});
      inconsistent = prelude.filter (atom: prelude.length (verdictsOf atom) > 1) (
        prelude.attrNames byAtom
      );
      offender = prelude.head inconsistent;

      # First-occurrence order, which is the order the extended base reports carried-only atoms in.
      domain = prelude.unique (map (e: e.atom) checked);
      withVerdict = v: prelude.filter (atom: prelude.head (verdictsOf atom) == v) domain;
    in
    if inconsistent != [ ] then
      throw "gen-scope: the interpretation is INCONSISTENT — '${offender}' is carried with verdicts ${
        prelude.concatMapStringsSep " and " (v: "'${v}'") (verdictsOf offender)
      }, and Van Gelder, Ross & Schlipf 1991 Definition 2.4 makes a partial interpretation a CONSISTENT set of literals"
    else
      {
        inherit domain;
        # `Pos(I)` is the primary's own name for this projection (VGRS Definition 5.1: "let Pos(I)
        # be the set of positive literals in I"). It is what both operators are seeded above and
        # what the interpreted stability criterion's augmented program is a function of.
        pos = withVerdict "true";
        # The carried-undefined atoms. `Neg(I)` has no consumer — FALSE is inert — so it is not
        # projected: a name for an inert projection invites the reading that it does something.
        undef = withVerdict "undefined";
      };

  # `Pos(I)`, published because it is what the interpreted stability criterion's `P′` is a function
  # of, so a consumer adjudicating a program under an interpretation can read it rather than
  # re-derive it. VGRS Definition 5.1's own name.
  Pos = entries: (parseInterpretation entries).pos;

  # `S(J)` at a given starting set, with the inner convergence flag carried out rather than
  # discarded — an inner loop that did not reach its fixpoint invalidates the outer round that
  # consumed it, and a result that cannot say so is a result whose validity has to be assumed.
  #
  # ★ THE SEED IS THE PARAMETER THAT MAKES THIS TWO OPERATORS RATHER THAN ONE, and which one a
  # stage uses is the parity the header states. Nothing else about `S` moves.
  stage =
    program: seed: guess:
    leastModelLib.leastModel {
      program = reduct program guess;
      inherit seed;
    };

  wellFoundedModel =
    { program, interpretation }:
    let
      parsed = parseInterpretation interpretation;
      # `T` — carried TRUE, the starting set of BOTH operators.
      trueCarry = prelude.genAttrs parsed.pos (_: true);
      # `T ∪ U` — the OVERESTIMATE operator's starting set, and the only place `U` is ever seen.
      possibleCarry = trueCarry // prelude.genAttrs parsed.undef (_: true);

      underestimate = stage program trueCarry;
      overestimate = stage program possibleCarry;

      # The reported base. Program atoms first, in declaration order — the order the ordered fold
      # over contributions is defined against — then interpretation atoms not already present, in
      # the interpretation's own order. A carried atom is not a contribution of this pass, which
      # is why it does not compete for a position among those that are.
      base = program.atoms ++ prelude.filter (a: !(prelude.elem a program.atoms)) parsed.domain;

      # `S²` is monotone and the iteration from ∅ is increasing over subsets of the base, so the
      # same theorem bounds this loop as bounds the inner one: at most one productive round per
      # atom, plus the round that observes none was. ★ The bound is taken over the EXTENDED base
      # rather than over `program.atoms`, which is the construction this build takes: the seeded
      # atoms are present from round zero and cost no round, so the extended figure is an upper
      # bound on a loop the shorter one already bounded — stated rather than assumed.
      roundBound = base ++ [ null ];
      step =
        acc:
        if acc.done then
          acc
        else
          let
            once = overestimate acc.w;
            twice = underestimate once.derived;
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
      # `S^U_T(W⁺)`: true or undefined. The complement of this set is false. ★ THE OVERESTIMATE
      # OPERATOR, not the underestimate — this is the stage a carried-UNDEFINED atom has to reach
      # if it is to come back undefined rather than false.
      possible = (overestimate trueSet).derived;

      # The three verdicts are emitted in the base's order rather than in the codepoint order an
      # attribute-set walk would give, because that order is the one the ordered fold over
      # contributions is defined against and a set that arrives sorted by name has already lost it.
      select = pred: builtins.filter pred base;
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
  # the third value has a name a consumer can bind rather than a string it has to know. ★ The
  # interpretation's verdict field is checked against THIS binding rather than against a re-spelled
  # list, so the two cannot drift.
  verdictNames = interpretationVocabulary;
in
{
  inherit
    reduct
    wellFoundedModel
    verdictNames
    Pos
    ;
}
