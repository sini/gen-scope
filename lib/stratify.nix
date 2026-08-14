# THE ONE STRATIFICATION DRIVER — a schedule of strata walked once each, given the instance's own
# stratum assignment as a parameter.
#
# It knows nothing about what an item is. Demands, kinds, minting, nodes: none of those words occur
# below, and the file imports nothing but the prelude's list primitives and the round-loop forcing
# it is handed. What an instance supplies is a run order, a way to place an item in it, an order
# inside one stratum, a starting set, and one function to run a stratum. What it gets back is every
# stratum's settled output in global schedule order, the items whose stratum the schedule never
# named, and how many strata ran.
#
# THEORY — WHAT STRATIFICATION BUYS, AND IT IS COMPLETENESS. Apt, Blair & Walker (1988), "Towards a
# Theory of Declarative Knowledge", in Minker (ed.), pp. 89-148, build their standard model stratum
# by stratum: `M₁ = T_{P₁}↑ω(∅)`, `M_i = T_{P_i}↑ω(M_{i-1})`, `M_P = M_n` (printed p. 108). The
# content of that construction is that EACH STRATUM REACHES ITS OWN FIXED POINT BEFORE THE NEXT
# BEGINS — which is the classical reason aggregation demands stratification, since a fold over a
# set still being added to answers about a prefix. This loop guarantees exactly that and nothing
# more: when a stratum runs, every stratum earlier in the schedule has finished and its settled
# output is closed.
#
# ★ WHAT IS DELIBERATELY NOT HERE: A VISIBILITY RULE. ABW's strictly-lower indexing (their
# Definition 3, printed p. 96) governs a relation symbol occurring NEGATIVELY; a symbol occurring
# positively has its definition within `⋃_{j ≤ i} P_j` — the same stratum included. Their own gloss:
# "each stratum defines new relations in terms of ITSELF ONLY POSITIVELY and in terms of the
# relations from the PREVIOUS STRATA, POSSIBLY NEGATIVELY." So strictly-below is a conservative
# SUFFICIENT CONDITION for a negated read to be sound, not the property stratification delivers. A
# driver that enforced the sufficient condition would be stricter than the theorem and would refuse
# programs the theorem admits. This one imposes no restriction on what an instance may read, and it
# hands out no frozen set. An instance that acquires a NEGATED read acquires ABW's clause 2 with it,
# and that is a change to this file rather than something it absorbs silently.
#
# ── THE BOUND IS A THEOREM ABOUT THE MEASURE, AND NOTHING HERE CEILINGS IT ──
# The loop runs once per element of `schedule`, and `schedule` is the stratum universe derived from
# the instance's own well-founded measure. Termination is Noetherian induction on that measure: an
# instance whose edges strictly decrease it has a finite stratum universe, and the loop visits each
# member once. No number here bounds a cost, nothing is refused for being large, and `strata` is
# reported rather than compared against anything. A ceiling would be the other thing — a number
# chosen to bound cost, which makes cost into correctness and constrains what a caller may express.
#
# ── ITERATIVE ENCODING, AND TOTAL PER-ROUND FORCING ──
# The walk is a fold, not a self-applying lambda: Nix does not reuse the frame of a call in tail
# position, so a recursive walk's descent depth is its iteration count and past the call-depth guard
# it aborts — an abort `tryEval` does not contain. The per-round forcing is `forceFields`, PASSED IN
# rather than defined again here, and it is derived from the accumulator's own fields, so a field
# added later is forced without anyone re-applying the discipline.
#
# ★ THE DISCIPLINE REACHES THE ACCUMULATOR'S FIELDS AND STOPS THERE, AND THE DIFFERENCE IS AN
# INSTANCE'S TO KNOW. Each field is forced to weak head normal form once per round, which is what
# keeps the loop from carrying a thunk chain; for a list field that means the spine, NOT the
# elements. So `advance`'s work fires in the round that produced it exactly when it is the field's
# own value — a refusal written as `settled = throw …` ends the run at that round, even for a
# caller who only reads `unrun`. A refusal written as an ELEMENT of that list — `settled = [ (throw
# …) ]` — survives the whole run and fires only when some consumer forces the element, which may be
# never. An instance whose refusals must fire when they are provoked owes itself that forcing;
# nothing here can supply it, because forcing an instance's values to a depth it did not ask for is
# an evaluation policy and not a loop invariant.
#
# ── NO REFUSALS LIVE HERE ──
# The driver throws nowhere. An item whose stratum the schedule does not name is RETURNED as
# `unrun` — nothing vanishes, nothing is refused, and the caller reads a fact instead of catching
# one. Emission into an already-run stratum is not detected either, because in the instances this
# serves it is inexpressible: a well-founded measure that strictly decreases across an emission
# edge leaves no such emission for an author to write. A detector would be a rule an author can
# meet or miss where the construction leaves nothing to miss. Any refusal an instance needs is the
# instance's own and rides on top of this one.
#
# ★ ONE REFUSAL IS REACHABLE HERE AND IT IS THE EVALUATOR'S, WHICH IS OUTSIDE WHAT "THROWS NOWHERE"
# CLAIMS. The argument record below is a strict pattern, so a caller supplying a seventh field is
# refused at application — `function 'stratify' called with unexpected argument '…'`, naming the
# function and the field, and a missing field is refused the same way. It is NAMED and it is
# UNCATCHABLE: `tryEval` reports `false` for a thrown value and does not contain this one at all,
# so a caller cannot recover from it and no cell can observe it. That is a property of the arity
# check rather than of anything written below, and it is worth knowing for a caller who wants to
# hand this loop a parameter it does not take.
{ prelude, forceFields }:
let
  inherit (prelude)
    elem
    filter
    head
    iterateBounded
    length
    sort
    tail
    ;
in
{
  # `describe` REACHES THIS FILE AND STOPS. It is never handed to `advance`, it appears in no field
  # of the result, and no line below applies it: it is a declaration in the signature and has no
  # runtime role here. What it declares is that an instance placing items in strata owes a way to
  # name one, and the live consumer of that obligation is the cascade's own `emittedBy`, which
  # writes the site into the instance's refusals. It is required to be total — a description that
  # throws on a malformed item turns a caller's diagnostic into an abort — and that totality is the
  # instance's obligation, checked nowhere here, because checking it would be a refusal.
  #
  # ★ THE ONE STRUCTURAL PRECONDITION ON `schedule`, NAMED BECAUSE NOTHING ELSE NAMES IT: its
  # members must be DISTINCT. A stratum appearing twice is walked twice, and the second visit
  # re-selects the same items and settles them again — the loop asks membership questions and never
  # asks whether it has been here before. Both derived instances exclude it by construction rather
  # than by check: the cascade's schedule is consecutive integers from a depth measure, and the
  # minting instance's is the declared passes deduplicated before they are ordered. A caller whose
  # schedule is neither owes the distinctness itself.
  stratify =
    {
      schedule,
      stratumOf,
      within,
      seed,
      advance,
      describe,
    }:
    let
      # One stratum per round, in the order the schedule states. The stratum's items are selected
      # from everything seen so far — the seed plus what earlier strata emitted — which is what
      # makes cross-stratum emission the mechanism it is rather than a special case: an item emitted
      # into a stratum that has not run yet is simply there when that stratum's turn comes.
      step =
        st:
        let
          stratum = head st.pending;
          items = sort within (filter (i: stratumOf i == stratum) st.items);
          round = advance { inherit stratum items; };
        in
        {
          pending = tail st.pending;
          items = st.items ++ round.emitted;
          settled = st.settled ++ round.settled;
        };

      final = iterateBounded forceFields step {
        pending = schedule;
        items = seed;
        settled = [ ];
      } schedule;
    in
    {
      # Stratum-major in schedule order, `within` inside: the loop appends one stratum's output at
      # a time and the selection was sorted before it ran, so the global order is the composition of
      # the two rather than a re-sort of the result.
      inherit (final) settled;

      # The partition's other half. Membership in the schedule is the only question asked, so this
      # is exact wherever `stratumOf` is total on the items, and it is computed over the seed AND
      # the emissions rather than as the difference between two lists — the driver has no notion of
      # an item's identity with which to take a difference, and inventing one would be a parameter
      # with no caller.
      unrun = filter (i: !(elem (stratumOf i) schedule)) final.items;

      strata = length schedule;
    };
}
