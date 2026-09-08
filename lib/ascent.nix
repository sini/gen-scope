# THE ONE BOUNDED-ASCENT DRIVER — a set of members carried together through rounds of the caller's
# own step, each member settled by its own predicate, the walk bounded by a list the caller supplies.
#
# It knows nothing about what a member is and nothing about what a value is. Lattices, joins,
# widenings, stores, node computations: none of those words occur below, and the file imports nothing
# but the prelude's iteration primitives and the round-loop forcing it is handed. What a caller
# supplies is a set of ids, a seed for each, ONE function that takes a whole round, a per-member
# quiescence test, and a list to walk. What it gets back is the last iterate, whether every member
# settled, and how many rounds ran.
#
# ── NO TERMINATION THEOREM IS CLAIMED HERE, AND THERE ARE TWO OF THEM ──
# A caller iterating a step to quiescence owes two separate arguments, and this file makes NEITHER.
# The first is that the step ascends a chain that ends — finite height, monotone step, or whatever
# else closes it for the structure the caller is actually iterating. The second is that the supplied
# bound is long enough to reach the end of that chain. Both are statements about the caller's own
# construction; neither is checkable from here, because a driver that has never seen a value cannot
# know whether two of them are ordered, let alone whether the order is well founded.
#
# ⇒ What this loop guarantees is exactly what a fold guarantees: `advance` is applied once per element
# of `bound`, in order, and the state after the last application comes back. Whether that state is a
# fixed point is `settled`, which is READ rather than asserted.
#
# ★ THE BOUND IS A LIST, AND THE REASON IS THE SAME ONE `lib/stratify.nix` GIVES. It is walked once
# per element and its elements are never read, so a caller passes a list it already holds and this
# file allocates nothing. It is also why no number here ceilings anything: nothing below compares the
# bound against a cost, refuses a caller for supplying a large one, or supplies one of its own. A
# caller whose bound is a declared iteration budget owns that declaration and owns the refusal that
# goes with it; a caller whose bound is a universe derived from a measure owns that instead. The
# difference between the two is invisible here by construction.
#
# ── ITERATIVE ENCODING, AND TOTAL PER-ROUND FORCING ──
# The walk is a fold, not a self-applying lambda: Nix does not reuse the frame of a call in tail
# position, so a recursive walk's descent depth is its round count and past the call-depth guard it
# aborts — an abort `tryEval` does not contain, which is precisely the catchable refusal a bounded
# caller wanted. The per-round forcing is `forceFields`, PASSED IN rather than defined again here,
# and it is derived from the accumulator's own fields, so a field added later is forced without
# anyone re-applying the discipline.
#
# ★ THE DISCIPLINE REACHES THE ACCUMULATOR'S FIELDS AND STOPS THERE. Each field is forced to weak
# head normal form once per round, which is what keeps the loop from carrying a thunk chain; for the
# `values` record that means the RECORD, not its members. So a caller whose per-member values must be
# forced at the round that produced them owes itself that forcing — forcing a caller's values to a
# depth it did not ask for is an evaluation policy and not a loop invariant.
#
# ── NO REFUSALS LIVE HERE ──
# The driver throws nowhere. A bound the walk exhausts without quiescence RETURNS, carrying
# `settled = false` and the iterate it got to — nothing vanishes, nothing is refused, and the caller
# reads a fact instead of catching one. That is deliberate and it is the whole seam: whether an
# unsettled result is a defect is a question about the caller's construction, and a caller that wants
# a located blame builds it from `values`, `settled` and `rounds` on its own side, where it still
# knows what a member is and what its bound was declared to mean.
#
# ★ ONE REFUSAL IS REACHABLE HERE AND IT IS THE EVALUATOR'S, WHICH IS OUTSIDE WHAT "THROWS NOWHERE"
# CLAIMS. The argument record below is a strict pattern, so a caller supplying a sixth field is
# refused at application — `function 'ascend' called with unexpected argument '…'`, naming the
# function and the field — and a missing field is refused the same way. It is NAMED and it is
# UNCATCHABLE: `tryEval` reports `false` for a thrown value and does not contain this one at all, so
# no caller can recover from it and no cell can observe it. That is a property of the arity check
# rather than of anything written below.
{ prelude, forceFields }:
let
  inherit (prelude)
    all
    genAttrs
    iterateBounded
    ;
in
{
  # `settledBy` is asked once per member per round, of that member's OWN previous and next value.
  # The quantifier is `all` over the members and it lives HERE rather than on the caller's side,
  # because "did the round move anything" is a question about the round and not about a member: a
  # caller answering it per member would have to re-derive the conjunction, and a caller answering
  # it once for the whole record would have replaced every member's predicate with `==` on an
  # attribute set. Which predicate a member gets is still entirely the caller's.
  ascend =
    {
      members,
      bottomOf,
      advance,
      settledBy,
      bound,
    }:
    let
      # Once settled, the step is the identity — which is `iterateBounded`'s stated obligation on its
      # caller: surplus elements of the bound idle and the result is the state a recursion would have
      # stopped at. It also means `advance` is applied at most once after the round that settled it,
      # never repeatedly against a fixed point.
      step =
        st:
        if st.settled then
          st
        else
          let
            next = advance st.values;
          in
          {
            values = next;
            settled = all (m: settledBy m st.values.${m} next.${m}) members;
            rounds = st.rounds + 1;
          };
    in
    iterateBounded forceFields step {
      values = genAttrs members bottomOf;
      settled = false;
      rounds = 0;
    } bound;
}
