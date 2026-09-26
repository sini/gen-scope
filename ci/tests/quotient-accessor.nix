# THE QUOTIENT ACCESSOR OBLIGATION: what each channel ANSWERS for a quotient-converged instance.
# Which refusal fires is a claim about a message, so those cells are `tests-error.nix`'s
# `quotient-accessor-refusals`; this file holds the answers and the controls beside them. The
# class-level control (the key set is fixed under one more step) is `circular.nix`'s
# `test-control-quotient-class-is-fixed`.
{ genScope, ... }:
let
  inherit (import ./_fixtures/quotient-accessor.nix { inherit genScope; })
    r
    debug
    warm
    tree
    tagged
    converged
    ;
in
{
  flake.tests."quotient-accessor" = {
    # The named demand answers the representative, marked with what the carrier decided about it.
    test-getRepresentative-answers-the-tagged-representative = {
      expr = r.getRepresentative "node" "enriched";
      expected = tagged converged;
    };

    # The raw demand's refusal is CATCHABLE — its text is pinned next door.
    test-a-raw-get-on-a-quotient-is-refused-catchably = {
      expr = builtins.tryEval (r.get "node" "enriched");
      expected = {
        success = false;
        value = false;
      };
    };

    # CONTROL: a guard refusing every circular `get` would pass the cell above and fail this one.
    test-control-get-on-a-non-quotient-instance-answers-raw = {
      expr = r.get "node" "counter";
      expected = 10;
    };

    # The refusals fire AT THE DEMAND, at weak head normal form, and not later when
    # `.representative` is forced: a lazily built record would read `success = true` here and throw
    # the height refusal outside the caller's `tryEval`.
    test-a-refusal-under-getRepresentative-fires-at-the-demand = {
      expr = builtins.tryEval (r.getRepresentative "node" "short");
      expected = {
        success = false;
        value = false;
      };
    };

    # A circular step's own accessor carries the named demand.
    test-a-step-reads-a-quotient-through-getRepresentative = {
      expr = r.get "node" "readerRep";
      expected = 3;
    };

    # The reuse path serves the prior's representative, tagged — the recompute arm throws, so the
    # value can only have come from the prior.
    test-the-warm-path-serves-the-tagged-representative-from-the-prior = {
      expr = warm.getRepresentative "node" "enriched";
      expected = tagged converged;
    };

    test-evalDebug-getRepresentative-answers-the-tagged-representative = {
      expr = debug.getRepresentative "node" "enriched";
      expected = tagged converged;
    };

    # ── THE CHANNELS NO ACCESSOR GUARDS ──
    # The tag is built where the value is PRODUCED, so a channel that bypasses both accessors still
    # returns it marked. Tagging inside `getRepresentative` alone passes every cell above and
    # returns the representative UNMARKED on these two.
    test-a-child-records-co-located-eval-carries-the-tag = {
      expr = (tree.get "p" "children").kid._eval.enriched;
      expected = tagged converged;
    };

    test-evalDebug-getTraced-value-carries-the-tag = {
      expr = (debug.getTraced "node" "enriched").value;
      expected = tagged converged;
    };
  };
}
