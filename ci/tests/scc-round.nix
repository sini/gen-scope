# THE SHARED ROUND'S VALUE CELLS — the tracked model corpus's answering fixtures, against the REAL
# evaluator.
#
# The fixtures and their provenance live in `_fixtures/scc-corpus.nix`: forty programs ported from
# the migration spec's tracked executable model, asserted here against that model's HAND-DERIVED
# default-column expectations (den-ag-design `specs/2026-08-22-gen-scc-admission-model/r28/
# HAND-DERIVED-r28.md`), which were derived before any cell ran. What is here is what can be
# asserted as a VALUE — the programs the round ANSWERS, and the controls beside each refusal
# family. WHICH refusal a refusing fixture earns is a claim about a message, so those cells live
# in `../tests-error.nix` where `expectedError` can read the text.
#
# ★ THE BLIND-SPOT CELL IS SELF-WITNESSING. `UNDEMERR`'s undemanded member divides by zero when
# forced — an anonymous, uncatchable death — so the cell asserting the value `2` asserts, in the
# same breath, that the settlement test at the bound FORCED NOTHING UNDEMANDED: the demand cone is
# compared, never the universe (round 28, C26-1). The pre-round-28 tracked suite was measured
# blind to this class; porting the corpus without it would re-import the blind spot.
{ genScope, ... }:
let
  corpus = import ./_fixtures/scc-corpus.nix { inherit genScope; };
  inherit (corpus) results;
in
{
  flake.tests."scc-round" = {
    # ── THE DEGENERATE UNIVERSE ──
    # One eligible instance is the k = 1 degeneration of the composed rule: the landed
    # single-attribute ascent, unchanged.
    test-control-a-lone-instance-answers-through-the-degenerate-ascent = {
      expr = results.CTLVALUE;
      expected = 7;
    };

    # ── THE COMPOSED BOUND IS Σhᵢ + 1, NEVER max(hᵢ) + 1 ──
    # The saturating ratchet: two members of declared height three ascending in ALTERNATION take
    # six strictly ascending levels — saturating Σhᵢ = 6 — and the seventh observes the fixed
    # point. Under max(hᵢ) + 1 = 4 the round would stop two ascents short of the least fixed
    # point, so this cell is the one family that separates the two composition rules.
    test-the-saturating-ratchet-converges-at-the-composed-bound = {
      expr = {
        a = corpus.ratchetA;
        b = corpus.ratchetB;
      };
      expected = {
        a = [
          1
          2
          3
        ];
        b = [
          1
          2
          3
        ];
      };
    };

    # ── THE OUTER SEAT'S FENCES, ANSWERING SIDE ──
    # The hybrid-only quotient at value 0: the same program whose value-9 twin is refused next
    # door — the declaration's VALUE decides whether the seat can see the step's
    # non-monotonicity, never whether a refusal it raises is sound.
    test-control-unevalxc-with-the-hybrid-quotient-at-zero-answers = {
      expr = results."UNEVALXC-ZR0";
      expected = 2;
    };

    # A quotient-steered demand shift: the member goes genuinely unforced at one transition and
    # forced at the next, and the entrywise clamp orders the pair without a forced-set gate.
    test-lazyi-a-quotient-steered-demand-shift-answers = {
      expr = results.LAZYI;
      expected = 2;
    };

    # A descending quotient behind two members: the clamp serves the ordered value entrywise, so
    # the inherited descent refutes nobody.
    test-h5-a-descending-quotient-behind-two-members-answers = {
      expr = results.H5;
      expected = 5;
    };

    # A24's specimen: a member whose step is antitone in a quotient it reads is ANSWERED where
    # the constructed pair does not descend — the stated price of a partial monotonicity cover,
    # pinned as a passing cell rather than described in prose.
    test-h2-an-antitone-quotient-behind-a-member-answers = {
      expr = results.H2;
      expected = 5;
    };

    # Incomparable entries take the NEUTRAL fallback (the later level's own value), which
    # contributes nothing to the verdict — the ⊥-fallback would refuse this program.
    test-unshow-incomparable-entries-take-the-neutral-fallback = {
      expr = results.UNSHOWINC;
      expected = 2;
    };

    # The ordered twin of the FLIP family: no descent on the walked trajectory, so the seat is
    # never armed and the program answers.
    test-control-flip-with-an-ordered-quotient-answers = {
      expr = results.FLIPORD;
      expected = 2;
    };

    # ── THE HEIGHT SEAT COUNTS A RUN, NOT A TALLY ──
    # A TRUTHFUL height = 1 on the exact two-element order {0 < 1}, under an oscillation driven
    # by a provisional intermediate: the longest strictly ascending run never exceeds one edge —
    # a descent RESETS the run — so the declaration is not refuted and the program answers. A
    # tally of strict ascents would refuse it with a witness the carrier does not contain
    # (round 27, C25-1).
    test-hosc-a-truthful-height-survives-descent-and-reascent = {
      expr = results.HOSC;
      expected = 1;
    };
    test-control-hosc-with-the-height-overdeclared-answers = {
      expr = results."HOSC-H2";
      expected = 1;
    };
    test-control-hosc-without-the-oscillation-answers = {
      expr = results."HOSC-NOOSC";
      expected = 1;
    };
    test-control-hosc-one-descent-and-no-reascent-answers = {
      expr = results."HOSC-ONEDESC";
      expected = 0;
    };

    # ── THE DEMAND CONE AT THE BOUND ──
    # ★ THE BLIND-SPOT CELL (C26-1): the target never reads `n.e`, and `n.e`'s step is a
    # division by zero when forced. The value `2` at exit 0 asserts that the settlement compared
    # the DEMAND CONE and forced nothing undemanded — under the withdrawn whole-universe rule
    # this very cell dies uncatchably.
    test-an-undemanded-erroring-member-is-never-forced-at-the-bound = {
      expr = results.UNDEMERR;
      expected = 2;
    };
    # The control that isolates the ERROR from the undemandedness: the same wiring with a total
    # member answers identically. (`DEMERR`, which isolates undemandedness by READING the
    # erroring member, dies by construction and is asserted next door.)
    test-control-an-undemanded-total-member-answers = {
      expr = results.UNDEMOK;
      expected = 2;
    };
    # Round 27's own control, no longer forcing the member its demand never read.
    test-control-boundquiet-without-the-oscillation-answers = {
      expr = results."BOUNDQUIET-NOOSC";
      expected = 1;
    };
    # The fathomed twin: enough declared height for the gated ascent to complete, and the whole
    # cone is stationary at the bound.
    test-control-boundquiet-with-a-fathomed-height-answers = {
      expr = results."BOUNDQUIET-FATH";
      expected = 1;
    };

    # ── THE LIFETIME RULE'S CLEAN PATH ──
    # The same demand the refusal cell next door raises through a child record's `_eval` cache,
    # routed through `self.get`: unaffected, and the round converges. A build that refused every
    # route could not pass this cell.
    test-control-a-childs-attribute-through-get-inside-a-round-answers = {
      expr = corpus.lifetime.getRead;
      expected = 3;
    };
  };
}
