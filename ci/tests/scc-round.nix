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
  forceGate = import ./_fixtures/scc-force-gate.nix { inherit genScope; };
  inherit (corpus) results;

  # Carrier vocabulary for the oracle-row cells below (the corpus keeps its own copy private).
  num = bottom: height: {
    inherit bottom height;
    leq = a: b: a <= b;
    quotient = false;
  };
  qnum = bottom: height: {
    inherit bottom height;
    leq = a: b: a <= b;
    quotient = true;
  };
  inherit (genScope) circular;
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
    # ── THE HEIGHT SEAT'S DEMAND SCOPE (LAZYI × UNDEMERR) ──
    # ★ THE CROSSING CELL: the member `n.b` joins the demand only from level 4 on, and its step
    # DIVIDES BY ZERO at exactly the level-1 input no demand ever produces. The value 3 at exit 0
    # asserts that the seats' own computation forced NOTHING the demand never did — a run counter
    # computed over a demanded member's whole raw column dies here uncatchably, the same
    # undemanded-forcing class the bound's cone rule excludes, one seat over.
    test-lateread-an-undemanded-early-level-is-never-forced-by-the-seats = {
      expr = results.LATEREAD;
      expected = 3;
    };
    # The strict UNDEMERR half at the same seats: `n.c` is an INSTANCE no demand ever forces —
    # `n.b` reads it only at early levels the demand skips — and its step always errors. The
    # value asserts no undemanded instance's step is run by the seats' own computation.
    test-lateread-an-undemanded-instance-behind-a-demand-gap-is-never-forced = {
      expr = results.LATEREAD2;
      expected = 3;
    };
    # The control that isolates the ERROR from the demand gap: the same wiring, total step.
    test-control-lateread-with-a-total-step-answers = {
      expr = results."LATEREAD-CTL";
      expected = 3;
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

    # ── THE FORCE GATE'S NON-TARGET SEAT (A26), ANSWERING SIDE ──
    # The monotone twin of the descending non-target member: the same three-node program with
    # dsc ascending answers — and answers the SAME value 1 the target-column-scoped build
    # returned on the descending fixture, which is why the refusal cell next door asserts the
    # message and never the value. Isolates the descent as the whole cause.
    test-control-a-monotone-non-target-member-answers = {
      expr = forceGate.monotoneAnswers;
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

    # ── THE ORACLE-TABLE ROWS GIVEN DEDICATED CELLS ──
    # Not corpus ports: each cell below is one row of the migration's oracle table that was
    # covered only transitively, landed as its own cell. Expectations hand-derived before the
    # cells ran. (The MEMOIZATION row — one evaluation for three reads of one attribute — is NOT
    # cellable here: the count is observable only as a `builtins.trace` on stderr, which this
    # runner cannot read. It lives as the instrument `ci/bench/eval-memo.sh`, defect arm included.)

    # A cycle closed THROUGH AN ORDINARY ATTRIBUTE converges: the ordinary attribute is re-derived
    # per level against the round's snapshot, so the cycle m → ord → m is the member's own
    # iteration wearing one extra hop, and a name-level condensation that refused it would raise
    # a false red. Hand-derived: m ascends 0→1→2→3 off its own previous level, settles at 3.
    test-a-cycle-closed-through-an-ordinary-attribute-converges = {
      expr = corpus.run {
        m = circular { carrier = num 0 4; } (
          self: _id: _prev:
          let
            o = self.get "n" "ord";
          in
          if o >= 3 then 3 else o + 1
        );
        ord = self: _id: self.get "n" "m";
      } "m";
      expected = 3;
    };

    # A circular STRUCTURAL attribute reaches the guard and iterates: the declaration-kind branch
    # sits inside the application, downstream of the partition on BOTH arms, so an `edges-*` name
    # selects the structural arm and still runs the ascent. Hand-derived: 0→1→2, settles at 2.
    test-a-circular-structural-attribute-reaches-the-guard-and-iterates = {
      expr = corpus.run {
        "edges-x" = circular { carrier = num 0 3; } (
          self: _id: _prev:
          let
            v = self.get "n" "edges-x";
          in
          if v >= 2 then 2 else v + 1
        );
      } "edges-x";
      expected = 2;
    };

    # Two quotient instances that DO NOT read each other both answer: the closure refusal keys on
    # the JOIN — a re-entry on the walked path — so a pair of independent ascents is never
    # checked against anything. Hand-derived: each ascent is bottom → constant, 5 and 7.
    test-two-quotient-instances-that-do-not-read-each-other-both-answer = {
      expr =
        let
          attrs = {
            q1 = circular { carrier = qnum 0 3; } (
              _self: _id: _prev:
              5
            );
            q2 = circular { carrier = qnum 0 3; } (
              _self: _id: _prev:
              7
            );
          };
        in
        {
          q1 = corpus.run attrs "q1";
          q2 = corpus.run attrs "q2";
        };
      expected = {
        q1 = 5;
        q2 = 7;
      };
    };

    # A fresh member demanded inside a TOP-LEVEL quotient's ascent opens its own round: the
    # quotient's accessor carries no open round, so the member's demand is CASE 1 and the member
    # is driven to ITS OWN least fixed point rather than one step against the quotient's iterate.
    # Hand-derived: m's own round settles at 3, the quotient ascends to 3 + 1 = 4.
    test-a-member-demanded-inside-a-top-level-quotients-ascent-opens-its-own-round = {
      expr = corpus.run {
        q = circular { carrier = qnum 0 4; } (
          self: _id: _prev:
          self.get "n" "m" + 1
        );
        m = circular { carrier = num 0 4; } (
          self: _id: _prev:
          let
            v = self.get "n" "m";
          in
          if v >= 3 then 3 else v + 1
        );
      } "q";
      expected = 4;
    };
  };
}
