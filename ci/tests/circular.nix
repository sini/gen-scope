# The circular attribute's DECLARED CARRIER, and what each of its three terms buys.
#
# Every cell here is either a converging run whose bound is exactly the declared height, or the
# clean-path control beside a refusal. WHICH refusal fires is a claim about a message, so those
# cells live in `../tests-error.nix` where `expectedError` can read the text: `tryEval` returns
# `{ success, value }` and discards it, so a suite of booleans is equally satisfied by a
# combinator with one refusal in it.
#
# ★ THE CONTROLS ARE THE POINT OF THE CLEAN CELLS. A guard that refused unconditionally would
# satisfy every refusal cell in the file next door and nothing else would notice, so each guard's
# clean path is asserted here under `test-control-*`: a carrier that IS declared converges, a step
# that DOES ascend is not refused as antitone, and a height that IS sufficient converges inside it.
{ lib, genScope, ... }:
let
  inherit (genScope) circular;

  roots = genScope.buildRoots {
    parentGraph = genScope.vertex "node";
    importGraph = genScope.empty;
    decls = {
      node = {
        init-val = 0;
        target = 10;
      };
    };
    types = { };
  };

  # The integer carrier: bottom 0, the arithmetic order, and a height that is the exact number of
  # strict ascents the step can take before it reaches the target. Nothing here is rounded up — a
  # height chosen larger than the lattice's would still converge, and would stop the cell from
  # saying that the derived bound is the theorem it claims to be.
  upTo = h: {
    bottom = 0;
    leq = a: b: a <= b;
    height = h;
    # The arithmetic order is antisymmetric on the raw values, so this is not a quotient — the
    # fourth term is required and total, and stating it truthfully is what admits the instance to
    # a shared round.
    quotient = false;
  };

  evalWith =
    scope: attr:
    genScope.eval {
      inherit scope;
      attributes = {
        children = _self: _id: { };
        imports = _self: _id: [ ];
      }
      // attr;
    };

  convergingResult = evalWith roots {
    counter = circular { carrier = upTo 10; } (
      self: id: prev:
      let
        target = (self.node id).decls.target;
      in
      if prev >= target then prev else prev + 1
    );
  };

  # The same grammar with a height ONE SHORT of the ascents it takes. The step is unchanged and
  # perfectly monotone, so what this separates is the height term from the monotonicity term: the
  # run refuses, and the refusal it earns names the declaration rather than the step.
  shortHeightResult = evalWith roots {
    counter = circular { carrier = upTo 9; } (
      self: id: prev:
      let
        target = (self.node id).decls.target;
      in
      if prev >= target then prev else prev + 1
    );
  };

  divergingRoots = genScope.buildRoots {
    parentGraph = genScope.vertex "div";
    importGraph = genScope.empty;
    decls = {
      div = { };
    };
    types = { };
  };

  # Monotone and unbounded: the step ascends forever on a carrier declared finite. The cell this
  # replaces read the same grammar as "diverges" and pinned the iteration-count throw, which is the
  # conflation this split exists to end — a monotone step on an unbounded carrier and an antitone
  # step are different facts and now earn different refusals.
  unboundedResult = evalWith divergingRoots {
    forever = circular { carrier = upTo 5; } (
      _self: _id: prev:
      prev + 1
    );
  };

  # Antitone: the two states oscillate, so no order ascends them. Under an equality convergence
  # test this is invisible by construction — consecutive states are never equal — and the run
  # reached the iteration cap and reported the count.
  oscillatingResult = evalWith divergingRoots {
    flip =
      circular
        {
          carrier = {
            bottom = 0;
            leq = a: b: a <= b;
            height = 4;
            quotient = false;
          };
        }
        (
          _self: _id: prev:
          if prev == 0 then 1 else 0
        );
  };

  # ── THE QUOTIENT CARRIER ──
  # The declared order is KEY-SET INCLUSION, and the raw values churn on every single pass. This is
  # the shape a coarsened convergence predicate used to express by supplying its own `eq`: it is
  # admissible, and what makes it admissible is that the coarsening is now the DECLARED ORDER with
  # a height stated for it, rather than an equality unrelated to any order. Three keys is the
  # lattice's height and the run takes exactly three strict ascents.
  keySetCarrier = {
    bottom = { };
    leq = a: b: builtins.all (k: b ? ${k}) (builtins.attrNames a);
    height = 3;
    # Key-set inclusion orders a QUOTIENT of the value space — raw values churn inside a class —
    # and the declaration says so: a quotient instance evaluates by the per-instance ascent and is
    # never a simultaneous member of a shared round.
    quotient = true;
  };

  enrichResult = evalWith roots {
    enriched = circular { carrier = keySetCarrier; } (
      _self: _id: prev:
      let
        bumped = builtins.mapAttrs (_: v: v + 1) prev;
        n = builtins.length (builtins.attrNames prev);
      in
      if n >= 3 then bumped else bumped // { "k${toString n}" = 0; }
    );
  };

  # What the quotient does NOT buy, exhibited rather than described: applying the step to the
  # converged answer moves it. The class is the fixed point; the representative is not one, and a
  # consumer that needs the finer stability asks for the finer carrier instead of reading this
  # value as though the carrier had been the raw one.
  enrichedOnceMore = builtins.mapAttrs (_: v: v + 1) (enrichResult.get "node" "enriched");
in
{
  flake.tests."circular" = {
    # ── THE DERIVED BOUND ──
    # Ten strict ascents on a lattice of declared height ten, and the eleventh step is the one that
    # observes no ascent. `h + 1` step evaluations is what the declaration buys and the cell is
    # pinned at the exact height so that the claim is falsifiable: the cell below shows nine fails.
    test-control-converges-to-target-within-declared-height = {
      expr = convergingResult.get "node" "counter";
      expected = 10;
    };

    test-height-one-short-is-refused = {
      expr = builtins.tryEval (shortHeightResult.get "node" "counter");
      expected = {
        success = false;
        value = false;
      };
    };

    # A monotone step on an unbounded carrier. The refusal is the height's, and the message that
    # says so is asserted in `../tests-error.nix`.
    test-unbounded-ascent-exceeds-declared-height = {
      expr = builtins.tryEval (unboundedResult.get "div" "forever");
      expected = {
        success = false;
        value = false;
      };
    };

    # An antitone step. Same boolean as the cell above and a DIFFERENT message, which is the whole
    # content of splitting them.
    test-antitone-step-is-refused = {
      expr = builtins.tryEval (oscillatingResult.get "div" "flip");
      expected = {
        success = false;
        value = false;
      };
    };

    # ── THE CARRIER IS REQUIRED ──
    test-no-declared-carrier-is-refused = {
      expr = builtins.tryEval (
        (evalWith roots {
          bare = circular { } (
            _self: _id: prev:
            prev
          );
        }).get
          "node"
          "bare"
      );
      expected = {
        success = false;
        value = false;
      };
    };

    # ── THE QUOTIENT CARRIER ──
    test-control-quotient-carrier-converges-on-the-class = {
      expr = enrichResult.get "node" "enriched";
      expected = {
        k0 = 3;
        k1 = 2;
        k2 = 1;
      };
    };

    # The residual, pinned as measured fact rather than described in a comment: the answer is a
    # fixed point of the DECLARED order and not of the step.
    test-quotient-answer-is-not-a-raw-fixpoint = {
      expr = enrichedOnceMore == enrichResult.get "node" "enriched";
      expected = false;
    };

    # …and the class it belongs to IS fixed, which is what was declared and what converged.
    test-control-quotient-class-is-fixed = {
      expr = builtins.attrNames enrichedOnceMore;
      expected = builtins.attrNames (enrichResult.get "node" "enriched");
    };
  };
}
