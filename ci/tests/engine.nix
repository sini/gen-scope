# The engine's front door: the partition it consumes, the provenance its result carries, the
# ordered fold, and the acceptance detector.
#
# ★ THE PROVENANCE CELLS ARE TWO-SIDED, and the inside-the-bound cell is the live control. A cell
# asserting only that a stamped result carries a field passes against an engine that stamps
# everything, which would say nothing at all about the input that produced it. The pair asserts
# the stamp appears EXACTLY when the input exceeds the verified bound.
#
# ★ AND THE END-TO-END CELL IS NOT REDUNDANT WITH THE BOUNDARY CELLS. The boundary cells read the
# stamp as a function of a depth, which is cheap and exact; the end-to-end cell is what says the
# door's reported depth is the number that reaches it. Without the second, the two could agree
# forever while nothing connected them.
{ genScope, ... }:
let
  inherit (genScope) verifiedDepth;

  # A chain of n atoms: the condensation is n singleton components in a line, so its longest path
  # is n - 1. The smallest shape that can carry a given depth, which is why it is the one used to
  # cross the bound.
  chain =
    n:
    genScope.mkProgram {
      rules = builtins.genList (
        i:
        if i == 0 then
          { head = "a${toString i}"; }
        else
          {
            head = "a${toString i}";
            pos = [ "a${toString (i - 1)}" ];
          }
      ) n;
    };

  small = genScope.solve (chain 8);
  # Two atoms past the bound: the least chain whose condensation depth exceeds it.
  beyond = genScope.solve (chain (verifiedDepth.depth + 3));

  gated = genScope.wellFoundedModel (
    genScope.mkProgram {
      rules = [
        { head = "on"; }
        {
          head = "u1";
          neg = [ "u2" ];
        }
        {
          head = "u2";
          neg = [ "u1" ];
        }
      ];
    }
  );
  contributions = [
    {
      atom = "on";
      value = "first";
    }
    {
      atom = "u1";
      value = "contested";
    }
    {
      atom = "off";
      value = "never";
    }
    {
      atom = "on";
      value = "second";
    }
  ];
  folded = genScope.foldContributions {
    model = gated;
    inherit contributions;
    op = acc: c: acc ++ [ c.value ];
    init = [ ];
  };
in
{
  flake.tests."engine-door" = {
    # The door is consumed, never re-implemented: the depth on the result is the field the
    # partition door publishes, read off a graph this engine derived and handed over unsigned.
    test-solve-reports-the-doors-condensation-depth = {
      expr = small.condensationDepth;
      expected = 7;
    };
    test-solve-carries-the-model = {
      expr = builtins.length small.trueAtoms;
      expected = 8;
    };

    # ── THE PROVENANCE STAMP, BOTH SIDES OF THE BOUND ──
    test-inside-the-bound-nothing-is-stamped = {
      expr = genScope.provenanceFor verifiedDepth.depth;
      expected = [ ];
    };
    test-one-below-the-bound-nothing-is-stamped = {
      expr = genScope.provenanceFor (verifiedDepth.depth - 1);
      expected = [ ];
    };
    test-past-the-bound-the-result-carries-the-fact = {
      expr = genScope.provenanceFor (verifiedDepth.depth + 1);
      expected = [
        {
          fact = "the input exceeds the engine's benchmark-verified condensation depth";
          condensationDepth = verifiedDepth.depth + 1;
          verifiedDepth = verifiedDepth.depth;
          inherit (verifiedDepth) derivation fixtures environment;
        }
      ];
    };
    # The figure is never a bare number: what it means travels with it, so a caller receiving the
    # warning can say what was verified and how.
    test-the-stamp-carries-the-derivation = {
      expr = (builtins.head (genScope.provenanceFor (verifiedDepth.depth + 1))).derivation;
      expected = verifiedDepth.derivation;
    };
    # ★ THE LIVE CONTROL for the end-to-end pair: a small program is inside the bound and is not
    # stamped, so the stamped cell below is reading the input rather than a field that is always
    # populated.
    test-end-to-end-a-small-program-is-not-stamped = {
      expr = small.provenance;
      expected = [ ];
    };
    test-end-to-end-a-deep-program-is-stamped = {
      expr = map (e: {
        inherit (e) fact condensationDepth verifiedDepth;
      }) beyond.provenance;
      expected = [
        {
          fact = "the input exceeds the engine's benchmark-verified condensation depth";
          condensationDepth = verifiedDepth.depth + 2;
          verifiedDepth = verifiedDepth.depth;
        }
      ];
    };
    # The warning is not a refusal: the deep program is answered, and answered correctly.
    test-a-warned-program-is-still-answered = {
      expr = [
        (builtins.length beyond.trueAtoms)
        beyond.converged
      ];
      expected = [
        (verifiedDepth.depth + 3)
        true
      ];
    };

    # ── THE ORDERED FOLD ──
    # Contributions combine in the order they were DECLARED and no strength annotation is read.
    # Both `on` contributions are admitted, in the order written; nothing is sorted or deduped.
    test-contributions-fold-in-declaration-order = {
      expr = folded.value;
      expected = [
        "first"
        "second"
      ];
    };
    # ★ A CONTESTED GATE IS NAMED, NEVER SILENT. An undefined gate does not derive its
    # contribution, and the contribution is not dropped either — it comes back, so a caller who
    # ignores it has decided to.
    test-a-contested-gate-comes-back-named = {
      expr = map (c: c.value) folded.contested;
      expected = [ "contested" ];
    };
    # A gate that is FALSE is neither admitted nor contested: it did not happen, and that is a
    # different fact from being undecided.
    test-a-false-gate-is-neither-admitted-nor-contested = {
      expr = map (c: c.value) folded.admitted;
      expected = [
        "first"
        "second"
      ];
    };

    # ── THE ACCEPTANCE DETECTOR ──
    # It detects a REGRESSION under three pinned terms and returns a signal. It executes nothing.
    test-signal-names-are-a-closed-enumeration = {
      expr = genScope.signalNames;
      expected = [
        "unbaselined"
        "voided"
        "fired"
        "steady"
      ];
    };
    test-the-first-run-cannot-fire = {
      expr =
        (genScope.acceptanceSignal {
          baseline = null;
          reading = verifiedDepth;
        }).signal;
      expected = "unbaselined";
    };
    test-an-unmoved-depth-is-steady = {
      expr =
        (genScope.acceptanceSignal {
          baseline = verifiedDepth;
          reading = verifiedDepth;
        }).signal;
      expected = "steady";
    };
    test-a-risen-depth-is-steady = {
      expr =
        (genScope.acceptanceSignal {
          baseline = verifiedDepth;
          reading = verifiedDepth // {
            depth = verifiedDepth.depth + 1;
          };
        }).signal;
      expected = "steady";
    };
    # ★ THE FIRING CELL. Without it every cell above would pass against a detector that never
    # fires at all.
    test-a-fallen-depth-fires = {
      expr =
        (genScope.acceptanceSignal {
          baseline = verifiedDepth;
          reading = verifiedDepth // {
            depth = verifiedDepth.depth - 1;
          };
        }).signal;
      expected = "fired";
    };
    # A change to any pinned term VOIDS the comparison — neither a pass nor a failure. Each is
    # asserted on its own, because a comparison that voided on only two of the three terms would
    # let the third change silently and read as a regression or as steadiness.
    test-a-changed-derivation-function-voids-the-comparison = {
      expr =
        (genScope.acceptanceSignal {
          baseline = verifiedDepth;
          reading = verifiedDepth // {
            depth = verifiedDepth.depth - 1;
            derivation = "a more generous rule";
          };
        }).signal;
      expected = "voided";
    };
    test-a-changed-fixture-family-voids-the-comparison = {
      expr =
        (genScope.acceptanceSignal {
          baseline = verifiedDepth;
          reading = verifiedDepth // {
            depth = verifiedDepth.depth - 1;
            fixtures = [ "chain" ];
          };
        }).signal;
      expected = "voided";
    };
    test-a-changed-environment-voids-the-comparison = {
      expr =
        (genScope.acceptanceSignal {
          baseline = verifiedDepth;
          reading = verifiedDepth // {
            depth = verifiedDepth.depth - 1;
            environment = verifiedDepth.environment // {
              maxCallDepth = 100000;
            };
          };
        }).signal;
      expected = "voided";
    };
    # The figure travels with what produced it, so a re-derivation can be compared at all.
    test-the-recorded-figure-carries-its-terms = {
      expr = builtins.attrNames verifiedDepth;
      expected = [
        "depth"
        "derivation"
        "environment"
        "fixtures"
        "reDerivationOwedOn"
      ];
    };
  };
}
