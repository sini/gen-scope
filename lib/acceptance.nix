# The benchmark-acceptance bound, its derivation, and the regression DETECTOR.
#
# THE ENGINE CONSTRAINS NOTHING ON COST. It accepts any program the semantics does not refuse,
# and costs what it costs: no depth, size or shape makes a program inadmissible. The figure below
# is an ACCEPTANCE bound — it states what has been VERIFIED, never what the engine permits. Past
# it the engine warns; it does not refuse. A runtime refusal past a stated depth was the
# recommendation that was rejected, on the ground that a refusal makes cost into correctness and
# constrains what a user may express.
#
# THE FIGURE IS NEVER A BARE NUMBER. It is derived at implementation from the engine's own
# measured cost curve and recorded WITH ITS DERIVATION, so a later reader can say what it means
# and re-derive it; and it is re-derived whenever the engine changes. "Changes" is made checkable
# rather than left to judgement — `reDerivationOwedOn` below names the constructions whose
# editing owes a re-derivation.
#
# ── THE DETECTOR DETECTS; THE JUDGE DECIDES ──
# A bound DERIVED FROM the measured curve cannot be FAILED BY that curve, so "the benchmark
# exceeded the figure" is unfalsifiable by construction and is not the signal. The signal is a
# re-derivation moving the verified depth DOWNWARD against the previously recorded figure — and
# it is compared under three pinned terms, because two figures produced under different terms are
# not two readings of one quantity:
#
#   1. the same fixture families,
#   2. the same DERIVATION FUNCTION — without this term a more generous rule would mask a shrunk
#      envelope by producing a larger number from a worse curve, and
#   3. the same environment terms every ceiling reading in this library holds under.
#
# A change to term 2 is neither a pass nor a failure: it VOIDS the comparison and a fresh
# baseline is owed, recorded as such.
#
# ★ WHAT A FIRED DETECTOR DOES: it returns a signal. It does not execute the retreat, and nothing
# here can. What the acceptance exit arms is a SEMANTICS retreat, not a performance ticket, and
# under an automatic term a measured depth regression would execute it with nobody deciding it.
#
# ★ WHAT THIS DETECTOR CANNOT SEE, stated because a silent instrument reads like a passing one:
# it detects REGRESSION, never INADEQUACY. An engine whose FIRST verified depth is far too low for
# the fleet it is for regresses against nothing and this stays silent; one that is uniformly
# inadequate never fires it at all. The first run is the extreme case of the same boundary — with
# no prior figure the detector cannot fire, and it says `unbaselined` rather than `steady`. What
# covers inadequacy is a person reading the reported curve against the fleet the engine is for,
# which is why the acceptance judge is a person and not a threshold.
{ prelude }:
let
  # The environment every ceiling and cost reading in this library holds under. It is part of the
  # comparison rather than a note beside it: a figure read under a different call-depth guard or
  # a different stack limit is a figure about a different machine.
  environment = {
    nix = "2.34.8";
    maxCallDepth = 10000;
    stackLimitKb = 8192;
  };

  # THE DERIVATION FUNCTION, stated as text because it is a PINNED TERM of the comparison and a
  # comparison whose rule lives only in someone's head cannot be voided when the rule changes.
  derivation = "the greatest condensation depth at which every arm of ci/bench/cost-classes.nix completed with converged=true, over the fixture families named beside it";

  fixtures = [
    "chain"
    "cycle"
    "blocks"
    "blocksWide"
    "deepContested"
    "layers"
  ];

  # The four constructions whose editing owes a re-derivation, as data rather than as prose, so
  # the trigger's content is one thing and not two that drift.
  reDerivationOwedOn = [
    "the partition arms consumed through the gen-graph door"
    "the least-model round loop"
    "the alternating fixpoint"
    "the accumulator forcing discipline"
  ];

  # THE RECORDED FIGURE. Derived by the function above from the cost curve committed beside it;
  # see README for the sweep that produced it and for the raw ladder.
  verifiedDepth = {
    depth = 2049;
    inherit
      derivation
      fixtures
      environment
      reDerivationOwedOn
      ;
  };

  # The comparison, and every outcome is NAMED. There is no branch that returns nothing.
  acceptanceSignal =
    { baseline, reading }:
    if baseline == null then
      {
        signal = "unbaselined";
        reason = "no prior figure: the detector cannot fire, and the reported curve is the only instrument";
      }
    else if baseline.fixtures != reading.fixtures then
      {
        signal = "voided";
        reason = "the fixture families differ: the two figures are not readings of one quantity";
      }
    else if baseline.derivation != reading.derivation then
      {
        signal = "voided";
        reason = "the derivation function differs: a fresh baseline is owed, recorded as such";
      }
    else if baseline.environment != reading.environment then
      {
        signal = "voided";
        reason = "the environment terms differ: every depth reading holds only under its own";
      }
    else if reading.depth < baseline.depth then
      {
        signal = "fired";
        reason = "the verified depth moved downward under three pinned terms: a signal to the judge, who takes the retreat or declines it";
      }
    else
      {
        signal = "steady";
        reason = "the verified depth did not move downward under three pinned terms";
      };

  # The closed vocabulary, as data. `unbaselined` is a member because the first run is a real
  # state of this instrument and not an absence of one.
  signalNames = [
    "unbaselined"
    "voided"
    "fired"
    "steady"
  ];
in
{
  inherit
    verifiedDepth
    acceptanceSignal
    signalNames
    ;
}
