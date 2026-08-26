# THE PER-PROCESS CELLS — fixtures whose verdict is a PROCESS EXIT, one fixture per process.
#
# WHY THESE CANNOT BE SUITE CELLS. Every cell here observes a failure channel `tryEval` does not
# catch — `division by zero` and `infinite recursion encountered` abort the evaluator — so there
# is no message a suite cell could read and no boolean it could return: the assertion IS the exit
# status, read by the runner in `tests-process.nix`, which evaluates each arm in its OWN
# evaluator process. One fixture per process is load-bearing, not hygiene: the (P2) death and the
# under-forcing defect the LATEREAD answering cells exist to catch are INDISTINGUISHABLE inside
# one evaluation — both are anonymous aborts — and only process isolation keeps a death in one
# cell from being diagnosed as the other cell's defect.
#
# Wiring mirrors `bench/eval-memo.nix`: the library's own files imported directly with explicit
# dependencies. Sources arrive as ARGUMENTS rather than through `fetchTree` because the runner
# evaluates inside the build sandbox, where fetching is (correctly) impossible — and because
# `libSrc` is the runner's own seam: the `hctl2` arm evaluates the SAME fixture against a
# deliberately mis-seeded copy of `lib/`.
{
  arm,
  genPreludeSrc,
  genGraphSrc,
  libSrc,
}:
let
  prelude = import "${genPreludeSrc}/lib";
  graph = import "${genGraphSrc}/lib" { inherit prelude; };
  inherit (import "${libSrc}/require-scope.nix" { inherit prelude; }) requireScope;
  evalLib = import "${libSrc}/eval.nix" { inherit prelude requireScope graph; };
  inherit (import "${libSrc}/build-nodes.nix" { inherit prelude; }) buildRoots;
  ag = import "${libSrc}/graph.nix";
  # The declaration constructor, inlined rather than imported: `resolve.nix` is not needed for
  # anything else here, and the record shape is the (K1)-capped one the evaluator checks.
  circular =
    { carrier }:
    f: {
      kind = "circular";
      inherit carrier;
      step = f;
    };

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

  scope = buildRoots {
    parentGraph = ag.vertex "n";
    importGraph = ag.empty;
    decls.n = { };
    types = { };
  };
  run =
    attrs: target:
    (evalLib.eval {
      inherit scope;
      attributes = {
        children = _self: _id: { };
        imports = _self: _id: [ ];
      }
      // attrs;
    }).get
      "n"
      target;

  # ── A27 CELL 2 — THE ONLY CELL THAT MEASURES D ∖ N. Three members, four lines: the target
  # `t` reads `m`'s checked entry at ONE level only (its own value passes 1 exactly once), `m`
  # reads `q` only from level 3 of its own column on (its own value ≥ 2), and `q`'s step is
  # `builtins.div 1 0`. Under the natural demand `q` is unreachable and the round answers 3 —
  # measured so at `1b222fd`. Under (D3) the completion of `m`'s column walks past level 2,
  # `m`'s step reads `q`, and the answer becomes an ANONYMOUS UNCATCHABLE ABORT — the (P2) cost,
  # priced at the oracle row and pinned here TO FIRE. The cell asserts the exit and (on the
  # control) the answer, never a message: `division by zero` is not `tryEval`-catchable and
  # carries no text of ours.
  lrp2 =
    qStep:
    run {
      t = circular { carrier = num 0 5; } (
        self: _id: _prev:
        let
          tv = self.get "n" "t";
        in
        if tv == 0 then
          1
        else if tv == 1 then
          (
            let
              mv = self.get "n" "m";
            in
            if mv > 90 then 99 else 2
          )
        else if tv < 3 then
          tv + 1
        else
          3
      );
      m = circular { carrier = num 0 5; } (
        self: _id: _prev:
        let
          mv = self.get "n" "m";
        in
        if mv < 2 then mv + 1 else self.get "n" "q"
      );
      q = circular { carrier = num 0 5; } (
        _self: _id: _prev:
        qStep
      );
    } "t";

  # ── A27's UNDEMERR CONTROL, unmoved: a member the demand reaches at NO level must have its
  # STEP APPLIED AT NO LEVEL. The answer 2 at exit 0 is self-witnessing — `e`'s step errors
  # when applied — and it is the bound row's cone rule and this gate agreeing on one class:
  # the gate did not simply widen forcing.
  undemerr = run {
    t = circular { carrier = num 0 2; } (
      self: _id: _prev:
      let
        t = self.get "n" "t";
      in
      if t + 1 >= 2 then 2 else t + 1
    );
    e = circular { carrier = num 0 2; } (
      _self: _id: _prev:
      1 / 0
    );
  } "t";

  # ── THE (F1) LATENT EXPOSURE, PINNED AS A RESIDUAL (the A9-row convention: a PASSING pair,
  # never a defect cell). At a member's FIRST live transition the outer seat's clamp is built
  # from `shadow[f(m) − 1]` — below `f(m)`, outside `D`. The fixture reaches it: `m` is first
  # demanded at level 2 (`t` reads its checked entry once, from t's level-3 computation), and
  # `m` DESCENDS at its first walked transition 2 → 3, so the clamp pairs levels 1 and 2. The
  # self-read that forces the clamp's own coordinate is steered by the quotient `q`, whose
  # hybrid derivation runs against the LATER snapshot (`qsnap = p1`) — so `m` reads its own
  # entry at the hybrid and at ladder levels ≥ 3, and NEVER at levels ≤ 2: `shadow[1].m` is
  # reached by the clamp and by nothing else. Measured with a `builtins.trace` probe on the
  # level-1 entry: one firing on the descending arm, zero on the monotone twin, at answer 3 on
  # both — the trace arms are tracked here so the reachability stays a measurement.
  #
  # WHAT THE PAIR PINS AND WHAT IT DOES NOT. The div arms pin the CONSEQUENCE: a poisoned
  # below-`f(m)` entry turns the same program from answer 3 into an anonymous abort, on the
  # descent alone (the control differs in ONE table value and never dies). This is the CURRENT,
  # well-defined behaviour, deliberately pinned as a residual: whether the clamp OWES a floor at
  # `f(m)` — or the first transition owes a provisional seat — is a design question the spec
  # does not settle (its only words are "the clamp the outer seat already constructs"), and a
  # cell must not settle it silently. If a floor ever lands, the div arm's verdict flips loudly
  # and this comment is the record of what the flip means.
  # `probeAt` selects which `da` value routes `m` through the probe branch: 0 puts the probe on
  # the level-1 entry (below `f(m)` — the trace/div arms), 1 puts it on the level-2 entry (AT
  # `f(m)`, inside the domain — the `f1-within` channel control).
  f1 =
    probeAt: probe: descVal:
    run {
      da = circular { carrier = num 0 6; } (
        self: _id: _prev:
        let
          c = self.get "n" "da";
        in
        if c >= 4 then 4 else c + 1
      );
      q = circular { carrier = qnum 0 9; } (
        self: _id: _prev:
        if self.get "n" "da" >= 2 then 8 else 0
      );
      m = circular { carrier = num 0 9; } (
        self: _id: _prev:
        let
          qv = self.get "n" "q";
        in
        if qv == 8 then
          builtins.seq (self.get "n" "m") descVal
        else if self.get "n" "da" == probeAt then
          probe
        else
          5
      );
      t = circular { carrier = num 0 9; } (
        self: _id: _prev:
        let
          tv = self.get "n" "t";
        in
        if tv < 2 then
          tv + 1
        else if tv == 2 then
          (
            let
              mv = self.get "n" "m";
            in
            if mv > 90 then 99 else 3
          )
        else
          3
      );
    } "t";
in
if arm == "lrp2" then
  lrp2 (builtins.div 1 0)
else if arm == "lrp2-ctl" then
  # LATEREAD-CTL for cell 2: the same wiring with a total late step — answers 3 at both
  # revisions, so a harness that fails everything cannot masquerade as the gate. Also the
  # fixture the `hctl2` arm re-evaluates against the mis-seeded ladder.
  lrp2 7
else if arm == "undemerr" then
  undemerr
else if arm == "f1-trace" then
  f1 0 (builtins.trace "F1-PROBE" 5) 2
else if arm == "f1-trace-ctl" then
  f1 0 (builtins.trace "F1-PROBE" 5) 5
else if arm == "f1-div" then
  f1 0 (1 / 0) 2
else if arm == "f1-div-ctl" then
  f1 0 (1 / 0) 5
else if arm == "f1-within" then
  # The trace-channel positive control: the same fixture with the probe moved to the level-2
  # entry — AT `f(m)`, inside the domain, demanded by the walked program itself — so the
  # F1-PROBE channel is proven live in the same runner run whatever the trace arms read. Exactly
  # one firing, invariant across the clamp floor (the floor withdraws only below-domain reads).
  f1 1 (builtins.trace "F1-PROBE" 5) 2
else
  throw "tests-process-cells: unknown arm '${arm}'"
