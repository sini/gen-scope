# THE FIRST-TRANSITION FIXTURES — the outer seat's clamp at a walk's FIRST live transition, and
# the height seat's unobserved-prefix scope at `f(m) > 1`. Shared between the value suite
# (`../scc-round.nix`) and the refusal suite (`../../tests-error.nix`) so the lie a refusal is
# earned on and the lie the round answers are one value rather than two kept equal by hand.
#
# NOT CORPUS PORTS. Provenance is the clamp-floor spec (den-ag-design
# `specs/2026-08-26-gen-scope-f1-clamp-floor-spec.md` §3), whose expectations were hand-derived
# before any cell ran. The same lane's per-process halves (the `f1-*` arms) live in
# `../../tests-process-cells.nix` — their verdicts are trace counts and uncatchable aborts, which
# no suite cell can read.
{ genScope }:
let
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
  inherit (import ./scc-corpus.nix { inherit genScope; }) run;

  # A height lie living WHOLLY INSIDE THE UNOBSERVED PREFIX, parameterized by where the target
  # first reads the lying member. `x` declares height 1 and ascends 0→1→2→3 — a run of 3 — but
  # every strict ascent sits at a transition strictly below `f(x)` when the read comes late.
  p1lieAt =
    readAt:
    run {
      da = circular { carrier = num 0 6; } (
        self: _id: _prev:
        let
          c = self.get "n" "da";
        in
        if c >= 4 then 4 else c + 1
      );
      x = circular { carrier = num 0 1; } (
        self: _id: _prev:
        let
          c = self.get "n" "da";
        in
        if c > 3 then 3 else c
      );
      t = circular { carrier = num 0 6; } (
        self: _id: _prev:
        let
          tv = self.get "n" "t";
        in
        if tv < readAt then
          tv + 1
        else if tv == readAt then
          (
            let
              xv = self.get "n" "x";
            in
            if xv > 90 then 99 else readAt + 1
          )
        else
          readAt + 1
      );
    } "t";
in
{
  # `t` reads `x` from its level-5 computation ⇒ `f(x) = 4`; `x`'s three strict ascents sit at
  # transitions (1→2)(2→3)(3→4), every one strictly below the walk's first comparison (4→5). The
  # walk seeds its run counter at `j0 = 4`, every observed transition is quiet, no descent, no
  # clamp — the program answers 5.
  p1lie = p1lieAt 4;

  # The positive control on the same predicate: the same lie READ EARLY (`f(x) = 1`), so the walk
  # from 0 counts the ascents and `runs = 2 > height 1` refuses the declaration by name.
  p1lieCtl = p1lieAt 1;

  # The per-process `f1` wiring with the lie branch descending TWICE: `m`'s ladder runs
  # … 5, 3, 1, 1 … — a descent at the walk's first transition (2 → 3) AND at (3 → 4). At (3 → 4)
  # the outer seat's clamp is in-domain (`p2 = shadow[2]`, `p1 = shadow[3]`): the re-applied step
  # returns 3, `leq 3 1` fails, and the step is refused by name at iteration 3 — a persistently
  # non-monotone member never survives on the first transition's seat alone.
  desc2 = run {
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
        builtins.seq (self.get "n" "m") (if self.get "n" "da" >= 3 then 1 else 3)
      else if self.get "n" "da" == 0 then
        builtins.trace "F1-PROBE" 5
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
}
