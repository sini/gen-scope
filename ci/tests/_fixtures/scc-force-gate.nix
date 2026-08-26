# THE FORCE GATE'S NON-TARGET FIXTURE — the A26 family: a member OTHER than the demanded target,
# descending on its own trajectory, refused BY NAME.
#
# Under `/_` like the corpus, so the tree importer never reaches it; the value cell lives in
# `../scc-round.nix` and the two refusal cells in `../../tests-error.nix`.
#
# THE FIXTURE IS MULTI-NODE ON PURPOSE. The `!ascends` refusal names the refusing instance by its
# NODE id, so a single-node program — the corpus's encoding — cannot exhibit WHICH member a
# refusal blames: every message would say `'n'`. One circular attribute `x` over three nodes,
# its step dispatching on the node id, puts each member on its own name:
#
#   drv.x  the ascending driver, 0 → 1 → 2 → 3 → 4;
#   dsc.x  driven by drv: 3, 3, then 1 — a DESCENT on its own trajectory at the 2 → 3 transition;
#   tgt.x  RATCHETS — 0, 0, 1, 1, … — so its own seat can never fire, and it reads dsc while
#          still at 0, which is what puts dsc's checked entry in the demand.
#
# Hand-derived before any arm ran: the demand at `tgt` answers 1 wherever no seat rides dsc's
# column (measured at `1b222fd`: EXIT 0, value 1, stderr empty — the shipped defect the oracle
# row records), and under the per-member seats dsc's walk sees 3 → 1, constructs the clamp, and
# the step at the clamped pair still descends — refused naming 'dsc', never 'tgt'. The monotone
# twin (0, 0, 1, 3) answers the SAME value 1, which is the oracle's own point: a value assertion
# cannot separate the two standings, so the cell asserts the MESSAGE.
{ genScope }:
let
  num = bottom: height: {
    inherit bottom height;
    leq = a: b: a <= b;
    quotient = false;
  };
  inherit (genScope) circular;

  scope = genScope.buildRoots {
    parentGraph = genScope.vertices [
      "drv"
      "dsc"
      "tgt"
    ];
    importGraph = genScope.empty;
    decls = {
      drv = { };
      dsc = { };
      tgt = { };
    };
    types = { };
  };

  run =
    dscTable: target:
    (genScope.eval {
      inherit scope;
      attributes = {
        children = _self: _id: { };
        imports = _self: _id: [ ];
        x = circular { carrier = num 0 4; } (
          self: id: _prev:
          if id == "drv" then
            (
              let
                c = self.get "drv" "x";
              in
              if c >= 4 then 4 else c + 1
            )
          else if id == "dsc" then
            dscTable (self.get "drv" "x")
          else
            (
              let
                t = self.get "tgt" "x";
              in
              if t >= 1 then 1 else (if self.get "dsc" "x" >= 3 then 1 else 0)
            )
        );
      };
    }).get
      target
      "x";

  descending = c: if c <= 1 then 3 else 1;
  monotone = c: if c <= 1 then 0 else (if c == 2 then 1 else 3);
in
{
  # The defect cell's shape: the demand at the ratcheting target, the non-target descending.
  refused = run descending "tgt";
  # Control (i): the member MONOTONE — answers, and answers the same 1.
  monotoneAnswers = run monotone "tgt";
  # Control (ii): the same program DEMANDED AT the descending member — refuses on a
  # target-column-scoped build too, so a harness that lost the seat outright cannot pass as
  # the capability.
  refusedAtMember = run descending "dsc";
}
