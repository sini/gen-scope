# `overlays` IS LINEAR IN ITS SEGMENTS — the complexity arms, read by `graph-overlays.sh`.
#
# WHY THIS CANNOT BE A SUITE CELL. The oracle is a COMPLEXITY CLASS, and a class is observable only
# across a sweep of sizes: no single evaluation of any size can exhibit it. The suite already pins
# this constructor's DENOTATION (`ci/tests/graph.nix`'s `test-overlays`, and `ci/tests/vertex-order.nix`
# in full) and it read 864/864 over the quadratic — a denotation oracle cannot see cost. The two are a
# conjunction and neither half is redundant.
#
#   arm "overlays"       — the shipped constructor on the REALISTIC CALLER PATH: one `overlays` over
#                          three n-long segments, the shape `examples/*/graph.nix` and `ci/tests/*.nix`
#                          actually write. This is the arm the budget refuses on.
#   arm "linear-control" — the LIVE CONTROL: the same three segments combined by a local
#                          `builtins.concatMap` that does not call `overlays` at all. The arms differ
#                          in exactly one term — the combiner — which is the substitution under test,
#                          so their costs are comparable and their values must be equal. A run in
#                          which the INSTRUMENT is broken — a dropped size, a stats table written over
#                          an evaluation that never applied the fixture — moves BOTH arms together,
#                          and the driver's identical-cell refusal sees it; a table carrying only the
#                          shipped arm would read clean off exactly that failure.
#
# ★ THE CONTROL IS NOT A FOLD. Everywhere else in this repair "fold" denotes the defect, and an arm
# written `builtins.foldl' overlay empty gs` measures exponent 2.00 — it would red this bench against
# a CORRECT build, permanently. What the control must be is linear on a correct build, which the
# one-pass form is by construction.
#
# ★ DEEP SHAPES ARE AN EXCLUDED AXIS, named rather than guarded. `tree` RECURSES through `overlays`
# and re-concatenates the subtree's vertex list once per level; that Theta(depth^2) lives in `tree`'s
# recursion, not in the accumulator this bench guards, and a depth arm would therefore read 2.00 on a
# correct build. This fixture is WIDE on purpose.
#
# EVERY ARM RETURNS THE SAME DENOTATION DIGEST, and the driver compares the arms at each size. The
# digest is order-sensitive on both ends of both lists, so a rewrite that keeps the node set and
# reverses the sequence is caught here as well as by the suite.
{
  arm ? "overlays",
  n ? 1000,
}:
let
  ag = import ../../lib/graph.nix;

  ids = builtins.genList (i: "n${toString i}") n;
  pairs = builtins.genList (i: {
    from = "n${toString i}";
    to = "n${toString (i + 1)}";
  }) n;

  # The three segments, as the shipped derived constructors build them.
  shippedSegments = [
    (ag.vertices ids)
    (ag.star "root" ids)
    (ag.edges pairs)
  ];

  graph =
    if arm == "overlays" then
      ag.overlays shippedSegments
    else if arm == "linear-control" then
      {
        vertices = builtins.concatMap (g: g.vertices) shippedSegments;
        edges = builtins.concatMap (g: g.edges) shippedSegments;
      }
    else
      throw "graph-overlays: unknown arm '${arm}'";

  nv = builtins.length graph.vertices;
  ne = builtins.length graph.edges;
  at = xs: i: builtins.elemAt xs i;
  e = i: "${(at graph.edges i).from}->${(at graph.edges i).to}";
in
# Forcing both lists end to end is the point: `++` allocates when forced, so a digest that only
# reached the head would leave the accumulator's copies unbuilt and every cell would read the
# evaluator's own baseline.
"nv=${toString nv} ne=${toString ne} v0=${at graph.vertices 0} vlast=${at graph.vertices (nv - 1)} e0=${e 0} elast=${e (ne - 1)}"
