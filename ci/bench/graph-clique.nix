# `clique` COSTS ITS OUTPUT — the complexity arms, read by `graph-clique.sh`.
#
# WHY THIS CANNOT BE A SUITE CELL. The oracle is a COMPLEXITY CLASS, and a class is observable only
# across a sweep of sizes: no single evaluation of any size can exhibit it. `ci/tests/graph.nix`'s
# `test-clique` pins this constructor's DENOTATION and read 893/893 over the cubic — a denotation
# oracle cannot see cost. The two are a conjunction and neither half is redundant.
#
# ★ AND THE DENOTATION HALF DID NOT EXIST UNTIL THIS BENCH WAS WRITTEN, which is worth recording
# because it is what a cost repair is exposed to: `clique` had NO cell anywhere in the 893, so a
# seeded direction swap in the replacement body left the suite green at 893/893 while the digest
# comparison below refused it. `test-clique` and `test-clique-empty` were added with the repair.
#
# ★ THE OUTPUT IS QUADRATIC AND THAT IS NOT THE DEFECT. A clique on n vertices HAS n(n-1)/2 edges,
# so the budget here is 2.05 per doubling, not the 1.05 `graph-overlays.sh` holds `overlays` to.
# What was cubic is the ACCUMULATOR: `foldl' connect empty` re-copied the edge list built so far at
# every one of the n steps, paying Theta(n^3) to emit Theta(n^2). A remedy that made this arm fast
# by emitting FEWER edges is a regression, not a repair, which is why the driver refuses on the
# graph's two sizes before it reads a single cost figure.
#
#   arm "clique"         — the shipped constructor. This is the arm the budget refuses on.
#   arm "linear-control" — the LIVE CONTROL: the same graph value built by a local index pass that
#                          does not reach `lib/graph.nix` at all. The arms differ in exactly one
#                          term, so their costs are comparable and their values must be equal. A run
#                          in which the INSTRUMENT is broken — a dropped size, a stats table written
#                          over an evaluation that never applied the fixture — moves BOTH arms
#                          together, and the driver's identical-cell refusal sees it.
#   arm "fold-defect"    — THE PRIOR FORM, kept so this bench can never read green off an
#                          instrument that stopped discriminating. It is held to the OPPOSITE
#                          assertion: it must EXCEED the budget in the same run in which the shipped
#                          arm clears it. Its denotation is compared to the other two, so it doubles
#                          as the equivalence proof for the rewrite that replaced it.
#
# ★ USE `nix-instantiate --arg`, NEVER `nix eval --file`. `nix eval --file f.nix --arg n 7` SILENTLY
# DROPS the argument and exits 0 with a lambda, and `NIX_SHOW_STATS` still writes a full table for
# the unapplied expression. The stats file cannot tell you the size you asked for was ignored.
{
  arm ? "clique",
  n ? 200,
}:
let
  ag = import ../../lib/graph.nix;

  ids = builtins.genList (i: "n${toString i}") n;

  graph =
    if arm == "clique" then
      ag.clique ids
    else if arm == "linear-control" then
      {
        vertices = ids;
        edges = builtins.concatMap (
          j:
          builtins.genList (i: {
            from = builtins.elemAt ids i;
            to = builtins.elemAt ids j;
          }) j
        ) (builtins.genList (j: j) n);
      }
    else if arm == "fold-defect" then
      builtins.foldl' ag.connect ag.empty (map ag.vertex ids)
    else
      throw "graph-clique: unknown arm '${arm}'";

  nv = builtins.length graph.vertices;
  ne = builtins.length graph.edges;
  at = xs: i: builtins.elemAt xs i;
  e = i: "${(at graph.edges i).from}->${(at graph.edges i).to}";
in
# Forcing both lists end to end is the point: `++` allocates when forced, so a digest that only
# reached the head would leave the accumulator's copies unbuilt and every cell would read the
# evaluator's own baseline.
"nv=${toString nv} ne=${toString ne} v0=${at graph.vertices 0} vlast=${at graph.vertices (nv - 1)} e0=${e 0} elast=${e (ne - 1)}"
