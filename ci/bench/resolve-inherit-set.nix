# `inheritSet` ALLOCATES ITS OUTPUT — the complexity arms, read by `resolve-inherit-set.sh`.
#
# WHY THIS CANNOT BE A SUITE CELL. The oracle is a COMPLEXITY CLASS, and a class is observable only
# across a sweep of sizes: no single evaluation of any size can exhibit it. The suite already pins
# this constructor's DENOTATION (`ci/tests/resolve.nix`'s seven `test-inheritSet-*` cells, the
# custom `eq` among them) and it read 893/893 over the quadratic — a denotation oracle cannot see
# cost. Six of the seven fire on an inverted dedup; `test-inheritSet-empty` is the one that does
# not, which is why the length assertion below is a closed form rather than a non-emptiness test.
#
# ★ THE FIXTURE IS WIDE ON PURPOSE, AND THE DEPTH AXIS IS EXCLUDED RATHER THAN GUARDED. `inheritAll`
# — which this constructor delegates its parent walk to — concatenates its accumulated result at
# every level of the chain and copies `_visited` beside it, so a DEEP fixture measures THAT and
# reads super-linear against a correct build of this one. The chain here is three nodes and the
# contribution per node is what grows, so the size swept is the length of the list handed to the
# dedup and nothing else. `inheritAll`'s own depth term is a separate site and is not addressed
# here.
#
# ★ EVERY VALUE IS DISTINCT, which is the dedup's worst case and the only case whose output size is
# a closed form: 3n in, 3n out. A fixture with collisions would let an arm look cheap by keeping
# fewer elements, and the driver could not tell that from a repair.
#
#   arm "inheritSet"     — the shipped constructor, read through `eval` the way a caller reads it.
#                          This is the arm the budget refuses on.
#   arm "linear-control" — the LIVE CONTROL: the same dedup over the same `inheritAll` result,
#                          computed by a local index pass that does not call `inheritSet`. The arms
#                          differ in exactly one term — the dedup — so their costs are comparable
#                          and their values must be equal. An instrument failure moves BOTH arms
#                          together and the driver's identical-cell refusal sees it.
#   arm "fold-defect"    — THE PRIOR FORM, `foldl' (acc: x: … acc ++ [ x ]) [ ]`, kept so this bench
#                          can never read green off an instrument that stopped discriminating. It is
#                          held to the OPPOSITE assertion: it must EXCEED the budget in the same run
#                          the shipped arm clears it. Its digest is compared to the other arms', so
#                          it is also the equivalence proof for the rewrite that replaced it.
#
# ★ THE COMPARISON AXIS IS REPORTED AND NOT BUDGETED, and that is a statement about the CONTRACT
# rather than a gap in the guard. `eq` is a caller-supplied predicate with no key to index by, so
# the pairwise scan is the specified semantics — the same way a clique's n(n-1)/2 edges are
# `clique`'s. What was removable is the ACCUMULATOR, and `list.elements` is where it lived. Printing
# `nrFunctionCalls` beside it is what stops a reader mistaking a linear allocation row for a linear
# constructor.
#
# ★ USE `nix-instantiate --arg`, NEVER `nix eval --file`. `nix eval --file f.nix --arg n 7` SILENTLY
# DROPS the argument and exits 0 with a lambda, and `NIX_SHOW_STATS` still writes a full table for
# the unapplied expression. The stats file cannot tell you the size you asked for was ignored.
{
  arm ? "inheritSet",
  n ? 500,
}:
let
  lock = builtins.fromJSON (builtins.readFile ../../flake.lock);
  fetch =
    name:
    let
      node = lock.nodes.${name}.locked;
    in
    builtins.fetchTree {
      inherit (node)
        type
        owner
        repo
        rev
        narHash
        ;
    };
  prelude = import "${fetch "gen-prelude"}/lib";
  # Through gen-graph's own standalone entry, never its bare `./lib`: the root shim's rule, so a
  # formal gained downstream is defaulted downstream instead of re-tracked here by hand.
  graph = import "${fetch "gen-graph"}" { inherit prelude; };
  # The registry discriminator ships with `mkKinds`; the two guards below take it as a formal.
  inherit (import ../../lib/cascade.nix { inherit prelude graph; }) isKindSet;
  inherit (import ../../lib/require-scope.nix { inherit prelude isKindSet; }) requireScope;
  inherit (import ../../lib/require-declared-dependencies.nix { inherit graph; })
    requireDeclaredDependencies
    ;
  evalLib = import ../../lib/eval.nix {
    inherit
      prelude
      requireScope
      requireDeclaredDependencies
      graph
      ;
  };
  inherit (import ../../lib/build-nodes.nix { inherit prelude isKindSet; }) buildRoots;
  resolveLib = import ../../lib/resolve.nix { inherit prelude; };
  ag = import ../../lib/graph.nix;

  # Three nodes, one chain, n distinct contributions each. Parent edges point child -> parent.
  chain = [
    "leaf"
    "mid"
    "root"
  ];
  supp = who: builtins.genList (i: "${who}-${toString i}") n;
  scope = buildRoots {
    parentGraph = ag.overlays [
      (ag.edge "leaf" "mid")
      (ag.edge "mid" "root")
    ];
    importGraph = ag.empty;
    decls = builtins.listToAttrs (
      map (who: {
        name = who;
        value.supp = supp who;
      }) chain
    );
    types = { };
  };

  extract = node: node.decls.supp or null;
  eq = a: b: a == b;

  # The three dedups. Only this binding differs between the arms; `inheritAll` is reached the same
  # way by all three, so the walk is a shared constant rather than a term under test.
  dedup =
    if arm == "inheritSet" then
      resolveLib.inheritSet { inherit extract eq; }
    else if arm == "linear-control" then
      (
        self: id:
        let
          all = resolveLib.inheritAll { inherit extract; } self id;
          idx = builtins.genList (i: i) (builtins.length all);
        in
        builtins.concatMap (
          i:
          let
            x = builtins.elemAt all i;
          in
          if builtins.any (j: j < i && eq (builtins.elemAt all j) x) idx then [ ] else [ x ]
        ) idx
      )
    else if arm == "fold-defect" then
      (
        self: id:
        let
          all = resolveLib.inheritAll { inherit extract; } self id;
        in
        builtins.foldl' (acc: x: if builtins.any (y: eq y x) acc then acc else acc ++ [ x ]) [ ] all
      )
    else
      throw "resolve-inherit-set: unknown arm '${arm}'";

  result = evalLib.eval {
    inherit scope;
    attributes = {
      children = _self: i: prelude.filterAttrs (_: node: node.parent == i) scope.nodes;
      imports = _self: _i: [ ];
      supp-set = dedup;
    };
    parseParent = i: (scope.nodes.${i} or { parent = null; }).parent;
  };
  out = result.get "leaf" "supp-set";
  nd = builtins.length out;
in
# Forcing the list end to end is the point: `++` allocates when forced, so a digest that only
# reached the head would leave the accumulator's copies unbuilt and every cell would read the
# evaluator's own baseline.
"nd=${toString nd} d0=${builtins.elemAt out 0} dlast=${builtins.elemAt out (nd - 1)}"
