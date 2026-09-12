# `collectionAttr` AND `inheritAll` ALLOCATE THEIR OUTPUT — the complexity arms, read by
# `resolve-folds.sh`.
#
# Two constructors, one bench, because they are one defect and one oracle: both folded a
# caller-supplied `combine` whose DEFAULT was `a: b: a ++ b`, so both re-copied their accumulated
# list once per step to emit a list that is linear in the size swept. Both fixtures are built so the
# gathered length is exactly n, which makes one size invariant serve every arm.
#
# WHY THIS CANNOT BE A SUITE CELL. The oracle is a COMPLEXITY CLASS, and a class is observable only
# across a sweep of sizes: no single evaluation of any size can exhibit it. The suite pins both
# constructors' DENOTATION — `ci/tests/collection-attr.nix`, and `ci/tests/resolve.nix`'s
# `test-inheritAll-accumulates` — and read 895/895 over both quadratics, because a denotation oracle
# cannot see cost.
#
# ★ AND THE SUPPLIED-`combine` ARM WAS PINNED BY NOTHING AT ALL until this repair, in either
# constructor: `combine` appeared in six `ci/tests` files and in none of them as an argument to
# these two. Three cells shipped with the repair —
# `test-inheritAll-supplied-combine-folds-right`, `test-inheritAll-cycle-repeats-its-entry-once`,
# `test-traverse-children-supplied-combine-folds-left` — because the repair moved the default to a
# `null` sentinel and replaced `inheritAll`'s fold and its cycle guard outright.
#
#   arm "collect"        — `collectionAttr` over n children with NO `combine` supplied, which is the
#                          shape `ci/tests/collection-attr.nix` and every in-repo caller writes.
#   arm "collect-defect" — THE PRIOR DEFAULT, reached through the PUBLIC SURFACE by supplying
#                          `combine = a: b: a ++ b` explicitly. It is not a local re-implementation:
#                          it is the same entry point taking the same fold it always took, so this
#                          arm doubles as the proof that a caller-supplied `combine` still folds.
#   arm "inherit"        — `inheritAll` up a chain of depth n with NO `combine` supplied.
#   arm "inherit-defect" — THE PRIOR IMPLEMENTATION, written out locally: the level-at-a-time
#                          recursion carrying a `_visited` attrset rebuilt with `//`. This one HAS
#                          to be local, because the repair replaced the guard as well as the
#                          accumulator — supplying a `combine` to the shipped constructor exercises
#                          the new linear chain walk and would understate the prior cost on the
#                          update axis.
#
# ★ EVERY ARM'S DIGEST IS COMPARED TO ITS FAMILY'S SHIPPED ARM at every size, ends included. The
# defect arms are the prior semantics, so that comparison is the equivalence proof for both
# rewrites rather than a second opinion about them.
#
# ★ TWO AXES, AND THE SECOND ONE ONLY MOVES FOR `inheritAll`. `list.elements` carries the `++`
# accumulator for both constructors; `nrOpUpdateValuesCopied` carries `inheritAll`'s `_visited //`
# guard, which `collectionAttr` never had. A one-axis version of this bench certifies half of the
# `inheritAll` repair.
#
# ★ USE `nix-instantiate --arg`, NEVER `nix eval --file`. `nix eval --file f.nix --arg n 7` SILENTLY
# DROPS the argument and exits 0 with a lambda, and `NIX_SHOW_STATS` still writes a full table for
# the unapplied expression. The stats file cannot tell you the size you asked for was ignored.
{
  arm ? "collect",
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
  inherit (import ../../lib/require-scope.nix { inherit prelude; }) requireScope;
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
  resolveLib = import ../../lib/resolve.nix { inherit prelude; };

  range = builtins.genList (i: i) n;
  # The two constructors take DIFFERENT extract signatures — `inheritAll` is handed the node record,
  # `collectionAttr` is handed the evaluator and an id — so the fixture carries one of each rather
  # than pretending they share a contract.
  extract = node: node.decls.supp or null;
  extractAt = self: i: (self.node i).decls.supp or [ ];

  # ── THE PRIOR `inheritAll`, verbatim ──
  # The level-at-a-time recursion with the `_visited` attrset rebuilt by `//` at every step, and the
  # accumulated result re-concatenated beside it.
  inheritAllPrior =
    {
      extract,
      combine ? a: b: a ++ b,
      _visited ? { },
    }:
    self: id:
    let
      node = self.node id;
      local = extract node;
      localResults = if local != null then (if builtins.isList local then local else [ local ]) else [ ];
    in
    if _visited ? ${id} then
      localResults
    else if node.parent == null then
      localResults
    else
      let
        parentResults = inheritAllPrior {
          inherit extract combine;
          _visited = _visited // {
            ${id} = true;
          };
        } self node.parent;
      in
      combine localResults parentResults;

  # ── FIXTURE A: one root, n children, one contribution each ⇒ gathered length n ──
  kids = builtins.listToAttrs (
    map (i: {
      name = "c${toString i}";
      value = {
        id = "c${toString i}";
        type = null;
        parent = "root";
        decls.supp = [ "c${toString i}" ];
      };
    }) range
  );
  wideScope = {
    nodes = kids // {
      root = {
        id = "root";
        type = null;
        parent = null;
        decls = { };
      };
    };
    nodeOrder = [ "root" ] ++ map (i: "c${toString i}") range;
    kinds = null;
  };

  # ── FIXTURE B: a chain of depth n, one contribution each ⇒ gathered length n ──
  chainNodes = builtins.listToAttrs (
    map (i: {
      name = "n${toString i}";
      value = {
        id = "n${toString i}";
        type = null;
        parent = if i + 1 < n then "n${toString (i + 1)}" else null;
        decls.supp = [ "n${toString i}" ];
      };
    }) range
  );
  deepScope = {
    nodes = chainNodes;
    nodeOrder = map (i: "n${toString i}") range;
    kinds = null;
  };

  run =
    scope: attr: readId:
    (evalLib.eval {
      inherit scope;
      attributes = {
        children = _self: i: prelude.filterAttrs (_: node: node.parent == i) scope.nodes;
        imports = _self: _i: [ ];
        gathered = attr;
      };
      parseParent = i: (scope.nodes.${i} or { parent = null; }).parent;
    }).get
      readId
      "gathered";

  out =
    if arm == "collect" then
      run wideScope (resolveLib.collectionAttr {
        traverse = "children";
        extract = extractAt;
      }) "root"
    else if arm == "collect-defect" then
      run wideScope (resolveLib.collectionAttr {
        traverse = "children";
        extract = extractAt;
        combine = a: b: a ++ b;
      }) "root"
    else if arm == "inherit" then
      run deepScope (resolveLib.inheritAll { inherit extract; }) "n0"
    else if arm == "inherit-defect" then
      run deepScope (inheritAllPrior { inherit extract; }) "n0"
    else
      throw "resolve-folds: unknown arm '${arm}'";

  len = builtins.length out;
in
# Forcing the list end to end is the point: `++` allocates when forced, so a digest that only
# reached the head would leave the accumulator's copies unbuilt and every cell would read the
# evaluator's own baseline.
"len=${toString len} first=${builtins.elemAt out 0} last=${builtins.elemAt out (len - 1)}"
