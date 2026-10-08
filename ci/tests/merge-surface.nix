# The refusing merge: over the library's real module record, and over module sets this file builds.
#
# `lib/default.nix` publishes a literal of `inherit (modules.<m>)` clauses, lazy per name, so the
# fold no longer runs at load (den-hoag-9lg69). It runs here instead, over the same record
# `lib/modules.nix` returns, and the literal is held equal to what the fold produces, name for name.
# Totality over the module set is kept: the fold reads every module, whoever authored it. What
# moved is when it is checked, and no caller input reaches it (the formals cell below).
#
# What the real record cannot show is the REFUSAL, because it has no duplicate to refuse: a merge
# that has never been seen to refuse is a `//` with extra steps. So the arming runs over synthetic
# modules, where a duplicate is something this file can put there.
#
# The refusal's MESSAGE is asserted in `ci/tests-error.nix`, where `tryEval`'s discarded text has an
# instrument.
{
  genPreludeLib,
  genGraph,
  genIdentity,
  genAlgebra,
  genScope,
  ...
}:
let
  mergeSurface = import ../../lib/merge-surface.nix { prelude = genPreludeLib; };

  args = {
    prelude = genPreludeLib;
    graph = genGraph;
    identity = genIdentity;
    algebra = genAlgebra;
  };
  modules = import ../../lib/modules.nix args;
  namesOf = builtins.mapAttrs (_: builtins.attrNames);
  folded = mergeSurface modules;
  published = builtins.attrNames genScope;
  missing = builtins.filter (n: !(genScope ? ${n})) (builtins.attrNames folded);
  extra = builtins.filter (n: !(folded ? ${n})) published;
  # Every published name forced: a name listed under a module that lacks it aborts here, naming it.
  forced = builtins.foldl' (
    a: n: builtins.seq (builtins.tryEval genScope.${n}).success a
  ) null published;
  # The fold runs first, so a name two modules export is refused by its own message, naming both.
  completeness = builtins.seq (builtins.attrNames folded) (
    builtins.seq forced (
      if missing != [ ] || extra != [ ] then
        throw "gen-scope surface: the literal surface and the module record disagree: missing ${builtins.toJSON missing}, extra ${builtins.toJSON extra}"
      else
        "complete: ${toString (builtins.length published)} names"
    )
  );
  poison = n: throw "gen-scope surface: a name set read `${n}`";

  distinct = {
    alpha = {
      one = 1;
      two = 2;
    };
    beta = {
      three = 3;
    };
  };
  # The same two modules, with `beta` re-exporting a name `alpha` already contributed.
  colliding = distinct // {
    beta = {
      one = 99;
      three = 3;
    };
  };
in
{
  flake.tests.merge-surface = {
    test-modules-with-no-shared-name-merge-to-their-union = {
      expr = builtins.attrNames (mergeSurface distinct);
      expected = [
        "one"
        "three"
        "two"
      ];
    };
    # The values arrive intact, so the fold is a merge and not just a name check.
    test-the-merged-surface-carries-the-modules-values = {
      expr = (mergeSurface distinct).two;
      expected = 2;
    };
    # ARMED: a name contributed twice is refused rather than resolved by position. Under a `//`
    # chain this same set merges silently, and `one` would be whichever module the writer put last.
    test-a-name-contributed-twice-is-refused = {
      expr = (builtins.tryEval (builtins.attrNames (mergeSurface colliding))).success;
      expected = false;
    };
    # The control beside it: the identical expression over the set without the duplicate. Without it
    # the cell above passes against a fold that refuses everything.
    test-control-the-same-modules-without-the-duplicate-are-not-refused = {
      expr = (builtins.tryEval (builtins.attrNames (mergeSurface distinct))).success;
      expected = true;
    };

    test-the-literal-surface-is-the-refusing-fold = {
      expr = completeness;
      expected = "complete: 101 names";
    };

    # No caller input reaches the fold above: every module's name set is the same with the three
    # library formals bound to throws, so a duplicate can enter only through a gen-scope commit. A
    # module that computed its names from `graph`, `identity` or `algebra` would red this cell.
    test-module-name-sets-read-no-library-formal = {
      expr =
        namesOf (
          import ../../lib/modules.nix {
            prelude = genPreludeLib;
            graph = poison "graph";
            identity = poison "identity";
            algebra = poison "algebra";
          }
        ) == namesOf modules;
      expected = true;
    };
  };
}
