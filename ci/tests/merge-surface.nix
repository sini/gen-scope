# The assembly's refusing merge, exercised over module sets this file builds.
#
# The library's own assembly is asserted by every other cell in this suite — nothing here evaluates
# unless the fold over the real modules produced a surface. What those cells cannot show is the
# REFUSAL, because the real set has no duplicate to refuse: a merge that has never been seen to
# refuse is a `//` with extra steps. So the arming runs over synthetic modules, where a duplicate is
# something this file can put there.
#
# The refusal's MESSAGE is asserted in `ci/tests-error.nix`, where `tryEval`'s discarded text has an
# instrument.
{ genPreludeLib, ... }:
let
  mergeSurface = import ../../lib/merge-surface.nix { prelude = genPreludeLib; };

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
  };
}
