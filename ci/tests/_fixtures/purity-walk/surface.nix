# NOT A SUITE and NOT library source. It sits under `_fixtures/` because the tree importer
# ignores any path containing that segment, and it sits at the surface of this fixture tree so
# the purity walk is held to returning both depths rather than only the nested one.
#
# The tether below is planted. The scan reads text and never evaluates this file, so the free
# `mkOption` is deliberate — changing it changes what the walk cell expects.
{
  tethered = mkOption { };
}
