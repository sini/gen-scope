# NOT A SUITE and NOT library source. It sits under `_fixtures/` because the tree importer
# ignores any path containing that segment, and one directory down because that is the point:
# the purity walk must descend to reach it, and a flat listing never would.
#
# The tether below is planted. The scan reads text and never evaluates this file, so the free
# `lib` is deliberate — changing it changes what the walk cell expects.
{
  tethered = lib.types.str;
}
