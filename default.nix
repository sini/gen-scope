# Standalone (non-flake) entry. Flake consumers should use the `.lib` output.
#
# gen-scope is nixpkgs-lib-free: this shim derives its three inputs from the pinned flake.lock
# (content-addressed via narHash, so it stays pure) and needs no `<nixpkgs>`. Pass `prelude`, `graph`
# or `schema` to override.
#
# The derived `graph` and `schema` are built on the SAME prelude this shim derives, rather than on the
# ones pinned inside those libraries' own locks. That is the shim's simplification and it is stated:
# the flake path above is where each library resolves its own pin, and this entry exists for a
# consumer who has no flake to do that with. For `schema` the simplification is inert where it
# matters — the identity authority and its closure are `builtins`-only, so no prelude of any revision
# reaches the identity formula.
#
# ★ EACH DEPENDENCY IS CONSTRUCTED THROUGH ITS OWN STANDALONE ENTRY, NEVER THROUGH ITS BARE `./lib`.
# Reaching past the entry obliges this file to name the dependency's whole formal list by hand, which
# is a SECOND SIGNATURE that nothing compares against the first: every formal that library gains or
# retires has to be re-tracked here, and when it drifts only the standalone path breaks while CI —
# which exercises the flake path — stays green. Measured both ways: the
# `/lib` form for `schema` passed an `identity` the pinned gen-schema does not take, and the `/lib`
# form one repository over omitted an `identity` that gen-types does. Through the entry, what a
# dependency needs is defaulted by that dependency from its own lock and the divergence cannot form —
# which is also why `merge` and `algebra` are no longer named here at all.
let
  lock = builtins.fromJSON (builtins.readFile ./flake.lock);
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
in
{
  prelude ? import "${fetch "gen-prelude"}/lib",
  graph ? import "${fetch "gen-graph"}" { inherit prelude; },
  # The one minting authority: a dependency-free leaf, so its lib is a bare value and this
  # takes no argument. Derived from THIS shim's lock so the whole construction mints through one
  # encoding — two instances would be two content-address formulas for one node. It is passed to
  # `./lib` and NOT to `schema`: the flake path binds `schema` from gen-schema's own output, which
  # at the pinned rev takes no identity, so naming one here is the standalone path claiming a
  # coupling the tested path does not have.
  identity ? import "${fetch "gen-identity"}/lib",
  schema ? import "${fetch "gen-schema"}" { inherit prelude; },
  ...
}:
import ./lib {
  inherit
    prelude
    graph
    schema
    identity
    ;
}
