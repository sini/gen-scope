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
  graph ? import "${fetch "gen-graph"}/lib" { inherit prelude; },
  schema ? import "${fetch "gen-schema"}/lib" {
    inherit prelude;
    merge = import "${fetch "gen-merge"}/lib" { inherit prelude; };
    algebra = import "${fetch "gen-algebra"}/lib";
  },
  ...
}:
import ./lib { inherit prelude graph schema; }
