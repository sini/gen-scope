# Standalone (non-flake) entry. Flake consumers should use the `.lib` output.
#
# gen-scope is nixpkgs-lib-free: this shim derives its two inputs from the pinned flake.lock
# (content-addressed via narHash, so it stays pure) and needs no `<nixpkgs>`. Pass `prelude` or
# `graph` to override.
#
# The derived `graph` is built on the SAME prelude this shim derives, rather than on the one
# pinned inside the graph library's own lock. That is the shim's simplification and it is stated:
# the flake path above is where each library resolves its own pin, and this entry exists for a
# consumer who has no flake to do that with.
{
  prelude ? (
    let
      lock = builtins.fromJSON (builtins.readFile ./flake.lock);
      node = lock.nodes.gen-prelude.locked;
    in
    import "${
      builtins.fetchTree {
        inherit (node)
          type
          owner
          repo
          rev
          narHash
          ;
      }
    }/lib"
  ),
  graph ? (
    let
      lock = builtins.fromJSON (builtins.readFile ./flake.lock);
      node = lock.nodes.gen-graph.locked;
    in
    import "${
      builtins.fetchTree {
        inherit (node)
          type
          owner
          repo
          rev
          narHash
          ;
      }
    }/lib" { inherit prelude; }
  ),
  ...
}:
import ./lib { inherit prelude graph; }
