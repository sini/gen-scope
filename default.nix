# Standalone (non-flake) entry. Flake consumers should use the `.lib` output.
#
# gen-scope is nixpkgs-lib-free: this shim derives gen-prelude from the pinned
# flake.lock (content-addressed via narHash, so it stays pure) and needs no
# `<nixpkgs>`. Pass `prelude` to override.
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
    }/lib" { }
  ),
  ...
}:
import ./lib { inherit prelude; }
