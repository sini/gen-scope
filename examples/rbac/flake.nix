{
  description = "RBAC permission resolver: role hierarchies and resource access control via scope graphs";
  inputs = {
    nixpkgs.url = "https://channels.nixos.org/nixos-unstable/nixexprs.tar.xz";
  };
  outputs =
    { nixpkgs, ... }:
    let
      lib = nixpkgs.lib;
      genScope = import ../.. { };
      inherit (import ./graph.nix { inherit genScope lib; }) roots;
      inherit (import ./attributes.nix { inherit genScope lib roots; }) rolePermissions attributes;
      result = genScope.eval { } attributes roots;
    in
    {
      tests = import ./tests.nix {
        inherit
          genScope
          lib
          result
          rolePermissions
          ;
      };
    };
}
