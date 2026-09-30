{
  description = "nix-config ACL: unified access control with three-level scope graph resolution";
  inputs = {
    nixpkgs.url = "https://channels.nixos.org/nixos-unstable/nixexprs.tar.xz";
  };
  outputs =
    { nixpkgs, ... }:
    let
      lib = nixpkgs.lib;
      genScope = import ../.. { };
      groups = import ./data/groups.nix;
      environments = import ./data/environments.nix;
      hosts = import ./data/hosts.nix;
      inherit
        (import ./graph.nix {
          inherit
            genScope
            lib
            groups
            environments
            hosts
            ;
        })
        roots
        ;
      inherit (import ./attributes.nix { inherit genScope lib roots; }) attributes;
      result = genScope.eval { } attributes roots;
      resolveOn = host: user: result.get "host:${host}" "resolveUser" user;
    in
    {
      tests = import ./tests.nix {
        inherit
          genScope
          lib
          result
          resolveOn
          ;
      };
    };
}
