{
  description = "Dependency resolver: package resolution with version constraints and conflict detection";
  inputs = {
    nixpkgs.url = "https://channels.nixos.org/nixos-unstable/nixexprs.tar.xz";
  };
  outputs =
    { nixpkgs, ... }:
    let
      lib = nixpkgs.lib;
      genScope = import ../.. { };
      graph = import ./graph.nix { inherit genScope lib; };
      attributes = import ./attributes.nix { inherit genScope lib; };
      inherit (graph) roots;
      result = genScope.eval { } (graph.mkAttributes roots attributes) roots;
    in
    {
      tests = import ./tests.nix {
        inherit
          genScope
          lib
          result
          roots
          ;
        attributes = graph.mkAttributes roots attributes;
      };
    };
}
