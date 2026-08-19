{
  description = "Module resolver: Neron 2015 LM-style module system with scope graphs";

  inputs = {
    gen-scope.url = "github:sini/gen-scope";
    nixpkgs.url = "https://channels.nixos.org/nixos-unstable/nixexprs.tar.xz";
  };

  outputs =
    { gen-scope, nixpkgs, ... }:
    let
      lib = nixpkgs.lib;
      genScope = gen-scope.lib;
      inherit (import ./graph.nix { inherit genScope lib; }) roots;
      attributes = import ./attributes.nix { inherit genScope lib roots; };
      result = genScope.eval {
        scope = roots;
        inherit attributes;
      };
    in
    {
      tests = import ./tests.nix { inherit genScope lib result; };
    };
}
