{
  description = "Module resolver: Neron 2015 LM-style module system with scope graphs";

  inputs = {
    nixpkgs.url = "https://channels.nixos.org/nixos-unstable/nixexprs.tar.xz";
  };

  outputs =
    { nixpkgs, ... }:
    let
      lib = nixpkgs.lib;
      genScope = import ../.. { };
      inherit (import ./graph.nix { inherit genScope lib; }) roots;
      attributes = import ./attributes.nix { inherit genScope lib roots; };
      result = genScope.eval { } attributes roots;
    in
    {
      tests = import ./tests.nix { inherit genScope lib result; };
    };
}
