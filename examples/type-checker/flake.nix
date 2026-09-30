{
  description = "Type checker: structural records and subtyping via scope graphs (van Antwerpen 2018)";

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
      result = genScope.eval { } (graph.mkAttributes graph.roots attributes) graph.roots;
    in
    {
      tests = import ./tests.nix { inherit genScope lib result; };
    };
}
