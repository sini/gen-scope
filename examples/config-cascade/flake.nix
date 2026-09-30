{
  description = "Config cascade resolver: hierarchical config override (.env/kustomize pattern)";
  inputs = {
    nixpkgs.url = "https://channels.nixos.org/nixos-unstable/nixexprs.tar.xz";
  };
  outputs =
    { nixpkgs, ... }:
    let
      lib = nixpkgs.lib;
      genScope = import ../.. { };
      inherit (import ./graph.nix { inherit genScope; }) roots;
      attributes = import ./attributes.nix { inherit genScope lib roots; };
      result = genScope.eval { } attributes roots;
    in
    {
      tests = import ./tests.nix { inherit genScope lib result; };
    };
}
