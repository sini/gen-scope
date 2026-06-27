{
  description = "gen-scope: demand-driven attribute grammar evaluator over algebraic scope graphs";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  outputs =
    { nixpkgs, ... }:
    {
      lib = import ./lib { lib = nixpkgs.lib; };
    };
}
