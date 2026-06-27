{
  lib ? (import <nixpkgs> { }).lib,
  ...
}:
import ./lib { inherit lib; }
