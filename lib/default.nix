{ lib }:
let
  graph = import ./graph.nix;
  buildNodes = import ./build-nodes.nix { inherit lib; };
  queries = import ./queries.nix { inherit lib; };
  resolve = import ./resolve.nix { inherit lib; };
  eval = import ./eval.nix { inherit lib; };
in
graph // buildNodes // queries // resolve // eval
