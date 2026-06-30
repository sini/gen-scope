{ prelude }:
let
  graph = import ./graph.nix;
  buildNodes = import ./build-nodes.nix { inherit prelude; };
  queries = import ./queries.nix { inherit prelude; };
  resolve = import ./resolve.nix { inherit prelude; };
  eval = import ./eval.nix { inherit prelude; };
in
graph // buildNodes // queries // resolve // eval
