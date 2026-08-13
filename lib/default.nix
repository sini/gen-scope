{ prelude, graph }:
let
  # The library's OWN algebraic-graph constructors, which are a different thing from the graph
  # library bound as `graph`: these build a scope graph out of vertices and overlays, that one
  # answers reachability and partition questions about a graph already built.
  algebraicGraph = import ./graph.nix;
  buildNodes = import ./build-nodes.nix { inherit prelude; };
  queries = import ./queries.nix { inherit prelude; };
  resolve = import ./resolve.nix { inherit prelude; };
  structural = import ./structural.nix { inherit prelude; };
  interface = import ./interface.nix { inherit prelude; };
  eval = import ./eval.nix { inherit prelude; };
  program = import ./program.nix { inherit prelude; };
  leastModel = import ./least-model.nix { inherit prelude; };
  wellFounded = import ./well-founded.nix { inherit prelude; };
  acceptance = import ./acceptance.nix { inherit prelude; };
  engine = import ./engine.nix { inherit prelude graph; };
  cascade = import ./cascade.nix { inherit prelude graph; };
in
algebraicGraph
// buildNodes
// queries
// resolve
// structural
// interface
// eval
// program
// leastModel
// wellFounded
// acceptance
// engine
// cascade
