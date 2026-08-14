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
  # The stratification driver takes the round-loop forcing rather than defining a second copy of
  # it: two copies of a discipline agree only for as long as someone keeps them in step, and this
  # one already lives next door.
  stratify = import ./stratify.nix {
    inherit prelude;
    inherit (leastModel) forceFields;
  };
  # A value algebra over fragments, which is why it takes the prelude and nothing else: the cascade
  # is one of its consumers rather than its home — and it is a consumer twice over, since a kind's
  # resource fold and a wiring splice both take the vocabulary as data.
  folds = import ./folds.nix { inherit prelude; };
  cascade = import ./cascade.nix {
    inherit prelude graph;
    inherit (folds) folds;
  };
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
// stratify
// folds
// cascade
