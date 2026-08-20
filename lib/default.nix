# The library's assembly point, and the one place an outside authority is bound to a module.
#
# `schema` is the identity authority's library and it is taken as a value rather than imported: the
# minting module below receives the ONE function it needs and never reaches for a library of its own,
# so the count of minting authorities is a fact about the dataflow rather than a rule an author obeys
# (ADR-0016 ruling 5). Nothing of it is re-exported under this library's name — re-exporting another
# library's value re-exports its build (ADR-0014), and the surface this seam adds is the minting
# entry and nothing else.
{
  prelude,
  graph,
  schema,
  identity,
}:
let
  # The library's OWN algebraic-graph constructors, which are a different thing from the graph
  # library bound as `graph`: these build a scope graph out of vertices and overlays, that one
  # answers reachability and partition questions about a graph already built.
  algebraicGraph = import ./graph.nix;
  buildRoots = import ./build-nodes.nix { inherit prelude; };
  queries = import ./queries.nix { inherit prelude; };
  resolve = import ./resolve.nix { inherit prelude; };
  structural = import ./structural.nix { inherit prelude; };
  interface = import ./interface.nix { inherit prelude; };
  inherit (import ./require-scope.nix { inherit prelude; }) requireScope;
  eval = import ./eval.nix { inherit prelude requireScope; };
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
  # The minting instance of that driver. The authority arrives here as a function and the driver as
  # the module next door, which is what keeps the minting module free of both a library import and a
  # second stratification loop.
  mint = import ./mint.nix {
    inherit prelude graph;
    inherit (identity) hashIdentity;
    inherit (stratify) stratify;
  };
  # A value algebra over fragments, which is why it takes the prelude and nothing else. The cascade
  # names it nowhere: a kind's resource fold arrives as a FIELD on the kind, so the vocabulary
  # reaches the run as the author's data rather than as an import of this module.
  folds = import ./folds.nix { inherit prelude; };
  cascade = import ./cascade.nix { inherit prelude graph; };
  # The cold fold over a validated schedule, which takes the demand fixpoint and the declared-read
  # projection from the module next door rather than reaching for a second evaluator: the entry is
  # the evaluator's caller, and the one it calls is this library's own.
  foldEquations = import ./fold-equations.nix {
    inherit prelude;
    inherit (eval) eval recordedDeps;
    inherit requireScope;
  };
  # The surface is folded rather than chained with `//`, so a name contributed by two modules is a
  # throw naming both instead of a silent last-wins shadowing.
  mergeSurface = import ./merge-surface.nix { inherit prelude; };
in
mergeSurface {
  inherit
    algebraicGraph
    buildRoots
    queries
    resolve
    structural
    interface
    eval
    program
    leastModel
    wellFounded
    acceptance
    engine
    stratify
    mint
    folds
    cascade
    foldEquations
    ;
}
