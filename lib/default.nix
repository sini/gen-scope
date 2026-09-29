# The library's assembly point, and the one place an outside authority is bound to a module.
#
# `identity` is the identity authority's library — `gen-identity`, a dependency-free leaf — and it is
# taken as a value rather than imported: the
# minting module below receives the ONE function it needs and never reaches for a library of its own,
# so the count of minting authorities is a fact about the dataflow rather than a rule an author obeys
# (ADR-0016 ruling 5). Nothing of it is re-exported under this library's name — re-exporting another
# library's value re-exports its build (ADR-0014), and the surface this seam adds is the minting
# entry and nothing else.
{
  prelude,
  graph,
  identity,
}:
let
  # The library's OWN algebraic-graph constructors, which are a different thing from the graph
  # library bound as `graph`: these build a scope graph out of vertices and overlays, that one
  # answers reachability and partition questions about a graph already built.
  #
  # `connect` and `edge` publish as R7 (b) records, `{ from; to; }` (den-hoag-7gp66 P2): both
  # operands are of one sort and the direction is the whole meaning, so each is named rather than
  # remembered by position. `lib/graph.nix` depends on nothing and keeps the positional cores, which
  # its own derived constructors (`star`, `edges`, `path`) call; the doors are bound here, where the
  # prelude is.
  algebraicGraph =
    let
      core = import ./graph.nix;
      fromTo =
        name: f:
        prelude.door {
          name = "gen-scope.${name}";
          required = [
            "from"
            "to"
          ];
          open = true;
        } (r: f r.from r.to);
    in
    core
    // {
      connect = fromTo "connect" core.connect;
      edge = fromTo "edge" core.edge;
    };
  # `kindSetDefect` is `cascade.nix`'s, for the reason `requireDeclaredDependencies` takes `graph`
  # below: the registry TYPE is decided beside the fold that mints its kinds, and the refusal is
  # minted at the door where the defect is. `cascade.nix` takes `{ prelude }` and reaches neither of
  # these two modules, so the binding is acyclic.
  buildRoots = import ./build-nodes.nix {
    inherit prelude;
    inherit (cascadeModule) kindSetDefect;
  };
  queries = import ./queries.nix { inherit prelude; };
  resolve = import ./resolve.nix { inherit prelude; };
  # The one resolution calculus. It takes gen-graph's published key former applied under THIS
  # library's name, so a refusal it raises reads `gen-scope.<door>` and the key discipline is the
  # one gen-graph states, bound once rather than copied (den-hoag-gayc C7).
  calculus = import ./calculus.nix {
    inherit prelude;
    key = graph.key "gen-scope";
  };
  structural = import ./structural.nix { inherit prelude; };
  interface = import ./interface.nix { inherit prelude; };
  inherit
    (import ./require-scope.nix {
      inherit prelude;
      inherit (cascadeModule) kindSetDefect;
    })
    requireScope
    ;
  # The declared relation's input type. It takes `graph` because the DISCRIMINATOR is `gen-graph`'s
  # — the tag only that library's constructors write — while the refusal is this library's, naming
  # this library's entry point for a defect at this library's door.
  inherit (import ./require-declared-dependencies.nix { inherit graph; })
    requireDeclaredDependencies
    ;
  # `graph` reaches the evaluator for ONE construct: the endpoint projection that reads a node's
  # structural attribute RECORD as an edge relation. That construct is edge vocabulary and lives in
  # the graph library beside its other endpoint extractors, so what arrives here is the CONSTRUCTOR;
  # what this side supplies to it are the two facts only an evaluated substrate holds — the
  # child-bearing predicate and the evaluated node set.
  evalModule = import ./eval.nix {
    inherit
      prelude
      requireScope
      requireDeclaredDependencies
      graph
      ;
  };
  # The unchecked cores leave before the merge: they are the library's own calls, not its surface.
  eval = builtins.removeAttrs evalModule [ "cores" ];
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
  # The bounded-ascent driver, a peer of the stratification one and wired the same way: it takes the
  # round-loop forcing rather than defining a second copy of it. The engine does not see it and does
  # not import it — it sits BESIDE the engine exactly as `stratify` does, and reaches its consumer as
  # a member of the library value that consumer is already handed.
  ascent = import ./ascent.nix {
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
  cascadeModule = import ./cascade.nix { inherit prelude; };
  # The registry door's predicate is the doors' and not the consumer's: it leaves before the merge.
  cascade = builtins.removeAttrs cascadeModule [ "kindSetDefect" ];
  # The cold fold over a validated schedule, which takes the demand fixpoint from the module next
  # door rather than reaching for a second evaluator: the entry is the evaluator's caller, and the
  # one it calls is this library's own.
  foldEquations = import ./fold-equations.nix {
    inherit prelude;
    inherit (evalModule.cores) eval;
    inherit requireScope requireDeclaredDependencies;
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
    calculus
    structural
    interface
    eval
    program
    leastModel
    wellFounded
    acceptance
    engine
    stratify
    ascent
    mint
    folds
    cascade
    foldEquations
    ;
}
