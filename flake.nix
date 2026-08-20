{
  description = "gen-scope: demand-driven attribute grammar evaluator over algebraic scope graphs";

  # gen-scope is nixpkgs-lib-free: its inputs are gen-prelude, gen-graph and gen-schema, all three
  # pure and nixpkgs-lib-free — gen-schema's `./lib` is checked by that library's own
  # `ci/tests/purity.nix`, which pulls nixpkgs no further than its `ci/`. The HOAG evaluator is
  # pure list/attr combinators + builtins — no module system, no nixpkgs.lib.
  #
  # gen-graph is the ENGINE's dependency, not the evaluator's: the well-founded engine consumes
  # that library's one published SCC-partition front door rather than carrying a second
  # partitioner, because reverse reachability and the condensation are its concern.
  #
  # gen-schema is the identity authority's home and it stays there. The authority reaches a minting
  # module by injection from `lib/default.nix`, never by that module importing a library of its
  # own, and gen-scope re-exports none of it: re-exporting another library's value re-exports its
  # build (ADR-0014), and the count of minting authorities is one (ADR-0016 ruling 5).
  #
  # The `follows` is load-bearing, not hygiene. Two instances of this library in one evaluation are
  # two identity formulas for the same node — a failure measured in a shipped consumer, not a
  # hazard imagined here.
  inputs = {
    gen-prelude.url = "github:sini/gen-prelude";
    gen-graph.url = "github:sini/gen-graph";
    gen-schema = {
      url = "github:sini/gen-schema";
      inputs.gen-prelude.follows = "gen-prelude";
    };
    # The one minting authority, now a dependency-free leaf. It is taken directly rather than
    # through gen-schema: a mint reached through a second library is a mint whose identity
    # depends on that library's pin.
    gen-identity.url = "github:sini/gen-identity";
  };

  outputs =
    {
      gen-prelude,
      gen-graph,
      gen-schema,
      gen-identity,
      ...
    }:
    {
      lib = import ./lib {
        prelude = gen-prelude.lib;
        graph = gen-graph.lib;
        schema = gen-schema.lib;
        identity = gen-identity.lib;
      };
    };
}
