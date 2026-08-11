{
  description = "gen-scope: demand-driven attribute grammar evaluator over algebraic scope graphs";

  # gen-scope is nixpkgs-lib-free: the library depends only on gen-prelude and gen-graph, both
  # pure and nixpkgs-lib-free. The HOAG evaluator is pure list/attr combinators + builtins — no
  # module system, no nixpkgs.lib.
  #
  # gen-graph is the ENGINE's dependency, not the evaluator's: the well-founded engine consumes
  # that library's one published SCC-partition front door rather than carrying a second
  # partitioner, because reverse reachability and the condensation are its concern.
  inputs = {
    gen-prelude.url = "github:sini/gen-prelude";
    gen-graph.url = "github:sini/gen-graph";
  };

  outputs =
    { gen-prelude, gen-graph, ... }:
    {
      lib = import ./lib {
        prelude = gen-prelude.lib;
        graph = gen-graph.lib;
      };
    };
}
