{
  description = "gen-scope: demand-driven attribute grammar evaluator over algebraic scope graphs";

  # gen-scope is nixpkgs-lib-free: the library depends only on gen-prelude (pure,
  # zero-input). The HOAG evaluator is pure list/attr combinators + builtins — no
  # module system, no nixpkgs.lib.
  inputs = {
    gen-prelude.url = "github:sini/gen-prelude";
  };

  outputs =
    { gen-prelude, ... }:
    {
      lib = import ./lib { prelude = gen-prelude.lib; };
    };
}
