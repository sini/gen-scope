{
  description = "gen-scope: demand-driven attribute grammar evaluator over algebraic scope graphs";

  # gen-scope is nixpkgs-lib-free: its inputs are gen-prelude, gen-graph and gen-identity, all three
  # pure and nixpkgs-lib-free. The HOAG evaluator is pure list/attr combinators + builtins — no
  # module system, no nixpkgs.lib.
  #
  # gen-graph is the ENGINE's dependency, not the evaluator's: the well-founded engine consumes
  # that library's one published SCC-partition front door rather than carrying a second
  # partitioner, because reverse reachability and the condensation are its concern.
  #
  # gen-identity is the identity authority's home — a DEPENDENCY-FREE LEAF, taken directly rather
  # than through an intermediary, because a mint reached through a second library is a mint whose
  # identity depends on that library's pin, and two pins of the intermediary are two
  # content-address formulas for one node. The authority reaches a minting module by injection from
  # `lib/default.nix`, never by that module importing a library of its own, and gen-scope
  # re-exports none of it: re-exporting another library's value re-exports its build (ADR-0014),
  # and the count of minting authorities is one (ADR-0016 ruling 5).
  #
  # ★★ gen-schema IS NOT AN INPUT, AND THE ABSENCE IS THE DEPENDENCY FACT RATHER THAN AN OMISSION.
  # Nothing this library builds reads it: over every file in `lib/`, `schema` occurs only in prose
  # about the schema STRATUM — a data stage of this evaluator, a different thing from the library of
  # that name — and in no expression at all. A declared-and-unread input is not free: it is a second
  # pin of a library this one never evaluates, and it is the back-edge on which a flake cycle
  # between the two would rest the moment gen-schema takes an edge this way. The reflection
  # authority reaches the evaluator at a consumer that already holds both, never here. Re-adding it
  # takes a reader in `lib/`, not a caller who happens to have one.
  #
  # A CONSUMER's `follows` over this library is load-bearing, not hygiene. Two instances of gen-scope
  # in one evaluation are two identity formulas for the same node — a failure measured in a shipped
  # consumer, not a hazard imagined here.
  inputs = {
    gen-prelude.url = "github:sini/gen-prelude";
    gen-graph.url = "github:sini/gen-graph";
    # The one minting authority, now a dependency-free leaf. It is taken directly rather than
    # through an intermediary: a mint reached through a second library is a mint whose identity
    # depends on that library's pin.
    gen-identity.url = "github:sini/gen-identity";
    # The mark readers (`hasMark`, `markOf`) a kind value is read through, from the library that
    # authors the `__mint` tagged sum. gen-algebra declares no inputs, so this adds a leaf.
    gen-algebra.url = "github:sini/gen-algebra";
  };

  outputs =
    {
      gen-prelude,
      gen-graph,
      gen-identity,
      gen-algebra,
      ...
    }:
    {
      # ★ THE ROOT, NOT `./lib`. `./.` and `./lib` were two independent constructions of one
      # value and so free to disagree; there is ONE construction site now, and the two entry
      # paths differ only in who supplies the arguments. Here the flake supplies them, so
      # `follows` governs every argument passed, while the standalone path resolves each default
      # from THIS file's own `flake.lock`, read as local data — never from `ci/flake.lock`, which
      # is the TEST graph's pin source and which no library code reads (ADR-0037 as amended
      # 2026-09-15; `default.nix` states the same rule at its head).
      lib = import ./. {
        prelude = gen-prelude.lib;
        graph = gen-graph.lib;
        identity = gen-identity.lib;
        algebra = gen-algebra.lib;
      };
    };
}
