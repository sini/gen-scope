{
  description = "gen-scope: demand-driven attribute grammar evaluator over algebraic scope graphs";

  # gen-scope is nixpkgs-lib-free: its inputs are gen-prelude, gen-graph, gen-schema and
  # gen-identity, all four pure and nixpkgs-lib-free — gen-schema's `./lib` is checked by that
  # library's own `ci/tests/purity.nix`, which pulls nixpkgs no further than its `ci/`. The HOAG
  # evaluator is pure list/attr combinators + builtins — no module system, no nixpkgs.lib.
  #
  # gen-graph is the ENGINE's dependency, not the evaluator's: the well-founded engine consumes
  # that library's one published SCC-partition front door rather than carrying a second
  # partitioner, because reverse reachability and the condensation are its concern.
  #
  # gen-identity is the identity authority's home — a DEPENDENCY-FREE LEAF, taken directly rather
  # than through gen-schema, because a mint reached through a second library is a mint whose
  # identity depends on that library's pin, and two pins of the intermediary are two
  # content-address formulas for one node. The authority reaches a minting module by injection from
  # `lib/default.nix`, never by that module importing a library of its own, and gen-scope
  # re-exports none of it: re-exporting another library's value re-exports its build (ADR-0014),
  # and the count of minting authorities is one (ADR-0016 ruling 5). gen-schema stays an input for
  # its own concern — the typed record registry and the identity-key REFLECTION that decides which
  # of a kind's options count — which is a different question from where the formula lives.
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
      # `nix flake check` forces the WHNF of every top-level output and nothing deeper, so this root's
      # green quantified over the `lib` SPINE alone: a member of the published surface could throw and
      # the check still exited 0 (measured — den-hoag-z1ta6). Hanging the force on that spine is what
      # makes the green mean "the surface evaluates", and a library needs no new output name for it.
      # The depth is each member's WHNF and no deeper: a retirement tombstone is a published `throw`
      # by design (gen-scope's `buildNodes`), so a deep force is red on a healthy tree.
      # `buildNodes` is excluded BY NAME because it is exactly that tombstone — forcing it is red on a
      # healthy tree. The exclusion states the check's domain rather than leaving a hole in it: every
      # other member of the surface is forced.
      lib =
        let
          surface = import ./lib {
            prelude = gen-prelude.lib;
            graph = gen-graph.lib;
            schema = gen-schema.lib;
            identity = gen-identity.lib;
          };
        in
        builtins.deepSeq (builtins.mapAttrs (_: builtins.typeOf) (
          builtins.removeAttrs surface [ "buildNodes" ]
        )) surface;
    };
}
