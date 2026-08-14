{
  inputs = {
    gen-harness.url = "github:sini/gen-harness";
    gen-prelude.url = "github:sini/gen-prelude";
    # The engine's dependency, pinned here directly rather than reached through the hub: the
    # partition door's published record is what the engine's provenance cells read, so the suite
    # must see the revision that publishes it rather than whatever revision the hub happens to
    # carry.
    gen-graph.url = "github:sini/gen-graph";
    # The identity authority, pinned here as well as at the root because this flake builds the
    # library from its OWN inputs (`import ../lib` below): a pin declared only at the root would
    # leave the suite asserting identity behaviour under a revision free to drift from the one the
    # library ships. The `follows` is what keeps the two declarations one instance — two instances
    # in one evaluation are two identity formulas for the same node.
    gen-schema = {
      url = "github:sini/gen-schema";
      inputs.gen-prelude.follows = "gen-prelude";
    };
    # nixpkgs is the CI runner's dependency (test harness, treefmt) and supplies the
    # `lib` the test modules use. The library itself (../lib) takes gen-prelude and gen-graph.
    nixpkgs.url = "https://channels.nixos.org/nixos-unstable/nixexprs.tar.xz";
  };

  outputs =
    inputs@{
      gen-harness,
      gen-prelude,
      gen-graph,
      ...
    }:
    let
      prelude = import "${gen-prelude}/lib";
      genScope = import ../lib {
        inherit prelude;
        graph = gen-graph.lib;
      };
    in
    gen-harness.lib.mkCi {
      inherit inputs;
      name = "gen-scope";
      testModules = ./tests;
      # `genGraph` and `genPreludeLib` are here for the armed negative controls: a refusal cell is
      # only meaningful beside a construction built the wrong way, and building one means calling
      # the same graph surface the library calls and instantiating the library against a
      # substituted one. `genPreludeLib` is a second name rather than an override of the harness's
      # `genPrelude`, whose surface is deliberately one function and stays that way.
      specialArgs = {
        inherit genScope;
        genGraph = gen-graph.lib;
        genPreludeLib = prelude;
      };
      # Cells whose subject is an error MESSAGE cannot live under `testModules`: the batch
      # asserter behind `checks.default` quantifies over `flake.tests` and forces every `expr`
      # unconditionally, so a throwing one crashes that gate instead of failing a cell. They get
      # their own output, read by `nix-unit --flake ./ci#testsError`, and being outside this tree
      # is what keeps that structural rather than conventional.
      extraModules = [
        ./tests-error.nix
        ./tests-pending.nix
      ];
    };
}
