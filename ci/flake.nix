{
  inputs = {
    gen-harness.url = "github:sini/gen-harness";
    gen-prelude.url = "github:sini/gen-prelude";
    # The engine's dependency, pinned here directly rather than reached through the hub: the
    # partition door's published record is what the engine's provenance cells read, so the suite
    # must see the revision that publishes it rather than whatever revision the hub happens to
    # carry.
    gen-graph.url = "github:sini/gen-graph";
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
      specialArgs = { inherit genScope; };
    };
}
