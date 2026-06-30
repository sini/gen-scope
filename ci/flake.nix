{
  inputs = {
    gen.url = "github:sini/gen";
    gen-prelude.url = "github:sini/gen-prelude";
    # nixpkgs is the CI runner's dependency (test harness, treefmt) and supplies the
    # `lib` the test modules use. The library itself (../lib) takes only gen-prelude.
    nixpkgs.url = "https://channels.nixos.org/nixos-unstable/nixexprs.tar.xz";
  };

  outputs =
    inputs@{
      gen,
      gen-prelude,
      ...
    }:
    let
      prelude = import "${gen-prelude}/lib" { };
      genScope = import ../lib { inherit prelude; };
    in
    gen.lib.mkCi {
      inherit inputs;
      name = "gen-scope";
      testModules = ./tests;
      specialArgs = { inherit genScope; };
    };
}
