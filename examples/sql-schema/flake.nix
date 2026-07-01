{
  description = "Infrastructure schema demo — all 8 gen libraries: schema, scope, graph, select, dispatch, bind, algebra";
  inputs = {
    gen-scope.url = "github:sini/gen-scope";
    gen-schema.url = "github:sini/gen-schema";
    gen-graph.url = "github:sini/gen-graph";
    gen-algebra.url = "github:sini/gen-algebra";
    gen-select.url = "github:sini/gen-select";
    gen-dispatch.url = "github:sini/gen-dispatch";
    gen-bind.url = "github:sini/gen-bind";
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };
  outputs =
    {
      gen-scope,
      gen-schema,
      gen-graph,
      gen-algebra,
      gen-select,
      gen-dispatch,
      gen-bind,
      nixpkgs,
      ...
    }:
    let
      lib = nixpkgs.lib;
      genScope = gen-scope.lib;
      genAlgebra = gen-algebra { inherit lib; };
      genSelect = gen-select.lib;
      genDispatch = gen-dispatch.lib;
      genBind = gen-bind.lib;
      genSchema = import "${gen-schema}/nix/lib" {
        inherit lib;
        inputs = {
          gen = genAlgebra;
        };
      };
      genGraph = gen-graph.lib;
      sql = import ./lib {
        inherit
          lib
          genSchema
          genScope
          genGraph
          genSelect
          genDispatch
          genBind
          ;
      };
    in
    {
      inherit sql;
      tests = import ./tests.nix {
        inherit
          lib
          sql
          genSchema
          genGraph
          ;
      };
    };
}
