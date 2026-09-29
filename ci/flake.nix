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
    # library ships.
    gen-identity.url = "github:sini/gen-identity";
    # nixpkgs is the CI runner's dependency (test harness, treefmt) and supplies the
    # `lib` the test modules use. The library itself (../lib) takes gen-prelude, gen-graph and
    # gen-identity.
    nixpkgs.url = "https://channels.nixos.org/nixos-unstable/nixexprs.tar.xz";
  };

  outputs =
    inputs@{
      gen-harness,
      gen-prelude,
      gen-graph,
      gen-identity,
      ...
    }:
    let
      prelude = import "${gen-prelude}/lib";
      genScope = import ../lib {
        inherit prelude;
        graph = gen-graph.lib;
        identity = gen-identity.lib;
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
      # `genIdentity` reaches the suite because `tests/entry.nix` applies the STANDALONE root entry
      # with explicit arguments — which is what keeps that cell pure, since supplying every
      # dependency formal means the shim's fetching defaults are never forced. It is the SAME
      # instance `genScope` above is built from, so the two sides of that comparison differ in entry
      # point and in nothing else.
      specialArgs = {
        inherit genScope;
        genGraph = gen-graph.lib;
        genPreludeLib = prelude;
        genIdentity = gen-identity.lib;
      };
      # Cells whose subject is an error MESSAGE cannot live under `testModules`: the batch
      # asserter behind `checks.default` quantifies over `flake.tests` and forces every `expr`
      # unconditionally, so a throwing one crashes that gate instead of failing a cell. They get
      # their own output, read by `nix-unit --flake ./ci#testsError`, and being outside this tree
      # is what keeps that structural rather than conventional.
      extraModules = [
        ./tests-error.nix
        # The per-process cells: verdicts that are PROCESS EXITS (uncatchable aborts), one
        # fixture per evaluator process. Exposed as `apps.<system>.tests-process` and run by
        # `ci --tests-process` under the column's evaluator, never as a sandboxed check.
        ./tests-process.nix
        # `buildNodes` is a TOMBSTONE (lib/build-nodes.nix): `checks.root-surface` excludes it from
        # the walk, and the generated `root-surface-retired.test-retired-buildNodes` cell pins this
        # exact message at the root seam, so a resurrected or reworded tombstone reds.
        {
          gen.ci.rootSurface.retired.buildNodes =
            "gen-scope: `buildNodes` is retired. Use `buildRoots`, which returns `{ nodes, nodeOrder }` — the node set together with its declared vertex order. Renaming the call is NOT sufficient: the evaluators take that whole record as `scope`, not a bare node map as `roots`, so `eval { roots = buildRoots {…}; }` is refused too.";
        }
        # The resolution surfaces the one calculus retired (den-hoag-gayc D16), pinned the same way.
        {
          gen.ci.rootSurface.retired = {
            ambiguous = "gen-scope: `ambiguous` is retired. Use `length (unique (map (a: a.node) (resolve { inherit (neron) wf; mode = \"witnesses\"; dataFilter = f; } self id).answers)) > 1`: an ambiguity is more than one distinct declaring node, never one declaration reached along several paths. Every evaluation `resolve` reads declares `marks` (`_: _: [ ]` states none).";
            query = "gen-scope: `query` is retired. Use the one resolution calculus: `(resolve (neron // { mode = \"visible\"; dataFilter = f; groupBy = _: \"k\"; }) self id).single \"k\"`. `transitiveImports = true` is `wf = wellFormed { alphabet = [ \"parent\" \"imports\" ]; expression = \"parent* imports*\"; }`, and the retired shadowing flags are a stated `order` (`labelOrder`). Every evaluation `resolve` reads declares `marks` (`_: _: [ ]` states none).";
            queryAll = "gen-scope: `queryAll` is retired. Use the one resolution calculus: `(resolve { inherit (neron) wf; mode = \"witnesses\"; dataFilter = f; } self id).answers`, one `{ node; value; path; state; }` per acyclic resolution path (a diamond answers twice). Every evaluation `resolve` reads declares `marks` (`_: _: [ ]` states none).";
            visibleFrom = "gen-scope: `visibleFrom` is retired. Use `(resolve (neron // { mode = \"visible\"; dataFilter = f; groupBy = _: \"k\"; }) self id).single \"k\"`. Every evaluation `resolve` reads declares `marks` (`_: _: [ ]` states none).";
            queryReverse = "gen-scope: `queryReverse` is retired. Use the one resolution calculus over the converse: `map (a: a.value) (resolve { wf = wellFormed { alphabet = [ \"imports\" ]; expression = \"imports\"; }; mode = \"witnesses\"; direction = \"inbound\"; dataFilter = f; } self id).answers`; `transitive = true` is `expression = \"imports imports*\"`. One answer per acyclic reverse path, importers in `allNodeIds` order, so a node on two reverse paths answers twice. Every evaluation `resolve` reads declares `marks` (`_: _: [ ]` states none).";
          };
        }
      ];
    };
}
