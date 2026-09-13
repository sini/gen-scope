# THE SHIPPED EXAMPLES, FORCED ON EVERY GATE.
#
# ★ WHY THIS FILE EXISTS. Each directory under `examples/` is a flake pinning `github:sini/gen-scope`
# in its own lock, so `nix eval "<example>#tests"` evaluates that example against ITS LOCK and never
# against this tree — the corpus drifted 137 commits behind the library it documents and nothing in
# the suite could see it (`den-hoag-5oag`). Here each example's `outputs` is applied to THIS suite's
# library, so the tree under test is the tree the examples run on.
#
# ★★ THE FORCE IS `deepSeq`, NOT `attrNames`. An example's `tests` output is an attrset whose spine
# survives WHNF with every failing cell unforced: measured, `builtins.attrNames` read a full name
# list with exit 0 on an example that fails under `deepSeq`. The control cell at the bottom shows the
# two forcing depths DISAGREE on a seeded value, in this run.
#
# ★ THE STATED DOMAIN. `outputs` is applied with the inputs this flake carries — the library and
# nixpkgs' `lib` — and two examples take libraries it does not: `nest-traits` (gen-schema, gen-aspects,
# gen-algebra, gen-graph) and `sql-schema` (those plus gen-select, gen-dispatch, gen-bind). Reaching
# them from here would pin each of those libraries a second time, beside the pin in the example's own
# lock. They are EXCLUDED BY NAME rather than left out, and the totality cell reads the directory so an
# example that is neither forced nor named is red the moment it appears.
{ lib, genScope, ... }:
let
  examplesDir = ../../examples;

  # The libraries the example flakes' `outputs` formals bind. `nixpkgs.lib` is what every example
  # reads off that input; `gen-scope.lib` is the surface under test.
  exampleInputs = {
    gen-scope.lib = genScope;
    nixpkgs.lib = lib;
  };

  outputsOf = name: (import (examplesDir + "/${name}/flake.nix")).outputs exampleInputs;

  forced = v: builtins.deepSeq v "forced";

  # The examples whose `tests` output is forced here, and the ones excluded with the reason above.
  testsBearing = [
    "config-cascade"
    "dep-resolver"
    "feature-flags"
    "module-resolver"
    "nix-config-acl"
    "rbac"
    "type-checker"
  ];
  excluded = [
    "nest-traits"
    "sql-schema"
  ];
in
{
  flake.tests.examples =
    lib.listToAttrs (
      map (name: {
        name = "test-${name}-tests-force-under-deepSeq";
        value = {
          expr = forced (outputsOf name).tests;
          expected = "forced";
        };
      }) testsBearing
    )
    // {
      # `demo` has no `tests` output: its eighteen top-level outputs ARE its demonstrations, each
      # annotated with the value it claims, so the whole output set is forced.
      test-demo-every-output-forces-under-deepSeq = {
        expr = forced (outputsOf "demo");
        expected = "forced";
      };

      # ★ TOTALITY OVER THE DIRECTORY. The forced set and the excluded set together are exactly what
      # is on disk, so a new example is either forced or named here — never silently neither.
      # Shown to fire in the run that landed it: with `demo` absent from this roster the cell read
      # ❌ against the directory that carries it, while every forcing cell above stayed ✅.
      test-every-example-directory-is-forced-or-excluded-by-name = {
        expr = builtins.attrNames (builtins.readDir examplesDir);
        expected = builtins.sort builtins.lessThan (testsBearing ++ [ "demo" ] ++ excluded);
      };

      # ★★ THE FORCING DEPTH DISCRIMINATES, in this run. A nested seeded throw survives `seq` and
      # fails `deepSeq`; if the two arms agreed, the cells above would be asserting on the spine.
      test-control-deepSeq-reaches-what-seq-does-not = {
        expr =
          let
            seeded = {
              outer = {
                inner = throw "seeded";
              };
            };
          in
          {
            shallow = (builtins.tryEval (builtins.seq seeded true)).success;
            deep = (builtins.tryEval (builtins.deepSeq seeded true)).success;
          };
        expected = {
          shallow = true;
          deep = false;
        };
      };
    };
}
