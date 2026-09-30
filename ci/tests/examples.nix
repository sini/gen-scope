# THE SHIPPED EXAMPLES, FORCED ON EVERY GATE.
#
# ★ WHY THIS FILE EXISTS. Each directory under `examples/` is a flake pinning `github:sini/gen-scope`
# in its own lock, so `nix eval "<example>#tests"` evaluates that example against ITS LOCK and never
# against this tree — the corpus drifted 137 commits behind the library it documents and nothing in
# the suite could see it (`den-hoag-5oag`). Here each example's `outputs` is applied to THIS suite's
# library, so the tree under test is the tree the examples run on.
#
# ★★ THE HARNESS HOLDS THEM. Each declared value is a `gen.ci.examples` entry, so gen-harness's
# `gen-ci-examples` suite forces it under `deepSeq` (never `attrNames`, whose spine survives WHNF
# with every failing cell unforced), checks every nix-unit leaf in it, and holds the directory total.
#
# ★ THE STATED DOMAIN. `outputs` is applied with the inputs this flake carries — the library and
# nixpkgs' `lib` — and two examples take libraries it does not: `nest-traits` (gen-schema, gen-aspects,
# gen-algebra, gen-graph) and `sql-schema` (those plus gen-select, gen-dispatch, gen-bind). Reaching
# them from here would pin each of those libraries a second time, beside the pin in the example's own
# lock. They are EXCLUDED BY NAME, citing the row that owes their wiring, and the harness's totality
# cell (`gen-ci-examples`) reads the directory, so an example that is neither declared nor excluded
# is red the moment it appears.
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

  # The examples whose `tests` output is declared here, and the ones excluded with the reason above.
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
  gen.ci.examples = lib.genAttrs testsBearing (name: (outputsOf name).tests) // {
    # `demo` has no `tests` output: its top-level outputs ARE its demonstrations, each annotated
    # with the value it claims, so the whole output set is declared.
    demo = outputsOf "demo";
  };
  gen.ci.examplesExcluded = lib.genAttrs excluded (_: {
    row = "den-hoag-tyu25";
    reason = "its flake pins a published gen-scope and libraries this suite does not carry";
  });
}
