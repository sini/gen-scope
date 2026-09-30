# THE SHIPPED EXAMPLES, FORCED ON EVERY GATE.
#
# ★ WHY THIS FILE EXISTS. Each directory under `examples/` used to be a flake pinning
# `github:sini/gen-scope` in its own lock, so `nix eval "<example>#tests"` evaluated that example
# against ITS LOCK and never against this tree — the corpus drifted 137 commits behind the library it
# documents and nothing in the suite could see it (`den-hoag-5oag`). A library example now binds
# gen-scope as `import ../.. { }`, the standalone entry of the tree it ships in, and declares no input
# for it (`den-hoag-eu9do`), so its README command and this suite evaluate ONE expression over this
# tree; this file is what forces it on every gate.
#
# ★★ THE HARNESS HOLDS THEM. Each declared value is a `gen.ci.examples` entry, so gen-harness's
# `gen-ci-examples` suite forces it under `deepSeq` (never `attrNames`, whose spine survives WHNF
# with every failing cell unforced), checks every nix-unit leaf in it, and holds the directory total.
#
# ★ THE STATED DOMAIN. `outputs` is applied with the one input this flake supplies, nixpkgs' `lib`;
# the library is the example's own `import ../.. { }`. Two examples take libraries this flake does not
# carry, and pin a published gen-scope beside them: `nest-traits` (gen-schema, gen-aspects,
# gen-algebra, gen-graph) and `sql-schema` (those plus gen-select, gen-dispatch, gen-bind). Reaching
# them from here would pin each of those libraries a second time, beside the pin in the example's own
# lock. They are EXCLUDED BY NAME, citing the row that owes their wiring, and the harness's totality
# cell (`gen-ci-examples`) reads the directory, so an example that is neither declared nor excluded
# is red the moment it appears.
{ lib, ... }:
let
  examplesDir = ../../examples;

  # The inputs the example flakes' `outputs` formals bind. `nixpkgs.lib` is what every example reads
  # off that input; the parent is NOT supplied, since an `outputs` with `...` would swallow it unread.
  exampleInputs = {
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
