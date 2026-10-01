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
# carry: `nest-traits` (gen-schema, gen-aspects, gen-algebra, gen-graph) and `sql-schema` (those plus
# gen-select, gen-dispatch, gen-bind), whose own inputs pin gen-scope again. They are INTEGRATION
# examples: their locks are not committed (one anchored `/examples/<d>/flake.lock` line each in the
# root `.gitignore`), and `relock` locks each fresh in a scratch copy and forces its `tests` there,
# with every gen-scope node in that lock replaced by this tree (`exampleAtOwnLock`, den-hoag-tyu25).
# This suite holds that their locks stay uncommitted; the harness's totality cell reads the directory,
# so an example that is not declared is red the moment it appears.
{ lib, exampleAtOwnLock, ... }:
let
  examplesDir = ../../examples;

  # The inputs the example flakes' `outputs` formals bind. `nixpkgs.lib` is what every example reads
  # off that input; the parent is NOT supplied, since an `outputs` with `...` would swallow it unread.
  exampleInputs = {
    nixpkgs.lib = lib;
  };

  outputsOf = name: (import (examplesDir + "/${name}/flake.nix")).outputs exampleInputs;

  # The library examples whose `tests` output is declared here.
  testsBearing = [
    "config-cascade"
    "dep-resolver"
    "feature-flags"
    "module-resolver"
    "nix-config-acl"
    "rbac"
    "type-checker"
  ];
  # The integration examples, forced by `relock` over the working tree.
  integration = [
    "nest-traits"
    "sql-schema"
  ];
in
{
  gen.ci.examples =
    lib.genAttrs testsBearing (name: (outputsOf name).tests)
    // {
      # `demo` has no `tests` output: its top-level outputs ARE its demonstrations, each annotated
      # with the value it claims, so the whole output set is declared.
      demo = outputsOf "demo";
    }
    // lib.genAttrs integration (name: exampleAtOwnLock name (flake: flake.tests));
}
