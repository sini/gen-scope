# gen-scope REPL — all exports in scope. Run: nix repl --impure --file ci/repl.nix
#
# The root declares only dependency formals, each defaulted from the root flake.lock, and never
# `lib`. So it is called with this entry's arguments minus `lib`: none under `nix repl --file`,
# where the root resolves its own pins, and the ci flake's own instances under `ci/tests/repl.nix`,
# which keeps that cell from fetching. `lib` rides beside the surface for convenience only.
{
  lib ? (builtins.getFlake "nixpkgs").lib,
  ...
}@args:
let
  genScope = import ./.. (removeAttrs args [ "lib" ]);
in
{ inherit lib genScope; } // genScope
