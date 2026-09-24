# The repl entry (`ci/repl.nix`, the harness `repl` command's file) loads, and loads exactly the
# library surface plus `lib` and `genScope`. Nothing else in the suite reaches that file, which is
# how it came to call the nullary root with an argument it never declared (den-hoag-s34cm).
{
  lib,
  genScope,
  genPreludeLib,
  genGraph,
  genIdentity,
  ...
}:
{
  flake.tests.repl.test-entry-loads-the-surface = {
    expr = builtins.attrNames (
      import ../repl.nix {
        inherit lib;
        prelude = genPreludeLib;
        graph = genGraph;
        identity = genIdentity;
      }
    );
    expected = builtins.attrNames ({ inherit lib genScope; } // genScope);
  };
}
