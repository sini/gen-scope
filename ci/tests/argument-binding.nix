# THE ARGUMENT-BINDING CONSTRUCTOR'S ADMITTING HALF (den-hoag-0cmbt U5, K1). Each key of the preimage
# separates two bindings that differ in it alone, so a constructor that dropped a key reds the arm
# naming it. The refusals — the closed route set and the definer rule — are message cells in
# `ci/tests-error.nix`'s `argument-binding-refusals`.
#
# R10 (the introducing scope, never the reaching one) is the CALLER's obligation and has no cell
# here: a constructor handed `scope` cannot tell the two apart, so `b "root" == b "root"` holds of a
# constructor that ignores every input. The cell that discriminates it walks the applying party's
# own scopes, in gen-demo.
{ genScope, ... }:
let
  b =
    scope:
    genScope.argumentBinding {
      inherit scope;
      name = "pkgs";
      supplyRoute = "specialArgs";
    };
  moduleArg =
    definer:
    genScope.argumentBinding {
      scope = "root";
      name = "pkgs";
      supplyRoute = "moduleArgs";
      inherit definer;
    };
in
{
  flake.tests.argument-binding = {
    # B-1
    test-the-scope-separates-bindings = {
      expr = b "host/h1" != b "host/h2";
      expected = true;
    };
    # B-2: an override is introduced by its own scope, so it is a new binding.
    test-an-overriding-scope-is-a-new-binding = {
      expr = b "group/g1" != b "root";
      expected = true;
    };
    # B-3
    test-the-route-separates-bindings = {
      expr = b "root" != moduleArg "/m.nix";
      expected = true;
    };
    test-the-definer-separates-bindings = {
      expr = moduleArg "/a.nix" != moduleArg "/b.nix";
      expected = true;
    };
    test-the-name-separates-bindings = {
      expr =
        b "root" != genScope.argumentBinding {
          scope = "root";
          name = "lib";
          supplyRoute = "specialArgs";
        };
      expected = true;
    };
    # `definer ? null`: an explicit null is the absent definer, not a fourth key.
    test-a-null-definer-is-no-definer = {
      expr =
        b "root" == genScope.argumentBinding {
          scope = "root";
          name = "pkgs";
          supplyRoute = "specialArgs";
          definer = null;
        };
      expected = true;
    };
    # The preimage is `{ scope; name; supplyRoute; }` under kind `argument-binding` through the one
    # authority, pinned to the digest the spec's prototype minted over gen-identity directly.
    test-the-identity-is-the-authoritys-mint = {
      expr = b "root";
      expected = "argument-binding:17ea51290d114ec95ee7457032a88384431e745e5c4630395932d684dfd9d7f3";
    };
  };
}
