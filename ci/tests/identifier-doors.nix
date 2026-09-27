# THE IDENTIFIER DOORS' ADMITTING HALF (den-hoag-bkdkg). The refusals are message cells in
# `ci/tests-error.nix`'s `identifier-door-refusals`; these are the same doors answering on an identifier,
# over the same fixture, so a guard that refused a string would go red here.
{ genScope, ... }:
let
  S = genScope;
  roots = S.buildRoots { parentGraph = S.edge "b" "a"; };
  attributes = {
    x = self: id: 1;
    children =
      self: id:
      builtins.removeAttrs (builtins.intersectAttrs { b = 0; } roots.nodes) (
        if id == "a" then [ ] else [ "b" ]
      );
  };
  self = S.eval {
    scope = roots;
    inherit attributes;
  };
  debug = S.evalDebug {
    scope = roots;
    inherit attributes;
    parseParent = id: if id == "b" then "a" else null;
  };
in
{
  flake.tests.identifier-doors = {
    test-self-get-admits-an-identifier = {
      expr = self.get "b" "x";
      expected = 1;
    };
    test-evalDebug-get-admits-an-identifier = {
      expr = debug.get "b" "x";
      expected = 1;
    };
    test-evalDebug-node-admits-an-identifier = {
      expr = (debug.node "b").parent;
      expected = "a";
    };
    test-isAncestor-admits-identifiers = {
      expr = S.isAncestor self "a" "b";
      expected = true;
    };
    test-isDescendant-admits-identifiers = {
      expr = S.isDescendant self "b" "a";
      expected = true;
    };
    test-nodesByType-admits-a-kind-name = {
      expr = builtins.attrNames (S.nodesByType self "t");
      expected = [ ];
    };
    # The string guards live in the door bodies. The record check is the one wrapper at the export
    # (den-hoag-7gp66 P1, `lib/door.nix`), and it erases the native formals, so the published door's
    # fields are observed by what it does: each is required, and refused catchably when missing.
    test-mintStrata-requires-its-published-fields = {
      expr =
        map
          (
            f:
            (builtins.tryEval (
              S.mintStrata (
                builtins.removeAttrs {
                  emitters = [ ];
                  kinds = { };
                } [ f ]
              )
            )).success
          )
          [
            "emitters"
            "kinds"
          ];
      expected = [
        false
        false
      ];
    };
  };
}
