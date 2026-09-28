# THE IDENTIFIER DOORS' ADMITTING HALF (den-hoag-bkdkg). The refusals are message cells in
# `ci/tests-error.nix`'s `identifier-door-refusals`; these are the same doors answering on an identifier,
# over the same fixture, so a guard that refused a string would go red here.
{ genScope, ... }:
let
  S = genScope;
  roots = S.buildRoots {
    parentGraph = S.edge {
      from = "b";
      to = "a";
    };
  };
  attributes = {
    x = self: id: 1;
    children =
      self: id:
      builtins.removeAttrs (builtins.intersectAttrs { b = 0; } roots.nodes) (
        if id == "a" then [ ] else [ "b" ]
      );
  };
  self = S.eval { } attributes roots;
  debug = S.evalDebug {
    parseParent = id: if id == "b" then "a" else null;
  } attributes roots;
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
    # The string guards live in the door bodies. The entry is positional (den-hoag-7gp66 P2, R7):
    # `mintStrata kinds emitters`, so its operands are its arity rather than a record's fields.
    test-mintStrata-takes-kinds-then-emitters = {
      expr = {
        waitsForEmitters = builtins.isFunction (S.mintStrata { });
        answers = builtins.isAttrs (S.mintStrata { } [ ]);
      };
      expected = {
        waitsForEmitters = true;
        answers = true;
      };
    };
  };
}
