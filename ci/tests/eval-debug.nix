{ lib, genScope, ... }:
let
  inherit (genScope) evalDebug;

  # Simple case: no cycles
  scope = genScope.buildRoots {
    parentGraph = genScope.vertex "a";
    importGraph = genScope.empty;
    decls = {
      a = {
        val = 42;
      };
    };
    types = { };
  };

  debugResult = evalDebug {
    inherit scope;
    attributes = {
      children = self: id: { };
      imports = self: id: [ ];
      value = self: id: (self.node id).decls.val or 0;
    };
    parseParent = _: null;
  };

  # Cycle case: a.x depends on a.y depends on a.x
  cycleRoots = genScope.buildRoots {
    parentGraph = genScope.vertex "a";
    importGraph = genScope.empty;
    decls = {
      a = { };
    };
    types = { };
  };

  cycleResult = evalDebug {
    scope = cycleRoots;
    attributes = {
      children = self: id: { };
      imports = self: id: [ ];
      x = self: id: self.get id "y";
      y = self: id: self.get id "x";
    };
    parseParent = _: null;
  };

  # Indirect cycle: a.p → b.q → a.p
  indirectRoots = genScope.buildRoots {
    parentGraph = genScope.vertices [
      "a"
      "b"
    ];
    importGraph = genScope.empty;
    decls = {
      a = { };
      b = { };
    };
    types = { };
  };

  indirectResult = evalDebug {
    scope = indirectRoots;
    attributes = {
      children = self: id: { };
      imports = self: id: [ ];
      p = self: id: self.get "b" "q";
      q = self: id: self.get "a" "p";
    };
    parseParent = _: null;
  };
in
{
  flake.tests."eval-debug" = {
    test-no-cycle-works = {
      expr = debugResult.get "a" "value";
      expected = 42;
    };

    test-direct-cycle-throws = {
      expr = builtins.tryEval (cycleResult.get "a" "x");
      expected = {
        success = false;
        value = false;
      };
    };

    test-indirect-cycle-throws = {
      expr = builtins.tryEval (indirectResult.get "a" "p");
      expected = {
        success = false;
        value = false;
      };
    };

    test-unknown-attr-throws = {
      expr = builtins.tryEval (debugResult.get "a" "nope");
      expected = {
        success = false;
        value = false;
      };
    };

    test-node-resolution = {
      expr = (debugResult.node "a").id;
      expected = "a";
    };

    # evalDebug materializes nothing, so the ordered enumeration refuses BY NAME alongside
    # `allNodes`. Without the entry a caller would meet an `attribute missing` error that
    # tryEval cannot catch and that names neither the record nor the reason.
    test-allNodeIds-refuses = {
      expr = builtins.tryEval debugResult.allNodeIds;
      expected = {
        success = false;
        value = false;
      };
    };
  };

  # THE TRACE AS A RETURNED VALUE. The read recording used to exist only as text inside a
  # cycle throw; it is now a value the caller receives, readable WITHOUT forcing the value it
  # accompanies. That is what makes the dynamic recording comparable against the static
  # structural derivation at all — while it lived in a throw message there was nothing to
  # compare.
  flake.tests."eval-debug-trace" = {
    test-accessor-trace-starts-empty = {
      expr = debugResult.trace;
      expected = [ ];
    };
    test-traced-read-answers-value-and-path = {
      expr = debugResult.getTraced "a" "value";
      expected = {
        value = 42;
        trace = [ "a.value" ];
      };
    };
    # The path is available even where the value is not — the case the throw message used to
    # be the only carrier for.
    test-cycle-trace-is-readable-without-forcing-the-value = {
      expr = (cycleResult.getTraced "a" "x").trace;
      expected = [ "a.x" ];
    };
    test-cycle-value-still-throws = {
      expr = builtins.tryEval (cycleResult.getTraced "a" "x").value;
      expected = {
        success = false;
        value = false;
      };
    };
    test-unknown-attribute-trace-is-readable = {
      expr = (debugResult.getTraced "a" "nope").trace;
      expected = [ "a.nope" ];
    };
    # The path deepens through the reads an attribute makes: `p` on `a` reads `q` on `b`,
    # which reads `p` on `a` again — the indirect cycle, recorded in order.
    test-nested-reads-extend-the-path = {
      expr =
        let
          r = builtins.tryEval (indirectResult.getTraced "a" "p").value;
        in
        [
          (indirectResult.getTraced "a" "p").trace
          r.success
        ];
      expected = [
        [ "a.p" ]
        false
      ];
    };
    # `get` is `getTraced` without the path, so the two cannot drift apart.
    test-get-agrees-with-traced-read = {
      expr = debugResult.get "a" "value" == (debugResult.getTraced "a" "value").value;
      expected = true;
    };
  };
}
