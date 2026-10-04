{ lib, genScope, ... }:
let
  inherit (genScope) collectionAttr;

  # Helper: standard attributes block for neron tests.
  # Every graph needs children, imports, and the neron-based vals attribute.
  mkAttrs = roots: {
    children = self: id: lib.filterAttrs (_: n: n.parent == id) roots;
    imports = self: id: (self.node id).decls.__edges.I or [ ];
    marks = _: _: [ ];
    vals = collectionAttr { } "neron" (self: id: (self.node id).decls.val or null);
  };

  # --- Test 1: P-only chain (root → mid → leaf) ---
  pOnlyRoots = genScope.buildRoots {
    parentGraph = genScope.overlays [
      (genScope.edge {
        from = "leaf";
        to = "mid";
      })
      (genScope.edge {
        from = "mid";
        to = "root";
      })
    ];
    decls = {
      root.val = "root-val";
      mid.val = "mid-val";
      leaf.val = "leaf-val";
    };
    types = { };
  };
  pOnlyResult = genScope.eval {
    parseParent = id: (pOnlyRoots.nodes.${id} or { parent = null; }).parent;
  } (mkAttrs pOnlyRoots) pOnlyRoots;

  # --- Test 2: I-edge graph (leaf imports dep; leaf → root via P) ---
  iEdgeRoots = genScope.buildRoots {
    parentGraph = genScope.edge {
      from = "leaf";
      to = "root";
    };
    importGraph = genScope.edge {
      from = "leaf";
      to = "dep";
    };
    decls = {
      root.val = "root-val";
      leaf.val = "leaf-val";
      dep.val = "dep-val";
    };
    types = { };
  };
  iEdgeResult = genScope.eval {
    parseParent = id: (iEdgeRoots.nodes.${id} or { parent = null; }).parent;
  } (mkAttrs iEdgeRoots) iEdgeRoots;

  # --- Test 3: Diamond dedup (leaf imports a and b; a also imports b) ---
  diamondRoots = genScope.buildRoots {
    importGraph = genScope.overlays [
      (genScope.edge {
        from = "leaf";
        to = "a";
      })
      (genScope.edge {
        from = "leaf";
        to = "b";
      })
      (genScope.edge {
        from = "a";
        to = "b";
      })
    ];
    decls = {
      leaf.val = "leaf-val";
      a.val = "a-val";
      b.val = "b-val";
    };
    types = { };
  };
  diamondResult = genScope.eval {
    parseParent = id: (diamondRoots.nodes.${id} or { parent = null; }).parent;
  } (mkAttrs diamondRoots) diamondRoots;

  # --- Test 4: Parent has its own imports ---
  parentImportsRoots = genScope.buildRoots {
    parentGraph = genScope.edge {
      from = "leaf";
      to = "root";
    };
    importGraph = genScope.overlays [
      (genScope.edge {
        from = "leaf";
        to = "leaf-dep";
      })
      (genScope.edge {
        from = "root";
        to = "root-dep";
      })
    ];
    decls = {
      leaf.val = "leaf-val";
      leaf-dep.val = "leaf-dep-val";
      root.val = "root-val";
      root-dep.val = "root-dep-val";
    };
    types = { };
  };
  parentImportsResult = genScope.eval {
    parseParent = id: (parentImportsRoots.nodes.${id} or { parent = null; }).parent;
  } (mkAttrs parentImportsRoots) parentImportsRoots;

  # --- Test 5: Root only (P-only chain queried at root) ---
  # Reuse pOnlyRoots/pOnlyResult, query at root

  # --- Test 6: Cycle — a imports b, b imports a, both children of root ---
  cycleRoots = genScope.buildRoots {
    parentGraph = genScope.overlays [
      (genScope.edge {
        from = "a";
        to = "root";
      })
      (genScope.edge {
        from = "b";
        to = "root";
      })
    ];
    importGraph = genScope.overlays [
      (genScope.edge {
        from = "a";
        to = "b";
      })
      (genScope.edge {
        from = "b";
        to = "a";
      })
    ];
    decls = {
      root = {
        val = "root-val";
      };
      a = {
        val = "a-val";
      };
      b = {
        val = "b-val";
      };
    };
    types = { };
  };
  cycleResult = genScope.eval {
    parseParent = id: (cycleRoots.nodes.${id} or { parent = null; }).parent;
  } (mkAttrs cycleRoots) cycleRoots;

  # --- Test 7: Null skip — mid has no val field ---
  nullRoots = genScope.buildRoots {
    parentGraph = genScope.overlays [
      (genScope.edge {
        from = "leaf";
        to = "mid";
      })
      (genScope.edge {
        from = "mid";
        to = "root";
      })
    ];
    decls = {
      root = {
        val = "root-val";
      };
      mid = { };
      leaf = {
        val = "leaf-val";
      };
    };
    types = { };
  };
  nullResult = genScope.eval {
    parseParent = id: (nullRoots.nodes.${id} or { parent = null; }).parent;
  } (mkAttrs nullRoots) nullRoots;
in
{
  flake.tests."neron-traverse" = {
    test-p-only-chain = {
      expr = pOnlyResult.get "leaf" "vals";
      expected = [
        "leaf-val"
        "mid-val"
        "root-val"
      ];
    };

    test-i-edge-graph = {
      expr = iEdgeResult.get "leaf" "vals";
      expected = [
        "leaf-val"
        "dep-val"
        "root-val"
      ];
    };

    test-diamond-dedup = {
      expr = diamondResult.get "leaf" "vals";
      expected = [
        "leaf-val"
        "a-val"
        "b-val"
      ];
    };

    test-parent-has-imports = {
      expr = parentImportsResult.get "leaf" "vals";
      expected = [
        "leaf-val"
        "leaf-dep-val"
        "root-val"
        "root-dep-val"
      ];
    };

    test-root-only = {
      expr = pOnlyResult.get "root" "vals";
      expected = [ "root-val" ];
    };

    test-cycle-safe = {
      expr = cycleResult.get "a" "vals";
      expected = [
        "a-val"
        "b-val"
        "root-val"
      ];
    };

    test-null-extraction-skipped = {
      expr = nullResult.get "leaf" "vals";
      expected = [
        "leaf-val"
        "root-val"
      ];
    };
  };
}
