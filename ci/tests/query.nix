{ lib, genScope, ... }:
let
  inherit (genScope)
    query
    queryAll
    queryReverse
    ambiguous
    ;

  # Graph: a imports b, b imports c. Parent: a → root.
  roots = genScope.buildNodes {
    parentGraph = genScope.edge "a" "root";
    importGraph = genScope.overlays [
      (genScope.edge "a" "b")
      (genScope.edge "b" "c")
    ];
    decls = {
      root = {
        val = "from-root";
      };
      a = { };
      b = {
        val = "from-b";
      };
      c = {
        val = "from-c";
        extra = "c-extra";
      };
    };
    types = { };
  };

  result = genScope.eval {
    inherit roots;
    attributes = {
      children = self: id: lib.filterAttrs (_: n: n.parent == id) roots;
      imports = self: id: (self.node id).decls.__edges.I or [ ];
      resolved = query {
        dataFilter = node: node.decls.val or null;
      };
    };
    parseParent = id: (roots.${id} or { parent = null; }).parent;
  };

  resultTransitive = genScope.eval {
    inherit roots;
    attributes = {
      children = self: id: lib.filterAttrs (_: n: n.parent == id) roots;
      imports = self: id: (self.node id).decls.__edges.I or [ ];
      resolved = query {
        dataFilter = node: node.decls.val or null;
        transitiveImports = true;
      };
    };
    parseParent = id: (roots.${id} or { parent = null; }).parent;
  };

  resultAll = genScope.eval {
    inherit roots;
    attributes = {
      children = self: id: lib.filterAttrs (_: n: n.parent == id) roots;
      imports = self: id: (self.node id).decls.__edges.I or [ ];
      all-vals = queryAll {
        dataFilter = node: node.decls.val or null;
      };
    };
    parseParent = id: (roots.${id} or { parent = null; }).parent;
  };

  # Ambiguity: node imports two nodes with same key
  ambRoots = genScope.buildNodes {
    parentGraph = genScope.empty;
    importGraph = genScope.overlays [
      (genScope.edge "x" "y")
      (genScope.edge "x" "z")
    ];
    decls = {
      x = { };
      y = {
        val = "from-y";
      };
      z = {
        val = "from-z";
      };
    };
    types = { };
  };

  ambResult = genScope.eval {
    roots = ambRoots;
    attributes = {
      children = self: id: { };
      imports = self: id: (self.node id).decls.__edges.I or [ ];
      is-ambiguous = ambiguous {
        dataFilter = node: node.decls.val or null;
      };
    };
  };

  # Reverse (neededBy): b and c import a; d imports b.
  revRoots = genScope.buildNodes {
    parentGraph = genScope.empty;
    importGraph = genScope.overlays [
      (genScope.edge "b" "a")
      (genScope.edge "c" "a")
      (genScope.edge "d" "b")
    ];
    decls = {
      a = { };
      b = {
        tag = "B";
      };
      c = {
        tag = "C";
      };
      d = {
        tag = "D";
      };
    };
    types = { };
  };

  revResult = genScope.eval {
    roots = revRoots;
    attributes = {
      children = self: id: { };
      imports = self: id: (self.node id).decls.__edges.I or [ ];
      needed-by = queryReverse {
        dataFilter = node: node.decls.tag or null;
      };
      needed-by-trans = queryReverse {
        dataFilter = node: node.decls.tag or null;
        transitive = true;
      };
    };
  };
in
{
  flake.tests."query" = {
    test-query-finds-import = {
      expr = result.get "a" "resolved";
      expected = "from-b";
    };

    test-query-local-shadows = {
      expr = result.get "b" "resolved";
      expected = "from-b";
    };

    test-query-no-transitive-by-default = {
      # a imports b, b imports c; without transitiveImports, a sees b but not c
      expr = result.get "a" "resolved";
      expected = "from-b";
    };

    test-query-transitive-finds-deep = {
      # With transitive, a→b→c; b has val so it wins (import shadows parent)
      expr = resultTransitive.get "a" "resolved";
      expected = "from-b";
    };

    test-query-parent-fallback = {
      # root has val; a inherits from root when imports have it too, import wins
      expr = result.get "a" "resolved";
      expected = "from-b";
    };

    test-queryAll-collects-multiple = {
      # a: no local val. imports b (has val). parent root (has val).
      expr = builtins.length (resultAll.get "a" "all-vals");
      expected = 2;
    };

    test-queryAll-from-root = {
      expr = resultAll.get "root" "all-vals";
      expected = [ "from-root" ];
    };

    test-ambiguity-detected = {
      expr = ambResult.get "x" "is-ambiguous";
      expected = true;
    };

    # queryReverse (neededBy): a is imported by b and c (direct reverse gather)
    test-queryReverse-direct-importers = {
      expr = builtins.sort builtins.lessThan (revResult.get "a" "needed-by");
      expected = [
        "B"
        "C"
      ];
    };

    # transitive: b,c import a; d imports b -> {B,C,D}
    test-queryReverse-transitive = {
      expr = builtins.sort builtins.lessThan (revResult.get "a" "needed-by-trans");
      expected = [
        "B"
        "C"
        "D"
      ];
    };

    # a leaf that nobody imports has an empty reverse set
    test-queryReverse-no-importers = {
      expr = revResult.get "d" "needed-by";
      expected = [ ];
    };

    test-ambiguity-not-when-single = {
      expr = ambResult.get "y" "is-ambiguous";
      expected = false;
    };

    test-query-self-no-import-loop = {
      # c has no imports, should return its own val
      expr = result.get "c" "resolved";
      expected = "from-c";
    };
  };
}
