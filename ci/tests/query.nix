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

  # NESTED reverse fixture — the one on which the materialization walk and the codepoint
  # key order DISAGREE, which is what makes the order tests below discriminating.
  #
  # `r` and `t` are the roots; `mid` is `r`'s child and `alpha` is `mid`'s child, so neither
  # is a root and the walk reaches them only by descending. The walk therefore emits
  # [ r mid alpha t ] while `attrNames allNodes` is [ alpha mid r t ]. Both `mid` and
  # `alpha` import `t`, and they are the pair whose relative order the two readings flip.
  # `revRoots` above cannot serve here: every one of its nodes is a root with no children,
  # so its walk order IS its codepoint order and it agrees under either reading.
  nestedNodes = {
    r = {
      id = "r";
      type = "root";
      parent = null;
      decls = { };
    };
    t = {
      id = "t";
      type = "target";
      parent = null;
      decls = { };
    };
    mid = {
      id = "mid";
      type = "node";
      parent = "r";
      decls = {
        tag = "M";
        imports = [ "t" ];
      };
    };
    alpha = {
      id = "alpha";
      type = "node";
      parent = "mid";
      decls = {
        tag = "A";
        imports = [
          "t"
          "mid"
        ];
      };
    };
  };

  nestedResult = genScope.eval {
    roots = {
      inherit (nestedNodes) r t;
    };
    attributes = {
      children = self: id: lib.filterAttrs (_: n: n.parent == id) nestedNodes;
      imports = self: id: (self.node id).decls.imports or [ ];
      needed-by = queryReverse {
        dataFilter = node: node.decls.tag or null;
      };
      needed-by-trans = queryReverse {
        dataFilter = node: node.decls.tag or null;
        transitive = true;
      };
    };
    parseParent = id: nestedNodes.${id}.parent or null;
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

    # ── queryReverse answers in reverse-walk discovery order ──

    # The fixture's PREMISE, asserted rather than assumed: on `nestedResult` the
    # materialization walk and the codepoint key order are different lists. A fixture
    # where they coincide cannot tell a pinned order from a lucky one, so if this pair ever
    # becomes equal the two order tests below stop discriminating and this test says so.
    test-nested-walk-order-differs-from-key-order = {
      expr = {
        walk = nestedResult.allNodeIds;
        keys = builtins.attrNames nestedResult.allNodes;
      };
      expected = {
        walk = [
          "r"
          "mid"
          "alpha"
          "t"
        ];
        keys = [
          "alpha"
          "mid"
          "r"
          "t"
        ];
      };
    };

    # THE discriminator. `mid` and `alpha` both import `t`. Discovery order reaches `mid`
    # first (it is `r`'s child, and `alpha` sits below it); codepoint key order reaches
    # `alpha` first. The answer is discovery order.
    test-queryReverse-discovery-order = {
      expr = nestedResult.get "t" "needed-by";
      expected = [
        "M"
        "A"
      ];
    };

    # Transitive: the same seeding order, and `alpha` contributes TWICE — once as a direct
    # importer of `t`, once as an importer of `mid`. A reverse gather counts contributions,
    # so the repeat is kept rather than silently collapsed.
    test-queryReverse-discovery-order-transitive = {
      expr = nestedResult.get "t" "needed-by-trans";
      expected = [
        "M"
        "A"
        "A"
      ];
    };

    # CONTROL, same suite: a fixture whose walk order and key order COINCIDE answers the
    # same list under either reading. Every node of `revRoots` is a root with no children,
    # so its walk is its root enumeration — codepoint order. This is the case the pinned order
    # cannot be observed in, and it is why the discriminator needs `nestedResult`.
    test-queryReverse-flat-fixture-orders-coincide = {
      expr = {
        walk = revResult.allNodeIds;
        keys = builtins.attrNames revResult.allNodes;
        answer = revResult.get "a" "needed-by";
      };
      expected = {
        walk = [
          "a"
          "b"
          "c"
          "d"
        ];
        keys = [
          "a"
          "b"
          "c"
          "d"
        ];
        answer = [
          "B"
          "C"
        ];
      };
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
