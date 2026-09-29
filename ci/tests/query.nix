{ lib, genScope, ... }:
let
  inherit (genScope)
    queryReverse
    collect
    collectByType
    ;

  # The retired `query`, `queryAll` and `ambiguous`, read through the one calculus (den-hoag-gayc
  # U1c): Néron's D < I < P is `neron` under mode "visible"; the identify-all reading is mode
  # "witnesses"; an ambiguity is more than one DISTINCT declaring node among the witnesses (D10).
  transitiveWf = genScope.wellFormed {
    alphabet = [
      "parent"
      "imports"
    ];
    expression = "parent* imports*";
  };
  query =
    wf: dataFilter: self: id:
    (genScope.resolve {
      inherit wf dataFilter;
      inherit (genScope.neron) order;
      mode = "visible";
      groupBy = _: "val";
    } self id).single
      "val";
  witnesses =
    dataFilter: self: id:
    (genScope.resolve {
      inherit (genScope.neron) wf;
      inherit dataFilter;
      mode = "witnesses";
    } self id).answers;
  queryAll =
    dataFilter: self: id:
    map (a: a.value) (witnesses dataFilter self id);
  ambiguous =
    dataFilter: self: id:
    builtins.length (lib.unique (map (a: a.node) (witnesses dataFilter self id))) > 1;

  # Graph: a imports b, b imports c. Parent: a → root.
  roots = genScope.buildRoots {
    parentGraph = genScope.edge {
      from = "a";
      to = "root";
    };
    importGraph = genScope.overlays [
      (genScope.edge {
        from = "a";
        to = "b";
      })
      (genScope.edge {
        from = "b";
        to = "c";
      })
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

  result =
    genScope.eval
      {
        parseParent = id: (roots.nodes.${id} or { parent = null; }).parent;
      }
      {
        children = self: id: lib.filterAttrs (_: n: n.parent == id) roots.nodes;
        imports = self: id: (self.node id).decls.__edges.I or [ ];
        marks = _: _: [ ];
        resolved = query genScope.neron.wf (node: node.decls.val or null);
      }
      roots;

  resultTransitive =
    genScope.eval
      {
        parseParent = id: (roots.nodes.${id} or { parent = null; }).parent;
      }
      {
        children = self: id: lib.filterAttrs (_: n: n.parent == id) roots.nodes;
        imports = self: id: (self.node id).decls.__edges.I or [ ];
        marks = _: _: [ ];
        resolved = query transitiveWf (node: node.decls.val or null);
      }
      roots;

  resultAll =
    genScope.eval
      {
        parseParent = id: (roots.nodes.${id} or { parent = null; }).parent;
      }
      {
        children = self: id: lib.filterAttrs (_: n: n.parent == id) roots.nodes;
        imports = self: id: (self.node id).decls.__edges.I or [ ];
        marks = _: _: [ ];
        all-vals = queryAll (node: node.decls.val or null);
      }
      roots;

  # Ambiguity: node imports two nodes with same key
  ambRoots = genScope.buildRoots {
    parentGraph = genScope.empty;
    importGraph = genScope.overlays [
      (genScope.edge {
        from = "x";
        to = "y";
      })
      (genScope.edge {
        from = "x";
        to = "z";
      })
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

  ambResult = genScope.eval { } {
    children = self: id: { };
    imports = self: id: (self.node id).decls.__edges.I or [ ];
    marks = _: _: [ ];
    is-ambiguous = ambiguous (node: node.decls.val or null);
  } ambRoots;

  # Reverse (neededBy): b and c import a; d imports b.
  revRoots = genScope.buildRoots {
    parentGraph = genScope.empty;
    importGraph = genScope.overlays [
      (genScope.edge {
        from = "b";
        to = "a";
      })
      (genScope.edge {
        from = "c";
        to = "a";
      })
      (genScope.edge {
        from = "d";
        to = "b";
      })
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

  revResult = genScope.eval { } {
    children = self: id: { };
    imports = self: id: (self.node id).decls.__edges.I or [ ];
    needed-by = queryReverse { } (node: node.decls.tag or null);
    needed-by-trans = queryReverse {
      transitive = true;
    } (node: node.decls.tag or null);
  } revRoots;

  # NESTED reverse fixture — the one on which the materialization walk and the codepoint
  # key order DISAGREE, which is what makes the order tests below discriminating.
  #
  # `r` and `t` LEAD THE DECLARED ORDER; `mid` is `r`'s child and `alpha` is `mid`'s child, so the
  # walk reaches both by descending before their own entries in that order come up, and
  # first-occurrence dedup keeps the descent positions. The walk therefore emits
  # [ r mid alpha t ] while `attrNames allNodes` is [ alpha mid r t ]. Both `mid` and
  # `alpha` import `t`, and they are the pair whose relative order the two readings flip.
  # `revRoots` above cannot serve here either, but no longer for the reason it once could not:
  # its nodes are all roots, so the walk IS the root enumeration — and the root enumeration is now
  # the DECLARED vertex order, which for that fixture is [ b a c d ] against a codepoint
  # [ a b c d ]. It discriminates on the root axis; `nestedNodes` is what discriminates on the
  # descent axis, which is what this fixture is for.
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

  nestedResult =
    genScope.eval
      {
        parseParent = id: nestedNodes.${id}.parent or null;
      }
      {
        children = _self: id: lib.filterAttrs (_: n: n.parent == id) nestedNodes;
        imports = self: id: (self.node id).decls.imports or [ ];
        needed-by = queryReverse { } (node: node.decls.tag or null);
        needed-by-trans = queryReverse {
          transitive = true;
        } (node: node.decls.tag or null);
      }
      {
        nodes = nestedNodes;
        # A hand-built scope states its own order at the site. `children` selects among the nodes
        # the scope carries, so the contained pair is registered here too and what distinguishes
        # them from `r` and `t` is their POSITION in the declared order, not their absence from it.
        nodeOrder = [
          "r"
          "t"
          "mid"
          "alpha"
        ];
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

    # ★ RE-EXPECTED UNDER THE CALCULUS (den-hoag-gayc U1c, T6). `b` and `c` both declare `val`, and
    # under transitive imports `a` reaches `b` along `imports` and `c` along `imports imports`. The
    # retired `query` refused the pair as an AMBIGUITY; the visibility order ranks `$` before
    # `imports`, so the one-step path is strictly more specific and `b` shadows `c`. An ambiguity is
    # two origins in the MINIMAL set, and this minimal set has one. The two cells that bracket this
    # one read the NON-transitive `result`, where `a` sees only `b`.
    test-query-transitive-takes-the-nearer-of-two-declarers = {
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

    # ★ RE-PINNED AND RENAMED, so the change is legible in the history: this fixture's
    # walk and key order NO LONGER COINCIDE. `revRoots` is built by the constructor, whose vertex
    # order is now the declared one, and its declaration is [ b a c d ] where its key order is
    # [ a b c d ]. What the cell still shows is the property that matters here — the ANSWER is
    # unchanged under the move, because every node of this fixture is a root with no children, so
    # nothing the query walks depends on the pair whose order flipped.
    test-queryReverse-flat-fixture-orders-diverge = {
      expr = {
        walk = revResult.allNodeIds;
        keys = builtins.attrNames revResult.allNodes;
        answer = revResult.get "a" "needed-by";
      };
      expected = {
        walk = [
          "b"
          "a"
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

    # ── collect / collectByType answer in materialization order ──
    # The SAME undeclared-order defect `queryReverse` had one surface over: `collect`
    # enumerated `self.allNodes` via `attrNames`, discarding the walk order the same way.
    # `nestedResult`'s premise (walk `[r mid alpha t]` vs keys `[alpha mid r t]`) is already
    # asserted above by `test-nested-walk-order-differs-from-key-order`; these cells reuse
    # that fixture rather than building a second one.

    # Unfiltered `collect` answers in `allNodeIds` order directly — codepoint order would
    # give `[alpha mid r t]`.
    test-collect-discovery-order = {
      expr = collect { } (_self: id: [ id ]) nestedResult;
      expected = [
        "r"
        "mid"
        "alpha"
        "t"
      ];
    };

    # THE discriminator. `mid` and `alpha` are both type "node"; discovery order reaches
    # `mid` first (it is `r`'s child, `alpha` sits below it), codepoint key order reaches
    # `alpha` first. `collectByType` delegates to `collect`, so it inherits the same order.
    test-collectByType-discovery-order = {
      expr = collectByType "node" (_self: id: [ id ]) nestedResult;
      expected = [
        "mid"
        "alpha"
      ];
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
