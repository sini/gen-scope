{ lib, genScope, ... }:
let
  inherit (genScope)
    shadow
    resolve
    inherit'
    inheritAll
    inheritSet
    ;

  # Build an eval over a parent chain/tree with ONE attribute under test, then read it.
  # Mirrors the inline fixtures below; shared only by the inheritSet cases.
  readAttr =
    {
      parentGraph,
      decls,
      attrName,
      attr,
      id,
    }:
    let
      roots = genScope.buildRoots { inherit parentGraph decls; };
      result = genScope.eval {
        scope = roots;
        attributes = {
          children = _self: i: lib.filterAttrs (_: n: n.parent == i) roots.nodes;
          imports = _self: _i: [ ];
          ${attrName} = attr;
        };
        parseParent = i: (roots.nodes.${i} or { parent = null; }).parent;
      };
    in
    result.get id attrName;
in
{
  flake.tests."resolve" = {
    test-shadow-inner-wins = {
      expr =
        shadow
          {
            a = 1;
            b = 2;
          }
          {
            a = 99;
            c = 3;
          };
      expected = {
        a = 1;
        b = 2;
        c = 3;
      };
    };

    test-shadow-disjoint = {
      expr = shadow { x = 1; } { y = 2; };
      expected = {
        x = 1;
        y = 2;
      };
    };

    test-shadow-identical = {
      expr = shadow { a = 1; } { a = 1; };
      expected = {
        a = 1;
      };
    };

    test-shadow-empty-inner = {
      expr = shadow { } { a = 1; };
      expected = {
        a = 1;
      };
    };

    test-shadow-empty-outer = {
      expr = shadow { a = 1; } { };
      expected = {
        a = 1;
      };
    };

    test-resolve-local-wins = {
      expr = resolve {
        local = "L";
        imported = "I";
        inherited = "P";
      };
      expected = "L";
    };

    test-resolve-imported-wins-over-inherited = {
      expr = resolve {
        local = null;
        imported = "I";
        inherited = "P";
      };
      expected = "I";
    };

    test-resolve-inherited-fallback = {
      expr = resolve {
        local = null;
        imported = null;
        inherited = "P";
      };
      expected = "P";
    };

    test-resolve-all-null = {
      expr = resolve {
        local = null;
        imported = null;
        inherited = null;
      };
      expected = null;
    };

    test-resolve-specificity-override = {
      expr = resolve {
        local = null;
        imported = "I";
        inherited = "P";
        localShadowsImport = false;
        importShadowsParent = false;
      };
      expected = "I";
    };

    test-inherit-walks-parent =
      let
        roots = genScope.buildRoots {
          parentGraph = genScope.edge "child" "parent";
          importGraph = genScope.empty;
          decls = {
            parent = {
              val = "found";
            };
            child = { };
          };
          types = { };
        };
        result = genScope.eval {
          scope = roots;
          attributes = {
            children = self: id: lib.filterAttrs (_: n: n.parent == id) roots.nodes;
            imports = self: id: [ ];
            resolved-val = inherit' {
              resolve = node: node.decls.val or null;
            };
          };
          parseParent = id: (roots.nodes.${id} or { parent = null; }).parent;
        };
      in
      {
        expr = result.get "child" "resolved-val";
        expected = "found";
      };

    test-inherit-stops-at-first =
      let
        roots = genScope.buildRoots {
          parentGraph = genScope.overlays [
            (genScope.edge "c" "b")
            (genScope.edge "b" "a")
          ];
          importGraph = genScope.empty;
          decls = {
            a = {
              val = "root";
            };
            b = {
              val = "mid";
            };
            c = { };
          };
          types = { };
        };
        result = genScope.eval {
          scope = roots;
          attributes = {
            children = self: id: lib.filterAttrs (_: n: n.parent == id) roots.nodes;
            imports = self: id: [ ];
            resolved-val = inherit' {
              resolve = node: node.decls.val or null;
            };
          };
          parseParent = id: (roots.nodes.${id} or { parent = null; }).parent;
        };
      in
      {
        expr = result.get "c" "resolved-val";
        expected = "mid";
      };

    test-inheritAll-accumulates =
      let
        roots = genScope.buildRoots {
          parentGraph = genScope.overlays [
            (genScope.edge "c" "b")
            (genScope.edge "b" "a")
          ];
          importGraph = genScope.empty;
          decls = {
            a = {
              tags = [ "root" ];
            };
            b = {
              tags = [ "mid" ];
            };
            c = {
              tags = [ "leaf" ];
            };
          };
          types = { };
        };
        result = genScope.eval {
          scope = roots;
          attributes = {
            children = self: id: lib.filterAttrs (_: n: n.parent == id) roots.nodes;
            imports = self: id: [ ];
            all-tags = inheritAll {
              extract = node: node.decls.tags or null;
            };
          };
          parseParent = id: (roots.nodes.${id} or { parent = null; }).parent;
        };
      in
      {
        expr = result.get "c" "all-tags";
        expected = [
          "leaf"
          "mid"
          "root"
        ];
      };

    # inheritSet: set-discipline sibling of inheritAll — self ∪ ancestors, deduped.

    # Leaf sees every ancestor's contribution, unioned nearest-first with duplicates
    # removed (b re-declares "p1", already contributed by a — it appears once).
    test-inheritSet-accumulates-deduped = {
      expr = readAttr {
        parentGraph = genScope.overlays [
          (genScope.edge "c" "b")
          (genScope.edge "b" "a")
        ];
        decls = {
          a.supp = [ "p1" ];
          b.supp = [
            "p2"
            "p1"
          ];
          c.supp = [ "p3" ];
        };
        attrName = "supp-set";
        attr = inheritSet { extract = node: node.decls.supp or null; };
        id = "c";
      };
      expected = [
        "p3"
        "p2"
        "p1"
      ];
    };

    # Where inheritAll keeps the duplicate (ordered-list discipline), inheritSet drops
    # it (set discipline). Same fixture, both attributes, side by side.
    test-inheritSet-dedups-what-inheritAll-keeps = {
      expr =
        let
          parentGraph = genScope.overlays [
            (genScope.edge "c" "b")
            (genScope.edge "b" "a")
          ];
          decls = {
            a.supp = [ "p1" ];
            b.supp = [
              "p2"
              "p1"
            ];
            c.supp = [ "p3" ];
          };
          extract = node: node.decls.supp or null;
        in
        {
          viaAll = readAttr {
            inherit parentGraph decls;
            attrName = "all";
            attr = inheritAll { inherit extract; };
            id = "c";
          };
          viaSet = readAttr {
            inherit parentGraph decls;
            attrName = "set";
            attr = inheritSet { inherit extract; };
            id = "c";
          };
        };
      expected = {
        viaAll = [
          "p3"
          "p2"
          "p1"
          "p1"
        ];
        viaSet = [
          "p3"
          "p2"
          "p1"
        ];
      };
    };

    # Siblings are isolated: c2 accumulates only b and a, never c1's contribution.
    test-inheritSet-siblings-isolated = {
      expr = readAttr {
        parentGraph = genScope.overlays [
          (genScope.edge "c1" "b")
          (genScope.edge "c2" "b")
          (genScope.edge "b" "a")
        ];
        decls = {
          a.supp = [ "pa" ];
          b.supp = [ "pb" ];
          c1.supp = [ "pc1" ];
          c2.supp = [ ];
        };
        attrName = "supp-set";
        attr = inheritSet { extract = node: node.decls.supp or null; };
        id = "c2";
      };
      expected = [
        "pb"
        "pa"
      ];
    };

    # A root's set is its OWN contribution only, deduped within the node.
    test-inheritSet-root-own-deduped = {
      expr = readAttr {
        parentGraph = genScope.vertex "a";
        decls = {
          a.supp = [
            "x"
            "x"
            "y"
          ];
        };
        attrName = "supp-set";
        attr = inheritSet { extract = node: node.decls.supp or null; };
        id = "a";
      };
      expected = [
        "x"
        "y"
      ];
    };

    # Demand-laziness: an off-path sibling whose extract THROWS is never forced when
    # accumulating a different branch (the walk touches only the parent chain).
    test-inheritSet-lazy-skips-offpath = {
      expr = readAttr {
        parentGraph = genScope.overlays [
          (genScope.edge "c" "b")
          (genScope.edge "b" "a")
          (genScope.edge "d" "a")
        ];
        decls = {
          a.supp = [ "pa" ];
          b.supp = [ "pb" ];
          c.supp = [ "pc" ];
          d.supp = throw "off-path node must not be forced";
        };
        attrName = "supp-set";
        attr = inheritSet { extract = node: node.decls.supp or null; };
        id = "c";
      };
      expected = [
        "pc"
        "pb"
        "pa"
      ];
    };

    # Custom element equality: dedup by first character collapses "a1"/"a2" to the
    # nearest ("a2"); exercises the optional `eq` (Sloane circular/subtypeOf idiom).
    test-inheritSet-custom-eq = {
      expr = readAttr {
        parentGraph = genScope.overlays [
          (genScope.edge "c" "b")
          (genScope.edge "b" "a")
        ];
        decls = {
          a.supp = [ "a1" ];
          b.supp = [ "a2" ];
          c.supp = [ "c1" ];
        };
        attrName = "supp-set";
        attr = inheritSet {
          extract = node: node.decls.supp or null;
          eq = x: y: builtins.substring 0 1 x == builtins.substring 0 1 y;
        };
        id = "c";
      };
      expected = [
        "c1"
        "a2"
      ];
    };

    # No contributions anywhere along the chain ⇒ empty set.
    test-inheritSet-empty = {
      expr = readAttr {
        parentGraph = genScope.edge "b" "a";
        decls = {
          a = { };
          b = { };
        };
        attrName = "supp-set";
        attr = inheritSet { extract = node: node.decls.supp or null; };
        id = "b";
      };
      expected = [ ];
    };
  };
}
