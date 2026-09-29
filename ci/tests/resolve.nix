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
      result =
        genScope.eval
          {
            parseParent = i: (roots.nodes.${i} or { parent = null; }).parent;
          }
          {
            children = _self: i: lib.filterAttrs (_: n: n.parent == i) roots.nodes;
            imports = _self: _i: [ ];
            ${attrName} = attr;
          }
          roots;
    in
    result.get id attrName;

  # The retired D < I < P selector's cells, read through the calculus: `c` declares the local value,
  # `m` (which `c` imports) the imported one and `p` (`c`'s parent) the inherited one. The selection
  # is `neron.order` under mode "visible", and the answer is the group's `single`.
  selected =
    {
      local ? null,
      imported ? null,
      inherited ? null,
      order ? genScope.neron.order,
    }:
    let
      roots = genScope.buildRoots {
        parentGraph = genScope.overlays [
          (genScope.edge {
            from = "c";
            to = "p";
          })
          (genScope.vertex "m")
        ];
        importGraph = genScope.edge {
          from = "c";
          to = "m";
        };
        decls = {
          c.x = local;
          m.x = imported;
          p.x = inherited;
        };
      };
      ev =
        genScope.eval
          {
            parseParent = i: (roots.nodes.${i} or { parent = null; }).parent;
          }
          {
            children = _self: i: lib.filterAttrs (_: n: n.parent == i) roots.nodes;
            imports = self: i: (self.node i).decls.__edges.I or [ ];
            marks = _: _: [ ];
          }
          roots;
    in
    (resolve (
      genScope.neron
      // {
        mode = "visible";
        inherit order;
        dataFilter = n: n.decls.x or null;
        groupBy = _: "x";
      }
    ) ev "c").single
      "x";
in
{
  flake.tests."resolve" = {
    test-shadow-inner-wins = {
      expr = shadow {
        inner = {
          a = 1;
          b = 2;
        };
        outer = {
          a = 99;
          c = 3;
        };
      };
      expected = {
        a = 1;
        b = 2;
        c = 3;
      };
    };

    test-shadow-disjoint = {
      expr = shadow {
        inner = {
          x = 1;
        };
        outer = {
          y = 2;
        };
      };
      expected = {
        x = 1;
        y = 2;
      };
    };

    test-shadow-identical = {
      expr = shadow {
        inner = {
          a = 1;
        };
        outer = {
          a = 1;
        };
      };
      expected = {
        a = 1;
      };
    };

    test-shadow-empty-inner = {
      expr = shadow {
        inner = { };
        outer = {
          a = 1;
        };
      };
      expected = {
        a = 1;
      };
    };

    test-shadow-empty-outer = {
      expr = shadow {
        inner = {
          a = 1;
        };
        outer = { };
      };
      expected = {
        a = 1;
      };
    };

    test-resolve-local-wins = {
      expr = selected {
        local = "L";
        imported = "I";
        inherited = "P";
      };
      expected = "L";
    };

    test-resolve-imported-wins-over-inherited = {
      expr = selected {
        imported = "I";
        inherited = "P";
      };
      expected = "I";
    };

    test-resolve-inherited-fallback = {
      expr = selected {
        inherited = "P";
      };
      expected = "P";
    };

    test-resolve-all-null = {
      expr = selected { };
      expected = null;
    };

    test-resolve-specificity-override = {
      # The retired selector's `localShadowsImport = false` row as an order: `imports` < `$` <
      # `parent`, through an empty middle rank.
      expr = selected {
        imported = "I";
        inherited = "P";
        order = genScope.labelOrder {
          alphabet = [
            "parent"
            "imports"
          ];
          layers = [
            [ "imports" ]
            [ ]
            [ "parent" ]
          ];
          endOfPath = 1;
        };
      };
      expected = "I";
    };

    test-inherit-walks-parent =
      let
        roots = genScope.buildRoots {
          parentGraph = genScope.edge {
            from = "child";
            to = "parent";
          };
          importGraph = genScope.empty;
          decls = {
            parent = {
              val = "found";
            };
            child = { };
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
              imports = self: id: [ ];
              resolved-val = inherit' { } (node: node.decls.val or null);
            }
            roots;
      in
      {
        expr = result.get "child" "resolved-val";
        expected = "found";
      };

    test-inherit-stops-at-first =
      let
        roots = genScope.buildRoots {
          parentGraph = genScope.overlays [
            (genScope.edge {
              from = "c";
              to = "b";
            })
            (genScope.edge {
              from = "b";
              to = "a";
            })
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
        result =
          genScope.eval
            {
              parseParent = id: (roots.nodes.${id} or { parent = null; }).parent;
            }
            {
              children = self: id: lib.filterAttrs (_: n: n.parent == id) roots.nodes;
              imports = self: id: [ ];
              resolved-val = inherit' { } (node: node.decls.val or null);
            }
            roots;
      in
      {
        expr = result.get "c" "resolved-val";
        expected = "mid";
      };

    test-inheritAll-accumulates =
      let
        roots = genScope.buildRoots {
          parentGraph = genScope.overlays [
            (genScope.edge {
              from = "c";
              to = "b";
            })
            (genScope.edge {
              from = "b";
              to = "a";
            })
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
        result =
          genScope.eval
            {
              parseParent = id: (roots.nodes.${id} or { parent = null; }).parent;
            }
            {
              children = self: id: lib.filterAttrs (_: n: n.parent == id) roots.nodes;
              imports = self: id: [ ];
              all-tags = inheritAll { } (node: node.decls.tags or null);
            }
            roots;
      in
      {
        expr = result.get "c" "all-tags";
        expected = [
          "leaf"
          "mid"
          "root"
        ];
      };

    # ── THE TWO ARMS OF `inheritAll` THAT NOTHING PINNED ──
    # The parent walk was a level-at-a-time recursion carrying a `_visited` attrset rebuilt with
    # `//`; it is one `genericClosure` now, whose key dedup IS the cycle guard. Both cells below
    # cover behaviour the 895 did not reach, and both values were derived by running the PRIOR
    # implementation and the replacement side by side rather than by reading either one.

    # A CYCLE ENDS BY REPEATING ITS ENTRY, ONCE. The `_visited` arm returned the revisited node's
    # own contribution before stopping — it answers `localResults`, not `[ ]` — so `a` contributes
    # at both ends. `genericClosure` drops a duplicate key outright, so the repeat is reconstructed
    # from the last node's parent; this cell is what says the reconstruction is the prior value and
    # not one step short or one step long.
    test-inheritAll-cycle-repeats-its-entry-once = {
      expr = readAttr {
        parentGraph = genScope.overlays [
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
          a.supp = [ "A" ];
          b.supp = [ "B" ];
        };
        attrName = "all-supp";
        attr = inheritAll { } (node: node.decls.supp or null);
        id = "a";
      };
      expected = [
        "A"
        "B"
        "A"
      ];
    };

    # A SUPPLIED `combine` FOLDS RIGHT — `combine local (combine parent (combine grandparent …))` —
    # and the association is the assertion, not the membership. The recursion got it from its own
    # shape; the replacement walks the chain first and has to fold back over it, and Nix publishes
    # no right fold. `bracket` is deliberately NON-ASSOCIATIVE so a left fold over the same three
    # segments yields `[ "<" "<" "L" "M" ">" "R" ">" ]` and fails here. This cell also guards the
    # `combine ? null` sentinel from the other side: if the supplied arm stopped being reached, the
    # brackets would vanish entirely.
    test-inheritAll-supplied-combine-folds-right = {
      expr = readAttr {
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
          leaf.supp = [ "L" ];
          mid.supp = [ "M" ];
          root.supp = [ "R" ];
        };
        attrName = "all-supp";
        attr = inheritAll {
          combine = a: b: [ "<" ] ++ a ++ b ++ [ ">" ];
        } (node: node.decls.supp or null);
        id = "leaf";
      };
      expected = [
        "<"
        "L"
        "<"
        "M"
        "R"
        ">"
        ">"
      ];
    };

    # inheritSet: set-discipline sibling of inheritAll — self ∪ ancestors, deduped.

    # Leaf sees every ancestor's contribution, unioned nearest-first with duplicates
    # removed (b re-declares "p1", already contributed by a — it appears once).
    test-inheritSet-accumulates-deduped = {
      expr = readAttr {
        parentGraph = genScope.overlays [
          (genScope.edge {
            from = "c";
            to = "b";
          })
          (genScope.edge {
            from = "b";
            to = "a";
          })
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
        attr = inheritSet { } (node: node.decls.supp or null);
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
            (genScope.edge {
              from = "c";
              to = "b";
            })
            (genScope.edge {
              from = "b";
              to = "a";
            })
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
            attr = inheritAll { } extract;
            id = "c";
          };
          viaSet = readAttr {
            inherit parentGraph decls;
            attrName = "set";
            attr = inheritSet { } extract;
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
          (genScope.edge {
            from = "c1";
            to = "b";
          })
          (genScope.edge {
            from = "c2";
            to = "b";
          })
          (genScope.edge {
            from = "b";
            to = "a";
          })
        ];
        decls = {
          a.supp = [ "pa" ];
          b.supp = [ "pb" ];
          c1.supp = [ "pc1" ];
          c2.supp = [ ];
        };
        attrName = "supp-set";
        attr = inheritSet { } (node: node.decls.supp or null);
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
        attr = inheritSet { } (node: node.decls.supp or null);
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
          (genScope.edge {
            from = "c";
            to = "b";
          })
          (genScope.edge {
            from = "b";
            to = "a";
          })
          (genScope.edge {
            from = "d";
            to = "a";
          })
        ];
        decls = {
          a.supp = [ "pa" ];
          b.supp = [ "pb" ];
          c.supp = [ "pc" ];
          d.supp = throw "off-path node must not be forced";
        };
        attrName = "supp-set";
        attr = inheritSet { } (node: node.decls.supp or null);
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
          (genScope.edge {
            from = "c";
            to = "b";
          })
          (genScope.edge {
            from = "b";
            to = "a";
          })
        ];
        decls = {
          a.supp = [ "a1" ];
          b.supp = [ "a2" ];
          c.supp = [ "c1" ];
        };
        attrName = "supp-set";
        attr = inheritSet {
          eq = x: y: builtins.substring 0 1 x == builtins.substring 0 1 y;
        } (node: node.decls.supp or null);
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
        parentGraph = genScope.edge {
          from = "b";
          to = "a";
        };
        decls = {
          a = { };
          b = { };
        };
        attrName = "supp-set";
        attr = inheritSet { } (node: node.decls.supp or null);
        id = "b";
      };
      expected = [ ];
    };
  };
}
