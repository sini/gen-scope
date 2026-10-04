# The calculus's refusal table (den-hoag-gayc build spec §2.4), one planted value per row and arm,
# each beside its unplanted twin. `ci/tests/calculus.nix` reads catchability (`tryEval` false on the
# plant, the twin answers); `ci/tests-error.nix` pins the text. Row 6 is dropped (D8); row 17 is the
# engine's ADR-0033 guard, unchanged, and is pinned by that guard's own cells.
{ lib, genScope }:
let
  S = genScope;
  ab = [
    "a"
    "b"
  ];
  wf =
    expression:
    S.wellFormed {
      alphabet = ab;
      inherit expression;
    };
  lo =
    layers: endOfPath:
    S.labelOrder {
      alphabet = ab;
      inherit layers endOfPath;
    };
  goodOrder = lo [
    [ "a" ]
    [ "b" ]
  ] (-1);

  # A lifted scope over `a`, `b`, `c`: `a —e→ b`; `b` and `c` declare `x`. Every attribute is
  # overridable, and `null` leaves it undeclared.
  scope =
    attrs:
    let
      roots = S.buildRoots {
        parentGraph = S.vertices (ab ++ [ "c" ]);
        decls = {
          b.x = "vb";
          c.x = "vc";
        };
      };
    in
    S.eval { parseParent = _: null; } (lib.filterAttrs (_: v: v != null) (
      {
        children = _: _: { };
        imports = _: _: [ ];
        marks = _: _: [ ];
        edges-e = _: id: if id == "a" then [ "b" ] else [ ];
      }
      // attrs
    )) roots;
  ok = scope { };
  e = S.wellFormed {
    alphabet = [ "e" ];
    expression = "e?";
  };
  x = n: n.decls.x or null;
  go =
    opts: ev:
    (S.resolve (
      {
        wf = e;
        dataFilter = x;
      }
      // opts
    ) ev "a").answers;
  vis = {
    mode = "visible";
    order = S.labelOrder {
      alphabet = [ "e" ];
      layers = [ [ "e" ] ];
      endOfPath = -1;
    };
    groupBy = _: "x";
  };
  # The same read under the declared key.
  gvis = builtins.removeAttrs vis [ "groupBy" ] // {
    group = "x";
  };
  # `e` and `imports`: a walk alphabet `vis`'s order (over `e` alone) cannot rank.
  eImports = S.wellFormed {
    alphabet = [
      "e"
      "imports"
    ];
    expression = "e? imports?";
  };
  mark = m: scope { marks = _: id: if id == "a" then m else [ ]; };
  # `a` reaches `b` by `e` and `c` by `imports`, both declaring `x`, at one rank.
  twoDecls = scope { imports = _: id: if id == "a" then [ "c" ] else [ ]; };
  # Inbound `parent*` from `from` over a containment declared in `nodes` order, `parents.<child>`
  # naming the parent; `marked` nodes refuse `parent`.
  upward =
    {
      nodes,
      parents,
      marked ? [ ],
    }:
    from:
    (S.resolve
      {
        wf = S.wellFormed {
          alphabet = [ "parent" ];
          expression = "parent*";
        };
        dataFilter = n: n.id;
        direction = "inbound";
      }
      (S.eval { parseParent = _: null; }
        {
          children = _: _: { };
          marks =
            _: id:
            if builtins.elem id marked then
              [
                {
                  name = "no-parent";
                  admits = l: l != "parent";
                }
              ]
            else
              [ ];
        }
        (
          S.buildRoots {
            parentGraph = S.overlay (S.vertices nodes) (
              S.edges (
                map (c: {
                  from = c;
                  to = parents.${c};
                }) (builtins.attrNames parents)
              )
            );
          }
        )
      )
      from
    ).answers;
  # rho: `s` sits in `a`, `c` in `s`; `a` and `b` contain each other unless `rooted`.
  rhoUp =
    rooted:
    upward {
      nodes = [
        "s"
        "a"
        "b"
        "c"
      ];
      parents = {
        s = "a";
        c = "s";
        b = "a";
      }
      // (if rooted then { } else { a = "b"; });
    } "s";
  # r and m contain each other unless `rooted`; x sits in r, y in m, and both refuse `parent`. They
  # come first in `allNodeIds`, so each is the FIRST converse source of its parent.
  markedCycle =
    rooted:
    upward {
      nodes = [
        "x"
        "y"
        "r"
        "m"
      ];
      parents = {
        r = "m";
        x = "r";
        y = "m";
      }
      // (if rooted then { } else { m = "r"; });
      marked = [
        "x"
        "y"
      ];
    } "r";
in
{
  # ── row: { plant; twin; } ──
  row1-malformed-expression = {
    plant = wf "a (";
    twin = wf "a (b)";
  };
  row2-longer-than-maxLength = {
    plant = S.wellFormed {
      alphabet = ab;
      expression = "a b a";
      maxLength = 3;
    };
    twin = S.wellFormed {
      alphabet = ab;
      expression = "a b";
      maxLength = 3;
    };
  };
  row3-unknown-wellFormed-option = {
    plant = S.wellFormed {
      alphabet = ab;
      expression = "a";
      depth = 1;
    };
    twin = wf "a";
  };
  row4-not-a-constructor-term = {
    plant = wf {
      t = "lit";
      l = "a";
    };
    twin = wf (S.wfl.lit "a");
  };
  row5-letter-outside-the-alphabet = {
    plant = wf "a c";
    twin = wf "a b";
  };
  row5-letter-not-a-string = {
    plant = S.wellFormed {
      alphabet = [ 1 ];
      expression = "a";
    };
    twin = wf "a";
  };
  row5-reserved-letter = {
    plant = S.wellFormed {
      alphabet = [ "$" ];
      expression = "a";
    };
    twin = wf "a";
  };
  row5-duplicate-letter = {
    plant = S.labelOrder {
      alphabet = [
        "a"
        "a"
      ];
      layers = [ [ "a" ] ];
      endOfPath = -1;
    };
    twin = goodOrder;
  };
  row7-unranked-letter = {
    plant = lo [ [ "a" ] ] (-1);
    twin = goodOrder;
  };
  row7-foreign-letter = {
    plant = lo [
      [ "a" ]
      [
        "b"
        "c"
      ]
    ] (-1);
    twin = goodOrder;
  };
  row7-layers-not-a-list-of-lists = {
    plant = lo [ "a" "b" ] (-1);
    twin = goodOrder;
  };
  row7-endOfPath-not-an-int = {
    plant = lo [
      [ "a" ]
      [ "b" ]
    ] "last";
    twin = goodOrder;
  };
  row7-label-outside-L-hat = {
    plant = goodOrder.pathPrecedes [ { label = "c"; } ] [ ];
    twin = goodOrder.pathPrecedes [ { label = "a"; } ] [ ];
  };
  row8-wf-missing = {
    plant = S.resolve { dataFilter = x; } ok "a";
    twin = go { } ok;
  };
  row8-dataFilter-missing = {
    plant = S.resolve { wf = e; } ok "a";
    twin = go { } ok;
  };
  row9-visible-without-a-key = {
    plant = go (builtins.removeAttrs vis [ "groupBy" ]) ok;
    twin = go vis ok;
  };
  # ── the declared key `group` (den-hoag-gayc C1): G1–G5 ──
  rowG1-group-and-groupBy = {
    plant = go (vis // { group = "x"; }) ok;
    twin = go gvis ok;
  };
  # G1 reads presence: a null `groupBy` beside `group` is two keys stated, not one.
  rowG1-group-beside-a-null-groupBy = {
    plant = go (gvis // { groupBy = null; }) ok;
    twin = go gvis ok;
  };
  rowG2-group-not-a-string = {
    plant = go (gvis // { group = 1; }) ok;
    twin = go gvis ok;
  };
  rowG3-group-outside-visible = {
    plant = go {
      mode = "witnesses";
      group = "x";
    } ok;
    twin = go { mode = "witnesses"; } ok;
  };
  rowG4-single-asks-another-group = {
    plant =
      (S.resolve (
        gvis
        // {
          wf = e;
          dataFilter = x;
        }
      ) ok "a").single
        "y";
    twin =
      (S.resolve (
        gvis
        // {
          wf = e;
          dataFilter = x;
        }
      ) ok "a").single
        "x";
  };
  rowG5-order-omits-a-wf-letter = {
    plant = go (gvis // { wf = eImports; }) ok;
    twin = go (
      gvis
      // {
        wf = eImports;
        order = S.labelOrder {
          alphabet = [
            "e"
            "imports"
          ];
          layers = [
            [
              "e"
              "imports"
            ]
          ];
          endOfPath = -1;
        };
      }
    ) ok;
  };
  row10-order-outside-visible = {
    plant = go { inherit (vis) order; } ok;
    twin = go { } ok;
  };
  row10-groupBy-outside-visible = {
    plant = go {
      mode = "witnesses";
      inherit (vis) groupBy;
    } ok;
    twin = go { mode = "witnesses"; } ok;
  };
  row10-visible-without-order = {
    plant = go (builtins.removeAttrs vis [ "order" ]) ok;
    twin = go vis ok;
  };
  row10-unknown-mode = {
    plant = go { mode = "all"; } ok;
    twin = go { mode = "reachable"; } ok;
  };
  row10-unknown-option = {
    plant = go { follow = 1; } ok;
    twin = go { } ok;
  };
  row10-unknown-direction = {
    plant = go { direction = "sideways"; } ok;
    twin = go { direction = "inbound"; } ok;
  };
  row11-dataFilter-not-callable = {
    plant = go { dataFilter = 1; } ok;
    twin = go { } ok;
  };
  row11-groupBy-not-callable = {
    plant = go (vis // { groupBy = "x"; }) ok;
    twin = go vis ok;
  };
  row11-groupBy-not-a-string = {
    plant = go (vis // { groupBy = _: 1; }) ok;
    twin = go vis ok;
  };
  row11-admits-not-callable = {
    plant = go { } (mark [
      {
        name = "m";
        admits = 1;
      }
    ]);
    twin = go { } (mark [
      {
        name = "m";
        admits = _: true;
      }
    ]);
  };
  row11-admits-not-a-bool = {
    plant = go { } (mark [
      {
        name = "m";
        admits = _: 1;
      }
    ]);
    twin = go { } (mark [
      {
        name = "m";
        admits = _: true;
      }
    ]);
  };
  row12-from-not-a-node-id = {
    plant = S.resolve {
      wf = e;
      dataFilter = x;
    } ok 1;
    twin = go { } ok;
  };
  row13-edge-attribute-not-a-list = {
    plant = go { } (scope {
      edges-e = _: _: "b";
    });
    twin = go { } ok;
  };
  row13-edge-target-not-a-string = {
    plant = go { } (scope {
      edges-e = _: id: if id == "a" then [ 1 ] else [ ];
    });
    twin = go { } ok;
  };
  row14-marks-not-a-list = {
    plant = go { } (mark { });
    twin = go { } (mark [ ]);
  };
  row14-mark-with-no-admits = {
    plant = go { } (mark [ { name = "m"; } ]);
    twin = go { } (mark [ ]);
  };
  row14-mark-with-no-name = {
    plant =
      (S.resolve {
        wf = e;
        dataFilter = x;
      } (mark [ { admits = _: false; } ]) "a").withheld
        "a";
    twin =
      (S.resolve
        {
          wf = e;
          dataFilter = x;
        }
        (mark [
          {
            name = "m";
            admits = _: false;
          }
        ])
        "a"
      ).withheld
        "a";
  };
  row15-ambiguity = {
    plant =
      (S.resolve {
        wf = S.wellFormed {
          alphabet = [
            "e"
            "imports"
          ];
          expression = "e | imports";
        };
        dataFilter = x;
        mode = "visible";
        order = S.labelOrder {
          alphabet = [
            "e"
            "imports"
          ];
          layers = [
            [
              "e"
              "imports"
            ]
          ];
          endOfPath = -1;
        };
        groupBy = _: "x";
      } twoDecls "a").single
        "x";
    twin =
      (S.resolve (
        vis
        // {
          wf = e;
          dataFilter = x;
        }
      ) ok "a").single
        "x";
  };
  row16-parent-cycle = {
    plant =
      let
        roots = S.buildRoots {
          parentGraph = S.overlays [
            (S.edge {
              from = "a";
              to = "b";
            })
            (S.edge {
              from = "b";
              to = "a";
            })
          ];
        };
      in
      (S.resolve
        {
          wf = S.neron.wf;
          dataFilter = x;
        }
        (S.eval { parseParent = id: roots.nodes.${id}.parent; } {
          children = _: _: { };
          imports = _: _: [ ];
          marks = _: _: [ ];
        } roots)
        "a"
      ).answers;
    twin =
      (S.resolve {
        inherit (S.neron) wf;
        dataFilter = x;
      } ok "a").answers;
  };
  # D9 under the converse (den-hoag-gayc U2e): the walk reads `parent` at the start, so a cycle at
  # it, or above it, is refused there; the twin is the same scope with the cycle broken.
  row16-parent-cycle-inbound = {
    plant = upward {
      nodes = [
        "root"
        "mid"
      ];
      parents = {
        mid = "root";
        root = "mid";
      };
    } "root";
    twin = upward {
      nodes = [
        "root"
        "mid"
      ];
      parents.mid = "root";
    } "root";
  };
  row16-parent-cycle-inbound-above = {
    plant = rhoUp false;
    twin = rhoUp true;
  };
  # A converse source whose own mark refuses `parent` does not hide the edges the others admit.
  row16-parent-cycle-inbound-marked = {
    plant = markedCycle false;
    twin = markedCycle true;
  };
  row18-edge-read-refusal-propagates = {
    plant = go { } (scope {
      edges-e = _: _: throw "planted: the edge read's own refusal";
    });
    twin = go { } ok;
  };
  row19-no-marks = {
    plant = go { } (scope {
      marks = null;
    });
    twin = go { } ok;
  };
  # The inbound twin: nothing imports or edges into `a`, so the walk considers no edge, and the
  # author error is refused all the same — at the door, not at the first edge.
  row19-no-marks-inbound = {
    plant = go { direction = "inbound"; } (scope {
      marks = null;
    });
    twin = go { direction = "inbound"; } ok;
  };
  row20-undeclared-letter = {
    plant =
      (S.resolve {
        wf = S.wellFormed {
          alphabet = [ "l1" ];
          expression = "l1";
        };
        dataFilter = x;
      } ok "a").answers;
    twin = go { } ok;
  };
  row21-reserved-lifted-label = {
    plant =
      (S.buildRoots {
        parentGraph = S.vertices ab;
        edgeGraphs = [
          {
            label = "imports";
            graph = S.edge {
              from = "a";
              to = "b";
            };
          }
        ];
      }).nodes;
    twin =
      (S.buildRoots {
        parentGraph = S.vertices ab;
        edgeGraphs = [
          {
            label = "peer";
            graph = S.edge {
              from = "a";
              to = "b";
            };
          }
        ];
      }).nodes;
  };
}
