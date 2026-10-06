# Resolution stays lazy in data it shadows (den-hoag-gayc C1, owner-ruled 2026-09-30) — the fixtures
# `ci/tests/lazy-shadowing.nix` (answers) and `ci/tests-error.nix`'s `lazy-shadowing` (what must
# still throw) share. Every throwing datum names itself, so an expected error says WHICH datum was
# forced.
{ lib, genScope }:
let
  S = genScope;
  node = id: parent: decls: {
    inherit id parent decls;
    type = "n";
  };
  scope =
    {
      nodes,
      order,
      imports ? (_: _: [ ]),
      marks ? (_: _: [ ]),
      extra ? { },
    }:
    S.eval { parseParent = id: nodes.${id}.parent; }
      (
        {
          children = _: _: { };
          inherit imports marks;
        }
        // extra
      )
      {
        inherit nodes;
        nodeOrder = order;
      };
  v = n: n.decls.v or null;
  boom = throw "ANCESTOR-DATUM-FORCED";
in
rec {
  inherit v;

  # The nixpkgs mandatory-option idiom: `a` declares, its parent `b`'s datum throws (overridden below).
  shadowing = scope {
    nodes = {
      a = node "a" "b" { v = "va"; };
      b = node "b" null { v = boom; };
    };
    order = [
      "a"
      "b"
    ];
  };
  # The nearer scope declares NOTHING, so the throwing ancestor IS the answer and must fire.
  unset = scope {
    nodes = {
      a = node "a" "b" { };
      b = node "b" null { v = boom; };
    };
    order = [
      "a"
      "b"
    ];
  };
  # Three deep: `a` declares; `b` and `c`, both farther, throw.
  deep = scope {
    nodes = {
      a = node "a" "b" { v = "va"; };
      b = node "b" "c" { v = boom; };
      c = node "c" null { v = throw "GRANDPARENT-FORCED"; };
    };
    order = [
      "a"
      "b"
      "c"
    ];
  };
  # THE THIRD FORCING SITE, AN EDGE (C1 spec gate §5): `b` declares a plain datum, but its computed
  # `imports` throws. Nothing past `a`'s own declaration needs reading; gen-scope main answered "va".
  # The siblings throw from `b`'s marks and from `b`'s own `parent` field instead.
  edgeForcing = scope {
    nodes = {
      a = node "a" "b" { v = "va"; };
      b = node "b" null { v = "vb"; };
    };
    order = [
      "a"
      "b"
    ];
    imports = _: id: if id == "b" then throw "ANCESTOR-EDGE-FORCED" else [ ];
  };
  marksForcing = scope {
    nodes = {
      a = node "a" "b" { v = "va"; };
      b = node "b" null { v = "vb"; };
    };
    order = [
      "a"
      "b"
    ];
    marks = _: id: if id == "b" then throw "ANCESTOR-MARKS-FORCED" else [ ];
  };
  parentForcing = scope {
    nodes = {
      a = node "a" "b" { v = "va"; };
      b = node "b" (throw "ANCESTOR-PARENT-FORCED") { v = "vb"; };
    };
    order = [
      "a"
      "b"
    ];
  };
  # D9 read where the walk reads it: a parent cycle ABOVE the shadowing declaration is never met, so
  # it is not refused (gen-scope main's `inherit'` answered "va"); a cycle the selection walks is.
  cycleAbove = scope {
    nodes = {
      a = node "a" "b" { v = "va"; };
      b = node "b" "c" { };
      c = node "c" "b" { };
    };
    order = [
      "a"
      "b"
      "c"
    ];
  };
  cycleMet = scope {
    nodes = {
      a = node "a" "b" { };
      b = node "b" "a" { };
    };
    order = [
      "a"
      "b"
    ];
  };
  # D9 is decided over the `parent` fields the selection READ, whatever the rank order: `s —imports→
  # p —imports→ q` with `p.parent = q` and `q.parent = p`, only `q` declaring. Both fields are read
  # under either order, so both orders refuse (`$ < imports < parent` once answered "vq" after
  # reading both, because the walk reaches `q` by `imports` and so never re-enters it by `parent`).
  cycleRead = scope {
    nodes = {
      s = node "s" null { };
      p = node "p" "q" { };
      q = node "q" "p" { v = "vq"; };
    };
    order = [
      "s"
      "p"
      "q"
    ];
    imports =
      _: id:
      {
        s = [ "p" ];
        p = [ "q" ];
        q = [ ];
      }
      .${id};
  };
  cycleReadUnder =
    layers:
    (S.resolve {
      wf = S.wellFormed {
        alphabet = [
          "imports"
          "parent"
        ];
        expression = "(imports|parent)*";
      };
      order = S.labelOrder {
        alphabet = [
          "imports"
          "parent"
        ];
        inherit layers;
        endOfPath = -1;
      };
      mode = "visible";
      dataFilter = v;
      group = "k";
    } cycleRead "s").single
      "k";

  # FORCING ORDER inside one tried rank class (den-hoag-f8ikh): `r` imports the class in kid order,
  # one rank under `imports*`, and two reads in it throw. The selection reads a class's members in
  # kid order, each member's edges then its datum, so the earlier read is the error reported: which
  # error surfaces, and whether a later abort is reached at all, is part of the denotation.
  # Kid order 1: `n` (first, non-leaf: it imports `m`) has a throwing datum, the leaf `l` after it too.
  # Kid order 2: two leaves; the first's datum throws, the second's edges throw.
  # Kid order 3: leaf `l1`, non-leaf `n`, leaf `l2`; `l1`'s datum throws, `n`'s edges throw.
  # Kid order 4: `n` (first, non-leaf) has a throwing datum, the leaf `l` after it throwing edges.
  classOrder =
    kids: importsOf: datum:
    (S.resolve
      {
        wf = S.wellFormed {
          alphabet = [ "imports" ];
          expression = "imports*";
        };
        order = S.labelOrder {
          alphabet = [ "imports" ];
          layers = [ [ "imports" ] ];
          endOfPath = -1;
        };
        mode = "visible";
        dataFilter = n: datum.${n.id} or null;
        group = "k";
      }
      (scope {
        nodes = builtins.listToAttrs (
          map
            (id: {
              name = id;
              value = node id null { };
            })
            (
              [
                "r"
                "m"
              ]
              ++ kids
            )
        );
        order = [
          "r"
          "m"
        ]
        ++ kids;
        imports = _: id: if id == "r" then kids else importsOf.${id} or [ ];
      })
      "r"
    ).answers;
  orderNonLeafFirst = classOrder [ "n" "l" ] { n = [ "m" ]; } {
    n = throw "EARLIER-DATUM-FORCED";
    l = throw "LATER-DATUM-FORCED";
  };
  orderLeafEdges = classOrder [ "l1" "l2" ] { l2 = throw "LATER-EDGE-FORCED"; } {
    l1 = throw "EARLIER-DATUM-FORCED";
  };
  orderNonLeafEdges = classOrder [ "l1" "n" "l2" ] { n = throw "LATER-EDGE-FORCED"; } {
    l1 = throw "EARLIER-DATUM-FORCED";
  };
  # A leaf the WF does not accept is not a candidate, so its datum is never read: `wf = imports imports`
  # leaves `r`'s two kids one step short, and both are leaves whose datum throws.
  unacceptedLeaves =
    (S.resolve
      {
        wf = S.wellFormed {
          alphabet = [ "imports" ];
          expression = "imports imports";
        };
        order = S.labelOrder {
          alphabet = [ "imports" ];
          layers = [ [ "imports" ] ];
          endOfPath = -1;
        };
        mode = "visible";
        dataFilter = n: if n.id == "r" then null else throw "UNACCEPTED-LEAF-DATUM-FORCED";
        group = "k";
      }
      (scope {
        nodes = builtins.listToAttrs (
          map
            (id: {
              name = id;
              value = node id null { };
            })
            [
              "r"
              "a"
              "b"
            ]
        );
        order = [
          "r"
          "a"
          "b"
        ];
        imports =
          _: id:
          if id == "r" then
            [
              "a"
              "b"
            ]
          else
            [ ];
      })
      "r"
    ).answers;
  orderSubtreeThenLeafEdges = classOrder [ "n" "l" ] {
    n = [ "m" ];
    l = throw "LATER-EDGE-FORCED";
  } { n = throw "EARLIER-DATUM-FORCED"; };
  # D9 over a leaf decided on class entry: `a.parent = c`, `c.parent = a`, and `a` imports `d`. `parent`
  # and `imports` share one rank, so `a`'s class is `{ c, d }`, both leaves. Nothing declares, so every
  # class is examined; `c`'s `parent` field is read only if the entry run puts `c` in `examined`.
  cycleBatched =
    (S.resolve
      {
        wf = S.wellFormed {
          alphabet = [
            "parent"
            "imports"
          ];
          expression = "parent* imports*";
        };
        order = S.labelOrder {
          alphabet = [
            "parent"
            "imports"
          ];
          layers = [
            [
              "parent"
              "imports"
            ]
          ];
          endOfPath = -1;
        };
        mode = "visible";
        dataFilter = _: null;
        group = "k";
      }
      (scope {
        nodes = {
          a = node "a" "c" { };
          c = node "c" "a" { };
          d = node "d" null { };
        };
        order = [
          "a"
          "c"
          "d"
        ];
        imports = _: id: if id == "a" then [ "d" ] else [ ];
      })
      "a"
    ).answers;

  # F1: `s —e→ t`; `wf` steps `e`, an `order` over `imports` alone cannot rank it.
  alphabetMismatch = scope {
    nodes = {
      s = node "s" null { v = "vs"; };
      t = node "t" null { };
    };
    order = [
      "s"
      "t"
    ];
    extra.edges-e = _: id: if id == "s" then [ "t" ] else [ ];
  };
  mismatchOpts = alphabet: {
    wf = S.wellFormed {
      alphabet = [
        "imports"
        "e"
      ];
      expression = "(imports|e)*";
    };
    order = S.labelOrder {
      inherit alphabet;
      layers = [ alphabet ];
      endOfPath = -1;
    };
    mode = "visible";
    dataFilter = v;
  };

  vis = S.neron // {
    mode = "visible";
    dataFilter = v;
  };
  group = ev: (S.resolve (vis // { group = "k"; }) ev "a").single "k";
  # A key that READS the datum: the strict form, which must force every candidate it groups.
  dataKey =
    ev: (S.resolve (vis // { groupBy = a: if a.value == "va" then "k" else "k"; }) ev "a").single "k";
  inherit' = ev: S."inherit'" { } v ev "a";

  # gen-scope's own example `config-cascade`, unedited, over the C1 fixture's shape.
  cascade =
    let
      nodes = {
        a = (node "a" "b" { }) // {
          decls.port = 8080;
        };
        b = (node "b" null { }) // {
          decls.port = throw "ANCESTOR-DATUM-FORCED";
        };
      };
      roots = {
        inherit nodes;
        nodeOrder = [
          "a"
          "b"
        ];
      };
      attrs = import ../../../examples/config-cascade/attributes.nix {
        inherit lib roots;
        genScope = S;
      };
    in
    attrs.config (S.eval { parseParent = id: nodes.${id}.parent; } attrs roots) "a" "port";
}
