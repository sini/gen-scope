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
      extra ? { },
    }:
    S.eval { parseParent = id: nodes.${id}.parent; }
      (
        {
          children = _: _: { };
          inherit imports;
          marks = _: _: [ ];
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
