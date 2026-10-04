# THE FOUR COLLECTION WALKS ARE RESOLUTIONS (den-hoag-4or0a) — the scopes both
# `tests/walks-through-resolve.nix` and `tests-error.nix`'s `walks-through-resolve` read.
#
# Each walk is asked twice: as shipped (`walks`) and as the question put to `resolve` directly
# (`refs`), which is what the walk IS — so a walk that leaves the calculus disagrees with its own
# reference on the same scope.
{ genScope }:
let
  S = genScope;
  node = id: parent: decls: {
    inherit id parent decls;
    type = "n";
  };
  # A mark that admits no label: every edge leaving its scope is withheld (ADR-0026).
  shut = {
    name = "shut";
    admits = _: false;
  };
  mk =
    {
      nodes,
      imports ? { },
      edgesInclude ? { },
      marked ? [ ],
    }:
    S.eval { parseParent = id: nodes.${id}.parent; }
      {
        children =
          _: id:
          builtins.listToAttrs (
            map (c: {
              name = c;
              value = nodes.${c};
            }) (builtins.filter (c: nodes.${c}.parent == id) (builtins.attrNames nodes))
          );
        imports = _: id: imports.${id} or [ ];
        edges-include = _: id: edgesInclude.${id} or [ ];
        marks = _: id: if builtins.elem id marked then [ shut ] else [ ];
      }
      {
        inherit nodes;
        nodeOrder = builtins.attrNames nodes;
      };
  v = n: n.decls.v or null;
  ex = self: id: v (self.node id);
  ids = _: id: [ id ];

  wfOf =
    e:
    S.wellFormed {
      alphabet = [ "parent" ];
      expression = e;
    };
  nodesOf =
    wf: mode: self: id:
    map (a: a.node)
      (S.resolve {
        inherit wf mode;
        dataFilter = _: true;
      } self id).answers;
  valuesAt = self: builtins.concatMap (i: if ex self i == null then [ ] else [ (ex self i) ]);

  # s imports x, s -parent-> p -parent-> g; `chain marked` carries `shut` at the scopes named.
  chain =
    marked:
    mk {
      nodes = {
        s = node "s" "p" { };
        x = node "x" null { v = "vx"; };
        p = node "p" "g" { v = "vp"; };
        g = node "g" null { v = "vg"; };
      };
      imports.s = [ "x" ];
      inherit marked;
    };
in
{
  inherit ids ex;

  shut = chain [ "s" ];
  open = chain [ ];

  walks = self: id: {
    all = S.inheritAll { } v self id;
    set = S.inheritSet { } v self id;
    ancestors = S.collectionAttr { } "ancestors" ex self id;
    neron = S.collectionAttr { } "neron" ex self id;
  };

  # Each walk's reference expression: `parent*` reachable, `parent parent*` reachable, and every
  # scope `neron.wf` reaches once, ordered by `<p` under `neron.order`.
  refs = self: id: rec {
    all = valuesAt self (nodesOf (wfOf "parent*") "reachable" self id);
    set = all;
    ancestors = valuesAt self (nodesOf (wfOf "parent parent*") "reachable" self id);
    neron = valuesAt self (
      map (a: a.node) (
        builtins.sort (a: b: S.neron.order.pathPrecedes a.path b.path)
          (S.resolve {
            inherit (S.neron) wf;
            mode = "witnesses";
            dataFilter = _: true;
          } self id).answers
      )
    );
  };

  # s imports its own parent p; p -parent-> g. `neron.wf` reaches g by `parent parent`.
  selfImport = mk {
    nodes = {
      s = node "s" "p" { };
      p = node "p" "g" { v = "vp"; };
      g = node "g" null { v = "vg"; };
    };
    imports.s = [ "p" ];
  };

  # The diamond: s imports x, s -parent-> p, p imports x. x is reached on two paths.
  diamond = mk {
    nodes = {
      s = node "s" "p" { v = "vs"; };
      p = node "p" null { v = "vp"; };
      x = node "x" null { v = "vx"; };
    };
    imports = {
      s = [ "x" ];
      p = [ "x" ];
    };
  };

  # A parent 2-cycle a <-> b.
  cycle = mk {
    nodes = {
      a = node "a" "b" { v = "va"; };
      b = node "b" "a" { v = "vb"; };
    };
  };

  # s -include-> r, the label carrying real store-path context.
  labelled = mk {
    nodes = {
      s = node "s" null { };
      r = node "r" null { };
    };
    edgesInclude.s = [ "r" ];
  };
  contextLabel = builtins.appendContext "include" {
    ${builtins.unsafeDiscardStringContext (builtins.toFile "4or0a-label" "x")} = {
      path = true;
    };
  };

  # A store-context node id (the `context-node-id.nix` shape): root contains ctx contains leaf, and
  # leaf imports ctx.
  contextId =
    let
      ctx = builtins.baseNameOf (builtins.toFile "4or0a-ctx-node" "x");
      plain = builtins.unsafeDiscardStringContext ctx;
      roots = S.buildRoots {
        parentGraph = S.overlays [
          (S.edge {
            from = ctx;
            to = "root";
          })
          (S.edge {
            from = "leaf";
            to = ctx;
          })
          (S.vertex "root")
        ];
        decls.root.v = 1;
        decls.${plain}.v = 7;
      };
    in
    {
      inherit ctx;
      ev =
        S.eval { parseParent = id: roots.nodes.${builtins.unsafeDiscardStringContext id}.parent or null; }
          {
            children =
              _: id:
              if id == "root" then
                { ${plain} = roots.nodes.${plain}; }
              else if id == ctx then
                { leaf = roots.nodes.leaf; }
              else
                { };
            imports = _: id: if id == "leaf" then [ ctx ] else [ ];
            marks = _: _: [ ];
          }
          roots;
    };
}
