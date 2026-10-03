# Module resolver attributes.
#
# lookup: parameterized name resolution via scope graph query.
# visibleDecls: all visible declarations with inner-shadows-outer.
# moduleCount: synthesized count of reachable modules.
{
  genScope,
  lib,
  roots,
}:
{
  children = _self: id: lib.filterAttrs (_: n: n.parent == id) roots.nodes;
  imports = _self: id: (_self.node id).decls.__edges.I or [ ];
  # The boundary-mark floor every resolution reads; `[ ]` states none.
  marks = _: _: [ ];

  # Lookup a declaration name. Walks: local decls → imports → parent chain (`neron`).
  lookup =
    self: id: name:
    (genScope.resolve (
      genScope.neron
      // {
        mode = "visible";
        dataFilter = node: node.decls.${name} or null;
        group = name;
      }
    ) self id).single
      name;

  # All visible declarations from this scope (local + imports + parent).
  visibleDecls =
    self: id:
    let
      node = self.node id;
      local = builtins.removeAttrs node.decls [ "__edges" ];
      importIds = self.get id "imports";
      importedDecls = lib.foldl' (
        acc: iid:
        genScope.shadow {
          inner = (builtins.removeAttrs (self.node iid).decls [ "__edges" ]);
          outer = acc;
        }
      ) { } importIds;
      parentDecls = if node.parent != null then self.get node.parent "visibleDecls" else { };
    in
    genScope.shadow {
      inner = local;
      outer = (
        genScope.shadow {
          inner = importedDecls;
          outer = parentDecls;
        }
      );
    };

  # Count modules reachable from this scope.
  moduleCount = self: id: builtins.length (genScope.descendants self id);
}
