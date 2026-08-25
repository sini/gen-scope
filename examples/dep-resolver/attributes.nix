# Dependency resolver attributes.
{ genScope, lib }:
{
  availableAPIs =
    self: id:
    let
      node = self.node id;
      own = node.decls.exports or [ ];
      imported = genScope.collectImports (self: iid: (self.node iid).decls.exports or [ ]) self id;
    in
    lib.unique (own ++ imported);

  depDepth =
    self: id:
    let
      importIds = self.get id "imports";
      childDepths = map (iid: self.get iid "depDepth") importIds;
    in
    if childDepths == [ ] then 0 else 1 + lib.foldl' (a: b: if a > b then a else b) 0 childDepths;

  depCount =
    self: id:
    let
      direct = self.get id "imports";
      transitive = lib.concatMap (iid: self.get iid "allDeps") direct;
    in
    builtins.length (lib.unique (direct ++ transitive));

  allDeps =
    self: id:
    let
      direct = self.get id "imports";
      transitive = lib.concatMap (iid: self.get iid "allDeps") direct;
    in
    lib.unique (direct ++ transitive);

  # The manifest's projections — attributes ON the manifest node, computed from the package it
  # DECLARES. They used to be computed inside the spawn builder and baked into `decls`, which is a
  # category error the declarations-only spawn handle makes inexpressible: a spawn declares what
  # nodes exist, and values are attributes.
  resolvedDeps =
    self: id:
    let
      pkg = (self.node id).decls.package or null;
    in
    if pkg == null then [ ] else self.get pkg "allDeps";

  totalAPIs =
    self: id:
    let
      pkg = (self.node id).decls.package or null;
    in
    if pkg == null then [ ] else self.get pkg "availableAPIs";
}
