# Config cascade attributes.
{
  genScope,
  lib,
  roots,
}:
{
  children = _self: id: lib.filterAttrs (_: n: n.parent == id) roots.nodes;
  imports = _self: id: (_self.node id).decls.__edges.I or [ ];

  config =
    self: id: key:
    genScope.query { } (node: node.decls.${key} or null) self id;

  resolvedConfig =
    self: id:
    let
      node = self.node id;
      local = builtins.removeAttrs node.decls [ "__edges" ];
      importIds = self.get id "imports";
      importedConfigs = lib.foldl' (
        acc: iid:
        genScope.shadow {
          inner = (self.get iid "resolvedConfig");
          outer = acc;
        }
      ) { } importIds;
      parentConfig = if node.parent != null then self.get node.parent "resolvedConfig" else { };
    in
    genScope.shadow {
      inner = local;
      outer = (
        genScope.shadow {
          inner = importedConfigs;
          outer = parentConfig;
        }
      );
    };

  overriddenKeys =
    self: id:
    let
      allResults = key: genScope.queryAll { } (node: node.decls.${key} or null) self id;
      localKeys = builtins.filter (k: k != "__edges") (builtins.attrNames (self.node id).decls);
    in
    builtins.filter (key: builtins.length (allResults key) > 1) localKeys;

  configSources =
    self: id:
    let
      resolved = self.get id "resolvedConfig";
    in
    lib.mapAttrs (
      key: _:
      let
        node = self.node id;
        isLocal = node.decls ? ${key};
        importIds = self.get id "imports";
        isImported = builtins.any (iid: (self.get iid "resolvedConfig") ? ${key}) importIds;
      in
      if isLocal then
        "local"
      else if isImported then
        "import"
      else
        "inherited"
    ) resolved;
}
