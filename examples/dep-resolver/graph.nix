# Package dependency resolver scope graph.
#
# Packages form a dependency graph. Each package declares its version
# and exports. Dependencies create import edges. HOAG synthesis computes
# resolved dependency sets. Ambiguity detection catches version conflicts.
#
# Package graph:
#   workspace (root)
#   ├── app@1.0 → depends on: lib-http@2.x, lib-json@1.x
#   ├── lib-http@2.3 → depends on: lib-json@1.x, lib-tls@1.x
#   ├── lib-json@1.5
#   ├── lib-json@2.0    ← conflict: app wants 1.x, but exists
#   ├── lib-tls@1.2
#   └── lib-logging@3.1 → depends on: lib-json@1.x
{ genScope, lib }:
let
  # ── THE KIND VOCABULARY, AND THE ONE EXPANSION IN IT ──
  # A workspace expands into a MANIFEST — a second-stage node whose declarations are read off the
  # first stage's attributes. The expansion is declared on `workspace`, whose `below` set is what
  # licenses it: `manifest` ranks under `workspace`, so the descent is settled at registration and
  # the builder cannot produce anything else. Its records carry no `type`; the substrate stamps the
  # kind from the key the builder is declared under.
  kinds = genScope.mkKinds [
    (genScope.mkKind { name = "lib"; })
    (genScope.mkKind { name = "app"; })
    (genScope.mkKind { name = "manifest"; })
    (genScope.mkKind {
      name = "workspace";
      below = [ "manifest" ];
      spawns.manifest = self: _id: {
        "resolved:app@1.0" = {
          id = "resolved:app@1.0";
          parent = "workspace";
          decls = {
            package = "app@1.0";
            resolvedDeps = self.get "app@1.0" "allDeps";
            totalAPIs = self.get "app@1.0" "availableAPIs";
          };
        };
      };
    })
  ];

  roots = genScope.buildRoots {
    parentGraph = genScope.star "workspace" [
      "app@1.0"
      "lib-http@2.3"
      "lib-json@1.5"
      "lib-json@2.0"
      "lib-tls@1.2"
      "lib-logging@3.1"
    ];
    importGraph = genScope.overlays [
      (genScope.edge "app@1.0" "lib-http@2.3")
      (genScope.edge "app@1.0" "lib-json@1.5")
      (genScope.edge "lib-http@2.3" "lib-json@1.5")
      (genScope.edge "lib-http@2.3" "lib-tls@1.2")
      (genScope.edge "lib-logging@3.1" "lib-json@1.5")
    ];
    edgeGraphs = [
      # D = devDependency (separate from runtime deps)
      {
        label = "D";
        graph = genScope.edge "app@1.0" "lib-logging@3.1";
      }
    ];
    decls = {
      workspace = {
        name = "my-workspace";
      };
      "app@1.0" = {
        name = "app";
        version = "1.0";
        exports = [
          "main"
          "cli"
        ];
      };
      "lib-http@2.3" = {
        name = "lib-http";
        version = "2.3";
        exports = [
          "get"
          "post"
          "request"
        ];
      };
      "lib-json@1.5" = {
        name = "lib-json";
        version = "1.5";
        exports = [
          "parse"
          "stringify"
        ];
      };
      "lib-json@2.0" = {
        name = "lib-json";
        version = "2.0";
        exports = [
          "parse"
          "stringify"
          "stream"
        ];
      };
      "lib-tls@1.2" = {
        name = "lib-tls";
        version = "1.2";
        exports = [
          "connect"
          "verify"
        ];
      };
      "lib-logging@3.1" = {
        name = "lib-logging";
        version = "3.1";
        exports = [
          "info"
          "warn"
          "error"
        ];
      };
    };
    kinds = kinds;
    types = {
      workspace = "workspace";
      "app@1.0" = "app";
      "lib-http@2.3" = "lib";
      "lib-json@1.5" = "lib";
      "lib-json@2.0" = "lib";
      "lib-tls@1.2" = "lib";
      "lib-logging@3.1" = "lib";
    };
  };

  # `children` SELECTS the packages the workspace contains — nothing here makes a node. The
  # manifest is GROWN by `spawns.manifest` on the `workspace` kind, where its descent is settled
  # at registration.
  mkAttributes =
    rootNodes: userAttrs:
    let
      baseAttrs = {
        children = _self: id: lib.filterAttrs (_: n: n.parent == id) rootNodes;
        imports = _self: id: (_self.node id).decls.__edges.I or [ ];
        "edges-D" = _self: id: (_self.node id).decls.__edges.D or [ ];
      };
    in
    baseAttrs // userAttrs;
in
{
  inherit roots mkAttributes;
}
