# Feature flag scope graph with HOAG rollout synthesis.
#
# Hierarchy:
#   global                         (default flag values)
#   ├── org:acme                   (org-level overrides)
#   │   ├── project:alpha          (project-level overrides)
#   │   │   ├── user:alice
#   │   │   └── user:bob
#   │   └── project:beta
#   │       └── user:carol
#   └── org:widgets
#       └── project:gamma
#           └── user:dave
#
# Flags:
#   dark-mode      — global=false, org:acme=true
#   new-editor     — global=false, project:alpha=true, user:bob=false
#   ai-assist      — global=false, depends on new-editor
#   beta-features  — global=false, org:widgets=true
#   max-items      — global=50, project:alpha=100
{ genScope, lib }:
let
  # ── THE KIND VOCABULARY, AND THE ONE EXPANSION IN IT ──
  # An ORG expands into a ROLLOUT for beta-enabled orgs. The host kind is no longer something the
  # builder tests for — it is the kind the declaration hangs on, so `node.type == "org"` stops being
  # a condition inside the body and becomes the reason the body runs at all. What is left in the
  # body is the genuine data condition.
  kinds = genScope.mkKinds [
    (genScope.mkKind { name = "global"; })
    (genScope.mkKind { name = "project"; })
    (genScope.mkKind { name = "user"; })
    (genScope.mkKind { name = "rollout"; })
    (genScope.mkKind {
      name = "org";
      below = [ "rollout" ];
      spawns.rollout =
        self: id:
        if (self.node id).decls.beta-features or false then
          {
            "rollout:${id}" = {
              id = "rollout:${id}";
              parent = id;
              decls = {
                stage = "canary";
                targetPct = 100;
              };
            };
          }
        else
          { };
    })
  ];

  roots = genScope.buildRoots {
    parentGraph = genScope.overlays [
      (genScope.star "global" [
        "org:acme"
        "org:widgets"
      ])
      (genScope.star "org:acme" [
        "project:alpha"
        "project:beta"
      ])
      (genScope.star "project:alpha" [
        "user:alice"
        "user:bob"
      ])
      (genScope.edge "user:carol" "project:beta")
      (genScope.edge "project:gamma" "org:widgets")
      (genScope.edge "user:dave" "project:gamma")
    ];
    decls = {
      global = {
        dark-mode = false;
        new-editor = false;
        ai-assist = false;
        beta-features = false;
        max-items = 50;
      };
      "org:acme" = {
        dark-mode = true;
      };
      "org:widgets" = {
        beta-features = true;
      };
      "project:alpha" = {
        new-editor = true;
        max-items = 100;
      };
      "project:beta" = { };
      "project:gamma" = { };
      "user:alice" = { };
      "user:bob" = {
        new-editor = false;
      };
      "user:carol" = { };
      "user:dave" = { };
    };
    kinds = kinds;
    types = {
      global = "global";
      "org:acme" = "org";
      "org:widgets" = "org";
      "project:alpha" = "project";
      "project:beta" = "project";
      "project:gamma" = "project";
      "user:alice" = "user";
      "user:bob" = "user";
      "user:carol" = "user";
      "user:dave" = "user";
    };
  };

  # Build attributes with children that include synthesized rollout nodes
  mkAttributes =
    rootNodes: userAttrs:
    let
      baseAttrs = {
        children = _self: id: lib.filterAttrs (_: n: n.parent == id) rootNodes;
        imports = _self: _id: [ ];
      };
    in
    baseAttrs // userAttrs;
in
{
  inherit roots mkAttributes;
}
