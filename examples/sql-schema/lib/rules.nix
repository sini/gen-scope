# Rule-based NixOS configuration engine — post loop⊥step split.
# gen-dispatch owns the dispatch STEP (guard->effect over ordered phases); the convergence
# LOOP is gen-scope.circular's Kleene ascent (paired via genDispatch.dispatchStep/dispatchInit);
# phase ORDERING is gen-graph.phaseOrder. Rules use gen-select selectors as conditions.
#
# Two phases:
#   structural — enrich actions feed back into context (the loop converges)
#   config     — nixos actions collect NixOS module fragments
{
  lib,
  genScope,
  genGraph,
  genDispatch,
  genSelect,
}:
let
  inherit (genDispatch)
    mkRule
    dispatch
    dispatchStep
    dispatchInit
    mkActions
    ;
  inherit (genGraph) entryAnywhere entryAfter phaseOrder;
  match = genDispatch.adapters.select.mkMatch genSelect;

  # Action vocabulary: two phases
  fx = mkActions {
    structural = [ "enrich" ];
    config = [ "nixos" ];
  };

  # Phase order: structural fires first, config after (ordering is gen-graph's job now)
  phaseOrderList = phaseOrder {
    structural = entryAnywhere;
    config = entryAfter [ "structural" ];
  };

  # Bridge server data to gen-select's five-field accessor context
  mkServerContext = serverData: {
    data = _id: serverData;
    parent = _: null;
    children = _: [ ];
    ancestors = _: [ ];
    siblings = _: [ ];
  };

  # Extract enrich actions as context feedback for the convergence loop
  extract =
    actions:
    lib.foldl' (acc: a: if a.__action == "enrich" then acc // { ${a.key} = a.value; } else acc) { } (
      actions.structural or [ ]
    );

  combine = ctx: ext: {
    data = _id: (ctx.data _id) // ext;
    inherit (ctx)
      parent
      children
      ancestors
      siblings
      ;
  };

  # Dispatch rules for a server: gen-scope.circular drives repeated gen-dispatch.dispatch
  # passes to a fixpoint; return the merged NixOS config. (Byte-identical to the retired
  # gen-dispatch.fixpoint — see gen-resolve/spike/gen-derive-loop-step/.)
  buildHostConfig =
    fleet: rules: serverName:
    let
      server = fleet.server.${serverName};
      serverData = server // {
        tags = server.tags or [ ];
        environment =
          if builtins.isAttrs (server.environment or null) then
            server.environment.tier or "unknown"
          else
            server.environment or "unknown";
      };
      cfg = {
        inherit
          rules
          match
          extract
          combine
          ;
        id = serverName;
        classify = fx.classify;
        phaseOrder = phaseOrderList;
      };
      result =
        (genScope.circular {
          init = dispatchInit (mkServerContext serverData);
          eq = a: b: (a.context.data serverName) == (b.context.data serverName);
        } (dispatchStep { inherit dispatch; } cfg))
          { }
          serverName;
      nixosActions = result.accActions.config or [ ];
    in
    lib.foldl' lib.recursiveUpdate { } (map (a: builtins.removeAttrs a [ "__action" ]) nixosActions);

  # Build all host configs: { serverName = mergedConfig; }
  buildAllHostConfigs =
    fleet: rules: lib.mapAttrs (name: _: buildHostConfig fleet rules name) (fleet.server or { });
in
{
  inherit
    fx
    match
    mkServerContext
    extract
    buildHostConfig
    buildAllHostConfigs
    ;
}
