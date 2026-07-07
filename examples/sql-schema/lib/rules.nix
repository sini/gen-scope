# Rule-based NixOS configuration engine — post loop⊥step split.
# gen-dispatch owns the dispatch STEP (a pure function of (rules, context) over ordered
# groups); the convergence LOOP is gen-scope.circular's Kleene ascent; group ORDERING is
# gen-graph.phaseOrder. Rules use gen-select selectors as conditions.
#
# Two groups:
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
    mkActions
    ;
  inherit (genGraph) entryAnywhere entryAfter phaseOrder;
  match = genDispatch.adapters.select.mkMatch genSelect;

  # Action vocabulary: two groups
  fx = mkActions {
    structural = [ "enrich" ];
    config = [ "nixos" ];
  };

  # Group order: structural fires first, config after (ordering is gen-graph's job now;
  # its function keeps the name `phaseOrder`, and dispatch consumes the result as `groupOrder`)
  groupOrderList = phaseOrder {
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
  # passes to convergence (Kleene ascent), then return the merged NixOS config. gen-dispatch
  # is a pure STEP, so the loop threads the plain domain state (the accessor context): each
  # pass is one one-shot dispatch whose output context is the next iterate, the enrich
  # feedback widens context until the server's data row reaches a fixpoint, and the NixOS
  # actions are read off the CONVERGED context by one post-convergence dispatch — a function
  # of the fixpoint, not the iteration path (recompute-at-fixpoint = confluence).
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
        groupOrder = groupOrderList;
      };
      converged =
        (genScope.circular
          {
            init = mkServerContext serverData;
            eq = a: b: (a.data serverName) == (b.data serverName);
          }
          (
            _self: _id: ctx:
            (dispatch (cfg // { context = ctx; })).context
          )
        )
          { }
          serverName;
      nixosActions = (dispatch (cfg // { context = converged; })).actions.config or [ ];
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
