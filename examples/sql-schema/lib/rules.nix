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
  # ── THE CONVERGENCE CARRIER ──
  # THEORY. The ascent is well defined only over a carrier with a bottom, an order and a bounded
  # height (Söderberg & Hedin 2013 §4.1). This is a QUOTIENT carrier: the order is read off the
  # server's DATA ROW and says nothing about the accessor context's other four fields, which the
  # loop never touches. What it declares is that a pass EXTENDS the row — every key already present
  # survives with the same value — so an enrich action that overwrote a key with a DIFFERENT value
  # is not an ascent and is refused by name. The projection equality this replaces could not see
  # that: it compared one row to the next and called them converged whenever they happened to
  # agree, with no claim that agreement was a fixed point of anything.
  #
  # The height is the number of keys the rule set can contribute. That is a fact about the RULES,
  # not about this function, so it arrives as the caller's declaration: each strict ascent adds at
  # least one key, so the declared key list bounds the chain by its own length.
  mkConvergenceCarrier = serverName: serverData: enrichKeys: {
    bottom = mkServerContext serverData;
    leq =
      a: b:
      let
        rowA = a.data serverName;
        rowB = b.data serverName;
      in
      builtins.all (k: (rowB ? ${k}) && rowB.${k} == rowA.${k}) (builtins.attrNames rowA);
    height = builtins.length enrichKeys;
    # The comment above already says it: this is a QUOTIENT carrier — the order is read off the
    # data row and says nothing about the context's other fields — and the fourth term states it,
    # which is what selects the per-instance ascent and keeps the instance out of shared rounds.
    quotient = true;
  };

  buildHostConfig =
    fleet: rules: enrichKeys: serverName:
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
      # The declaration is reached THROUGH THE EVALUATOR: `circular` returns a kind-tagged
      # record the demand path reads, so the loop runs where the carrier is readable rather than
      # inside an applied closure.
      converged =
        (genScope.eval {
          scope = genScope.buildRoots {
            parentGraph = genScope.vertex serverName;
            importGraph = genScope.empty;
            decls.${serverName} = { };
            types = { };
          };
          attributes = {
            children = _self: _id: { };
            imports = _self: _id: [ ];
            converged-context =
              genScope.circular { carrier = mkConvergenceCarrier serverName serverData enrichKeys; }
                (
                  _self: _id: ctx:
                  (dispatch (cfg // { context = ctx; })).context
                );
          };
        }).get
          serverName
          "converged-context";
      nixosActions = (dispatch (cfg // { context = converged; })).actions.config or [ ];
    in
    lib.foldl' lib.recursiveUpdate { } (map (a: builtins.removeAttrs a [ "__action" ]) nixosActions);

  # Build all host configs: { serverName = mergedConfig; }
  buildAllHostConfigs =
    fleet: rules: enrichKeys:
    lib.mapAttrs (name: _: buildHostConfig fleet rules enrichKeys name) (fleet.server or { });
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
