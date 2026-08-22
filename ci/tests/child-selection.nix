# THE SELECTION CHANNEL, ARMED.
#
# `children` names WHICH of the scope's nodes stand below this one; it does not make them. What
# these cells measure is that the two shapes the channel used to carry now separate cleanly: a
# SELECTION over registered nodes passes, and a body that MINTS a record the scope does not carry
# is refused by name.
#
# ★ EVERY REFUSAL CELL RUNS BESIDE ITS CONTROL IN THE SAME FIXTURE. The minting and selecting arms
# differ in the `children` body and in nothing else, so a refusal that fired for some unrelated
# reason — a malformed scope, a missing attribute — would take the control down with it and the
# pair would stop discriminating. A refusal cell whose control cannot be seen failing is not armed.
#
# ★★ THE NESTED-DIRECTORY CELL IS THE ONE THE RULING TURNS ON. Requiring children to DESCEND was
# the arm that could not be taken: `dir` contains `dir` in the config-cascade shape, a self-loop in
# `below` is refused at registration, and nested directories would have become inexpressible.
# Selection introduces no node to rank, so it moves nothing through the kind order — and that cell
# is what says so rather than leaving it argued.
{ lib, genScope, ... }:
let
  succeeds = e: (builtins.tryEval (builtins.deepSeq e null)).success;

  # A FLAT kind vocabulary, which is what every shipped example registers: the names this graph's
  # nodes are, with no order between them.
  flatKinds = names: genScope.mkKinds (map (name: genScope.mkKind { inherit name; }) names);

  # ── THE CONFIG-CASCADE SHAPE, REPRODUCED ──
  # Measured at `examples/config-cascade/graph.nix`: a directory tree whose containment is
  # SAME-KIND — `apps` is a `dir` and so are `api` and `web` below it. The example flake itself
  # cannot be exercised end to end (its `children` filters the whole `buildRoots` record rather
  # than that record's `nodes`, a staleness that predates this channel), so the shape is
  # reproduced here, where it runs on every gate.
  dirScope = genScope.buildRoots {
    kinds = flatKinds [
      "root"
      "dir"
    ];
    parentGraph = genScope.overlays [
      (genScope.star "global" [
        "apps"
        "shared"
        "infra"
      ])
      (genScope.star "apps" [
        "api"
        "web"
      ])
    ];
    types = {
      global = "root";
      apps = "dir";
      api = "dir";
      web = "dir";
      shared = "dir";
      infra = "dir";
    };
  };
  dirResult = genScope.eval {
    scope = dirScope;
    attributes = {
      children = _self: id: lib.filterAttrs (_: n: n.parent == id) dirScope.nodes;
    };
  };

  # ── THE TWO BODIES, OVER ONE SCOPE ──
  pairScope = {
    nodes = {
      host = {
        id = "host";
        type = "t";
        parent = null;
        decls = { };
      };
      kid = {
        id = "kid";
        type = "t";
        parent = "host";
        decls = { };
      };
    };
    nodeOrder = [
      "host"
      "kid"
    ];
  };
  runWith =
    children:
    genScope.eval {
      scope = pairScope;
      attributes = { inherit children; };
    };
  selecting = runWith (_self: id: lib.filterAttrs (_: n: n.parent == id) pairScope.nodes);
  minting = runWith (
    _self: id:
    if id == "host" then
      {
        minted = {
          id = "minted";
          type = "t";
          parent = "host";
          decls = { };
        };
      }
    else
      { }
  );

  # ── GROWTH, ON THE CHANNEL THAT CARRIES THE DESCENT GUARANTEE ──
  # The capability is not removed, it is MOVED, and a landing that only measured the refusal would
  # not say so.
  spawnScope = {
    nodes = {
      host = {
        id = "host";
        type = "container";
        parent = null;
        decls = { };
      };
      kid = {
        id = "kid";
        type = "sub";
        parent = "host";
        decls = { };
      };
    };
    nodeOrder = [
      "host"
      "kid"
    ];
    kinds = genScope.mkKinds [
      (genScope.mkKind { name = "sub"; })
      (genScope.mkKind {
        name = "container";
        below = [ "sub" ];
        # No `type` on the record: the substrate stamps `sub` from the key this builder is
        # declared under.
        spawns.sub = _self: id: {
          "${id}-mint" = {
            id = "${id}-mint";
            parent = id;
            decls = { };
          };
        };
      })
    ];
  };
  spawnResult = genScope.eval {
    scope = spawnScope;
    attributes = {
      children = _self: id: lib.filterAttrs (_: n: n.parent == id) spawnScope.nodes;
    };
  };
in
{
  flake.tests."child-selection" = {
    # ── (i) AND (ii): THE MINTING BODY IS REFUSED, THE SELECTION SHAPE IS NOT ──
    test-a-minted-child-is-refused-and-the-selection-shape-is-not = {
      expr = {
        mints = succeeds minting.allNodeIds;
        selects = succeeds selecting.allNodeIds;
      };
      expected = {
        mints = false;
        selects = true;
      };
    };

    # The selection answers the containment it was asked for, so the passing arm above is passing
    # for the right reason rather than by walking nothing.
    test-control-the-selection-shape-walks-the-tree-it-selects = {
      expr = {
        walked = builtins.sort builtins.lessThan selecting.allNodeIds;
        childrenOfHost = genScope.childrenIds selecting "host";
      };
      expected = {
        walked = [
          "host"
          "kid"
        ];
        childrenOfHost = [ "kid" ];
      };
    };

    # THE GUARD SITS ON THE `children` ATTRIBUTE, NOT ON THE CHILD-RESOLUTION SEAM. The query
    # surface reads `self.get id "children"` directly (`lib/queries.nix`, and the resolver's
    # `children` traversal), so a guard homed at the seam would leave a minted record reachable
    # through a route that never passes it. This cell reads through that route.
    test-the-refusal-is-reached-through-the-query-surface = {
      expr = {
        mints = succeeds (genScope.childrenIds minting "host");
        selects = genScope.childrenIds selecting "host";
      };
      expected = {
        mints = false;
        selects = [ "kid" ];
      };
    };

    # The membership test reads KEYS, which are eager, and never the records, which are lazy — so
    # a selected child whose record would throw is still selectable. That is what says the guard
    # forces no sibling record, which is the strictness `childRecordsOf` decided and this must not
    # quietly spend.
    test-control-the-membership-test-does-not-force-child-records = {
      expr = genScope.childrenIds (runWith (
        _self: id: if id == "host" then { kid = throw "a child record was forced"; } else { }
      )) "host";
      expected = [ "kid" ];
    };

    # ── (iii) ★ THE NESTED-DIRECTORY CASE: SAME-KIND STATIC CONTAINMENT, GREEN ──
    test-control-nested-directories-of-the-same-kind-stay-expressible = {
      expr = {
        childrenOfApps = genScope.childrenIds dirResult "apps";
        hostKind = (dirResult.node "apps").type;
        childKind = (dirResult.node "api").type;
        walked = builtins.sort builtins.lessThan dirResult.allNodeIds;
      };
      expected = {
        childrenOfApps = [
          "api"
          "web"
        ];
        # The pair the ruling rests on: the containment is same-kind and it registers anyway,
        # because selection introduces no node to rank.
        hostKind = "dir";
        childKind = "dir";
        walked = [
          "api"
          "apps"
          "global"
          "infra"
          "shared"
          "web"
        ];
      };
    };

    # ── GROWTH IS MOVED, NOT REMOVED ──
    test-control-growth-is-available-on-the-spawn-channel = {
      expr = builtins.sort builtins.lessThan spawnResult.allNodeIds;
      expected = [
        "host"
        "host-mint"
        "kid"
      ];
    };
  };
}
