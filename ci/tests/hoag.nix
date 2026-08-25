{ lib, genScope, ... }:
let
  # A FLAT kind vocabulary: names, and no order between them, so no kind expands into another.
  # These fixtures declare types and never spawn, which is exactly what an empty `below` says.
  flatKinds = names: genScope.mkKinds (map (name: genScope.mkKind { inherit name; }) names);

  # Multi-level: env → host → user
  roots = genScope.buildRoots {
    kinds = flatKinds [
      "env"
      "host"
      "user"
    ];
    parentGraph = genScope.overlays [
      (genScope.edge "host1" "env")
      (genScope.edge "user1" "host1")
      (genScope.edge "user2" "host1")
    ];
    importGraph = genScope.empty;
    decls = {
      env = {
        name = "production";
      };
      host1 = {
        hostname = "srv1";
      };
      user1 = {
        username = "alice";
      };
      user2 = {
        username = "bob";
      };
    };
    types = {
      env = "env";
      host1 = "host";
      user1 = "user";
      user2 = "user";
    };
  };

  result = genScope.eval {
    scope = roots;
    attributes = {
      children = self: id: lib.filterAttrs (_: n: n.parent == id) roots.nodes;
      imports = self: id: [ ];
      label =
        self: id:
        let
          node = self.node id;
        in
        node.decls.hostname or node.decls.username or node.decls.name or id;
    };
    parseParent = id: (roots.nodes.${id} or { parent = null; }).parent;
  };

  # ── DERIVED CHILDREN: THE EXPANSION IS DECLARED ON THE KIND IT EXPANDS FROM ──
  # `cluster` expands into `proxy` and says so at registration, where `proxy` must already be one
  # of its `below` names — so the descent is settled before the grammar runs and the builder cannot
  # produce anything else. The builder is written under the key naming what it produces and the
  # substrate stamps `type` from that key: nothing in the body chooses a kind.
  proxyKinds = genScope.mkKinds [
    (genScope.mkKind { name = "proxy"; })
    (genScope.mkKind { name = "service"; })
    (genScope.mkKind {
      name = "cluster";
      below = [ "proxy" ];
      spawns = {
        proxy =
          self: id:
          let
            node = self.node id;
          in
          if node.decls.proxy or false then
            {
              "${id}-proxy" = {
                id = "${id}-proxy";
                parent = id;
                decls = {
                  upstream = id;
                };
              };
            }
          else
            { };
      };
    })
  ];

  proxyRoots = genScope.buildRoots {
    parentGraph = genScope.edge "svc" "cluster";
    importGraph = genScope.empty;
    kinds = proxyKinds;
    decls = {
      cluster = {
        proxy = true;
      };
      svc = {
        port = 8080;
      };
    };
    types = {
      cluster = "cluster";
      svc = "service";
    };
  };

  proxyResult = genScope.eval {
    scope = proxyRoots;
    attributes = {
      children = self: id: lib.filterAttrs (_: n: n.parent == id) proxyRoots.nodes;
      imports = self: id: [ ];
      port = self: id: (self.node id).decls.port or null;
    };
    parseParent =
      id:
      if proxyRoots.nodes ? ${id} then
        proxyRoots.nodes.${id}.parent
      else
        # Derived children: parse parent from id suffix
        let
          parts = lib.splitString "-proxy" id;
        in
        if builtins.length parts > 1 then builtins.head parts else null;
  };

  # A builder that records what its handle SERVES: the observation rides the spawned child's own
  # `decls`, so the measurement is taken at the one position the handle exists for.
  spawnHandleObs =
    (genScope.eval {
      scope = genScope.buildRoots {
        parentGraph = genScope.vertex "h";
        importGraph = genScope.empty;
        decls.h = { };
        types.h = "host";
        kinds = genScope.mkKinds [
          (genScope.mkKind { name = "low"; })
          (genScope.mkKind {
            name = "host";
            below = [ "low" ];
            spawns = {
              low = handle: id: {
                "${id}-obs" = {
                  id = "${id}-obs";
                  decls = {
                    handleNames = builtins.attrNames handle;
                    nodeRecordNames = builtins.attrNames (handle.node id);
                  };
                };
              };
            };
          })
        ];
      };
      attributes = {
        children = _self: _id: { };
        imports = _self: _id: [ ];
      };
    }).node
      "h-obs";
in
{
  flake.tests."hoag" = {
    test-multi-level-env-label = {
      expr = result.get "env" "label";
      expected = "production";
    };

    test-multi-level-host-label = {
      expr = result.get "host1" "label";
      expected = "srv1";
    };

    test-multi-level-user-label = {
      expr = result.get "user1" "label";
      expected = "alice";
    };

    test-multi-level-children-env = {
      expr = builtins.attrNames (result.get "env" "children");
      expected = [ "host1" ];
    };

    test-multi-level-children-host = {
      expr = builtins.sort builtins.lessThan (builtins.attrNames (result.get "host1" "children"));
      expected = [
        "user1"
        "user2"
      ];
    };

    test-multi-level-parent-chain = {
      expr = (result.node "user1").parent;
      expected = "host1";
    };

    test-multi-level-grandparent = {
      expr = (result.node "host1").parent;
      expected = "env";
    };

    test-derived-children-proxy-exists = {
      expr = builtins.attrNames (proxyResult.get "cluster" "derived-children");
      expected = [ "cluster-proxy" ];
    };

    test-derived-children-non-proxy = {
      expr = proxyResult.get "svc" "derived-children";
      expected = { };
    };

    test-derived-child-reachable = {
      expr = (proxyResult.node "cluster-proxy").type;
      expected = "proxy";
    };

    test-derived-child-decls = {
      expr = (proxyResult.node "cluster-proxy").decls.upstream;
      expected = "cluster";
    };

    test-allNodes-includes-derived = {
      expr = builtins.sort builtins.lessThan (builtins.attrNames proxyResult.allNodes);
      expected = [
        "cluster"
        "cluster-proxy"
        "svc"
      ];
    };

    # ── THE TWO PATH CLASSES, BOTH ASSERTED ──
    # gen-scope is a demand-driven evaluator, so asking for ONE spawned node by id resolves through
    # `resolveNode` and never touches the materialization walk. A suite carrying only the
    # enumeration cell above would say nothing about the route the evaluator actually uses most, and
    # the two cells would agree with a substrate that handed out unstamped records on demand.
    test-the-spawned-kind-is-stamped-on-the-demand-path = {
      expr = (proxyResult.node "cluster-proxy").type;
      expected = "proxy";
    };
    test-the-spawned-kind-is-stamped-on-the-enumeration-path = {
      expr = proxyResult.allNodes."cluster-proxy".type;
      expected = "proxy";
    };

    # ── THE SPAWN HANDLE'S NAME SET IS AN EXACT SET, never a presence check ──
    # The handle is a PROJECTION rebuilt from named fields, and only name-set equality separates
    # that from a FILTER over the evaluator — a filter passes every presence check identically
    # while carrying whatever its author forgot and re-acquiring every field a later wrapper
    # adds. Compared on NAMES, so a widening, a narrowing or a rename each fail these cells (the
    # ground `fold-equations.nix` pins ResolveCtx's ten fields on, in its own words). The exact
    # set is ALSO what bounds the builder: the in-flight value has no name through the handle —
    # `get` and `_eval` are absent BY THE SET, not by two deletions.
    test-the-spawn-handles-name-set-is-exactly-node = {
      expr = spawnHandleObs.decls.handleNames;
      expected = [ "node" ];
    };
    test-the-node-record-a-builder-reads-has-exactly-its-four-fields = {
      expr = spawnHandleObs.decls.nodeRecordNames;
      expected = [
        "decls"
        "id"
        "parent"
        "type"
      ];
    };

    # ── THE SPAWN CHANNEL CANNOT BE WRITTEN BY HAND ──
    # It is the one surface on which an expansion could still be declared outside the kind order, so
    # leaving it open would make the order a convention. WHICH refusal fires is asserted by text in
    # `../tests-error.nix`.
    test-a-hand-written-spawn-attribute-is-refused = {
      expr =
        !(builtins.tryEval (
          (genScope.eval {
            scope = proxyRoots;
            attributes = {
              children = _self: _id: { };
              imports = _self: _id: [ ];
              derived-children = _self: _id: { };
            };
          }).get
            "cluster"
            "children"
        )).success;
      expected = true;
    };

    # ── AND A BUILDER CANNOT CHOOSE ITS CHILD'S KIND ──
    # The kind is the key the builder is declared under. `type` on a returned record is the only way
    # a firing-time choice could still be attempted, and it is refused by name rather than
    # overwritten — silently stamping over it would leave the author believing the field was read.
    test-a-builder-writing-its-own-type-is-refused =
      let
        kinds = genScope.mkKinds [
          (genScope.mkKind { name = "low"; })
          (genScope.mkKind {
            name = "high";
            below = [ "low" ];
            spawns.low = _self: id: {
              "${id}-c" = {
                id = "${id}-c";
                parent = id;
                type = "low";
                decls = { };
              };
            };
          })
        ];
        scope = genScope.buildRoots {
          inherit kinds;
          parentGraph = genScope.vertex "h";
          types.h = "high";
        };
      in
      {
        expr =
          !(builtins.tryEval (
            builtins.deepSeq
              (genScope.eval {
                inherit scope;
                attributes = {
                  children = _self: _id: { };
                  imports = _self: _id: [ ];
                };
              }).allNodes
              null
          )).success;
        expected = true;
      };

    # THE CONTROL FOR BOTH REFUSALS ABOVE: the same shape with the `type` dropped materializes, and
    # the stamp puts the declared kind on it. Without this the two cells are equally consistent with
    # an evaluator that refuses every spawn it is given.
    test-control-the-same-spawn-without-a-written-type-materializes =
      let
        kinds = genScope.mkKinds [
          (genScope.mkKind { name = "low"; })
          (genScope.mkKind {
            name = "high";
            below = [ "low" ];
            spawns.low = _self: id: {
              "${id}-c" = {
                id = "${id}-c";
                parent = id;
                decls = { };
              };
            };
          })
        ];
        scope = genScope.buildRoots {
          inherit kinds;
          parentGraph = genScope.vertex "h";
          types.h = "high";
        };
        ev = genScope.eval {
          inherit scope;
          attributes = {
            children = _self: _id: { };
            imports = _self: _id: [ ];
          };
        };
      in
      {
        expr = (ev.node "h-c").type;
        expected = "low";
      };
  };
}
