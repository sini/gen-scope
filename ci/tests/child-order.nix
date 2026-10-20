# CHILDREN KEEP THEIR PRODUCTION ORDER.
#
# A spawn builder and a `children` body each return a list of `{ name; value; }`, whose order is
# the list's, or an attribute set keyed by child id, whose order is its names'. The channel
# normalizes that one value into `{ nodes; nodeOrder; }` (`lib/eval.nix`, `childSetOf`), and every
# ORDERED member of the query surface reads `nodeOrder`: `childrenIds`, `siblings`, `descendants`,
# `collectionAttr`'s `children` and `siblings`, `allNodeIds` and the facade's `nodeIds`. `get` keeps
# publishing the identity-keyed map, so the record is reached by no published value route.
#
# ★ EVERY ORDER CELL RUNS BESIDE ITS CONTROL. The fixture writes `user:alice`, `guest:ci`,
# `user:bob`, whose name order is `guest:ci` first; the same list through `listToAttrs` must read
# the name order, so a reader that answered a constant would fail one arm or the other.
{ lib, genScope, ... }:
let
  inherit (genScope)
    mkKind
    mkKinds
    buildRoots
    childrenIds
    siblings
    descendants
    collectionAttr
    ;
  written = [
    {
      name = "user:alice";
      value.decls.n = 1;
    }
    {
      name = "guest:ci";
      value.decls.n = 2;
    }
    {
      name = "user:bob";
      value.decls.n = 3;
    }
  ];
  hostWith =
    below: spawns:
    mkKinds [
      (mkKind { } "member")
      (mkKind { } "agent")
      (mkKind { inherit below spawns; } "host")
    ];
  scopeOf =
    kinds:
    buildRoots {
      inherit kinds;
      parentGraph = genScope.empty;
      importGraph = genScope.empty;
      decls.h = { };
      types.h = "host";
    };
  parseParent = id: if id == "h" then null else "h";
  attrs = {
    imports = _: _: [ ];
    children = _: _: { };
  };
  evOf = kinds: genScope.eval { inherit parseParent; } attrs (scopeOf kinds);
  one = builder: evOf (hostWith [ "member" ] { member = builder; });
  evList = one (_: _: written);
  evAttrs = one (_: _: builtins.listToAttrs written);
  reads = ev: {
    childrenIds = childrenIds ev "h";
    siblings = siblings ev "user:bob";
    descendants = descendants ev "h";
    allNodeIds = ev.allNodeIds;
    collectChildren = collectionAttr { } "children" (_: id: [ id ]) ev "h";
    collectSiblings = collectionAttr { } "siblings" (_: id: [ id ]) ev "user:bob";
    facadeNodeIds = ev.facade.nodeIds;
  };

  # Two produced kinds: `below` lists `member` before `agent`, and their children sort the other way.
  twoKinds =
    form:
    evOf (
      hostWith [ "member" "agent" ] {
        member = _: _: form "m:a";
        agent = _: _: form "a:z";
      }
    );
  asList = k: [
    {
      name = k;
      value = { };
    }
  ];
  asAttrs = k: { ${k} = { }; };

  # A selected `z:sel` and a spawned `a:sp` on one host.
  mixedScope =
    form:
    buildRoots {
      kinds = hostWith [ "member" ] { member = _: _: form "a:sp"; };
      parentGraph = genScope.edge {
        from = "z:sel";
        to = "h";
      };
      importGraph = genScope.empty;
      decls = {
        h = { };
        "z:sel" = { };
      };
      types = {
        h = "host";
        "z:sel" = "member";
      };
    };
  mixed =
    form:
    let
      s = mixedScope form;
    in
    genScope.eval { inherit parseParent; } (
      attrs // { children = _: id: if id == "h" then { "z:sel" = s.nodes."z:sel"; } else { }; }
    ) s;

  # The selection channel, list form: two registered children selected against their name order.
  selScope = buildRoots {
    kinds = mkKinds [
      (mkKind { } "member")
      (mkKind { } "host")
    ];
    parentGraph = genScope.overlays [
      (genScope.edge {
        from = "s:b";
        to = "h";
      })
      (genScope.edge {
        from = "s:a";
        to = "h";
      })
    ];
    importGraph = genScope.empty;
    decls = {
      h = { };
      "s:a" = { };
      "s:b" = { };
    };
    types = {
      h = "host";
      "s:a" = "member";
      "s:b" = "member";
    };
  };
  selectWith =
    pick:
    genScope.eval { inherit parseParent; } (
      attrs // { children = _: id: if id == "h" then pick selScope.nodes else [ ]; }
    ) selScope;
  selList = selectWith (ns: [
    {
      name = "s:b";
      value = ns."s:b";
    }
    {
      name = "s:a";
      value = ns."s:a";
    }
  ]);
  selAttrs = selectWith (ns: {
    inherit (ns) "s:b" "s:a";
  });

  # ── THE RECORD STAYS BEHIND `published` ──
  # A host kind that spawns `leaf` children in list order and carries an `nta` family of hosts, so an
  # `nta` child has a child channel of its own for `getNta` to read; and the `evalDebug` twin.
  ntaKinds = mkKinds [
    (mkKind { } "leaf")
    (mkKind {
      below = [ "leaf" ];
      spawns.leaf =
        _: id:
        if id == "r" then
          [ ]
        else
          [
            {
              name = "c:z";
              value = { };
            }
            {
              name = "c:a";
              value = { };
            }
          ];
      nta.sub = _: id: if id == "r" then { g.k1 = [ ]; } else { };
    } "host")
  ];
  ntaScope = buildRoots {
    kinds = ntaKinds;
    parentGraph = genScope.vertex "r";
    importGraph = genScope.empty;
    decls.r = { };
    types.r = "host";
  };
  ntaAttrs = {
    children = _: _: { };
    imports = _: _: [ ];
    # The production `getNta` arm with no round open.
    probe =
      self: id:
      if id == "r" then builtins.attrNames (self.getNta "sub" "g" "k1" "derived-children") else null;
    # The `nta` child's own reader: its `get` on its own child channel, on the production accessor.
    own = self: id: if id == kid then builtins.attrNames (self.get id "derived-children") else null;
    # The arm an open round runs: `probe`, demanded from inside a declared-circular step, runs on
    # the round's accessor, whose `getNta` applies the child's attribute rather than reading `_eval`.
    probeInRound =
      genScope.circular
        {
          carrier = {
            bottom = [ ];
            leq = _: _: true;
            height = 1;
            quotient = false;
          };
        }
        (
          self: id: _:
          if id == "r" then self.get "r" "probe" else [ ]
        );
  };
  ntaEv = genScope.eval { } ntaAttrs ntaScope;
  ntaDbg = genScope.evalDebug { } (builtins.removeAttrs ntaAttrs [ "probeInRound" ]) ntaScope;
  kid = genScope.mintNtaId {
    host = "r";
    name = "sub";
    group = "g";
    key = "k1";
  };
  dbg = genScope.evalDebug { inherit parseParent; } attrs (
    scopeOf (hostWith [ "member" ] { member = _: _: written; })
  );
in
{
  flake.tests.child-order = {
    # ── 3a.1: production order through every ORDERED member ──
    test-a-list-builder-reads-back-in-production-order = {
      expr = reads evList;
      expected = {
        childrenIds = [
          "user:alice"
          "guest:ci"
          "user:bob"
        ];
        siblings = [
          "user:alice"
          "guest:ci"
        ];
        descendants = [
          "user:alice"
          "guest:ci"
          "user:bob"
        ];
        allNodeIds = [
          "h"
          "user:alice"
          "guest:ci"
          "user:bob"
        ];
        collectChildren = [
          "user:alice"
          "guest:ci"
          "user:bob"
        ];
        collectSiblings = [
          "user:alice"
          "guest:ci"
        ];
        facadeNodeIds = [
          "h"
          "user:alice"
          "guest:ci"
          "user:bob"
        ];
      };
    };
    # ── 3a.2: the control; an attribute-set producer reads its names' order, as before ──
    test-control-the-same-children-as-an-attribute-set-read-in-name-order = {
      expr = reads evAttrs;
      expected = {
        childrenIds = [
          "guest:ci"
          "user:alice"
          "user:bob"
        ];
        siblings = [
          "guest:ci"
          "user:alice"
        ];
        descendants = [
          "guest:ci"
          "user:alice"
          "user:bob"
        ];
        allNodeIds = [
          "h"
          "guest:ci"
          "user:alice"
          "user:bob"
        ];
        collectChildren = [
          "guest:ci"
          "user:alice"
          "user:bob"
        ];
        collectSiblings = [
          "guest:ci"
          "user:alice"
        ];
        facadeNodeIds = [
          "h"
          "guest:ci"
          "user:alice"
          "user:bob"
        ];
      };
    };
    test-a-list-selection-reads-back-in-its-written-order = {
      expr = {
        list = childrenIds selList "h";
        attrs = childrenIds selAttrs "h";
      };
      expected = {
        list = [
          "s:b"
          "s:a"
        ];
        attrs = [
          "s:a"
          "s:b"
        ];
      };
    };
    # The published value is the identity-keyed map on either producer shape.
    test-get-publishes-the-identity-keyed-map = {
      expr = {
        list = builtins.attrNames (evList.get "h" "derived-children");
        attrs = builtins.attrNames (evAttrs.get "h" "derived-children");
        selection = builtins.attrNames (selList.get "h" "children");
      };
      expected = {
        list = [
          "guest:ci"
          "user:alice"
          "user:bob"
        ];
        attrs = [
          "guest:ci"
          "user:alice"
          "user:bob"
        ];
        selection = [
          "s:a"
          "s:b"
        ];
      };
    };

    # ── 3a.2: a host's producers compose in blocks ──
    # Spawn kinds in `below` order, whatever their children are called. HEAD read `[ "a:z" "m:a" ]`.
    test-spawn-kinds-compose-in-below-order = {
      expr = {
        list = childrenIds (twoKinds asList) "h";
        attrs = childrenIds (twoKinds asAttrs) "h";
      };
      expected = {
        list = [
          "m:a"
          "a:z"
        ];
        attrs = [
          "m:a"
          "a:z"
        ];
      };
    };
    # The selected half before the spawned. HEAD read `[ "a:sp" "z:sel" ]`.
    test-the-selected-half-precedes-the-spawned = {
      expr = {
        list = childrenIds (mixed asList) "h";
        attrs = childrenIds (mixed asAttrs) "h";
      };
      expected = {
        list = [
          "z:sel"
          "a:sp"
        ];
        attrs = [
          "z:sel"
          "a:sp"
        ];
      };
    };

    # ── C1: no published value route hands out the internal record ──
    # `getNta` on an `nta` child's child channel answers the map, in both of its arms, and so does the
    # child's own `get`; its order is the query surface's.
    test-getNta-on-a-child-channel-answers-the-map = {
      expr = {
        closed = ntaEv.get "r" "probe";
        inRound = ntaEv.get "r" "probeInRound";
        own = ntaEv.get kid "own";
        order = childrenIds ntaEv kid;
      };
      expected = {
        closed = [
          "c:a"
          "c:z"
        ];
        inRound = [
          "c:a"
          "c:z"
        ];
        own = [
          "c:a"
          "c:z"
        ];
        order = [
          "c:z"
          "c:a"
        ];
      };
    };
    # `evalDebug`'s `getTraced`, `get` and `getNta` answer the map too, and its query surface the order.
    test-evalDebug-routes-answer-the-map = {
      expr = {
        getTraced = builtins.attrNames (dbg.getTraced "h" "derived-children").value;
        get = builtins.attrNames (dbg.get "h" "derived-children");
        getNta = ntaDbg.get "r" "probe";
        order = childrenIds dbg "h";
      };
      expected = {
        getTraced = [
          "guest:ci"
          "user:alice"
          "user:bob"
        ];
        get = [
          "guest:ci"
          "user:alice"
          "user:bob"
        ];
        getNta = [
          "c:a"
          "c:z"
        ];
        order = [
          "user:alice"
          "guest:ci"
          "user:bob"
        ];
      };
    };
    # An empty list is a host with no children, as `{ }` is.
    test-an-empty-list-is-no-children = {
      expr = childrenIds (one (_: _: [ ])) "h";
      expected = [ ];
    };
  };
}
