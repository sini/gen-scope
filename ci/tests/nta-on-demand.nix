# AN ON-DEMAND `nta` (`mkKind { ntaOnDemand = [ <name> ]; }`, den-hoag-8qenh OQ6 (c′)): its children are nodes of
# the one evaluation, reached by identifier and by `getNta`, and absent from every enumerating read. The kinds
# and the graph are `_fixtures/nta-on-demand.nix`, shared with the circular refusal in `../tests-error.nix`.
{ genScope, ... }:
let
  od = import ./_fixtures/nta-on-demand.nix { inherit genScope; };
  inherit (genScope) mkKind;
  inherit (od)
    sub
    eager
    run
    nextOf
    ev
    ;
  # fifty `next` hops below the root, by identifier
  deep = builtins.foldl' (h: _: nextOf h) "r" (builtins.genList (i: i) 50);
  isNext = i: builtins.match ".*4:next1:g.*" i != null;
  # `ntaOnDemand` is a set (den-hoag-bs7q7): two registries mint one `host` whose on-demand families
  # are declared in the order given, and `leaf` from the second is merged into the first, so the
  # registry door compares the first's `host` with the one the second's `leaf` resolved.
  hostDecl =
    order:
    mkKind {
      nta = {
        a = _: _: { };
        b = _: _: { };
      };
      ntaOnDemand = order;
    } "host";
  regOf =
    order:
    genScope.mkKinds [
      (hostDecl order)
      (mkKind { below = [ "host" ]; } "leaf")
    ];
  mergedWith =
    order:
    let
      base = regOf [
        "a"
        "b"
      ];
    in
    base
    // {
      kinds = base.kinds // {
        inherit ((regOf order).kinds) leaf;
      };
    };
  buildWith =
    kinds:
    genScope.buildRoots {
      parentGraph = genScope.vertex "root";
      types.root = "leaf";
      decls.root = { };
      inherit kinds;
    };
  # ── THE ORDER HOLDS ON THE ENUMERATED VIEW (den-hoag-jlmmr) ──
  # A host spawning `leaf` children written `z:sp` then `a:sp`, with an enumerable `sub` (keys `k2`,
  # `k1`) and a bounded `next`. Arm `od` declares `next` on demand; arm `en` does not. An on-demand
  # family is never enumerated, so it carries no order, and the enumerated order is `en`'s with the
  # `next` ids deleted.
  orderKinds =
    onDemand:
    genScope.mkKinds [
      (mkKind { } "leaf")
      (mkKind (
        {
          below = [ "leaf" ];
          spawns.leaf =
            _: id:
            if id == "r" then
              [
                {
                  name = "z:sp";
                  value = { };
                }
                {
                  name = "a:sp";
                  value = { };
                }
              ]
            else
              [ ];
          nta = {
            sub =
              _: id:
              if id == "r" then
                {
                  g = {
                    k2 = [ ];
                    k1 = [ ];
                  };
                }
              else
                { };
            next = _: id: if id == "r" then { g.k = [ ]; } else { };
          };
        }
        // (if onDemand then { ntaOnDemand = [ "next" ]; } else { })
      ) "host")
    ];
  orderRun =
    onDemand:
    genScope.eval { }
      {
        children = _: _: { };
        imports = _: _: [ ];
        defs = _: _: [ ];
      }
      (
        genScope.buildRoots {
          kinds = orderKinds onDemand;
          parentGraph = genScope.vertex "r";
          importGraph = genScope.empty;
          decls.r = { };
          types.r = "host";
        }
      );
  orderOd = orderRun true;
  orderEn = orderRun false;
  odOrder = [
    "z:sp"
    "a:sp"
    "nta:1:r3:sub1:g2:k1"
    "nta:1:r3:sub1:g2:k2"
  ];
in
{
  flake.tests.nta-on-demand = {
    test-the-enumerated-view-keeps-the-production-order = {
      expr = {
        od = genScope.childrenIds orderOd "r";
        en = genScope.childrenIds orderEn "r";
        odAll = orderOd.allNodeIds;
      };
      expected = {
        od = odOrder;
        en = odOrder ++ [ "nta:1:r4:next1:g1:k" ];
        odAll = [ "r" ] ++ odOrder;
      };
    };
    test-the-enumerated-order-is-the-full-order-with-the-on-demand-ids-deleted = {
      expr = {
        children =
          genScope.childrenIds orderOd "r"
          == builtins.filter (i: !(isNext i)) (genScope.childrenIds orderEn "r");
        allNodeIds = orderOd.allNodeIds == builtins.filter (i: !(isNext i)) orderEn.allNodeIds;
        odNext = builtins.length (builtins.filter isNext orderOd.allNodeIds);
        enNext = builtins.length (builtins.filter isNext orderEn.allNodeIds);
        nextIsANode = (orderOd.node (nextOf "r")).type;
      };
      expected = {
        children = true;
        allNodeIds = true;
        odNext = 0;
        enNext = 1;
        nextIsANode = "host";
      };
    };
    test-the-enumeration-holds-the-enumerable-family-only = {
      expr = builtins.length ev.allNodeIds;
      expected = 3;
    };
    test-no-on-demand-child-is-enumerated = {
      expr = builtins.filter isNext (
        ev.allNodeIds
        ++ builtins.attrNames ev.allNodes
        ++ builtins.attrNames (ev._childRecords "r")
        ++ builtins.attrNames (ev.structuralAttributes "r").nta-children
      );
      expected = [ ];
    };
    test-the-structural-relation-has-no-finding = {
      expr = ev.projectionFindings "r";
      expected = [ ];
    };
    test-an-on-demand-child-is-a-node-by-identifier = {
      expr = (ev.node (nextOf "r")).type;
      expected = "lazy";
    };
    test-an-on-demand-child-fifty-levels-down-is-a-node = {
      expr = ev.get deep "defs";
      expected = [ ];
    };
    test-getNta-reads-an-on-demand-child = {
      expr = ev.get "r" "nextDefs";
      expected = [ ];
    };
    # the control: the same family, enumerable, is in the node set
    test-control-an-enumerable-family-is-enumerated = {
      expr = builtins.length (builtins.filter isNext (run eager).allNodeIds);
      expected = 1;
    };
    # the circular refusal's clean path: a round over an enumerated node converges (the refusal on a
    # `next` child is `tests-error.nix`'s `nta-on-demand-refusals`)
    test-control-a-circular-attribute-converges-on-an-enumerated-node = {
      expr = ev.get "r" "counter";
      expected = 3;
    };
    test-a-kind-names-only-its-own-ntas-on-demand = {
      expr =
        (builtins.tryEval (
          mkKind {
            nta.sub = sub;
            ntaOnDemand = [ "next" ];
          } "bad"
        )).success;
      expected = false;
    };
    # The families in another order are the same set, so the merge is one kind, and each record
    # carries the order it was declared in.
    test-the-same-families-in-two-orders-are-one-kind = {
      expr =
        let
          built = buildWith (mergedWith [
            "b"
            "a"
          ]);
        in
        {
          filed = built.kinds.kinds.host.ntaOnDemand;
          resolved = built.kinds.kinds.leaf.belowKinds.host.ntaOnDemand;
        };
      expected = {
        filed = [
          "a"
          "b"
        ];
        resolved = [
          "b"
          "a"
        ];
      };
    };
    # the control: a different set is a different kind, refused at the door
    test-control-a-different-on-demand-set-is-a-different-kind = {
      expr = (builtins.tryEval (buildWith (mergedWith [ "a" ])).nodes).success;
      expected = false;
    };
    test-a-family-named-twice-on-demand-is-refused-catchably = {
      expr =
        (builtins.tryEval (
          mkKind {
            nta.sub = sub;
            ntaOnDemand = [
              "sub"
              "sub"
            ];
          } "twice"
        )).success;
      expected = false;
    };
  };
}
