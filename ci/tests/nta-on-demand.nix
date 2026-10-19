# AN ON-DEMAND `nta` (`mkKind { ntaOnDemand = [ <name> ]; }`, den-hoag-8qenh OQ6 (c′)): its children are nodes of
# the one evaluation, reached by identifier and by `getNta`, and absent from every enumerating read. The `lazy`
# kind grows `next` from EVERY node, without end, as gen-merge's evaluation's own type does, and `sub` from its
# data, so an enumeration is total only because `next` is never descended. `eager` is the control: the same
# `next`, declared enumerable and grown from the root only, is in the node set.
{ genScope, ... }:
let
  fx = import ./_fixtures/nta.nix { inherit genScope; };
  inherit (genScope) mkKind mkKinds mintNtaId;
  inherit (builtins) head isAttrs;
  addr = def: at: {
    attr = "defs";
    inherit def at;
  };
  sub =
    self: id:
    let
      d = self.get id "defs";
    in
    {
      g = if d != [ ] && isAttrs (head d) && head d ? s then { k = [ (addr 0 [ "s" ]) ]; } else { };
    };
  lazy = mkKind {
    nta = {
      inherit sub;
      next = _: _: { g.k = [ ]; };
    };
    ntaOnDemand = [ "next" ];
  } "lazy";
  eager = mkKind {
    nta = {
      inherit sub;
      next = _: id: if id == "r" then { g.k = [ ]; } else { };
    };
  } "eager";
  attributes = fx.attributes // {
    nextDefs = self: id: self.getNta "next" "g" "k" "defs";
  };
  run =
    kind:
    genScope.eval { } attributes (
      fx.scopeOf (mkKinds [ kind ]) (fx.root kind.name { defs = [ { s.s = { }; } ]; })
    );
  ev = run lazy;
  nextOf =
    host:
    mintNtaId {
      inherit host;
      name = "next";
      group = "g";
      key = "k";
    };
  # fifty `next` hops below the root, by identifier
  deep = builtins.foldl' (h: _: nextOf h) "r" (builtins.genList (i: i) 50);
  isNext = i: builtins.match ".*4:next1:g.*" i != null;
in
{
  flake.tests.nta-on-demand = {
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
  };
}
