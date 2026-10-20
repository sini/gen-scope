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
  };
}
