# THE ON-DEMAND `nta` WITNESS — one fixture shared by the value suite (`tests/nta-on-demand.nix`) and
# the refusal cell in `tests-error.nix`, so the graph the circular refusal is earned on and the graph
# the clean path converges on are one value.
#
# The `lazy` kind grows `next` from EVERY node, without end, as gen-merge's evaluation's own type
# does, and `sub` from its data, so an enumeration is total only because `next` is never descended.
# `eager` is the control: the same `next`, declared enumerable and grown from the root only, is in the
# node set. `counter` is a circular attribute, read on the root (whose node is enumerated) and on a
# `next` child (whose node is not).
{ genScope }:
let
  fx = import ./nta.nix { inherit genScope; };
  inherit (genScope)
    mkKind
    mkKinds
    mintNtaId
    circular
    ;
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
    counter =
      circular
        {
          carrier = {
            bottom = 0;
            leq = a: b: a <= b;
            height = 3;
            quotient = false;
          };
        }
        (
          _: _: prev:
          if prev >= 3 then prev else prev + 1
        );
  };
  run =
    kind:
    genScope.eval { } attributes (
      fx.scopeOf (mkKinds [ kind ]) (fx.root kind.name { defs = [ { s.s = { }; } ]; })
    );
  nextOf =
    host:
    mintNtaId {
      inherit host;
      name = "next";
      group = "g";
      key = "k";
    };
in
{
  inherit
    sub
    lazy
    eager
    run
    nextOf
    ;
  ev = run lazy;
}
