# THE QUOTIENT ACCESSOR OBLIGATION's fixtures (ADR-0020 never-silence, ADR-0008 §3), shared by
# `tests/quotient-accessor.nix` (what each channel ANSWERS) and `tests-error.nix`'s
# `quotient-accessor-refusals` (which refusal fires, by its text).
#
# NOT A SUITE: under `_fixtures/`, which the tree importer skips.
#
# The contract under test: a quotient carrier's convergence is a class representative, so `get` —
# the raw demand — refuses it by name, and `getRepresentative` — the named demand — returns
# `{ _type = "gen-scope/quotient-representative"; representative; }`. The tag is constructed at the
# PRODUCER, so the channels that reach the value without an accessor (a child record's co-located
# `_eval`, `evalDebug`'s `getTraced`) carry it too: those two channels are what separates the
# construction from tagging inside `getRepresentative` alone, which passes every accessor cell.
{ genScope }:
let
  inherit (genScope) circular;

  roots = genScope.buildRoots {
    parentGraph = genScope.vertex "node";
    importGraph = genScope.empty;
    decls.node.target = 10;
    types = { };
  };
  base = {
    children = _self: _id: { };
    imports = _self: _id: [ ];
  };

  # Key-set inclusion: a quotient of the value space, whose raw values churn inside a class.
  keySet = height: {
    bottom = { };
    leq = a: b: builtins.all (k: b ? ${k}) (builtins.attrNames a);
    inherit height;
    quotient = true;
  };
  # The arithmetic order: antisymmetric, so not a quotient.
  upTo = height: {
    bottom = 0;
    leq = a: b: a <= b;
    inherit height;
    quotient = false;
  };
  enrichStep =
    _self: _id: prev:
    let
      bumped = builtins.mapAttrs (_: v: v + 1) prev;
      n = builtins.length (builtins.attrNames prev);
    in
    if n >= 3 then bumped else bumped // { "k${toString n}" = 0; };

  decls = {
    enriched = circular { carrier = keySet 3; } enrichStep;
    # a height one short of the three ascents the step takes
    short = circular { carrier = keySet 2; } enrichStep;
    counter = circular { carrier = upTo 10; } (
      self: id: prev:
      if prev >= (self.node id).decls.target then prev else prev + 1
    );
    # a quotient = false instance whose step reads the quotient through its own accessor, raw…
    reader = circular { carrier = upTo 10; } (
      self: _id: _prev:
      builtins.length (builtins.attrNames (self.get "node" "enriched"))
    );
    # …and through the named demand
    readerRep = circular { carrier = upTo 10; } (
      self: _id: _prev:
      builtins.length (builtins.attrNames (self.getRepresentative "node" "enriched").representative)
    );
  };

  r = genScope.eval { } (base // decls) roots;
in
{
  inherit r;

  tagged = representative: {
    _type = "gen-scope/quotient-representative";
    inherit representative;
  };
  converged = {
    k0 = 3;
    k1 = 2;
    k2 = 1;
  };

  debug = genScope.evalDebug { } (base // decls) roots;

  # The reuse path: the step now THROWS, so a value can only arrive from the prior.
  warm =
    genScope.eval
      {
        prior = r;
        decision = {
          isClean = _: true;
          reusable = _: [ "enriched" ];
        };
      }
      (
        base
        // decls
        // {
          enriched = circular { carrier = keySet 3; } (
            _: _: _:
            throw "quotient-accessor fixture: recomputed, not served"
          );
        }
      )
      roots;

  # Two nodes, so the child's record carries the co-located `_eval` cache.
  tree =
    genScope.eval { }
      {
        children = self: id: if id == "p" then { kid = self.node "kid"; } else { };
        imports = _self: _id: [ ];
        inherit (decls) enriched;
      }
      (
        genScope.buildRoots {
          parentGraph = genScope.overlays [
            (genScope.edge {
              from = "kid";
              to = "p";
            })
          ];
          importGraph = genScope.empty;
          decls = {
            p = { };
            kid = { };
          };
          types = { };
        }
      );
}
