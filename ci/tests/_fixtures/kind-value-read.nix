# THE COHERENCE CONJUNCT DECIDED AT THE NODE'S OWN READ (den-hoag-25mup) — one fixture shared by the
# admitting cells (`tests/kind-value.nix`) and the refusing ones (`../tests-error.nix`'s
# `kind-value-refusals`), so the reads that serve and the reads that refuse are taken over one value.
#
# Roots `h0 … h3` of kind `thimble`, each spawning one `needle` under the canonical key
# `<root>/needles/<root>-m`, `parseParent` that key's inverse. In the planted scope `h1` carries the
# `needle` kind's value, so `h1` is the refusal's subject and every other node is not. The kind values
# are shape fixtures (`kind-value.nix`'s header says why that is the whole of what gen-scope reads).
# `sel` is the same graph whose `h0` SELECTS the registered `h1` under its key, handing `h1`'s own
# record — the route a raw selection record takes past a by-id read.
{ genScope, genGraph }:
let
  S = genScope;
  valueOf = name: mark: {
    kind = name;
    __mint.minted = mark;
    __sealed = { };
  };
  thimbleV = valueOf "thimble" "thimble:t";
  needleV = valueOf "needle" "needle:n";
  kinds = S.mkKinds [
    (S.mkKind { kindValue = needleV; } "needle")
    (S.mkKind {
      kindValue = thimbleV;
      below = [ "needle" ];
      spawns.needle = _self: id: { "${id}/needles/${id}-m".decls = { }; };
    } "thimble")
  ];
  ids = [
    "h0"
    "h1"
    "h2"
    "h3"
  ];
  scopeOf = planted: {
    inherit kinds;
    nodeOrder = ids;
    nodes = builtins.listToAttrs (
      map (id: {
        name = id;
        value = {
          inherit id;
          type = "thimble";
          parent = null;
          decls.def = { };
          kindValue = if planted && id == "h1" then needleV else thimbleV;
        };
      }) ids
    );
  };
  parseParent =
    id:
    let
      p = builtins.filter builtins.isString (builtins.split "/" id);
    in
    if builtins.length p == 3 then builtins.head p else null;
  attributes = {
    children = _self: _id: { };
  };
  selecting = scope: {
    children = _self: id: if id == "h0" then { h1 = scope.nodes.h1; } else { };
  };
  graphOf = scope: {
    inherit scope;
    ev = S.eval { inherit parseParent; } attributes scope;
    sel = S.eval { inherit parseParent; } (selecting scope) scope;
    dbg = S.evalDebug { inherit parseParent; } attributes scope;
    fold = S.foldEquations { } {
      inherit scope parseParent;
      schedule.equations.v = {
        name = "v";
        kind = "synthesized";
        readsAttrs = [ ];
        stratum = "resolution";
        compute = self: id: (self.node id).id;
      };
      declaredDependencies = import ./declared.nix { inherit genGraph scope; } { };
    };
  };
in
{
  inherit thimbleV needleV;
  planted = graphOf (scopeOf true);
  unplanted = graphOf (scopeOf false);
}
