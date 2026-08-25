# MEMOIZATION SURVIVES THE GUARD — the evaluation-count arms, read by `eval-memo.sh`.
#
# WHY THIS CANNOT BE A SUITE CELL. The oracle is an EVALUATION COUNT, and the count is observable
# only as `builtins.trace` lines on stderr — no wall-clock number is asserted, only how many times
# one body ran. nix-unit cannot read traces, so the row lives here beside the other stderr/exit-code
# instruments, and `tests/scc-round.nix` names this location where the suite would otherwise be
# read as claiming the row.
#
#   arm "eval"      — the shipped evaluator: ONE traced ACYCLIC attribute read from three PLACES —
#                     two consumer `get`s and another attribute's own body — evaluates its body
#                     ONCE. Every route passes the round guard, so the 1 prices the guard on the
#                     programs that never open a round. (A child record rebuilt by the structural
#                     always-recompute law carries a FRESH co-located cache; that is the priced
#                     cost recorded at `evalAttr`, not this memo law, and is not read here.)
#   arm "evalDebug" — the DEFECT ARM, the naive form the memo law names: a fresh self per `get`
#                     defeats thunk sharing, and the same attribute read three times evaluates
#                     three times. This arm firing is what makes the two 1s above a measurement
#                     rather than a hope.
{
  arm ? "eval",
}:
let
  lock = builtins.fromJSON (builtins.readFile ../../flake.lock);
  fetch =
    name:
    let
      node = lock.nodes.${name}.locked;
    in
    builtins.fetchTree {
      inherit (node)
        type
        owner
        repo
        rev
        narHash
        ;
    };
  prelude = import "${fetch "gen-prelude"}/lib";
  graph = import "${fetch "gen-graph"}/lib" { inherit prelude; };
  inherit (import ../../lib/require-scope.nix { inherit prelude; }) requireScope;
  evalLib = import ../../lib/eval.nix { inherit prelude requireScope graph; };
  inherit (import ../../lib/build-nodes.nix { inherit prelude; }) buildRoots;
  ag = import ../../lib/graph.nix;

  # A two-node acyclic grammar: the traced attribute lives on the child, and the three places it
  # is read from are two consumer `get`s and the body of `reader` on the parent.
  scope = buildRoots {
    parentGraph = ag.overlays [ (ag.edge "c" "p") ];
    importGraph = ag.empty;
    decls = {
      p = { };
      c = { };
    };
    types = { };
  };
  attributes = {
    children =
      self: id:
      if id == "p" then
        {
          c = self.node "c";
        }
      else
        { };
    imports = _self: _id: [ ];
    probe = _self: _id: builtins.trace "EVAL-P" 3;
    reader = self: _id: self.get "c" "probe";
  };
in
if arm == "eval" then
  let
    ev = evalLib.eval { inherit scope attributes; };
  in
  [
    (ev.get "c" "probe")
    (ev.get "c" "probe")
    (ev.get "p" "reader")
  ]
else if arm == "evalDebug" then
  let
    ev = evalLib.evalDebug {
      inherit scope attributes;
      parseParent = id: if id == "c" then "p" else null;
    };
  in
  [
    (ev.get "c" "probe")
    (ev.get "c" "probe")
    (ev.get "c" "probe")
  ]
else
  throw "eval-memo: unknown arm '${arm}'"
