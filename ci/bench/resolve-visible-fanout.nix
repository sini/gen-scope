# What `visible` under a declared `group` costs per walk-tree visit, on fan-out — the arms read by
# `resolve-visible-fanout.sh`.
#
# WHY THIS CANNOT BE A SUITE CELL. The oracle is a cost per visit, observable only as the difference
# between two sizes of one fixture. The suite pins the selection's DENOTATION (`lazy-shadowing`'s
# generated agreement with `groupBy`, the D9-under-`group` cells); a frame per trie leaf answered
# every one of them and cost 1.4–1.6x what deciding a run of leaves in place costs.
#
# THE FIXTURES. Nothing is shadowed and every candidate is examined, so the arm measures the
# selection's machinery rather than its laziness.
#   arm "fanout" — a layered import DAG: the root imports 4 scopes, each of which imports the same
#                  next 4, d layers deep; `imports*`, one rank. Only the deepest layer declares.
#                  The walk tree has (4^(d+1) - 1) / 3 visits; three of every four are leaves.
#   arm "neron"  — gen-scope's `neron` preset (`parent* imports?`) over a `parent` chain of d + 1
#                  scopes, each importing 4 scopes of its own: every import is a leaf in a rank
#                  class with its siblings. Only the chain's end declares. 5(d + 1) visits.
#   arm "chain"  — an `imports` chain of d + 1 scopes, one kid per visit: the shape that has NO leaf
#                  but its last. It guards the other way: a leaf test that taxes every frame reads
#                  here. Only the end declares. d + 1 visits.
{
  arm ? "fanout",
  d ? 3,
}:
let
  S = import ../../. { };
  w = 4;
  name = i: j: if i == 0 && j == 0 then "r" else "l${toString i}-${toString j}";
  width =
    if arm == "fanout" then
      (i: if i == 0 then 1 else w)
    else if arm == "neron" then
      (_: w + 1)
    else if arm == "chain" then
      (_: 1)
    else
      throw "resolve-visible-fanout: no arm ${arm} (fanout | neron | chain)";
  coords = builtins.concatLists (
    builtins.genList (i: builtins.genList (j: { inherit i j; }) (width i)) (d + 1)
  );
  nodes = builtins.listToAttrs (
    map (c: {
      name = name c.i c.j;
      value = {
        id = name c.i c.j;
        type = "n";
        parent = if arm == "neron" && c.j == 0 && c.i < d then name (c.i + 1) 0 else null;
        decls = if c.i == d && c.j == 0 then { v = "hit"; } else { };
        inherit (c) i j;
      };
    }) coords
  );
  importsOf =
    id:
    let
      n = nodes.${id};
    in
    if arm == "neron" then
      (if n.j == 0 then builtins.genList (k: name n.i (k + 1)) w else [ ])
    else if n.i >= d then
      [ ]
    else
      builtins.genList (name (n.i + 1)) (width (n.i + 1));
  ev =
    S.eval { parseParent = id: nodes.${id}.parent; }
      {
        children = _: _: { };
        imports = _: importsOf;
        marks = _: _: [ ];
      }
      {
        inherit nodes;
        nodeOrder = map (c: name c.i c.j) coords;
      };
  imports' = {
    wf = S.wellFormed {
      alphabet = [ "imports" ];
      expression = "imports*";
    };
    order = S.labelOrder {
      alphabet = [ "imports" ];
      layers = [ [ "imports" ] ];
      endOfPath = -1;
    };
  };
  q = (if arm == "neron" then { inherit (S.neron) wf order; } else imports') // {
    mode = "visible";
    dataFilter = n: n.decls.v or null;
    group = "k";
  };
in
# The fanout arm declares on every deepest scope's (i, 0), one per walk-tree path to it, so it answers
# 4^(d-1) values; the neron and chain arms answer one. The answer count is part of the reading, so a
# resolution that dropped its candidates cannot read cheap.
map (a: a.node) (S.resolve q ev "r").answers
