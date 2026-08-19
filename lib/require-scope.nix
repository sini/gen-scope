# The input type every entry taking a materialized node set demands, and its refusal.
#
# It lives in its own module because two modules need it — the evaluators and the cold fold — and
# because it is INTERNAL: the assembly point binds it and hands it on, but does not merge it into
# the published surface. A guard is not a consumer-facing construct.
{ prelude }:
# ── THE INPUT TYPE, REFUSED BY NAME ──
# Every entry taking a materialized node set takes the WHOLE record `buildRoots` returns, not a
# bare node map. The two are near-indistinguishable to a caller and catastrophically different to
# an enumerating read: handed a record, `allNodes` / `allNodeIds` / `allNodesWhere` all answer
# `[ "nodeOrder" "nodes" ]` with no error, and only a lookup of a known id is loud. Making the
# record the input TYPE means that call cannot be written.
#
# ★ THE CHECK IS KEYED ON THE FAILED CONJUNCT, NOT ON A ROSTER OF EXAMPLE SHAPES. A roster leaves
# gaps by construction; the predicate has three conjuncts and each fails as ABSENT or as WRONGLY
# TYPED, so the message names which conjunct and which mode. A key-set predicate would not do:
# a graph whose node ids are literally `nodes` and `nodeOrder` has the same key set as the record,
# and only the TYPE separates them — a node map's `nodeOrder` entry is an attrset, the record's is
# a list.
#
# ★ AND IT IS FORCED BEFORE ANY FIELD IS READ. Written alongside the field reads, Nix would demand
# `scope.nodeOrder` first and throw `attribute 'nodeOrder' missing` — verbatim the generic error
# this refusal exists to replace. `requireScope` returns the scope, so selecting any field of the
# result forces the guard first.
{
  requireScope =
    entry: scope:
    let
      must = "gen-scope.${entry}: `scope` must be the record returned by `buildRoots` ({ nodes, nodeOrder })";
      pass = "A node map alone no longer carries the declared order — pass the whole record.";
      bad = detail: throw "${must}; ${detail}. ${pass}";
    in
    if !(builtins.isAttrs scope) then
      bad "received a ${builtins.typeOf scope}"
    else if !(scope ? nodes) then
      bad "received an attrset with no `nodes`"
    else if !(builtins.isAttrs scope.nodes) then
      bad "received an attrset whose `nodes` is a ${builtins.typeOf scope.nodes}, not an attrset"
    else if !(scope ? nodeOrder) then
      bad "received an attrset with no `nodeOrder`"
    else if !(builtins.isList scope.nodeOrder) then
      bad "received an attrset whose `nodeOrder` is a ${builtins.typeOf scope.nodeOrder}, not a list"
    else
      scope;
}
