# The input type every entry taking a materialized node set demands, and its refusal.
#
# It lives in its own module because two modules need it — the evaluators and the cold fold — and
# because it is INTERNAL: the assembly point binds it and hands it on, but does not merge it into
# the published surface. A guard is not a consumer-facing construct.
#
# `isKindSet` is `cascade.nix`'s, for the reason `require-declared-dependencies.nix` takes `graph`:
# the DISCRIMINATOR belongs with the constructor that writes the tag, and the REFUSAL belongs at the
# door where the defect is. The assembly point binds the two together.
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
#
# ── AND THE REGISTRY THE RECORD CARRIES ──
# The record's `kinds` field is the second conjunct of the same input type, and it is an ACCEPT-LIST
# for `require-declared-dependencies.nix`'s reason: the registry `mkKinds` returns is admitted, and
# everything else is refused rather than a roster of known-bad shapes being enumerated.
#
# ★ WHAT THE TAG BUYS IS TERMINATION. `mkKinds` forces `graph.coneRank` over the whole `below`
# relation as it builds, so a tagged registry's `below` is acyclic; `mkKind` already refuses
# `spawns ⊄ below`, so every spawn strictly descends an acyclic rank and the spawn expansion in
# `eval.nix` is bounded. An untagged registry decides none of that, and the evaluator reading it
# does not diverge politely — it exceeds the call depth, which `tryEval` DOES NOT CONTAIN. So the
# caller gets no value to act on at all unless this door refuses first.
#
# ★ ABSENT AND `null` ARE BOTH THE NO-KINDS CASE AND BOTH PASS, read as `scope.kinds or null`.
# `buildRoots`' own default is `null`, callers that declare no types pass no registry, and a
# hand-built record need not carry the field — a node set with no kinds has nothing to spawn and
# therefore nothing to bound.
{ prelude, isKindSet }:
{
  requireScope =
    entry: scope:
    let
      must = "gen-scope.${entry}: `scope` must be the record returned by `buildRoots` ({ nodes, nodeOrder })";
      pass = "A node map alone no longer carries the declared order — pass the whole record.";
      bad = detail: throw "${must}; ${detail}. ${pass}";

      kinds = scope.kinds or null;
      kindsMust = "gen-scope.${entry}: `scope.kinds` must be the registry `mkKinds` returns";
      kindsPass = "Build it with `mkKinds` and pass the result: the `below` relation's acyclicity is decided where the registry is constructed, so a value this entry cannot tell apart from a registered one is one it must refuse.";
      badKinds = detail: throw "${kindsMust}; ${detail}. ${kindsPass}";
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
    else if kinds == null || isKindSet kinds then
      scope
    else if builtins.isAttrs kinds then
      badKinds "received an attrset that `mkKinds` did not build"
    else
      badKinds "received a ${builtins.typeOf kinds}";
}
