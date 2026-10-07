# The input type every entry taking a materialized node set demands, and its refusal.
#
# It lives in its own module because two modules need it — the evaluators and the cold fold — and
# because it is INTERNAL: the assembly point binds it and hands it on, but does not merge it into
# the published surface. A guard is not a consumer-facing construct.
#
# `kindSetDefect` is `cascade.nix`'s, for the reason `require-declared-dependencies.nix` takes
# `graph`: the registry TYPE is decided beside the fold that mints its kinds, and the REFUSAL belongs
# at the door where the defect is. The assembly point binds the two together.
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
# The record's `kinds` field is the second conjunct of the same input type, and it is a TYPE check,
# not a provenance one: every entry must be a kind `mkKinds` minted, filed under its own name, and
# coherent with every resolved `below` that reaches it (`cascade.nix`, `kindSetDefect`). A registry
# of declarations is refused as one, by name.
#
# ★ TERMINATION DOES NOT REST ON THIS DOOR. Every minted kind has a finite `depth`, and the spawn
# channel follows resolved kind records (`eval.nix`, `kindOf`), so any collection of minted kinds,
# a `//` merge included, expands finitely. What the door refuses is a registry that is not made of
# kinds at all, and one whose name map disagrees with the kinds its own entries resolved, which a
# reader looking a kind up by name would silently get wrong.
#
# ★ ABSENT AND `null` ARE BOTH THE NO-KINDS CASE AND BOTH PASS, read as `scope.kinds or null`.
# `buildRoots`' own default is `null`, callers that declare no types pass no registry, and a
# hand-built record need not carry the field — a node set with no kinds has nothing to spawn and
# therefore nothing to bound.
#
# ── AND EVERY NODE'S KIND VALUE AGREES WITH ITS KIND'S (den-hoag-l0y) ──
# A kind carries its gen-schema kind value and every node of it carries the same one; gen-select
# matches `sel.kind` on the NODE's copy. A hand-built record whose node of registered kind K carries
# a value K does not declare gives the node two kinds that silently disagree — the registry's and
# the carried one — which is the registry door's own coherence defect at node grain. So it is
# refused by name, decided by `cascade.nix`'s `sameKindValue`: the mark, then at an equal mark the
# sealed subjects through gen-algebra's `sealedCollisionEq`. Decided ONCE per scope: only a
# registry in which some kind declares a value is walked, so a scope whose kinds declare none pays
# nothing per node. A node omitting the field is admitted (it stays kind-blind at `sel.kind`, and
# is refused there by name); a node carrying a value in a scope whose registry declares none is the
# node's own declaration and is admitted too.
{
  prelude,
  kindSetDefect,
  sameKindValue,
}:
{
  requireScope =
    entry: scope:
    let
      must = "gen-scope.${entry}: `scope` must be the record returned by `buildRoots` ({ nodes, nodeOrder })";
      pass = "A node map alone no longer carries the declared order — pass the whole record.";
      bad = detail: throw "${must}; ${detail}. ${pass}";

      kinds = scope.kinds or null;
      kindsDefect = if kinds == null then null else kindSetDefect kinds;
      kindsMust = "gen-scope.${entry}: `scope.kinds` must be a kind registry, whose `kinds` maps each name to the kind `mkKinds` minted under it";
      kindsPass = "Mint the kinds with `mkKinds` over their declarations and pass the result.";
      badKinds = detail: throw "${kindsMust}; ${detail}. ${kindsPass}";

      contradicting =
        if !(prelude.any (k: k.kindValue != null) (prelude.attrValues kinds.kinds)) then
          [ ]
        else
          builtins.filter (
            id:
            let
              n = scope.nodes.${id};
              t = n.type or null;
            in
            n ? kindValue
            && builtins.isString t
            && kinds.kinds ? ${t}
            && !(sameKindValue "gen-scope.${entry}: node '${id}' of kind '${t}'" n.kindValue
              kinds.kinds.${t}.kindValue
            )
          ) (builtins.attrNames scope.nodes);
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
    else if kindsDefect != null then
      badKinds kindsDefect
    else if kinds == null || contradicting == [ ] then
      scope
    else
      let
        id = builtins.head contradicting;
        t = scope.nodes.${id}.type;
      in
      throw "gen-scope.${entry}: node '${id}' of kind '${t}' carries a `kindValue` that is not the one its kind declares (compared by the kind value's mark and, at an equal mark, its sealed subjects). A node of a registered kind carries its kind's value, and a different one gives the node two kinds that disagree. Build the scope with `buildRoots`, which stamps the value, or carry the kind's own value.";
}
