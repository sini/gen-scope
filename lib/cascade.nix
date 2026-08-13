# The demand cascade's kind registry — the downward-only DAG whose depth stratifies a run.
#
# `mkKind` builds one kind record and refuses a `dedupKey` without a `fold` and a `fold` without a
# `dedupKey`: grouping and merging are only meaningful together, so the pairing is a
# registration-time error rather than a resolution-time surprise. `mkKinds` validates the whole
# set — name uniqueness, `below`-name resolution, acyclicity — and publishes the per-kind `depth`
# measure with its maximum.
#
# ── THE DEPTH MEASURE AND THE ACYCLICITY VERDICT ARE ONE READ, AND THE READ IS NOT THIS LIBRARY'S ──
# Both come from the graph library's cone-rank surface, over the accessor the registry already
# holds. Nothing here re-implements the recurrence, and the reason is a cost fact rather than a
# preference: a plain per-node recursion over `below` never consults the map it is building, so a
# node reachable by several paths is re-expanded once per path and the walk is exponential on a
# shared producer. The graph library binds its rank map through a fixed point — every node forced
# at most once — and warms it in a producers-first sequence, so the descent stays flat. A second
# recurrence here would be a slower copy of a construction that already ships, and it would be a
# per-node recursive descent, which this engine does not build.
#
# The verdict rides the same read. A cyclic `below` relation has no producers-first rank, and the
# rank surface refuses it BY NAME rather than answering. So acyclicity is not a guard bolted onto
# the registry — it is what asking for the measure already costs, and the registry forces that
# answer at the point of registration so a cyclic set is refused where it is DEFINED and not where
# some later reader happens to touch a field.
#
# ── THE UNRESOLVED-NAME REFUSAL DOMINATES THE PATH TO THE MEASURE ──
# The rank surface restricts each node's producers to the cone it was handed, so an edge naming
# something unregistered is not an error there — it is ABSENT, and the node reports as a leaf at
# depth 0 with no diagnostic. That is a silent wrong answer, so the registry must refuse the
# unregistered name itself, and it is not enough for the check merely to exist: this is a lazy
# language and sibling bindings have no evaluation order, so a check bound beside the measure is a
# check a reader can step around. What holds instead is DOMINATION — the record carrying the
# measure is constructed only inside the branch the refusal falls through to, so no path reaches a
# depth value without the refusal having been decided.
#
# ── ONLY THE MEASURE IS CONSUMED ──
# The rank surface publishes a linearisation beside its depth map, and this construction reads the
# depth map alone. Two topological linearisations of the same relation can differ element for
# element and both be correct, so a consumer that reads one has taken on a cross-library contract
# about which valid answer it gets. The depth map carries no such freedom: it is a function of the
# relation, identical under any tie-break.
#
# THEORY. Acyclicity is the stratifiability condition made a definition-time error. The measure is
# the longest path to a leaf: `depth k = 0` where `k` has no registered successor, else
# `1 + max { depth b : b ∈ below(k) registered }`. Every `below` edge to a REGISTERED name
# therefore strictly decreases it — `b` is in the cone, hence among `k`'s producers, hence
# `depth k ≥ 1 + depth b > depth b` — and a strictly decreasing natural-number measure is what
# makes the cascade terminate by Noetherian induction on ℕ, in `maxDepth + 1` strata, as a theorem
# about the measure rather than an iteration budget. The restriction to registered names costs the
# theorem nothing: the filter removes only names outside the cone, and an unregistered name is
# refused above before any measure exists.
{ prelude, graph }:
let
  inherit (builtins)
    isList
    isString
    length
    seq
    toJSON
    ;
  inherit (prelude)
    attrValues
    concatMap
    filter
    listToAttrs
    map
    max
    nameValuePair
    unique
    ;

  kindMarker = "gen-scope/kind";
  kindSetMarker = "gen-scope/kind-set";

  mkKind =
    {
      name,
      below ? [ ],
      resolve,
      dedupKey ? null,
      fold ? null,
    }:
    let
      hasDedup = dedupKey != null;
      hasFold = fold != null;
    in
    if !isString name then
      throw "gen-scope.mkKind: `name` must be a string"
    else if hasDedup && !hasFold then
      throw "gen-scope.mkKind: kind '${name}' declares `dedupKey` without `fold` (a fold is required to merge grouped fragments)"
    else if hasFold && !hasDedup then
      throw "gen-scope.mkKind: kind '${name}' declares `fold` without `dedupKey` (a fold has nothing to merge without grouping)"
    else
      {
        _type = kindMarker;
        inherit
          name
          below
          resolve
          dedupKey
          fold
          ;
      };

  mkKinds =
    kindsArg:
    let
      kindList = if isList kindsArg then kindsArg else attrValues kindsArg;
      names = map (k: k.name) kindList;

      duplicates = unique (filter (n: length (filter (m: m == n) names) > 1) names);

      kinds = listToAttrs (map (k: nameValuePair k.name k) kindList);

      allBelow = unique (concatMap (k: k.below) kindList);
      unresolved = filter (b: !(kinds ? ${b})) allBelow;

      # One read: the measure and the acyclicity verdict come out of the same call, over the
      # relation the registry already describes.
      ranked = graph.coneRank {
        nodes = names;
        edges = n: kinds.${n}.below;
      } names;

      # Taken over the published map, which is total on the registered names, so every kind's
      # depth lies in `[0, maxDepth]` and a schedule enumerating that range reaches all of them.
      maxDepth = prelude.foldl' max 0 (attrValues ranked.depth);
    in
    if duplicates != [ ] then
      throw "gen-scope.mkKinds: duplicate kind name(s): ${toJSON duplicates}"
    else if unresolved != [ ] then
      throw "gen-scope.mkKinds: `below` names with no registered kind: ${toJSON unresolved}"
    else
      # Forcing the ranked record here is what makes a cyclic relation a definition-time refusal:
      # the verdict is decided as the registry is built, not when a reader first wants a depth.
      seq ranked {
        _type = kindSetMarker;
        inherit kinds maxDepth;
        inherit (ranked) depth;
      };
in
{
  inherit mkKind mkKinds;
}
