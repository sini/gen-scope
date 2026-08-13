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
# ── THE REGISTRY VALIDATES ITS OWN INTAKE, AND DOES NOT DELEGATE THAT TO THE CONSTRUCTOR ──
# `mkKind` refuses a `name` that is not a string and a `below` that is not a list of them, at the
# construction site, where the author is and where the kind can be named. That is not enough on
# its own, because `mkKinds` receives whatever a caller hands it and a record that never passed
# through `mkKind` carries none of those guarantees. A precondition that a function's OWN
# evaluation depends on cannot be delegated to a constructor its input may not have visited, so
# the registry decides well-formedness itself, at intake, ahead of everything else.
#
# What it decides is both halves, and only one of them is a proof.
#
# The marker answers PROVENANCE, and it answers it for a COOPERATIVE CALLER: a record that came out
# of the constructor has been through everything the constructor refuses, while a record that
# merely writes the token has asserted something about its own origin that nothing here can check.
# So what the token does NOT establish is exactly the three fields the constructor writes and the
# intake never reads — `resolve`, `dedupKey` and `fold`. A record carrying `_type`, `name` and
# `below` alone registers, and it has no resolver. ANYTHING DOWNSTREAM THAT NEEDS ONE MUST SAY SO
# ITSELF: a registered kind is not evidence that one is there.
#
# The field checks answer USABILITY, and they are the half that holds against any input at all —
# `name` is used as an attribute name and `below` as a list of them, and those obligations are the
# registry's own whether or not the token in front of them is honest. That is why they sit beside
# the marker rather than behind it.
#
# The stakes are what makes these refusals rather than documentation: a non-string reaching an
# attribute position aborts with a type error, and a type error is not a value — it terminates the
# evaluation and no `tryEval` around the call contains it. A caller cannot detect it, cannot
# recover from it, and gets no name to act on. So the shape is decided while it is still data.
#
# ── THE SUBSTRATE'S OWN GUARDS ARE NOT REACHED FOR, AND THE REASON IS RECORDED ──
# The ordering arm beneath the rank surface publishes refusals for a non-string ordering key, for
# two nodes sharing one key, and for an edge naming a node outside the set — three checks that
# overlap this registry's, and called directly it does refuse all three by name and catchably.
# They are still not consumed, on two grounds.
#
# THEY ARE UNREACHABLE THROUGH THE DOOR THE MEASURE COMES FROM. The rank surface sanitises before
# the arm exists: it builds a membership set out of the cone it was handed and filters every edge
# against it, so a node key that is not a string dies building that set and an edge target that is
# not a string dies in the filter — both ahead of the arm, and both UNCATCHABLY. That is measured
# on this library's own pin, and it is the same shape of defect this substrate has been recorded
# carrying before: an exported ordering surface whose abort no caller can contain. Reaching the
# arm's refusals would mean calling the arm instead of the door the measure is taken from, and
# paying a second ordering pass for verdicts the registry is already holding.
#
# AND HALF OF WHAT IS BEING REFUSED IS UPSTREAM OF ANY ACCESSOR AT ALL. An entry that is not an
# attribute set, or that lacks the fields the node list and the edge function are built out of, is
# refused before either can be constructed — no graph surface, arm or door, could have seen it. So
# this check is the registry's whatever the substrate publishes, and what delegation would change
# is only what the caller is told: a refusal about kind registration, reported in a vocabulary of
# node indices and ordering keys.
#
# ── ONLY THE MEASURE IS CONSUMED ──
# The rank surface publishes a linearisation beside its depth map, and this construction reads the
# depth map alone. Two topological linearisations of the same relation can differ element for
# element and both be correct, so a consumer that reads one has taken on a cross-library contract
# about which valid answer it gets. The depth map carries no such freedom: it is a function of the
# relation, identical under any tie-break.
#
# ── WHAT THIS REGISTRY DOES NOT ESTABLISH ──
# Written down rather than left for the next construction to discover, because the next
# construction is what builds on it.
#
# `resolve`, `dedupKey` and `fold` are not type-checked. The pairing between the last two is a
# registration-time error, and that is all: a kind whose resolver is not a function registers here
# and fails wherever it is finally applied. Nothing here constrains what a resolver may RETURN
# either, so the conformance of a returned fragment is not a property this registry has
# established — a consumer that needs plain data must obtain it somewhere else.
#
# And the marker's limit above is the scope of every completeness claim on this page. The intake is
# total on the shapes an ordinary caller can reach; it is not total against a caller who writes the
# constructor's token by hand, and no check on this page makes it so.
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
    attrNames
    isAttrs
    isList
    isString
    length
    seq
    toJSON
    typeOf
    ;
  inherit (prelude)
    all
    attrValues
    concatMap
    filter
    imap0
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
    else if !isList below then
      throw "gen-scope.mkKind: kind '${name}' declares a `below` that is a ${typeOf below} rather than a list"
    else if !(all isString below) then
      throw "gen-scope.mkKind: kind '${name}' declares a `below` holding a name that is not a string"
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

  # The reason an entry is not a kind, or null. Total on any value: each arm establishes what the
  # next one needs, so nothing here reads a field it has not already found. The reason names the
  # defect and never renders the entry — a kind record holds its resolver, and rendering a
  # function is itself an abort no caller can catch, which would replace one uncatchable
  # termination with another while claiming to diagnose it.
  notAKind =
    k:
    if !isAttrs k then
      "is a ${typeOf k} rather than a kind record"
    else if (k._type or null) != kindMarker then
      "was not built by `mkKind`"
    else if !isString (k.name or null) then
      "carries a `name` that is not a string"
    else if !isList (k.below or null) then
      "carries a `below` that is not a list"
    else if !(all isString k.below) then
      "carries a `below` holding a name that is not a string"
    else
      null;

  mkKinds =
    kindsArg:
    let
      # Labelled at intake so a refusal can point at the entry a caller wrote, in the caller's own
      # coordinates: a position for the list form, the attribute name for the attribute-set one.
      labelled =
        if isList kindsArg then
          imap0 (i: k: {
            label = "entry ${toString i}";
            kind = k;
          }) kindsArg
        else
          map (n: {
            label = "entry `${n}`";
            kind = kindsArg.${n};
          }) (attrNames kindsArg);

      malformed = filter (m: m != null) (
        map (
          e:
          let
            reason = notAKind e.kind;
          in
          if reason == null then null else "${e.label} ${reason}"
        ) labelled
      );

      kindList = map (e: e.kind) labelled;
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
    if !(isList kindsArg || isAttrs kindsArg) then
      throw "gen-scope.mkKinds: expected a list or attribute set of kinds, not a ${typeOf kindsArg}"
    else if malformed != [ ] then
      throw "gen-scope.mkKinds: not every entry is a kind record: ${toJSON malformed}"
    else if duplicates != [ ] then
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
