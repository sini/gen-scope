# The demand cascade: the downward-only DAG of kinds whose depth stratifies a run, the typed
# request the run consumes, and the stratified resolution itself.
#
# The word "demand" in this library means demand-driven evaluation, and it means only that. The
# request value this cascade carries is a CLAIM — something an author asks for and a resolver
# satisfies — and it is named for what it is rather than for the evaluation strategy that happens
# to drive it.
#
# `mkKind` builds one kind record and refuses a `dedupKey` without a `fold` and a `fold` without a
# `dedupKey`: grouping and merging are only meaningful together, so the pairing is a
# registration-time error rather than a resolution-time surprise. `mkKinds` validates the whole
# set — name uniqueness, `below`-name resolution, acyclicity — and publishes the per-kind `depth`
# measure with its maximum.
#
# ── WHAT THIS FILE STANDS ON, AND THE THREE ANSWERS ARE DIFFERENT IN KIND ──
# TERMINATION is classical mathematics and claims no primary: the round bound is Noetherian
# induction on ℕ over a strictly decreasing measure, argued below where that measure is defined.
# COMPLETENESS is a published result and carries its citation: Apt, Blair & Walker (1988), quoted
# below against the printed pages named there. What is this library's OWN is neither — it is the
# CONSTRUCTION that makes them apply here, and it is stated as original rather than left to read as
# borrowed: a depth measure taken off the graph library's rank surface rather than recomputed, and
# a schedule that IS that measure rather than a linearisation of it. That novelty is an absence
# claim, so the search behind it is named. The stratification literature this project holds — Apt,
# Blair & Walker (1988), Przymusinski (1988), Gelfond & Lifschitz (1988), Van Gelder, Ross &
# Schlipf (1991) — fixes what a stratified schedule MEANS and what model it yields; none of them
# derives a schedule from a registry's own relation, which is the step taken here. A primary that
# does would falsify the claim, and this paragraph is where it would land.
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
# So what the token does NOT establish is WHAT the three fields the constructor writes actually are
# — whether `resolve` is a function of the right shape, whether `dedupKey` returns a string,
# whether `fold` merges anything sensible. Those are questions about values, and the answers live
# where the values are applied.
#
# ★ THEIR PRESENCE IS A DIFFERENT QUESTION, AND THE REGISTRY DOES ANSWER IT. "Is the field there"
# is decidable on any value at all, cheaply and totally, exactly like the `name` and `below` checks
# beside it — and every one of them is READ by a consumer at a point where no refusal can follow.
# A projection of a missing attribute is a type error, and a type error is not a value: it
# terminates the evaluation, `tryEval` does not contain it, and the caller gets no name. So a
# record that registers WITHOUT them would be this registry publishing something it has called a
# kind while leaving the first reader to discover, from an abort, that it is not one. That is the
# failure this intake exists to prevent, and declining it here on the grounds that the token cannot
# vouch for the fields' CONTENTS would be answering a question nobody asked.
#
# ★ AND THE ORDINARY DOOR ALREADY REQUIRES ALL THREE, so this costs a cooperative caller nothing:
# `mkKind` gives `resolve` no default and writes `dedupKey` and `fold` as null when a kind declares
# neither. No record it builds can fail these arms. What they reach is precisely the forged record
# — the one case the marker was never able to speak for.
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
# `resolve`, `dedupKey` and `fold` are PRESENT on anything that registers, and each is APPLICABLE —
# a function, or an attribute set this evaluator applies. The pairing between the last two is a
# registration-time error. What is NOT established is everything past the point of application, and
# the boundary is drawn where a check stops being possible rather than where it stops being
# convenient:
#
#   · ARITY IS NOT CHECKED, and it is not checkable. A resolver taking one argument is applicable,
#     is applied, returns a value, and that value is then applied again — so it fails with the same
#     uncatchable type error a non-function does. This language offers no predicate that decides
#     how many arguments a value will accept, so this is a bound with a reason and not an omission.
#     ★ It is the one member of the uncatchable class left open, and it is left open knowingly.
#   · WHAT A RESOLVER'S ANSWER CONTAINS is unconstrained: the CONFORMANCE of a resource fragment —
#     whether it is plain data, whether it is a function — is not a property established anywhere in
#     this library, and a consumer needing that must obtain it elsewhere. ★ This is about the VALUES
#     inside the answer. The answer's own SHAPE is not left open and never was: the record itself
#     and the three containers the run reads off it are decided at the point the resolver returns,
#     because `isAttrs` and `isList` decide them on any value and the alternative is a type error
#     with no kind and no path in it — or, for a record that is not a set at all, no error and no
#     output either.
#   · WHAT A `dedupKey` RETURNS is checked, but at APPLICATION and not here: a non-string grouping
#     key is a named refusal carrying the kind and the path, which is where the value first exists.
#
# ⇒ the line is not "existence, not shape". Two shape properties ARE decided — a `below` that is a
# list of strings, and applicability — because both are decidable on any value, cheaply and totally,
# and both are read where no refusal could follow. What sits past the line is what this evaluator
# gives no predicate for, and what has no meaning until a value is in hand.
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
#
# ══ THE RUN ══
#
# ── THE SCHEDULE IS THE MEASURE, NOT A LINEARISATION ──
# The run visits the strata in DESCENDING depth, `[ maxDepth … 0 ]`, because a kind at depth `d`
# emits only into strictly smaller depths: here EARLIER means LARGER. That list is consecutive
# integers read straight off the measure — no sort, no ties, no tie-break — so a claim's position
# in the run is a function of the relation and not of which valid answer an ordering algorithm
# happened to return. Two topological linearisations of one relation can differ element for element
# and both be correct, and a run whose positions were taken from one would silently mean something
# different under the other.
#
# The schedule's LENGTH is the loop's bound, and it is a theorem rather than a budget: the measure
# is a natural number that strictly decreases along every registered `below` edge, so `maxDepth + 1`
# rounds exhaust it by Noetherian induction on ℕ. Nothing here tests for convergence and nothing
# here caps the iteration.
#
# ── COMPLETENESS, WHICH IS WHAT STRATIFICATION BUYS, AND IT IS NOT A VISIBILITY RULE ──
# When a stratum runs, every stratum earlier in the schedule has finished: its claims are all
# resolved and its fact set is closed. That is what makes the per-stratum aggregation — the dedup
# fold over a kind's resource fragments — meaningful, and it is the classical reason aggregation
# demands stratification.
#
# THEORY. Apt, Blair & Walker (1988), "Towards a Theory of Declarative Knowledge", in Minker (ed.),
# pp. 89–148, §"Stratified Programs", Definition 3 (printed p. 96), stratify a program so that a
# relation occurring POSITIVELY in a stratum is defined within that stratum or below, and a relation
# occurring NEGATIVELY is defined strictly below. The invariant this buys is the standard model
# built stratum by stratum, `M_i = T_{P_i}↑ω(M_{i-1})` (printed p. 108) — each stratum reaches its
# own fixed point before the next begins. Strictly-lower indexing is their rule for the NEGATIVE
# case and a sufficient condition for completeness, not the property itself; this
# cascade has no negation anywhere, so what it takes from the construction is completeness alone.
# A resolver may therefore read anything the caller handed it. If a negated read is ever added
# here, ABW's second clause acquires a subject and the strictly-lower rule applies to it — that
# would be a change to this construction, not something it absorbs quietly.
#
# ── WHAT A RESOLVER SEES, AND WHY THE LIST IS EXHAUSTIVE ──
# A resolver receives the claim's own fields plus `_path`, and the caller's constant context. It
# receives no resolved state at all: no resources, no wiring, no trace, no partial view of the run.
# This is the emission ⊥ consumption invariant of the claim/provide design — what a resolver
# EMITS and what it CONSUMES are separated by construction, so no resolver's answer can depend on
# where in a stratum it ran. The engine's own bookkeeping channel is stripped; everything else the
# claim carries, INCLUDING ITS TYPE MARKER, is passed through. That list is the whole of it, and it
# is written here because a view documented as "its own fields and nothing else" while carrying a
# marker is a surface whose readers are told something false about it.
#
# ── ABSENCE MEANS NOT REGISTERED ──
# The result is TOTAL on what was declared. A registered kind that no claim ever named still gets
# an entry in `resources` — an empty one — and a subject that nothing wired still gets an entry in
# `wiring`, with an empty `byKind`. So a consumer reading past a missing key learns something
# definite: the key was never registered, rather than registered and quiet. The alternative makes
# "no claims of this kind" and "no such kind" the same observation, which is a distinction the
# caller cannot recover from anywhere else.
#
# ── THE TRACE IS A RECORD, AND DELIBERATELY NOT AN ALGEBRA ──
# Each resource key maps to the claims that produced it, each wiring entry to the claim that
# emitted it, and each claim to its parent chain. THEORY: this is why/derivation provenance in the
# sense of Cheney, Chiticariu & Tan (2009). The provenance SEMIRING of Green, Karvounarakis & Tannen
# — annotations carrying a `(+, ×)` algebra that composes under the query operators — is
# DELIBERATELY NOT REALIZED here and is not planned: these traces are records about a run, not
# algebraic values, and nothing in this library computes with them.
#
# ── THE LOOP CARRIES NO REFUSAL, AND THE REFUSALS IT DOES NOT CARRY ARE INEXPRESSIBLE ──
# A backward or same-stratum emission is not detected, because it cannot be written: a sub-claim's
# kind must be a registered member of the emitting kind's `below` set, and every such member has
# strictly smaller depth, hence a strictly later position in the schedule. There is no check to
# meet or miss.
#
# A claim the run did not settle is RETURNED as `unrun`, never thrown. Over a registry this library
# built the list is always empty — the measure is total on the registered names and the schedule
# enumerates its whole range — so `unrun` is a fact the caller can read rather than a coincidence
# they have to trust. For a caller whose registry says something the run cannot honour, a refusal
# would destroy the very information they need.
#
# ── `unrun` IS WHAT THE LOOP DID NOT SETTLE, AND THAT IS NOT THE SAME AS AN UNSCHEDULED STRATUM ──
# The registry the run is handed may be a record it did not build. The kind-set marker answers
# PROVENANCE for a cooperative caller, exactly as the kind marker does, and what it does NOT
# establish is that `depth` and `maxDepth` are the measure of the `kinds` beside them: a record can
# carry the token and a depth map that no `below` relation would produce. Nothing here can check
# that, and refusing every record that merely writes the token would remove the pass-through the
# run exists to offer.
#
# What that costs is bounded by where the answer is read from. "Not settled" is a fact about the
# LOOP — the claims it created minus the claims it resolved — and it is that difference that is
# reported. Deriving it instead from stratum membership in the schedule would be a PROXY: equivalent
# to the property only while the depth map really is the rank of the relation, and wrong in exactly
# the case the paragraph above says cannot be checked. Under such a registry a claim could go
# unresolved while the proxy called it scheduled, and its kind would report an empty entry —
# indistinguishable from a kind nobody claimed, which is the one reading the totality rule exists to
# rule out. The difference has no proxy in it, so the two ways a registry can be wrong — a maximum
# that does not cover the measure, and a measure that is not the relation's — are both reported and
# neither is silent.
{
  prelude,
  graph,
}:
let
  inherit (builtins)
    attrNames
    isAttrs
    isBool
    isFunction
    isInt
    isList
    isString
    length
    removeAttrs
    seq
    toJSON
    typeOf
    ;
  inherit (prelude)
    all
    attrValues
    concatLists
    concatMap
    elem
    elemAt
    filter
    foldl'
    groupBy
    head
    imap0
    iterateBounded
    listToAttrs
    map
    mapAttrs
    max
    nameValuePair
    range
    sort
    tail
    unique
    ;

  # The per-round forcing this engine already defines, bound where it lives rather than written a
  # second time: two copies of a discipline agree only for as long as someone keeps them in step.
  leastModelLib = import ./least-model.nix { inherit prelude; };
  inherit (leastModelLib) forceFields;

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

  # Whether a value can be APPLIED — approximated, because the exact property is not decidable by
  # any terminating predicate and the approximation is chosen to err in the safe direction.
  #
  # `isFunction` alone is too NARROW: it is false for an attribute set carrying `__functor`, which
  # this evaluator applies perfectly well. Carrying the attribute is too WIDE: applying such a set
  # evaluates `v.__functor v arg`, so what gets applied is the attribute's VALUE, and a `__functor`
  # holding an integer aborts at the call site exactly as a bare integer would. Both are the same
  # defect — a predicate that does not decide the property it is named for — pointed in opposite
  # directions.
  #
  # ★ WHY ONE LEVEL AND NOT A WALK. The `__functor` chain has no bound, and it can refer to itself:
  # `let f = { __functor = f; }; in f` is a value whose application diverges, so a predicate that
  # followed the chain would diverge deciding it. A depth ceiling would be a number nobody can
  # justify. One level is what terminates on every input.
  #
  # WHAT THAT COSTS: a NESTED functor applies, and this admits only the first level, so it refuses
  # the deeper ones. Measured at TWO, THREE AND FOUR levels — each evaluates to its innermost
  # function — which is a sample and not an induction; nothing here claims a depth that was not run.
  # The approximation therefore errs toward refusing working input rather than admitting input that
  # aborts, which is the direction where the caller gets a name instead of a dead evaluation.
  callable = v: isFunction v || (isAttrs v && v ? __functor && isFunction v.__functor);

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
    else if !(k ? resolve) then
      "carries no `resolve` field"
    else if !(k ? dedupKey) then
      "carries no `dedupKey` field"
    else if !(k ? fold) then
      "carries no `fold` field"
    else if !(callable k.resolve) then
      "carries a `resolve` that cannot be applied"
    else if k.dedupKey != null && !(callable k.dedupKey) then
      "carries a `dedupKey` that is neither null nor applicable"
    else if k.fold != null && !(callable k.fold) then
      "carries a `fold` that is neither null nor applicable"
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
      maxDepth = foldl' max 0 (attrValues ranked.depth);
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

  # A registry, or the raw kinds to build one out of. A caller who already registered hands the
  # record back and pays nothing; one who did not gets registration, with every refusal above.
  # Internal: the run needs it, and a caller reaching a registry through this instead of through
  # `mkKinds` would be relying on a shortcut whose whole purpose is that the run does not care
  # which of the two it was given.
  #
  # THE PASS-THROUGH IS THE SAME COOPERATIVE-CALLER BARGAIN THE KIND MARKER MAKES, AND IT HAS THE
  # SAME LIMIT. A record that came out of `mkKinds` carries a `depth` that is the rank of its own
  # `below` relation and a `maxDepth` that covers it; a record that merely writes the token has
  # asserted that and nothing here can check it. So what the token does NOT establish is the
  # agreement between `kinds`, `depth` and `maxDepth` — and the run is built so that a disagreement
  # is REPORTED rather than absorbed: it reads what it settled, never what the record declared.
  asKindSet =
    kinds: if isAttrs kinds && (kinds._type or null) == kindSetMarker then kinds else mkKinds kinds;

  claimMarker = "gen-scope/claim";

  # The engine's own field names, reserved against payload shadowing. A payload attempting any of
  # them is claiming a channel that is already spoken for, and letting it win would mean a resolver
  # reading an engine field that an author wrote.
  #
  # `kind` and `subject` are reserved too and are NOT in this list, because they are not shadowable:
  # the payload is what remains after both are taken out of the arguments, so an author writing
  # `kind` has set the kind rather than shadowed it. A check over a domain two of whose members no
  # input can reach reads as coverage it does not have.
  engineKeys = [
    "_type"
    "_path"
    "_reserved"
  ];

  # The kind NAME a `kind` field denotes: a kind record's own name, or the name itself. Total on
  # any value — anything that is neither yields something that is not a string, which the
  # constructor refuses. There is one decision, and it is made there rather than half here.
  kindNameOf = k: if isAttrs k && (k._type or null) == kindMarker then k.name or null else k;

  mkClaim =
    args:
    let
      payload = removeAttrs args [
        "kind"
        "subject"
      ];
      shadowed = filter (k: elem k engineKeys) (attrNames payload);
      # Canonicalized in the CONDITION of the chain below, not in a field of the record it
      # returns. A record is already in weak head normal form before any of its fields is looked
      # at, so a malformed kind bound as a field is a refusal that travels — it fires wherever
      # something finally forces that field, arbitrarily far from the site an author can fix. The
      # missing-field refusals are eager; there is no reason for this one to be the exception.
      kindName = kindNameOf (args.kind or null);
    in
    if !(args ? kind) then
      throw "gen-scope.mkClaim: missing required field `kind`"
    else if !(args ? subject) then
      throw "gen-scope.mkClaim: missing required field `subject`"
    else if !isString kindName then
      throw "gen-scope.mkClaim: `kind` must be a kind value carrying a string `name`, or a kind-name string, not a ${typeOf args.kind}"
    else if shadowed != [ ] then
      # Refused HERE, where the author is, and on the same terms as the three arms above. The
      # earlier reading — that a constructor holds no path and so should hand the violation on for
      # the run to report with one — is contradicted by its own siblings: a missing `kind` is
      # refused with no path at all, and nobody is worse off for it. A site an author can fix is
      # the arguments they just wrote, not a coordinate in a run they have not started.
      throw "gen-scope.mkClaim: payload shadows engine field(s) ${toJSON shadowed} (kind '${kindName}')"
    else
      # Payload first, fixed fields last: the marker, the kind and the subject are authoritative
      # over anything an author wrote. `_reserved` is written empty and stays the channel a record
      # that did NOT come through here can declare a violation on — the run refuses on it, which is
      # what keeps that refusal reachable for exactly the records the marker cannot vouch for.
      payload
      // {
        _type = claimMarker;
        kind = kindName;
        subject = args.subject;
        _reserved = [ ];
      };

  # A display string for a subject. Output only: identity is `id_hash` and never this.
  #
  # ★★ TOTAL, AND ON A STRING — because every refusal in this module interpolates it, and a message
  # is built at exactly the moment something has already gone wrong. Each arm below asked whether a
  # field was PRESENT and then returned it unexamined, so a subject carrying a non-string `name`,
  # `rendered` or `id_hash` made the DIAGNOSTIC coerce a non-string and terminate the evaluation —
  # in place of the named refusal that was about to be thrown, and for exactly the inputs those
  # refusals exist to catch. A refusal that cannot render its subject is not a refusal; it is the
  # same abort wearing a different stack.
  #
  # So each arm asks whether the field can BE a rendering, not whether it is there, and the fallback
  # is a literal. There is no input for which this returns a non-string.
  renderSubject =
    e:
    let
      shown = f: isAttrs e && isString (e.${f} or null);
    in
    if !isAttrs e then
      "<non-entity>"
    else if shown "name" then
      e.name
    else if shown "rendered" then
      e.rendered
    else if shown "id_hash" then
      e.id_hash
    else
      "<unrenderable-subject>";

  # Total rendering of an arbitrary caller value inside a diagnostic. `toJSON` ABORTS on anything
  # containing a function, at any depth, so a message that renders a value it did not choose is a
  # message that can kill the evaluation it was written to explain. Scalars and name lists render in
  # full because those are the shapes a caller can act on; anything else is named by its type, which
  # is total on every value.
  renderValue =
    v:
    if isString v || isInt v || isBool v || v == null then
      toJSON v
    else if isList v && all isString v then
      toJSON v
    else
      "<a ${typeOf v}>";

  hasId = e: isAttrs e && e ? id_hash;

  # Carrying an identity is not the same as carrying a USABLE one. `id_hash` becomes an ATTRIBUTE
  # NAME — the result keys its subjects by it — and a non-string attribute name is a type error at
  # the point the result is assembled, far from the claim that supplied it, uncatchably and with no
  # mention of a subject at all. So the two questions are asked separately: whether an identity was
  # supplied, and whether the one supplied can be what the engine needs it to be.
  hasUsableId = e: hasId e && isString e.id_hash;

  # Lexicographic order over integer-list paths — roots by intake index, children by parent path
  # plus emission index — which is a strict total order because one stratum's paths are distinct
  # by construction. Written as a scan over the common prefix rather than as a walk that calls
  # itself on the tail: a self-applying loop spends one evaluator frame per element and past the
  # call-depth guard it aborts uncatchably, and this comparison is the sort key of every stratum.
  #
  # ★ THE PREFIX ARM — the length comparison reached when neither path differs from the other
  # inside the shared prefix — IS WHAT MAKES THIS COMPARATOR TOTAL, AND NO INPUT THE CASCADE CAN
  # BUILD REACHES IT. Two paths are prefix-related only when one is an ancestor of the other, and
  # a child's path is created DURING the round that resolves its parent, after that round's item
  # set was selected — so no two items sorted together are ever prefix-related, whatever the
  # registry says. The arm is therefore an obligation of the comparator rather than a reachable
  # state of the run, and nothing in the suite pins it: `sort` is undefined on a partial order,
  # so it is not removable, and it is not testable from outside this module either. Written down
  # rather than left as a branch a reader assumes some fixture covers.
  pathLt =
    a: b:
    let
      shared = if length a < length b then length a else length b;
      differing = filter (i: elemAt a i != elemAt b i) (range 0 (shared - 1));
    in
    if differing == [ ] then
      length a < length b
    else
      let
        i = head differing;
      in
      elemAt a i < elemAt b i;

  resolveClaims =
    {
      kinds,
      claims,
      ctx ? { },
    }:
    let
      kindSet = asKindSet kinds;
      ks = kindSet.kinds;
      inherit (kindSet) depth maxDepth;

      # ── the registry's SHAPE, which is this run's precondition and not the registry's claim ──
      # A record the run built satisfies all of this and pays nothing for the check. A record that
      # merely carries the marker may not, and the three fields below are read where no refusal can
      # follow: `maxDepth` enters integer arithmetic and a kind's `depth` entry is projected while
      # a child is being built. Both are TYPE ERRORS if the shape is wrong, and a type error is not
      # a value — it terminates the evaluation and `tryEval` around the call does not contain it,
      # so a caller gets no name and no way to recover. Measured on this evaluator: `tryEval` holds
      # a `throw` and does not hold a missing attribute.
      #
      # WHAT THIS DOES NOT CHECK, and the line is deliberate: whether `depth` is the RANK of the
      # `below` relation. Deciding that means computing the rank, which is what registration is
      # for, and a run that recomputed it would make the pass-through pointless. A depth map that
      # is well-shaped and wrong is admitted — and the run reports what it did not settle, so the
      # claims such a map strands are named rather than dropped.
      registryDefect =
        if !isAttrs (kindSet.kinds or null) then
          "carries no `kinds` attribute set"
        else if !isAttrs (kindSet.depth or null) then
          "carries no `depth` attribute set"
        else if !isInt (kindSet.maxDepth or null) then
          "carries a `maxDepth` that is not an integer"
        else
          let
            registered = attrNames kindSet.kinds;
            # The same question the registration door asks, asked again on the door that skips it.
            # A record carrying the kind-set token was never handed to `mkKinds`, so no entry in it
            # has met `notAKind` — and this run projects `below`, `resolve`, `dedupKey` and `fold`
            # off those entries at points where a missing one is a type error rather than a
            # refusal. Deciding it here and not there would be this run publishing an empty entry
            # for something it never established was a kind, which is the reading the registration
            # door exists to prevent; the token cannot vouch for the entries any more than the kind
            # token vouches for the fields inside one.
            malformed = filter (m: m != null) (
              map (
                n:
                let
                  reason = notAKind kindSet.kinds.${n};
                in
                if reason == null then null else "`${n}` ${reason}"
              ) registered
            );
            undepthed = filter (n: !(kindSet.depth ? ${n})) registered;
          in
          if malformed != [ ] then
            "holds entries that are not kind records: ${toJSON malformed}"
          else if undepthed != [ ] then
            "registers kind(s) ${toJSON undepthed} with no `depth` entry"
          else
            null;

      # ── the refusal chain, shared by intake and emission ──
      # `chain` names the emitting claim for a sub-claim's errors, and is empty for a root. Each
      # arm establishes what the next one reads, so the chain is total on any value: a claim that
      # is not a claim is refused before anything asks it for a kind.
      validate =
        { path, chain }:
        c:
        let
          pathStr = toJSON path;
          rendered = renderSubject (c.subject or null);
        in
        if !(isAttrs c && (c._type or null) == claimMarker) then
          throw "gen-scope.resolveClaims: value at path ${pathStr} is not a claim (build it with `mkClaim`)${chain}"
        else if !isString (c.kind or null) then
          throw "gen-scope.resolveClaims: claim at path ${pathStr} carries a `kind` that is a ${typeOf (c.kind or null)} rather than a string${chain}"
        else if !(ks ? ${c.kind}) then
          throw "gen-scope.resolveClaims: unknown kind '${toString c.kind}' at path ${pathStr}${chain}"
        else if (c._reserved or [ ]) != [ ] then
          throw "gen-scope.resolveClaims: claim at path ${pathStr} (kind '${c.kind}', subject '${rendered}') shadows reserved payload key(s) ${renderValue c._reserved}${chain}"
        else if !(hasId (c.subject or null)) then
          throw "gen-scope.resolveClaims: claim at path ${pathStr} (kind '${c.kind}') has a subject without id_hash (renders as '${rendered}')${chain}"
        else if !(hasUsableId c.subject) then
          throw "gen-scope.resolveClaims: claim at path ${pathStr} (kind '${c.kind}') has a subject whose id_hash is a ${typeOf c.subject.id_hash} rather than a string (renders as '${rendered}')${chain}"
        else
          c;

      emittedBy =
        i:
        " (emitted by claim at path ${toJSON i.path}, kind '${i.kind}', subject '${renderSubject i.claim.subject}')";

      # THEORY: the emission ⊥ consumption invariant of the claim/provide design. The claim's own
      # fields plus `_path`, and the caller's constant `ctx` — the engine's bookkeeping channel is
      # stripped and no resolved state is ever threaded in.
      resolverView = i: removeAttrs i.claim [ "_reserved" ] // { _path = i.path; };

      # ── WHAT A RESOLVER HANDS BACK, DECIDED WHERE THE VALUE FIRST EXISTS ──
      # The run reads three fields off this record: `resources` as an attribute set, `wiring` as a
      # set or a list, `claims` as a list. Each is read at a site where the wrong container is a
      # TYPE ERROR — `attrNames` on a list, `imap0` on an integer — and a type error is not a
      # value: it terminates the evaluation, `tryEval` does not hold it, and what surfaces is the
      # evaluator's own sentence with no library, no kind and no path in it.
      #
      # ★★ AND THE RECORD ITSELF IS THE WORSE HALF. A resolver returning a list, a number or null
      # is not a type error anywhere: every field is read through an `or` default, so all three
      # defaults fire and the claim contributes NOTHING — silently, and byte-identically to a
      # resolver that returned an empty set on purpose. Something vanishes and nothing says so,
      # which is the failure this engine's whole result contract is built to make impossible.
      # Checking only the loud half would leave the quiet one exactly as it was.
      #
      # This sits beside the `dedupKey` refusal below and works the same way: the value is in hand,
      # the emitting kind and its path are in hand, and the caller is told which of them produced
      # what.
      resultDefect =
        result:
        if !isAttrs result then
          "returned a ${typeOf result} rather than an attribute set"
        else if result ? resources && !isAttrs result.resources then
          "returned a `resources` that is a ${typeOf result.resources} rather than an attribute set"
        else if result ? wiring && !(isAttrs result.wiring || isList result.wiring) then
          "returned a `wiring` that is a ${typeOf result.wiring} rather than an attribute set or a list"
        else if result ? claims && !isList result.claims then
          "returned a `claims` that is a ${typeOf result.claims} rather than a list"
        else
          null;

      groupKeyOf =
        i: rv:
        let
          dk = ks.${i.kind}.dedupKey;
        in
        if dk == null then
          null
        else
          let
            r = dk rv;
          in
          if !isString r then
            throw "gen-scope.resolveClaims: dedupKey for kind '${i.kind}' at path ${toJSON i.path} returned a non-string: ${renderValue r}"
          else
            r;

      # ── intake ──
      roots = imap0 (
        i: c:
        let
          v = validate {
            path = [ i ];
            chain = "";
          } c;
        in
        {
          claim = v;
          path = [ i ];
          parent = null;
          stratum = depth.${v.kind};
          kind = v.kind;
        }
      ) claims;

      # Consecutive integers off the measure, largest first. THEORY: its length is the loop's
      # bound and the bound is a theorem — every registered `below` edge strictly decreases a
      # natural number, so `maxDepth + 1` rounds exhaust the relation by Noetherian induction on
      # ℕ. Nothing is capped and nothing tests for convergence.
      schedule = map (d: maxDepth - d) (range 0 maxDepth);

      # One stratum. The stratum being run is carried in the state rather than read from the
      # bound, because the loop below reads its bound's LENGTH and never its elements.
      step =
        st:
        let
          d = head st.pending;
          atD = sort (a: b: pathLt a.path b.path) (filter (i: i.stratum == d) st.instances);
          resolvedAtD = map (
            i:
            let
              rv = resolverView i;
              # Every read of `result` below and downstream goes through this binding, and forcing
              # it to weak head normal form decides the chain — so no path reaches a field of a
              # resolver's answer without its shape having been decided first.
              result =
                let
                  answered = ks.${i.kind}.resolve rv ctx;
                  defect = resultDefect answered;
                in
                if defect != null then
                  throw "gen-scope.resolveClaims: kind '${i.kind}' at path ${toJSON i.path} ${defect}"
                else
                  answered;
              emitted = result.claims or [ ];
              below = ks.${i.kind}.below;
              children = imap0 (
                j: sc:
                let
                  cpath = i.path ++ [ j ];
                  v = validate {
                    path = cpath;
                    chain = emittedBy i;
                  } sc;
                in
                if !(elem v.kind below) then
                  throw "gen-scope.resolveClaims: kind '${i.kind}' at path ${toJSON i.path} emitted a sub-claim of kind '${v.kind}' not in its `below` set ${toJSON below}${emittedBy i}"
                else
                  {
                    claim = v;
                    path = cpath;
                    parent = i.path;
                    stratum = depth.${v.kind};
                    kind = v.kind;
                  }
              ) emitted;
            in
            {
              inherit (i)
                path
                parent
                stratum
                kind
                ;
              subject = i.claim.subject;
              gk = groupKeyOf i rv;
              inherit result children;
            }
          ) atD;
          newChildren = concatMap (r: r.children) resolvedAtD;
        in
        {
          pending = tail st.pending;
          instances = st.instances ++ newChildren;
          resolved = st.resolved ++ resolvedAtD;
          # A loop-carried field whose only job is to be forced. The loop forces every field of
          # the state each round, so binding the round's own claims here is what makes an
          # emission refusal fire in the round that produced it — and, for a claim that no
          # consumer ever reads, what makes it fire at all. A leaf that emits anything is a loud
          # error even though its emission has nowhere left to run.
          validated = foldl' (a: i: seq i a) st.validated newChildren;
        };

      # `iterateBounded` applies the step once per element of its bound and forces every field of
      # the state between rounds. The forcing is derived from the state's own fields rather than
      # from a list of names kept beside it, so a field added here is forced without anyone
      # re-applying the discipline; a field written every round and read by no control flow is
      # exactly the shape that accumulates a thunk chain and then dies forcing it.
      final = iterateBounded forceFields step {
        pending = schedule;
        instances = roots;
        resolved = [ ];
        validated = foldl' (a: i: seq i a) true roots;
      } schedule;

      # Already in global schedule order: stratum-major descending, path-lexicographic within.
      inherit (final) resolved;

      # Claims the loop created and did not settle — the difference between the two lists it
      # carried, and not a re-derivation from the strata the schedule holds. A claim's path is
      # assigned once and never reused (roots by intake index, children by parent path plus
      # emission index), so it identifies the instance and the difference is exact. Empty over any
      # registry this library built; returned rather than refused, because the caller for whom it
      # is non-empty is precisely the caller who needs to know which claim it was.
      settledPaths = listToAttrs (map (r: nameValuePair (toJSON r.path) null) resolved);
      unrun = filter (i: !(settledPaths ? ${toJSON i.path})) final.instances;

      # ── resource combination, per kind, per dedup group, per key ──
      # THEORY: stratum-local aggregation on a COMPLETE fact set — Apt, Blair & Walker (1988),
      # "Towards a Theory of Declarative Knowledge", in Minker (ed.), pp. 89–148, whose standard
      # model is built stratum by stratum with each reaching its own fixed point before the next
      # begins (printed p. 108). A kind's fragments are folded
      # only once its stratum has finished, which is the classical reason aggregation demands
      # stratification: a fold over a set still being added to answers about a prefix.
      combineKind =
        kn:
        let
          insts = filter (r: r.kind == kn) resolved;
          kd = ks.${kn}.dedupKey;
          kf = ks.${kn}.fold;
          # The dedup partition, or one singleton group per claim where a kind declares none.
          groups =
            if kd == null then
              map (i: {
                gkey = null;
                insts = [ i ];
              }) insts
            else
              let
                g = groupBy (i: i.gk) insts;
              in
              map (k: {
                gkey = k;
                insts = g.${k};
              }) (attrNames g);
          foldGroup =
            grp:
            let
              allKeys = unique (concatMap (i: attrNames (i.result.resources or { })) grp.insts);
              keyEntry =
                key:
                let
                  contributors = filter (i: (i.result.resources or { }) ? ${key}) grp.insts;
                  values = map (i: i.result.resources.${key}) contributors;
                  paths = map (i: i.path) contributors;
                in
                {
                  inherit key paths;
                  groupKey = grp.gkey;
                  value = if kf == null then head values else kf key values;
                };
            in
            map keyEntry allKeys;
          allEntries = concatLists (map foldGroup groups);
          # A key produced by more than one group has two authors and no merge rule between them.
          byKeyName = groupBy (e: e.key) allEntries;
          collisions = filter (k: length byKeyName.${k} > 1) (attrNames byKeyName);
        in
        if collisions != [ ] then
          throw "gen-scope.resolveClaims: kind '${kn}' resource-key collision on ${toJSON collisions} — key(s) contributed by distinct groups at paths ${
            toJSON (map (k: map (e: e.paths) byKeyName.${k}) collisions)
          }"
        else
          {
            resources = listToAttrs (map (e: nameValuePair e.key e.value) allEntries);
            trace = listToAttrs (
              map (
                e:
                nameValuePair e.key {
                  claims = e.paths;
                  folded = kf != null;
                  groupKey = e.groupKey;
                }
              ) allEntries
            );
          };

      # Over EVERY registered kind, not only the ones something claimed: a kind with no claims
      # gets an empty entry, so a missing key means the kind was never registered.
      combined = listToAttrs (map (kn: nameValuePair kn (combineKind kn)) (attrNames ks));
      resources = mapAttrs (_: c: c.resources) combined;
      traceResources = mapAttrs (_: c: c.trace) combined;

      # ── wiring accumulation, per subject, per kind, in schedule order ──
      wiringEntriesFor =
        r:
        let
          w = r.result.wiring or { };
        in
        if isList w then
          w
        else if attrNames w == [ ] then
          [ ]
        else
          [
            {
              subject = r.subject;
              wiring = w;
            }
          ];

      flatWiring = concatMap (
        r:
        map (
          e:
          if !hasId (e.subject or null) then
            throw "gen-scope.resolveClaims: wiring at path ${toJSON r.path} (kind '${r.kind}') targets a subject without id_hash (renders as '${
              renderSubject (e.subject or null)
            }')"
          else if !hasUsableId e.subject then
            throw "gen-scope.resolveClaims: wiring at path ${toJSON r.path} (kind '${r.kind}') targets a subject whose id_hash is a ${typeOf e.subject.id_hash} rather than a string (renders as '${renderSubject e.subject}')"
          else
            {
              id = e.subject.id_hash;
              inherit (e) subject wiring;
              inherit (r) kind path;
            }
        ) (wiringEntriesFor r)
      ) resolved;

      byId = groupBy (e: e.id) flatWiring;
      # Every subject a claim was ABOUT, whether or not anything wired it. Without this a subject
      # with no wiring is indistinguishable from a subject no claim ever named.
      claimedSubjects = listToAttrs (map (r: nameValuePair r.subject.id_hash r.subject) resolved);
      wiredIds = unique (attrNames claimedSubjects ++ attrNames byId);

      entriesFor = id: byId.${id} or [ ];

      # ── THE THIRD FIELD IS A GUARANTEE AND NOT A CONVENIENCE ──
      # One list is published three ways here. `byKind` carries the VALUES grouped by the kind that
      # emitted them, and has lost the order ACROSS kinds; `trace.wiring.<id>` below carries the
      # EMISSIONS flat in the run's global schedule order, and carries no values; `entries` is the
      # list neither of those alone recovers. A consumer holding one subject wants the third, and a
      # consumer reaching for `byKind` instead gets a per-kind order silently in place of the global
      # one — the ordering discipline the whole cascade exists to produce, dropped without a
      # diagnostic. Publishing the list is what removes the reason to re-derive it: the two
      # projections stay for the readers they suit, and nothing has to reassemble the whole from
      # them.
      #
      # THEORY: why/derivation provenance in the sense of Cheney, Chiticariu & Tan (2009) — every
      # entry names the claim that emitted it, so a consumer holding a wiring value can say which
      # claim contributed it and where in the run. The Green–Karvounarakis–Tannen provenance
      # SEMIRING — annotations carrying a `(+, ×)` algebra that composes under the query operators —
      # is DELIBERATELY NOT REALIZED here and is not planned: these entries are records about a run,
      # not algebraic values, and nothing in this library computes with them. The rider is part of
      # the citation and travels with it, because a provenance citation arriving on its own reads as
      # a claim that the receiving library implements the semiring algebra, which it does not and
      # will not.
      #
      # ── HOW THIS IS READ, WHICH IS BY TESTING THE KEY AND NOT BY DEFAULTING IT ──
      # A key sits here for every subject a claim was ABOUT, so a MISSING key means the subject was
      # never registered and a present record with `entries = [ ]` means it was registered and
      # nothing wired it. Those are two observations, not one. A consumer defaulting the record —
      # `(wiring.${id} or { }).entries` — collapses them back together and re-creates one call
      # outward the erasure this record's totality exists to rule out; a consumer reading
      # `wiring.${id}.entries` without testing aborts on the unregistered subject with an
      # interpreter error no `tryEval` contains. `if wiring ? ${id} then … else …` keeps both.
      wiring = listToAttrs (
        map (
          id:
          let
            es = entriesFor id;
          in
          nameValuePair id {
            subject = if es == [ ] then claimedSubjects.${id} else (head es).subject;
            byKind = mapAttrs (_: ek: map (e: e.wiring) ek) (groupBy (e: e.kind) es);
            entries = map (e: {
              inherit (e) kind wiring;
              claim = e.path;
            }) es;
          }
        ) wiredIds
      );

      traceWiring = listToAttrs (
        map (
          id:
          nameValuePair id (
            map (e: {
              inherit (e) kind;
              claim = e.path;
            }) (entriesFor id)
          )
        ) wiredIds
      );

      # ── the claim trace, in global schedule order ──
      # THEORY: why/derivation provenance in the sense of Cheney, Chiticariu & Tan (2009) — each
      # artifact maps to the claims that produced it, extended by parent chains to the roots. The
      # Green–Karvounarakis–Tannen provenance SEMIRING is DELIBERATELY NOT REALIZED: these are
      # records about a run, not annotations carrying an algebra that composes under operators,
      # and nothing in this library computes with them.
      traceClaims = map (r: {
        inherit (r)
          path
          parent
          stratum
          kind
          ;
        subject = {
          inherit (r.subject) id_hash;
          rendered = renderSubject r.subject;
        };
        groupKey = r.gk;
      }) resolved;
    in
    # The argument's own shape is decided here, ahead of everything, and the result is built only
    # inside the branch the refusal falls through to. `claims` is walked by index, so a value that
    # is not a list reaches a list position and aborts with a type error — and a type error is not
    # a value: it terminates the evaluation, no `tryEval` around the call contains it, and the
    # caller gets no name to act on. The registry decides its own argument's shape for the same
    # reason; a run that did not would be the one door in this module a caller can fall through.
    if !isList claims then
      throw "gen-scope.resolveClaims: `claims` must be a list of claims, not a ${typeOf claims}"
    else if registryDefect != null then
      throw "gen-scope.resolveClaims: the kind set ${registryDefect}"
    else
      # Every field below forces the loop, so each one independently carries the run's refusals —
      # including an emission made in the schedule's last round, which no field SELECTS. Wrapping
      # the record in a forcing `seq` would add nothing to that and would make the record's own
      # weak head normal form run every resolver, which is a cost no caller asked for.
      {
        inherit resources wiring unrun;
        trace = {
          claims = traceClaims;
          resources = traceResources;
          wiring = traceWiring;
        };
      };
in
{
  inherit
    mkKind
    mkKinds
    mkClaim
    resolveClaims
    ;
}
