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
# THEORY. Apt, Blair & Walker (1988), "Stratified Programs", Definition 3 (printed p. 96), stratify
# a program so that a relation occurring POSITIVELY in a stratum is defined within that stratum or
# below, and a relation occurring NEGATIVELY is defined strictly below. The invariant this buys is
# the standard model built stratum by stratum, `M_i = T_{P_i}↑ω(M_{i-1})` (printed p. 108) — each
# stratum reaches its own fixed point before the next begins. Strictly-lower indexing is ABW's rule
# for the NEGATIVE case and a sufficient condition for completeness, not the property itself; this
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
# A claim whose stratum is not in the schedule is RETURNED as `unrun`, never thrown. Over a registry
# this library built the list is always empty — the measure is total on the registered names and the
# schedule enumerates its whole range — so `unrun` is a fact the caller can read rather than a
# coincidence they have to trust. It is non-empty only for a caller who supplied a kind-set record
# by hand whose declared maximum does not cover its own measure, and for that caller a refusal would
# destroy the very information they need.
{ prelude, graph }:
let
  inherit (builtins)
    attrNames
    isAttrs
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
  asKindSet =
    kinds: if isAttrs kinds && (kinds._type or null) == kindSetMarker then kinds else mkKinds kinds;

  claimMarker = "gen-scope/claim";

  # Reserved against payload shadowing. `kind` and `subject` are the semantic fields; `_type`,
  # `_path` and `_reserved` are the engine's own. A payload attempting any of them is claiming a
  # channel that is already spoken for, and silently letting it win would mean a resolver reading
  # an engine field that an author wrote.
  reservedKeys = [
    "kind"
    "subject"
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
      shadowed = filter (k: elem k reservedKeys) (attrNames payload);
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
    else
      # Payload first, fixed fields last: the marker, the kind and the subject are authoritative
      # over anything an author wrote. `_reserved` carries the shadow violation for the run to
      # report WITH a path — a constructor has no path context, and a violation reported without
      # one names no site.
      payload
      // {
        _type = claimMarker;
        kind = kindName;
        subject = args.subject;
        _reserved = shadowed;
      };

  # A display string for a subject. Output only: identity is `id_hash` and never this.
  renderSubject =
    e:
    if !isAttrs e then
      "<non-entity>"
    else if e ? name then
      e.name
    else if e ? rendered then
      e.rendered
    else
      e.id_hash or "<no-id>";

  hasId = e: isAttrs e && e ? id_hash;

  # Lexicographic order over integer-list paths — roots by intake index, children by parent path
  # plus emission index — which is a strict total order because one stratum's paths are distinct
  # by construction. Written as a scan over the common prefix rather than as a walk that calls
  # itself on the tail: a self-applying loop spends one evaluator frame per element and past the
  # call-depth guard it aborts uncatchably, and this comparison is the sort key of every stratum.
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
        else if !(ks ? ${c.kind}) then
          throw "gen-scope.resolveClaims: unknown kind '${toString c.kind}' at path ${pathStr}${chain}"
        else if (c._reserved or [ ]) != [ ] then
          throw "gen-scope.resolveClaims: claim at path ${pathStr} (kind '${c.kind}', subject '${rendered}') shadows reserved payload key(s) ${toJSON c._reserved}${chain}"
        else if !(hasId (c.subject or null)) then
          throw "gen-scope.resolveClaims: claim at path ${pathStr} (kind '${c.kind}') has a subject without id_hash (renders as '${rendered}')${chain}"
        else
          c;

      emittedBy =
        i:
        " (emitted by claim at path ${toJSON i.path}, kind '${i.kind}', subject '${renderSubject i.claim.subject}')";

      # THEORY: the emission ⊥ consumption invariant of the claim/provide design. The claim's own
      # fields plus `_path`, and the caller's constant `ctx` — the engine's bookkeeping channel is
      # stripped and no resolved state is ever threaded in.
      resolverView = i: removeAttrs i.claim [ "_reserved" ] // { _path = i.path; };

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
            throw "gen-scope.resolveClaims: dedupKey for kind '${i.kind}' at path ${toJSON i.path} returned a non-string: ${toJSON r}"
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
              result = ks.${i.kind}.resolve rv ctx;
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

      # Claims the schedule never reaches. Empty over any registry this library built; returned
      # rather than refused, because the caller for whom it is non-empty needs to know which.
      unrun = filter (i: !(elem i.stratum schedule)) final.instances;

      # Already in global schedule order: stratum-major descending, path-lexicographic within.
      inherit (final) resolved;

      # ── resource combination, per kind, per dedup group, per key ──
      # THEORY: stratum-local aggregation on a COMPLETE fact set — Apt, Blair & Walker (1988),
      # "Stratified Programs", whose standard model is built stratum by stratum with each reaching
      # its own fixed point before the next begins (printed p. 108). A kind's fragments are folded
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

      wiring = listToAttrs (
        map (
          id:
          let
            es = entriesFor id;
          in
          nameValuePair id {
            subject = if es == [ ] then claimedSubjects.${id} else (head es).subject;
            byKind = mapAttrs (_: ek: map (e: e.wiring) ek) (groupBy (e: e.kind) es);
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
    seq final.validated {
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
