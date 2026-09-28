# The demand cascade: the downward-only DAG of kinds whose depth stratifies a run, the typed
# request the run consumes, and the stratified resolution itself.
#
# The word "demand" in this library means demand-driven evaluation, and it means only that. The
# request value this cascade carries is a CLAIM — something an author asks for and a resolver
# satisfies — and it is named for what it is rather than for the evaluation strategy that happens
# to drive it.
#
# `mkKind` builds one kind DECLARATION and refuses a `dedupKey` without a `fold` and a `fold`
# without a `dedupKey`: grouping and merging are only meaningful together, so the pairing is a
# registration-time error rather than a resolution-time surprise. It also refuses a `spawns` entry
# whose produced kind is outside the host's own `below` set. A declaration is not a kind. `mkKinds`
# is the one producer of kind records: a left fold over an ORDERED list of declarations that
# resolves each `below` name against the frozen set of kinds minted strictly earlier, so a
# self-naming or cyclic `below` cannot be named at all, rather than being named and then detected.
#
# ★ THIS REGISTRY IS THE SUBSTRATE'S, NOT THE CASCADE'S. It began as the demand vocabulary and now
# carries the kind order every node kind is ranked in, so the two things a kind can be — something
# a demand resolves against, and something a node IS — register once, in one relation, minted by
# one fold. `resolve` marks the demand subset; `spawns` marks the expanding subset; a
# kind may be in either, both or neither.
#
# ── WHAT THIS FILE STANDS ON, AND THE THREE ANSWERS ARE DIFFERENT IN KIND ──
# TERMINATION is classical mathematics and claims no primary: the round bound is Noetherian
# induction on ℕ over a strictly decreasing measure, argued below where that measure is defined.
# COMPLETENESS is a published result and carries its citation: Apt, Blair & Walker (1988), quoted
# below against the printed pages named there. What is this library's OWN is neither — it is the
# CONSTRUCTION that makes them apply here, and it is stated as original rather than left to read as
# borrowed: a depth measure minted with each kind rather than decided over the finished set, and
# a schedule that IS that measure rather than a linearisation of it. That novelty is an absence
# claim, so the search behind it is named. The stratification literature this project holds — Apt,
# Blair & Walker (1988), Przymusinski (1988), Gelfond & Lifschitz (1988), Van Gelder, Ross &
# Schlipf (1991) — fixes what a stratified schedule MEANS and what model it yields; none of them
# derives a schedule from a registry's own relation, which is the step taken here. A primary that
# does would falsify the claim, and this paragraph is where it would land.
#
# ── THE KINDS ARE MINTED BY A STAGED FOLD, AND THE DEPTH IS ITS WITNESS ──
# THEORY. Krishnan & Van Wyk (2012), Fig. 7 and Theorem 3, make termination follow from the
# EXISTENCE of a well-founded ordering on the nonterminals; Söderberg & Hedin (2013) §7 restate it
# as ordering node types so that "each new NTA has a lower order than its host". The fold
# CONSTRUCTS that ordering's witness instead of deciding a relation for one. It is `mintStrata`'s
# frozen-set move (`lib/mint.nix`, ADR-0016 ruling 7): a declaration's `below` names resolve only
# against the kinds minted strictly EARLIER in the list, so a same-position or later name misses
# for the same reason a nonexistent one does. A self-naming or cyclic `below` is therefore
# INEXPRESSIBLE, never detected (ADR-0033 clause 3, substrate-constructed stratum closure): no cycle
# check exists anywhere in this file, and none is needed.
#
# A minted kind carries its resolved `below` RECORDS as `belowKinds`, beside the declared names, and
# `depth = 1 + max { depth b : b ∈ belowKinds }` (0 for none). Every record a minted kind reaches was
# minted before it, so the records form a finite DAG by induction on list position and `depth` is a
# natural number that strictly decreases along every resolved edge. Each kind's depth is computed
# once, when it is minted, and read from its `below` records thereafter, so a shared producer is
# never re-expanded.
#
# ★ THE UNIVERSAL IS SCOPED TO RECORDS THE FOLD PRODUCED AND NOTHING RECORD-UPDATED. Nix record
# update keeps the `_type` tag, so a minted kind edited with `//` is still tagged, and a knot tied
# through `belowKinds` by a recursive `let` is a value no fold produced. Writing that internal field
# by hand is forging, and it is out of scope; what an ordinary `//` edit can reach is refused by name
# at the evaluator (`lib/eval.nix`, `kindOf`) or at the registry door (`kindSetDefect` below).
#
# ── ADMISSIBILITY DEPENDS ON LIST ORDER; THE MINTED REGISTRY DOES NOT ──
# ADR-0016 ruling 7 owes the minting spec invariance of pass assignment under presentation order.
# Here the pass is the list position, and what is invariant is the RESULT: every admissible order
# of one declaration set mints the same `depth`, `maxDepth` and `below` for every kind, because
# `depth` is the longest descent through the declared relation and no position enters it. What is
# NOT invariant is admissibility: a list that declares a host before a kind its `below` names is
# refused by name, even though another order of the same declarations is admitted. That is
# user-visible, and it is why the attribute-set form of `mkKinds` is retired: an attribute set has no
# order to stage over, and ordering it by name would make admissibility a function of spelling.
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
# The declaration marker answers PROVENANCE, and it answers it for a COOPERATIVE CALLER: a record
# that came out of the constructor has been through everything the constructor refuses, while a record that
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
# ★ AND THE ORDINARY DOOR ALREADY REQUIRES THE FIELDS TO BE PRESENT, so this costs a cooperative
# caller nothing: `mkKind` writes `resolve`, `dedupKey` and `fold` as null when a kind declares
# none of them, so no record it builds can fail a PRESENCE arm. What they reach is precisely the
# forged record — the one case the marker was never able to speak for.
#
# ★★ WHAT `resolve` IS AND IS NOT REQUIRED FOR. It is the answer to a DEMAND, and this registry is
# no longer only the demand vocabulary: it is the substrate's kind registry, and a structural node
# kind has no demand semantics to supply. So a kind may register without one. What that does NOT
# relax is the answer to a demand — a kind carrying no `resolve` cannot resolve a claim, and a
# claim naming it is refused BY NAME at the run, where the caller is and where the kind can be
# named. The requirement moved from the door to the consumer; it did not disappear, and demand
# kinds are exactly the subset that carry the field.
#
# The constructor's arms are written as SENTINEL DEFAULTS rather than bare required formals, and
# the reason is this same paragraph read one level down: a bare formal makes an omission Nix's
# refusal instead of the library's, which is the uncatchable termination described above happening
# at the door that exists to prevent it. See `mkKind` for the argument in full.
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
#     inside the answer, and about nothing else. The answer's own SHAPE is not left open and never
#     was: the record itself and the three containers the run reads off it are decided at the point
#     the resolver returns, because `isAttrs` and `isList` decide them on any value and the
#     alternative is a type error with no kind and no path in it — or, for a record that is not a
#     set at all, no error and no output either. ★★ Nor is its KEY SET left open: the record is
#     CLOSED to `resources`, `wiring` and `claims`, and a key outside those three is a named
#     refusal carrying the key, the closed set, the kind and the path. It was once open, and what
#     that bought was the failure this library exists to remove — a misspelled field read by
#     nothing, a claim contributing nothing, and no one told.
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
# THEORY. Acyclicity is the stratifiability condition, made unwritable rather than checked. The
# measure is the longest path to a leaf: `depth k = 0` where `k` has an empty `below`, else
# `1 + max { depth b : b ∈ belowKinds(k) }`, so every resolved edge strictly decreases it —
# `depth k ≥ 1 + depth b > depth b` — and a strictly decreasing natural-number measure is what
# makes the cascade terminate by Noetherian induction on ℕ, in `maxDepth + 1` strata, as a theorem
# about the measure rather than an iteration budget.
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
# sense of Cheney, Chiticariu & Tan (2009) — a name taken from the literature rather than a citation
# checked against a held copy; neither that survey nor the semiring paper is in the project archive,
# which is stated because an unmarked citation reads as a checked one. The provenance SEMIRING of
# Green, Karvounarakis & Tannen
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
# The run reads `depth` and `maxDepth` off the kinds it is handed, each of which carries the depth it
# was minted with, and never off a registry field a merged or hand-assembled registry may have left
# stale. What it still does not establish is that a kind's `depth` is the one the fold minted: a
# minted record updated with `//` keeps its tag, and a `depth` written by hand is a value no fold
# produced.
#
# What that costs is bounded by where the answer is read from. "Not settled" is a fact about the
# LOOP — the claims it created minus the claims it resolved — and it is that difference that is
# reported. Deriving it instead from stratum membership in the schedule would be a PROXY: equivalent
# to the property only while the depth map really is the rank of the relation, and wrong in exactly
# the case the paragraph above says is not established. Under such a registry a claim could go
# unresolved while the proxy called it scheduled, and its kind would report an empty entry —
# indistinguishable from a kind nobody claimed, which is the one reading the totality rule exists to
# rule out. The difference has no proxy in it, so the two ways a registry can be wrong — a maximum
# that does not cover the measure, and a measure that is not the relation's — are both reported and
# neither is silent.
{ prelude }:
let
  door = import ./door.nix { inherit prelude; };
  inherit (builtins)
    attrNames
    isAttrs
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
    any
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
  declarationMarker = "gen-scope/kind-declaration";

  # ★★ THIS IS THE SUBSTRATE'S KIND REGISTRY, AND `resolve` IS ONE VOCABULARY INSIDE IT.
  # It was built as the cascade's demand vocabulary and `resolve` was total: a kind that could not
  # answer a demand was not a kind. That reading made the registry unusable as the home of the NODE
  # kind order — a structural node kind has no demand semantics, and requiring it to invent one is
  # imposing a resolution vocabulary on something that has no use for it. The alternative, a second
  # registry beside this one, pays the price this file states twice: two
  # copies of a discipline agree only for as long as someone keeps them in step.
  #
  # So the registry generalizes and `resolve` becomes a sentinel-guarded OPTION. DEMAND KINDS ARE
  # THE SUBSET THAT CARRY IT. A kind without one is a perfectly good kind — it takes a rank in the
  # order, it may declare what it spawns, it may be a node's type — and it cannot answer a demand,
  # which `resolveClaims` refuses by name at the claim that asks it to. The requirement did not
  # disappear; it moved to the consumer that actually needs it, where the kind can be named and the
  # caller is standing.
  #
  # ★ THE NULL IS STILL HOW A REFUSAL GETS TO FIRE, for the fields that remain constrained. Written
  # as a formal with no default, an omitted field is refused by NIX, at application, with
  # `called without required argument '…'` — a termination this library never names, that `tryEval`
  # does not contain, and that arrives BEFORE any arm below can run. That is the same uncatchable
  # class the header refuses on the registry's behalf, reaching the ordinary door. The sentinel's
  # only job is to let the arm underneath it decide, and `null` can serve because it is not a
  # resolver, a fold or a key on any reading.
  #
  # THE PRESENCE CLAIM THE HEADER MAKES IS PRESERVED: no record this constructor builds can reach
  # the registry with a field MISSING, so the registry's presence arms still cannot fire on its
  # output. What the constructor no longer claims is that the field is non-null.
  #
  # ★ WHAT IT RETURNS IS A DECLARATION, NOT A KIND. Its tag is `gen-scope/kind-declaration`, and the
  # fold in `mkKinds` is the sole producer of a `gen-scope/kind` record. A declaration whose `below`
  # names itself, or one half of a two-cycle, still builds here, and it is a declaration the fold
  # cannot mint: no well-typed kind outside the domain exists to be handed to the evaluator.
  mkKind =
    {
      name,
      below ? [ ],
      resolve ? null,
      spawns ? { },
      nta ? { },
      dedupKey ? null,
      fold ? null,
    }:
    let
      hasDedup = dedupKey != null;
      hasFold = fold != null;
      # ── THE SPAWN DECLARATION, AND WHY ITS DESCENT IS DECIDED HERE ──
      # THEORY. Söderberg §7 (printed 320) states the finiteness technique as "ordering the
      # nonterminals (the node types), so that each new NTA has a lower order than its host", and in
      # Vogt's formalism an expansion produces a symbol the GRAMMAR declares — the produced symbol is
      # never a runtime choice. `spawns` is that declaration: a host kind says, at registration, which
      # kinds it can expand into, and the substrate stamps the produced kind from the KEY rather than
      # reading it off whatever the builder returned.
      #
      # Every declared key must already be a `below` name, so descent is not a separate condition to
      # check: `mkKinds` resolves each `below` name to a kind minted strictly earlier, whose `depth`
      # is strictly smaller. A NON-DESCENDING SPAWN IS THEREFORE INEXPRESSIBLE — no kind carrying it
      # can be minted — rather than admitted and refused when it fires. That is the
      # same shape the emission guard already enforces for CLAIMS, where a sub-claim outside its
      # emitter's `below` set is a topology error; nodes and claims now expand under one rule.
      spawnKinds = if isAttrs spawns then attrNames spawns else [ ];
      undeclaredSpawn = filter (k: !(elem k below)) spawnKinds;
      unbuildableSpawn = filter (k: !(callable spawns.${k})) spawnKinds;
      # ── THE `nta` DECLARATION: the recursive NTA form, beside `spawns` and not inside it ──
      # `nta` is Vogt, Swierstra & Kuiper 1989 Def. 3.14's recursive `F → F̄` form, whose children
      # are of the HOST's own kind; `spawns` above is the non-recursive fragment Lemma 3.2 / Söderberg
      # §7 make finite by kind order. So `nta` adds NO `below` entry and needs none, and a self-`below`
      # stays unmintable. Its admission rule and its stated price live
      # at its channel in `lib/eval.nix`. Every refusal here carries the `nta:` token, so a reader
      # tells the two rules apart by the token rather than by the builder's shape.
      #
      # The circular arm is ordered BEFORE the applicability arm on purpose: a circular declaration
      # is not `callable`, so under the opposite order its message could never fire.
      ntaNames = if isAttrs nta then attrNames nta else [ ];
      circularNta = filter (k: isCircularDecl nta.${k}) ntaNames;
      unbuildableNta = filter (k: !(callable nta.${k})) ntaNames;
    in
    if !isString name then
      throw "gen-scope.mkKind: `name` must be a string"
    else if !isList below then
      throw "gen-scope.mkKind: kind '${name}' declares a `below` that is a ${typeOf below} rather than a list"
    else if !(all isString below) then
      throw "gen-scope.mkKind: kind '${name}' declares a `below` holding a name that is not a string"
    else if resolve != null && !(callable resolve) then
      throw "gen-scope.mkKind: kind '${name}' declares a `resolve` that cannot be applied (it is a ${typeOf resolve})"
    else if !isAttrs spawns then
      throw "gen-scope.mkKind: kind '${name}' declares a `spawns` that is a ${typeOf spawns} rather than an attribute set keyed by the kind each builder produces"
    else if undeclaredSpawn != [ ] then
      throw "gen-scope.mkKind: kind '${name}' declares a spawn producing kind(s) ${toJSON undeclaredSpawn} that its `below` set ${toJSON below} does not carry. A spawn's produced kind must be BELOW its host's, which is what makes the expansion descend a rank that strictly decreases — declare the kind in `below`, or spawn a kind that is already there."
    else if unbuildableSpawn != [ ] then
      throw "gen-scope.mkKind: kind '${name}' declares a spawn for kind(s) ${toJSON unbuildableSpawn} whose builder cannot be applied"
    else if !isAttrs nta then
      throw "gen-scope.mkKind: nta: kind '${name}' declares an `nta` that is a ${typeOf nta} rather than an attribute set of builders keyed by NTA name"
    else if circularNta != [ ] then
      throw "gen-scope.mkKind: nta: kind '${name}' declares NTA(s) ${toJSON circularNta} whose builder is a circular declaration. An `nta` builder computes the NODE SET, and a node set that is a fixed point of its own iterate is the per-step growth the spawn-read restriction refuses. A child's ATTRIBUTES may be circular; its EXISTENCE may not. Declare the builder as a plain function."
    else if unbuildableNta != [ ] then
      throw "gen-scope.mkKind: nta: kind '${name}' declares NTA(s) ${toJSON unbuildableNta} whose builder cannot be applied"
    else if hasDedup && !hasFold then
      throw "gen-scope.mkKind: kind '${name}' declares `dedupKey` without `fold` (a fold is required to merge grouped fragments)"
    else if hasFold && !hasDedup then
      throw "gen-scope.mkKind: kind '${name}' declares `fold` without `dedupKey` (a fold has nothing to merge without grouping)"
    else
      {
        _type = declarationMarker;
        inherit
          name
          below
          resolve
          spawns
          nta
          dedupKey
          fold
          ;
      };

  # The applicability approximation, bound where it lives rather than written a second time: the
  # circular carrier decides the same property of its `leq`, and two copies of a discipline agree
  # only for as long as someone keeps them in step. The argument for the approximation, and for
  # what it costs, is stated at its module.
  callable = import ./callable.nix;

  # The circular-declaration classifier, the evaluator's own (`lib/eval.nix`), repeated as the one
  # line it is because `mkKind` refuses a circular `nta` builder before any evaluator exists. The
  # declaration shape is `circular`'s record (`lib/resolve.nix`), tagged `kind = "circular"`.
  isCircularDecl = v: isAttrs v && (v.kind or null) == "circular";

  # The reason an entry is not a well-shaped declaration or kind, or null. Total on any value: each
  # arm establishes what the next one needs, so nothing here reads a field it has not already found.
  # The reason names the defect and never renders the entry — a kind record holds its resolver, and
  # rendering a function is itself an abort no caller can catch, which would replace one
  # uncatchable termination with another while claiming to diagnose it.
  #
  # Split by what is being admitted: `notADeclaration` is the fold's intake, `notAKind` the
  # evaluator's and the run's. Each tells the other's record apart by its tag, so a declaration
  # handed to the evaluator is a TYPE refusal naming it as a declaration rather than a domain one.
  notADeclaration =
    k:
    if !isAttrs k then
      "is a ${typeOf k} rather than a kind declaration"
    else if (k._type or null) == kindMarker then
      "is a kind `mkKinds` already minted, not a declaration: pass the declaration `mkKind` built"
    else if (k._type or null) != declarationMarker then
      "was not built by `mkKind`"
    else
      shapeDefect k;

  notAKind =
    k:
    if !isAttrs k then
      "is a ${typeOf k} rather than a kind record"
    else if (k._type or null) == declarationMarker then
      "is a kind declaration built by `mkKind`, not a kind `mkKinds` minted: pass the declarations through `mkKinds`"
    else if (k._type or null) != kindMarker then
      "was not minted by `mkKinds`"
    else if !isInt (k.depth or null) then
      "carries no integer `depth`"
    else if !isAttrs (k.belowKinds or null) then
      "carries no `belowKinds` attribute set"
    else
      shapeDefect k;

  # The `!= [ ]` and `{ } !=` guards below skip a pass over an empty list or key set, which holds
  # vacuously. They force nothing the passes would not, and the OPERAND ORDER is what makes that so
  # for the attribute set: Nix's `==` on two attribute sets first asks whether BOTH are derivations,
  # which reads the LEFT operand's `type` attribute. With `k.spawns` on the left, a spawn named
  # `type` would have its builder forced before the refusal that names it (den-hoag-n6dh7 gate F-1);
  # with the empty literal on the left the question is answered without touching `k.spawns`. Two
  # lists compare lengths before elements, so `k.below != [ ]` forces no name.
  shapeDefect =
    k:
    if !isString (k.name or null) then
      "carries a `name` that is not a string"
    else if !isList (k.below or null) then
      "carries a `below` that is not a list"
    else if k.below != [ ] && !(all isString k.below) then
      "carries a `below` holding a name that is not a string"
    else if !(k ? resolve) then
      "carries no `resolve` field"
    else if !(k ? spawns) then
      "carries no `spawns` field"
    else if !(k ? dedupKey) then
      "carries no `dedupKey` field"
    else if !(k ? fold) then
      "carries no `fold` field"
    # `resolve` is an OPTION now — a kind without one is structural and cannot answer a demand,
    # which the run refuses at the claim rather than here. What stays refused is a resolve that is
    # PRESENT and unapplicable, because that one aborts at the call site with no name of ours.
    else if k.resolve != null && !(callable k.resolve) then
      "carries a `resolve` that cannot be applied"
    else if !isAttrs k.spawns then
      "carries a `spawns` that is not an attribute set"
    else if { } != k.spawns && !(all (p: elem p k.below) (attrNames k.spawns)) then
      "declares a spawn outside its own `below` set"
    else if { } != k.spawns && !(all (p: callable k.spawns.${p}) (attrNames k.spawns)) then
      "carries a spawn builder that cannot be applied"
    else if !(k ? nta) then
      "nta: carries no `nta` field"
    else if !isAttrs k.nta then
      "nta: carries an `nta` that is not an attribute set"
    else if any (p: isCircularDecl k.nta.${p}) (attrNames k.nta) then
      "nta: carries an `nta` builder that is a circular declaration"
    else if !(all (p: callable k.nta.${p}) (attrNames k.nta)) then
      "nta: carries an `nta` builder that cannot be applied"
    else if k.dedupKey != null && !(callable k.dedupKey) then
      "carries a `dedupKey` that is neither null nor applicable"
    else if k.fold != null && !(callable k.fold) then
      "carries a `fold` that is neither null nor applicable"
    else
      null;

  mkKinds =
    decls:
    let
      # Labelled at intake so a refusal can point at the entry a caller wrote, by its position.
      malformed = filter (m: m != null) (
        imap0 (
          i: d:
          let
            reason = notADeclaration d;
          in
          if reason == null then null else "entry ${toString i} ${reason}"
        ) decls
      );

      names = map (d: d.name) decls;

      # Decided ahead of the fold and not by it: a second declaration of a name would resolve its
      # `below` against the first, and the frozen map would silently keep whichever came last.
      duplicates = unique (filter (n: length (filter (m: m == n) names) > 1) names);

      # ── THE FOLD ──
      # One step mints one declaration against `frozen`, the kinds minted strictly earlier. A `below`
      # name `frozen` does not carry is refused by name, and that is the only refusal the step has:
      # a name that is later in the list, the declaration's own name, and a name nothing declares all
      # miss here for the same reason, so no cycle is ever formed to be found.
      mint =
        frozen: d:
        let
          resolved = map (
            n:
            frozen.${n}
              or (throw "gen-scope.mkKinds: kind '${d.name}' names '${n}' in `below`, which no kind registered before it carries. A kind resolves its `below` names against the kinds declared EARLIER in the list, so declare every kind after the kinds its `below` names; a kind naming itself, or a cycle of kinds, has no such order and cannot be declared.")
          ) d.below;
        in
        frozen
        // {
          ${d.name} = d // {
            _type = kindMarker;
            belowKinds = listToAttrs (map (k: nameValuePair k.name k) resolved);
            depth = foldl' (m: k: max m (k.depth + 1)) 0 resolved;
          };
        };

      kinds = foldl' mint { } decls;
      depth = mapAttrs (_: k: k.depth) kinds;
      maxDepth = foldl' max 0 (attrValues depth);

      # Every kind's depth forced in LIST order, so a registry with a `below` miss is refused as it
      # is built and the refusal names the first entry, in the caller's own order, that misses.
      minted = foldl' (acc: n: seq kinds.${n}.depth acc) null names;
    in
    if isAttrs decls then
      throw "gen-scope.mkKinds: expected a LIST of kind declarations, not an attribute set. Kinds are minted in list order, each against the kinds declared before it, and an attribute set has no order to mint in: list the declarations with every kind after the kinds its `below` names."
    else if !isList decls then
      throw "gen-scope.mkKinds: expected a list of kind declarations, not a ${typeOf decls}"
    else if malformed != [ ] then
      throw "gen-scope.mkKinds: not every entry is a kind declaration: ${toJSON malformed}"
    else if duplicates != [ ] then
      throw "gen-scope.mkKinds: duplicate kind name(s): ${toJSON duplicates}"
    else
      seq minted { inherit kinds depth maxDepth; };

  # ── THE REGISTRY A CONSUMER HANDS BACK, DECIDED AS A TYPE AND NOT AS A PROVENANCE ──
  # The reason `reg` is not a kind registry, or null. A registry is an attribute set whose `kinds`
  # maps each name to the kind `mkKinds` minted under it. It need not be one `mkKinds` returned: a
  # registry assembled by hand out of minted kinds, a `//` merge of two, is admitted, because every
  # minted kind is in the domain and so is any collection of them. What the door asks is a TYPE
  # question per entry, and one COHERENCE question across entries:
  #
  #   · every entry is filed under its own name;
  #   · every kind an entry's resolved `below` carries is the registry's entry under that name.
  #
  # The second is what a merge can break. Termination does not rest on it — the evaluator follows
  # resolved records (`lib/eval.nix`, `kindOf`), so a merged registry cannot re-route a spawn chain —
  # but a registry filing two different kinds under one name gives a reader looking a spawned
  # node's kind up by name a different kind from the one the evaluator follows, and the caller's
  # declared expansion silently does not happen. So it is refused by name. Two kinds are compared on
  # `name`, `below`, `depth` and the key sets of `spawns` and `nta`; builders are functions and are
  # not compared, so two kinds differing only in a builder's body are one kind to this door.
  #
  # COST: one pass over the entries and one over each entry's resolved `below`, paid per door
  # crossing (every `eval` and `buildRoots` handed a registry) and never per node.
  #
  # Internal: `default.nix` binds it into the two doors and keeps it off the published surface.
  sameKind =
    a: b:
    a.name == b.name
    && a.below == b.below
    && a.depth == b.depth
    && attrNames a.spawns == attrNames b.spawns
    && attrNames a.nta == attrNames b.nta;

  # ADMISSION FIRST, THE REASON ONLY ON A REFUSAL. `kindSetAdmitted` decides the set
  # `kindSetDefect'` accepts, conjunct for conjunct and in its order — every entry a kind, every
  # entry under its own name, every resolved `below` present, then the same kind — as four `all`
  # passes that build no list of findings; a registry it does not admit goes to `kindSetDefect'`,
  # which builds the reason. Each pass forces only what the reason's walk forces before reaching
  # the same conjunct, so the two agree on every registry, a throwing one included, and the answer
  # and its message are the reason's (den-hoag-n6dh7: the door is crossed twice per evaluation).
  kindSetAdmitted =
    reg:
    isAttrs reg
    && isAttrs (reg.kinds or null)
    && (
      let
        ks = reg.kinds;
        registered = attrNames ks;
      in
      all (n: notAKind ks.${n} == null) registered
      && all (n: ks.${n}.name == n) registered
      && all (n: all (b: ks ? ${b}) (attrNames ks.${n}.belowKinds)) registered
      && all (
        n: all (b: sameKind ks.${b} ks.${n}.belowKinds.${b}) (attrNames ks.${n}.belowKinds)
      ) registered
    );

  kindSetDefect = reg: if kindSetAdmitted reg then null else kindSetDefect' reg;

  kindSetDefect' =
    reg:
    if !isAttrs reg then
      "received a ${typeOf reg}"
    else if !isAttrs (reg.kinds or null) then
      "received an attrset with no `kinds` attribute set"
    else
      let
        ks = reg.kinds;
        registered = attrNames ks;
        malformed = filter (m: m != null) (
          map (
            n:
            let
              reason = notAKind ks.${n};
            in
            if reason == null then null else "`${n}` ${reason}"
          ) registered
        );
        misfiled = filter (n: ks.${n}.name != n) registered;
        edges = concatMap (
          n:
          map (b: {
            host = n;
            name = b;
          }) (attrNames ks.${n}.belowKinds)
        ) registered;
        absent = filter (e: !(ks ? ${e.name})) edges;
        split = filter (e: !(sameKind ks.${e.name} ks.${e.host}.belowKinds.${e.name})) edges;
      in
      if malformed != [ ] then
        "holds entries that are not minted kinds: ${toJSON malformed}"
      else if misfiled != [ ] then
        "files kind(s) under a name other than their own: ${
          toJSON (map (n: "`${n}` holds kind '${ks.${n}.name}'") misfiled)
        }"
      else if absent != [ ] then
        "holds kind '${(head absent).host}', whose resolved `below` carries kind '${(head absent).name}', which the registry does not"
      else if split != [ ] then
        "files under '${(head split).name}' a kind that differs from the kind '${(head split).name}' that entry '${(head split).host}' resolved in its `below` (compared on `name`, `below`, `depth` and the `spawns`/`nta` key sets). Two different kinds share one name — a merge of registries built from different declarations"
      else
        null;

  # A registry, or the declarations to mint one from. A list is declarations and goes through the
  # fold, with every refusal above; an attribute set without `kinds` is the retired attribute-set
  # form, and `mkKinds` refuses it by name. Anything else is taken as a registry, and the run's own
  # door (`registryDefect`) decides it with `kindSetDefect`.
  asKindSet =
    kinds: if isList kinds || (isAttrs kinds && !(kinds ? kinds)) then mkKinds kinds else kinds;

  claimMarker = "gen-scope/claim";

  # The engine's own field names, reserved against payload shadowing. A payload attempting any of
  # them is claiming a channel that is already spoken for, and letting it win would mean a resolver
  # reading an engine field that an author wrote.
  #
  # `kind` and `subject` are reserved too and are NOT in this list, because they are not shadowable:
  # the payload is what remains after both are taken out of the arguments, so an author writing
  # `kind` has set the kind rather than shadowed it. A check over a domain two of whose members no
  # input can reach reads as coverage it does not have.
  #
  # ★★ AND THIS IS THE OPEN HALF OF A DELIBERATE ASYMMETRY. The payload is OPEN — anything not
  # named here is carried — while the RESOLVER'S RESULT RECORD is CLOSED, an unrecognised key
  # there being a named refusal. The two are opposite because the reader is: a payload is read by
  # the caller's own resolvers and this library only carries it, whereas the result record is read
  # by the run and by nothing else. The full reason is written once, at `resultDefect` in the run
  # below, where the closure is enforced.
  engineKeys = [
    "_type"
    "_path"
    "_reserved"
  ];

  # The kind NAME a `kind` field denotes: a kind's or a declaration's own name, or the name itself. Total on
  # any value — anything that is neither yields something that is not a string, which the
  # constructor refuses. There is one decision, and it is made there rather than half here.
  kindNameOf =
    k:
    if
      isAttrs k
      && elem (k._type or null) [
        kindMarker
        declarationMarker
      ]
    then
      k.name or null
    else
      k;

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

  # Total rendering of an arbitrary caller value inside a diagnostic: the one shared renderer, owned
  # by gen-prelude (its contract and the reason `toJSON` alone cannot do this live there).
  inherit (prelude) renderValue;

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
      # The measure is read off the kinds themselves, each of which carries the `depth` it was minted
      # with, and never off a registry field a hand-assembled or merged registry may have left stale.
      depth = mapAttrs (_: k: k.depth) ks;
      maxDepth = foldl' max 0 (attrValues depth);

      # ── the registry's TYPE, which is this run's precondition ──
      # The same question the evaluator's door asks: every entry a minted kind, filed under its own
      # name, and coherent with every resolved `below` that reaches it. This run projects `below`,
      # `resolve`, `dedupKey`, `fold` and `depth` off those entries at points where a missing one is
      # a type error rather than a refusal, and a type error is not a value — `tryEval` does not
      # contain it — so the type is decided before any of them is read.
      registryDefect = kindSetDefect kindSet;

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
        # The demand vocabulary is the SUBSET of the registry that carries a `resolve`. A kind
        # without one is registered, ranked and possibly spawning, and it still cannot answer a
        # demand — so the requirement the constructor no longer imposes is imposed here, at the
        # claim that asks for it, where both the kind and the caller's path can be named. Refusing
        # here rather than at registration is what lets one registry serve both vocabularies.
        else if ks.${c.kind}.resolve == null then
          throw "gen-scope.resolveClaims: kind '${c.kind}' at path ${pathStr} declares no `resolve`, so it cannot answer a demand — it is a registered kind and not a demand kind${chain}"
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
      #
      # ── AND THE RECORD IS CLOSED: A KEY OUTSIDE THE THREE IS A NAMED REFUSAL ──
      # All three fields are OPTIONAL, so "absent because misspelled" and "absent because intended"
      # are ONE OBSERVATION to everything downstream: `{ resourcez = …; }` returned cleanly and
      # produced nothing. It arrives through the door the shape arms above leave open — they decide
      # the record's TYPE and its known fields' CONTAINERS, and membership is neither.
      #
      # ★ THE EMPTY RECORD IS NOT WHAT THIS REFUSES, and the distinction is the whole construction.
      # `{ }` carries no key outside the set, takes no arm, and keeps returning — a legitimate empty
      # answer, and the control the silent half above is measured against. A check on the RECORD
      # would have refused it too; a check on its KEYS refuses neither it nor a record all of whose
      # keys are known.
      #
      # ★★ TWO RECORDS IN THIS LIBRARY HAVE OPPOSITE OPENNESS, AND WHOSE CONTRACT EACH ONE IS
      # DECIDES WHICH. `mkClaim`'s payload is OPEN: it is user-domain data this substrate carries
      # opaquely, never reads, and cannot enumerate — an unrecognised key there is the ORDINARY
      # CASE, and the only thing a payload may not do is take one of the engine's own names, which
      # is what `engineKeys` reserves. This record is the SUBSTRATE'S OWN CONTRACT WITH THE RUN. Its
      # key set is enumerable precisely because the run enumerates it — `resources`, `wiring` and
      # `claims` are read here and nowhere else — so an unrecognised key cannot be data addressed to
      # anyone: it is a field this library was meant to read and did not, which is a claim that
      # vanishes with nothing said. Open where the reader is the caller; closed where the reader is
      # this library.
      resultKeys = [
        "resources"
        "wiring"
        "claims"
      ];

      resultDefect =
        result:
        let
          # The `isAttrs` test the first arm already makes, made again, and deliberately. Laziness
          # means this binding is forced only where the chain has established it — but the chain's
          # totality is a property of the ARMS, and a binding beside them is one edit from being
          # forced first, where `attrNames` on a non-set is exactly the uncatchable abort these arms
          # exist to replace. Total on any value for the cost of one predicate.
          unknown = filter (k: !elem k resultKeys) (if isAttrs result then attrNames result else [ ]);
        in
        if !isAttrs result then
          "returned a ${typeOf result} rather than an attribute set"
        else if unknown != [ ] then
          "returned unrecognised result key(s) ${toJSON unknown}: this record is closed to ${toJSON resultKeys}, and a key outside that set is read by nothing here — correct the spelling or drop it"
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
      # THEORY: why/derivation provenance in the sense of Cheney, Chiticariu & Tan (2009), named
      # from the literature rather than checked against a held copy (neither primary is in the
      # project archive) — every entry names the claim that emitted it, so a consumer holding a wiring value can say which
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
      # THEORY: why/derivation provenance in the sense of Cheney, Chiticariu & Tan (2009), named
      # from the literature rather than checked against a held copy — each
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
    mkKinds
    mkClaim
    # INTERNAL, and removed before the surface merge in `default.nix`: the two doors take it as a
    # formal, and no consumer needs a predicate the doors already decide.
    kindSetDefect
    ;
  mkKind = door "mkKind" mkKind;
  resolveClaims = door "resolveClaims" resolveClaims;
}
