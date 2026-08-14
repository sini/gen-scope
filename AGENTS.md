# gen-scope — agent capability sheet

## Scope

Demand-driven higher-order attribute-grammar evaluator over algebraic scope graphs: you supply root node descriptors (`{ id, type, parent, decls }`) and attribute definitions (`self: id: value`), and `eval` returns an accessor record (`node` / `get` / four materializers) whose attributes compute lazily and memoize on an `_eval` cache co-located on each node.

**TWO FURTHER, INDEPENDENT CONCERNS LIVE HERE.** The **well-founded engine** computes the meaning of a rule program with negation — `mkProgram` in, a three-valued model out, with `UNDEFINED` a named verdict for contested atoms. **Staged minting** (`mintStrata`) goes the other way from the evaluator: emitters in, a scope graph out — vertices under their own identifiers, one labelled edge per relatum, each relatum resolved against what strictly earlier passes settled. Neither touches a node, an attribute or a scope graph.

Routing a task: atoms, rules, negation or a fixpoint over a policy program ⇒ the engine. Nodes, attributes or scopes ⇒ the evaluator. Emitters, passes, relata, identifiers or identities ⇒ minting. ★ **"Strata" alone does NOT route** — the engine's stratum is a layer of a rule program and minting's is a declared pass. The two constructions share exactly one thing, `forceFields` — the round-loop forcing, taken from `lib/least-model.nix` by both rather than written twice — and nothing else.

## Not this library's job

Quoted text is the owner's own `flake.nix` `description` field, verbatim. Grep counts below are `grep -rEl '<pattern>' --include='*.nix' <dir> | wc -l` — files with a match — run from `/home/sini/Documents/repos/sini`. In the patterns, `\|` is markdown table escaping for the ERE alternation `|`. Rows carrying no grep cite attribution from the sibling description alone: the predicates tried for `gen-dispatch` matched nothing in its own `lib/`, so no absence is claimed against it.

| Responsibility | Owner |
|---|---|
| Static read-dependency analysis (`readsAttrs`), attribute stratification, the scheduled convergence fold | `gen-resolve` — "gen-resolve — demand-driven higher-order RAG evaluator over algebraic scope graphs (Knuth 1968 attribute schedule + Vogt 1989 HOAG)". gen-scope ships `circular` as the bare fixed-point loop primitive; `readsAttrs\|stratum\|schedule` over `gen-scope/lib` ⇒ 0 files, same predicate over `gen-resolve/lib` ⇒ 6 |
| Graph traversal, SCC/condensation, phase ordering over accessor-graphs | `gen-graph` — "gen-graph: accessor-based graph query combinators". `lib/graph.nix` here is Mokhov *construction* only; `condensation\|stronglyConnected\|topoSort\|topological\|phaseOrder` over `gen-scope/lib` ⇒ 0, control `gen-graph/lib` ⇒ 2 |
| Predicate / selector matching over graph positions | `gen-select` — "gen-select: selector algebra for attributed graph positions". `__sel\|selectorEq` over `gen-scope/lib` ⇒ 0, control `gen-select/lib` ⇒ 3 |
| Minting identity, kinds, instances, registries | `gen-schema` — "gen-schema: typed record registry with extension points for the pure-gen module system". It is an INPUT here and the ownership is unchanged by that: `hashIdentity` is injected into the minting module by `lib/default.nix`, so gen-scope derives no identity and re-exports none — `hashIdentity` over `gen-scope/lib` ⇒ 2 files, the injection site and the module it reaches, and `lib/mint.nix` contributes exactly ONE name to the merged surface. `id_hash\|hashString\|builtins\.hash` over `gen-scope/lib` ⇒ 1 file, control `gen-schema/lib` ⇒ 6 files; the single hit is `lib/cascade.nix` READING a subject's `id_hash`, never minting one |
| Module merge, `evalModules`, option priorities | `gen-merge` — "gen-merge — pure-Nix byte-mode module MERGE engine (evalModuleTree) for the pure-gen module system". Enforced, not merely absent: `test-library-source-is-nixpkgs-lib-free` (`ci/tests/purity.nix`) fails CI on `evalModules` / `mkOption` / `lib.` / `nixpkgs` appearing in `lib/**.nix`, `flake.nix` or `default.nix` |
| Type checking / `verify` | `gen-types` — "gen-types: pure, nixpkgs-lib-free structural type checker for the gen ecosystem" |
| General utilities — the EVALUATOR's only dependency; `flake.nix` declares three inputs, and the other two are the engine's (`gen-graph`) and staged minting's (`gen-schema`) | `gen-prelude` — "gen-prelude: vendored, nixpkgs-lib-free pure utilities for the gen ecosystem" |
| Graph products, coordinate tuples, slices, fibers | `gen-product` — "gen-product — graph products as first-class operations over accessor-graphs (Cartesian / tensor / strong / lexicographic; cells, slices, fibers, projections, quotients, restriction, containment chains), lazy in and out". `coordsOf\|cartesian\|tensor` over `gen-scope/lib` ⇒ 0, control `gen-product/lib` ⇒ 4 |
| Computing the dirty set / change propagation for an incremental rebuild | `gen-rebuild` — "gen-rebuild: pure-Nix incremental rebuilder core (Mokhov rebuilder dimension)". gen-scope supplies only the consumer-driven hooks: `evalWarm`'s `decision` (`isClean` + `reusable`) over a `prior` accessor, the `facade` the plane reads through, and `recordedDeps` |
| Choosing a winner among matched rules (guard→effect step, ordering, conflict resolution) | `gen-dispatch` — "gen-dispatch: relational rule dispatch over ordered groups (the dispatch STEP)" |
| Layered settings resolution with precedence and structured provenance | `gen-settings` — "gen-settings — stratified settings resolution as a pure layered fold, with refs-as-data, structured provenance, and the graduated injection construct". `stratif\|precedence\|provenance` over `gen-scope/lib` ⇒ 0, control `gen-settings/lib` ⇒ 4 |
| Typed resource demands resolving into resources + wiring — a different sense of "demand" from gen-scope's demand-*driven* evaluation | `gen-demand` — "gen-demand — typed demand cascade (kinds resolve demands into resources + wiring + sub-demands; a stratified, terminating fold resolves the multiset with full provenance)" |
| Aspect traits / classification | `gen-aspects` — "gen-aspects: aspect-oriented composition types (pure-gen, re-hosted on gen-merge)" |
| Channels / dataflow riding over scopes | `gen-pipe` — "gen-pipe — scoped channels + dataflow algebra (map/filter/fold/scan/route/join/tee) with B5 determinism, provenance, dedup, and class-aware contributions"; `gen/lib/mkGenLibs.nix` records its deps as `prelude+select+scope` |
| The nixpkgs boundary: value injection, building systems | `gen-flake` — "gen-flake — the pure composition boundary of the pure-gen module ecosystem" |

## Exports

Entry: `inputs.gen-scope.lib` (flake). Root `default.nix` is a function `{ prelude ? <derived from flake.lock>, graph ? <derived from flake.lock>, schema ? <derived from flake.lock>, ... }` — callable as `import ./gen-scope { }`, which content-addresses gen-prelude, gen-graph and gen-schema out of the pinned lock and needs no `<nixpkgs>`.

`lib/default.nix` is one flat merge — `algebraicGraph // buildNodes // queries // resolve // structural // interface // eval // program // leastModel // wellFounded // acceptance // engine // stratify // mint // folds // cascade`. All 87 exports sit at top level; there is no nested namespace and no key is shadowed (see traps). ★ In that merge `algebraicGraph` is this library's OWN `lib/graph.nix`; the parameter named `graph` is the **gen-graph library**, and the two are different things. `schema` is the third parameter and is bound to ONE function: `lib/default.nix` passes `hashIdentity` into `lib/mint.nix` and nothing else of that library reaches any module here.

**Algebraic graph construction** — `lib/graph.nix`. A graph value is `{ vertices = [id]; edges = [{ from; to; }]; }`.

| Export | Signature |
|---|---|
| `empty` | `graph` (a value, not a function) |
| `vertex` / `vertices` | `id -> graph` / `[id] -> graph` |
| `overlay` / `overlays` | `graph -> graph -> graph` / `[graph] -> graph` |
| `connect` | `graph -> graph -> graph` (cross-product edges) |
| `edge` / `edges` | `from -> to -> graph` / `[{from; to;}] -> graph` |
| `path` / `circuit` | `[id] -> graph` |
| `star` | `center -> [leaf] -> graph` (leaves→center, see traps) |
| `clique` | `[id] -> graph` |
| `tree` / `forest` | `{ root; children = [tree]; } -> graph` / `[tree] -> graph` |
| `gmap` | `(id -> id) -> graph -> graph` |
| `induce` | `(id -> bool) -> graph -> graph` |
| `transpose` | `graph -> graph` |
| `hasVertex` / `hasEdge` | `id -> graph -> bool` / `from -> to -> graph -> bool` |
| `removeVertex` / `removeEdge` | `id -> graph -> graph` / `from -> to -> graph -> graph` |

**Node construction** — `lib/build-nodes.nix`

| Export | Signature |
|---|---|
| `buildNodes` | `{ parentGraph ? empty, importGraph ? empty, edgeGraphs ? {}, decls ? {}, types ? {}, strict ? true } -> { <id> = { id; type; parent; decls; }; }` |

Vertices are collected from every edge graph plus the `decls` and `types` key sets, then deduplicated. `parentGraph` becomes the `P` label and `importGraph` the `I` label; all edge targets are written into `decls.__edges` as `{ <label> = [id]; }`.

**Evaluators** — `lib/eval.nix`

| Export | Signature |
|---|---|
| `eval` | `{ roots, attributes, parseParent ? null, prior ? null, decision ? coldDecision, provenance ? [] } -> accessorRecord` |
| `evalDebug` | `{ roots, attributes, parseParent ? null } -> { node; get; getTraced; trace; allNodes; allNodeIds; }` — shadow-stack cycle tracing; defeats memoization. Both materializers are named throws |
| `evalWarm` | `{ roots, attributes, parseParent ? null, prior, decision, provenance ? [] } -> accessorRecord` — thin wrapper over `eval`, same code path; `prior` and `decision` MANDATORY |
| `recordedDeps` | `{ declaredEdges } -> id -> [id]` |

**The plane interface** — `lib/structural.nix`, `lib/interface.nix`

| Export | Signature |
|---|---|
| `structural` | `name -> bool` — the syntactic partition: `children`, `derived-children`, `edges-*`, `includes`. Total on every string |
| `resolutionalNames` | `[name] -> [name]` — the complement |
| `edgePrefix` | `"edges-"` — the reserved structural namespace |
| `childBearing` | `name -> bool` — the two attributes whose values are child-node records (a materialization concern, not a partition one) |
| `coldDecision` | `{ isClean = _: false; reusable = _: []; }` |
| `mkDecision` | `{ isClean, reusable } -> Decision` — argument set CLOSED, both required; an extra field is an arity error `tryEval` cannot catch |
| `mkFacade` | `{ get, nodeIds, resolutional } -> Facade` — same closure |
| `facadeNames` | `[ "get" "nodeIds" "resolutional" ]`, the enumeration as data |
| `decisionFindings` | `{ decision, resolutional, nodeIds } -> [{ nodeId; attrName; reason; }]` |

`accessorRecord` keys, observed: `node`, `get`, `allNodes`, `allNodeIds`, `allNodesWhere`, `subtreeOf`, `nodesOfType`, `_walkFrom`, plus the plane interface — `facade`, `resolutional`, `served`, `structuralEdges`, `decisionFindings`, `provenance`. Tier 1 is `node id` / `get id attrName`; the rest are Tier 2 materializers that force the tree.

`evalAttr` has THREE branches and only the second is ever the plane's. The first tests `structural attrName` and **always recomputes** — it never consults the decision, by branch order rather than by a check — so no structural value is served from a prior evaluation and a decision naming one is inconsequential rather than dangerous. The second is `decision.isClean nodeId && elem attrName (decision.reusable nodeId)`, which at that point IS membership in `reusable ∩ resolutional`, because the structural branch has already fired and `evalAttr` only ever sees a name in `attributes`. The third recomputes. Anything outside the served set therefore falls to a recompute, so over the `reusable` axis the worst a buggy or hostile plane achieves is a MISSED REUSE, never a stale serve. That does **not** hold over the `isClean` axis: a decision calling a dirty node clean serves stale resolutional values, and byte-parity against a cold run is that class's only instrument.

`decisionFindings` on the accessor is the debug-mode validator and is a VALUE, not a guard — nothing in the production path forces it, so it alters no result. `provenance` is a pass-through carrier: this library never invents a record for it, because the fact that gets stamped (an input past a benchmark-verified bound) and the threshold it is compared against belong to the engine above, which holds the cost curve they derive from.

`allNodes` and `allNodeIds` are two projections of ONE walk (`walkEntries` in `lib/eval.nix`), so asking for both costs one traversal. They carry the same node set; they differ in what survives of the walk. `allNodes` is an attrset, so `attrNames` on it answers in codepoint order and the traversal order is gone. `allNodeIds` keeps it: **root order, then pre-order depth-first through `children` / `derived-children`** (subtree contiguous, parent before descendants), repeats dropped **first-occurrence-wins** so `sort lessThan allNodeIds == attrNames allNodes`.

Two tie-breaks, both declared:

- **root and sibling ties break on `attrNames` = BYTEWISE CODEPOINT order**, not dictionary order — `attrNames { z; A; a; _b; "1"; }` ⇒ `[ "1" "A" "_b" "a" "z" ]`. ★ This is NOT "attrsets carry no order": `lib/graph.nix` carries a declaration-ordered vertex LIST (`overlay`/`connect` concatenate) and `lib/build-nodes.nix` collapses it `list -> listToAttrs -> attrNames` — the same construction `allNodeIds` exists to stop doing — so `eval` is handed `roots` already set-shaped. Measured: declared `[ "z" "y" "b" "a" ]` ⇒ `buildNodes` keys `[ "a" "b" "y" "z" ]`. The tie-break is that collapse's residue; recovering the declared order is a constructor change, not a walk change. Consequence: on a flat graph (every node a root, no children — what `buildNodes` alone yields) the two orders COINCIDE and a fixture of that shape cannot tell them apart.
- **a `derived-children` node INTERLEAVES with its `children` siblings**, it does not follow them: `_walkFrom` descends `children // derived` as ONE attrset. Measured, root with children `b`,`z` + derived `aa` ⇒ `allNodeIds` = `[ "r" "aa" "b" "z" ]`. Nothing in the list marks a node as derived.

Tests: `test-allNodeIds-dedups-repeat-visit`, `test-allNodeIds-is-allNodes-key-set` (`ci/tests/eval.nix`).

**Declared-reads surface** (the `readsAttrs` analogue). gen-scope has no `readsAttrs`; `git grep -n readsAttrs` over tracked files ⇒ no hits, and the same predicate hits `gen-resolve/lib` (see negative space). The only declared-reads construct here is `recordedDeps`, whose body is `{ declaredEdges }: id: declaredEdges id`. What it governs, enumerated:

- **Evaluation order** — not governed. `eval` schedules nothing; Nix's laziness is the scheduler.
- **Memoization** — not governed. `recordedDeps` never runs through `get`, so it neither reads nor populates any `_eval` cache.
- **Reuse admission** — not governed. `evalWarm` decides reuse from `decision.isClean id` and `decision.reusable id` only, and never for a structural attribute.
- **Reachability / error reporting** — not governed. Node resolution uses `roots`, `parseParent`, and the `children` / `derived-children` attributes.
- **Its own return value** — governed, and nothing else: it applies the caller's function to the caller's id. Neither evaluator accepts a `declaredEdges` argument (both patterns are closed; passing one is an arity error).

The evaluator's actual read channels are `self.node id`, `self.get id attrName`, and the four Tier-2 materializers. Recovering the *dynamic* read-set requires `evalDebug`'s fresh-`self`-per-`get`, which is why it defeats memoization.

**Resolution and attribute combinators** — `lib/resolve.nix`. Every combinator returns an attribute function, i.e. it ends in `self: id: value` (except `collect` / `collectByType`, which end at `self`).

| Export | Signature |
|---|---|
| `shadow` | `inner -> outer -> attrset` (inner wins per key) |
| `resolve` | `{ local ? null, imported ? null, inherited ? null, localShadowsImport ? true, importShadowsParent ? true } -> value \| null` |
| `query` | `{ dataFilter, localShadowsImport ? true, importShadowsParent ? true, transitiveImports ? false } -> self -> id -> value \| null` |
| `queryAll` | `{ dataFilter, transitiveImports ? false } -> self -> id -> [value]` (no shadowing) |
| `queryReverse` | `{ dataFilter, transitive ? false } -> self -> id -> [value]` — walks the *reverse* import relation; Tier 2 (forces `allNodes`). Answers in **reverse-walk discovery order**: pre-order DFS over the reverse relation, importers enumerated in `allNodeIds` (materialization) order, NOT `attrNames`. No sort, no dedup — a node on two reverse paths contributes twice |
| `ambiguous` | `queryAllArgs -> self -> id -> bool` |
| `visibleFrom` | `dataFilter -> self -> id -> value \| null` |
| `inherit'` | `{ resolve } -> self -> id -> value \| null` (first non-null up the parent chain) |
| `inheritAll` | `{ extract, combine ? (a: b: a ++ b) } -> self -> id -> [value]` (ordered-list discipline) |
| `inheritSet` | `{ extract, eq ? (a: b: a == b) } -> self -> id -> [value]` (set discipline, deduped) |
| `paramAttr` | `(self -> id -> param -> v) -> self -> id -> param -> v` |
| `circular` | `{ init, eq ? (a: b: a == b), maxIter ? 100 } -> (self -> id -> prev -> next) -> self -> id -> value` |
| `collectionAttr` | `{ traverse, extract, combine ? (a: b: a ++ b), filter ? (_: true) } -> self -> id -> [value]` |
| `collectImports` | `extract -> self -> id -> [value]` |
| `collect` | `{ filter ? (_: true) } -> extract -> self -> [value]` — Tier 2, **no `id` argument** |
| `collectByType` | `type -> extract -> self -> [value]` — Tier 2, no `id` argument |
| `followEdge` | `label -> self -> id -> [id]` |
| `collectByLabel` | `label -> extract -> self -> id -> [value]` |
| `subtypeOf` | `{ eq ? (_k: _a: _b: true) } -> self -> idA -> idB -> bool` |

`traverse` accepted by `collectionAttr`: a function `self -> id -> [id]`, or one of the strings `"imports"`, `"children"`, `"siblings"`, `"ancestors"`, `"neron"`, `"label:<edgeLabel>"`. Anything else throws.

**Structural queries** — `lib/queries.nix`. Thin wrappers over `self.node` / `self.get`; note the argument order is `self` first.

| Export | Signature |
|---|---|
| `parent` | `self -> id -> id \| null` |
| `children` / `childrenIds` | `self -> id -> { <id> = node; }` / `self -> id -> [id]` |
| `ancestors` / `descendants` | `self -> id -> [id]` (both cycle-safe) |
| `siblings` | `self -> id -> [id]` |
| `isAncestor` / `isDescendant` | `self -> otherId -> id -> bool` (early-terminating walks) |
| `nodesByType` | `self -> type -> { <id> = node; }` — delegates to `self.nodesOfType` |

**Attribute-name contract** (consumed, not exported). `children` and `derived-children` are reserved attribute *names* that the evaluator special-cases; `imports` and `edges-<label>` are the names the resolution combinators read. None of the four is supplied for you — the consumer declares them all in `attributes`.

**The well-founded engine — the program** — `lib/program.nix`

| Export | Signature |
|---|---|
| `mkRule` | `{ head, pos ? [], neg ? [] } -> rule` — the pattern refuses an unknown field BY NAME, and that refusal is NOT catchable (see traps) |
| `mkProgram` | `{ rules } -> { rules; atoms; bodyArity; unaryBodies; dependency; signs; }` |

`atoms` is the Herbrand base, CLOSED (every atom the rules mention, head or not) and in DECLARATION order. `bodyArity` is the greatest **positive** body arity and `unaryBodies` is `bodyArity <= 1` — the routing discriminator, computed once. `dependency` is `{ nodes; edges; }`, the UNSIGNED accessor the partition door is handed; `signs` is `atom -> { positive; negative; }`, the labelled view read beside it, total on every string.

**The least model of a definite program** — `lib/least-model.nix`

| Export | Signature |
|---|---|
| `leastModel` | `program -> { derived; converged; work; }` — the DOOR; routes on `armFor` |
| `leastModelUnary` | same, `genericClosure`; **refuses conjunctive input by name**. `work = { arm = "unary"; }` — no round count, because the done-set is C++-side |
| `leastModelRounds` | same, round loop; `work = { arm = "conjunctive"; rounds; }` |
| `armFor` / `armNames` | `program -> "unary" \| "conjunctive"` / the closed enumeration |
| `forceFields` | `acc -> null` — `seq` over every value in a record; the R-loop forcing discipline, exported so a consumer's own fold can use it |

**The well-founded model** — `lib/well-founded.nix`

| Export | Signature |
|---|---|
| `reduct` | `program -> guess -> { atoms; unaryBodies; rules; }` — Gelfond–Lifschitz; the result is DEFINITE |
| `wellFoundedModel` | `program -> { trueAtoms; undefinedAtoms; falseAtoms; verdict; outerRounds; converged; arm; }` |
| `verdictNames` | `[ "true" "undefined" "false" ]` — the closed vocabulary |

`verdict` is TOTAL on every string: an atom no rule mentions answers `"false"`, never an absence. Atom lists come back in the program's DECLARATION order, not codepoint order.

**Benchmark acceptance** — `lib/acceptance.nix`

| Export | Signature |
|---|---|
| `verifiedDepth` | `{ depth; derivation; fixtures; environment; reDerivationOwedOn; }` — never a bare number |
| `acceptanceSignal` | `{ baseline, reading } -> { signal; reason; }`; `baseline = null` answers `"unbaselined"` |
| `signalNames` | `[ "unbaselined" "voided" "fired" "steady" ]` |

**The engine's front door** — `lib/engine.nix`

| Export | Signature |
|---|---|
| `solve` | `program -> wellFoundedModel // { condensationDepth; provenance; }` |
| `provenanceFor` | `depth -> [ entry ]` — empty inside `verifiedDepth.depth`, one entry past it |
| `foldContributions` | `{ model, contributions, op, init } -> { value; admitted; contested; }` |

`solve` consumes gen-graph's `condensation` door for the depth and **never partitions itself**. The depth is demand-driven: a caller that never reads `provenance` never pays for the condensation.

**Staged minting** — `lib/mint.nix`. The only surface here that BUILDS a scope graph instead of reading one.

| Export | Signature |
|---|---|
| `mintStrata` | `{ emitters, kinds } -> { nodes; edges; strata; unrun; }` — argument set CLOSED at those two names |

`emitters` is `[ { pass; identifier; kind; relata; content; site; } ]`, a fixed list; `relata` is `{ <label> = <identifier>; }` and `site` is the string a conflicting-contribution refusal reports. `kinds` is the schema stratum's already-evaluated output — forced to WHNF and never read, which establishes that it is a value this call received rather than a fixpoint it participates in. `nodes` is `{ <identifier> = { identity; kind; content; }; }`; `edges` is `[ { from; to; label; } ]`, one per relatum, the label being the identity key; `strata` is the number of distinct declared passes; `unrun` is the driver's leftovers, empty on every run.

**Neither `hashIdentity` nor a frozen set is a formal.** The authority is injected by `lib/default.nix` (ADR-0016 ruling 5's one minting authority is a fact of the dataflow, not a convention), and the frozen set is built by this module's own fold — a caller-supplied one would be forgeable. Stratum 0 resolves against `{ }`. The identity key set is `[ "identifier" ] ++ attrNames relata`, values being the relata's resolved IDENTITIES and, for the reserved key, the node's own identifier string.

**What `mintStrata` does NOT do**, stated because each absence is load-bearing rather than pending:

- **No cascade rewire.** `resolveClaims` runs its own bounded loop over its own subject; `lib/mint.nix` names it nowhere and `lib/cascade.nix` names nothing of the minting module. Two constructions sharing a library, not a pipeline.
- **No graph query.** The `graph` formal reaches the module and no line applies it. The entry publishes the graph's CONTENT as plain data; reachability and partition are a later phase's questions.
- **No cap and no ceiling.** The schedule is what the emitters declared; nothing refuses a program for its size, and the attrset frozen set is a cost argument rather than a limit.
- **No lazy result.** Each stratum is forced in the round that produced it and the whole result is forced before return, so a refusal is a property of the call (see traps).
- ★ **The cross-pass replacement refusal is a PROPOSAL, not ruled law.** A later pass disagreeing about a key an earlier pass settled is refused here pending the substrate's general content rule, which ADR-0016 leaves open in its own words. The half that IS settled: a later pass naming a frozen identifier contributes content and never yields a second node. Do not cite the disagreement branch as ruled.

## Entry points by task

| Task | Reach for |
|---|---|
| Build a parent/import graph from parts | `overlay` / `overlays` / `edge` / `star` / `tree` |
| Turn graphs into root node descriptors | `buildNodes { parentGraph; importGraph; edgeGraphs; decls; types; }` |
| Evaluate attributes | `eval { roots; attributes; parseParent; }` then `result.get id attrName` |
| Diagnose an "infinite recursion" | `evalDebug` (named cycle trace; no `allNodes`) |
| Re-evaluate incrementally against a prior evaluation | `evalWarm { …; prior; decision = mkDecision { isClean; reusable; }; }` |
| Expose a consumer's declared dependency edges | `recordedDeps { declaredEdges }` |
| Synthesize nodes on demand | declare a `children` attribute; for a second stage that reads first-stage attrs, `derived-children` |
| Inherit a value down the parent chain | `inherit'` (first hit) / `inheritAll` (all, ordered) / `inheritSet` (all, deduped) |
| Resolve a name across imports + parents | `query { dataFilter; }`; all reachable results `queryAll`; who imports me `queryReverse` |
| Detect a name clash | `ambiguous` |
| Fixed-point / mutually recursive attribute | `circular { init; eq; maxIter; }` |
| Gather over children/siblings/ancestors/imports | `collectionAttr { traverse; extract; }` |
| Gather over the whole tree | `collect` / `collectByType` (Tier 2 — forces `allNodes`) |
| Follow a custom labelled edge | declare an `edges-<label>` attribute, then `followEdge` / `collectByLabel` |
| Navigate the tree | `parent` / `children` / `ancestors` / `siblings` / `descendants` |
| Materialize nodes | `result.allNodes` / `allNodesWhere pred` / `subtreeOf id` / `nodesOfType t` |
| Enumerate nodes in WALK order rather than codepoint order | `result.allNodeIds` (same set as `allNodes`, order kept) |
| Give a rule program with negation a meaning | `wellFoundedModel (mkProgram { rules; })` — read `verdict`, which is total |
| Get the meaning AND the out-of-verified-range warning | `solve (mkProgram { rules; })` — `provenance` is `[ ]` inside the bound |
| Ask which engine arm a program routes to | `armFor program` (never a mode you pass) |
| Combine contributions gated on a model | `foldContributions { model; contributions; op; init; }` — declaration order, `contested` named |
| Write your own round loop over a record accumulator | `prelude.iterateBounded forceFields step init bound` |
| Compare a fresh acceptance reading against the recorded one | `acceptanceSignal { baseline; reading; }` — it SIGNALS; it executes nothing |
| Build a scope graph from emitters, resolving relata against earlier passes | `mintStrata { emitters; kinds; }` — read `nodes` and `edges`; `strata` is reported and bounds nothing |
| Make a relation between two nodes expressible | give the relatum's emitter a STRICTLY LOWER `pass` than the relating emitter's — same-pass and root relata do not resolve, by construction |
| Find out why a mint refused | read the message: `unresolved relatum` names the relatum, label, kind and pass; `conflicting contributions` names the identity, the key and both sites |
| Resolve a claim multiset into resources and wiring | `resolveClaims { kinds; claims; ctx; }` — read `resources`, `wiring` and `trace` |
| Read ONE subject's wiring, in the run's global schedule order | `resolution.wiring.<id>.entries`, each entry `{ kind; claim; wiring; }`. There is no accessor: the run publishes the list, so this is a field read. **Test the key first** — see the totality trap below |
| Splice one subject's wiring into a single record | fold the entries per top-level key with a `key: [v]: v` combine drawn from `folds` — the same vocabulary a kind's resource fold is written against. `ci/tests/_fixtures/consumer.nix` carries the worked form |

## Measured traps

Each row verified in this run against `s = import ./. { }`. Shared fixtures: `roots = s.buildNodes { parentGraph = overlays [ (edge "a" "root") (edge "b" "root") (edge "c" "a") ]; importGraph = edge "b" "a"; edgeGraphs.uses = edge "c" "b"; decls = { root = { x = "R"; }; a = { }; b = { x = "B"; }; c = { }; }; types = {…}; }`. `R` = `eval` over those roots declaring both `children` and `imports`; `Rbare` = `eval` over the same roots declaring *neither*; `ok e = (builtins.tryEval e).success`.

| Trap | Evidence |
|---|---|
| `children` / `derived-children` are reserved attribute *names* the evaluator special-cases, but nothing supplies them — a consumer that omits `children` gets a throw from every structural query | `evalAttr` in `lib/eval.nix`; `ok (s.children Rbare "root")` ⇒ `false`, error text `gen-scope: unknown attribute 'children' on node 'root'`. Positive control `s.children R "root"` ⇒ `[ "a" "b" ]` |
| `self.get id "children"` does **not** include `derived-children`; only Tier-2 materialization unions the two | `_walkFrom` / `allNodesWhere` in `lib/eval.nix`; fixture with `children` ⇒ `kid@r` and `derived-children` ⇒ `shadow@r`: `get "r" "children"` ⇒ `[ "kid@r" ]`, `allNodes` ⇒ `[ "kid@r" "r" "shadow@r" ]`, and `node "shadow@r"` still resolves (`type` ⇒ `"d"`). Tests: `test-allNodes-includes-derived`, `test-derived-child-reachable` (`ci/tests/hoag.nix`) |
| `allNodes` with no `children` attribute declared **silently** returns the roots only — no error | `_walkFrom` guards with `if attributes ? "children"`; over a 3-node graph (`root` → `a` → `c`), an eval passed only `{ root = …; }` and no `children` attribute ⇒ `allNodes` = `[ "root" ]`. Positive control, same 3 nodes passed as roots plus a `children` attribute ⇒ `[ "a" "c" "root" ]`. The defect self-masks on `buildNodes` output, where every vertex is already a root: with and without a `children` attribute both ⇒ `[ "a" "c" "root" ]` |
| `buildNodes` defaults to `strict = true`, and the parent-uniqueness throw fires on `attrNames` alone — before any field is read | `parentIndex` in `lib/build-nodes.nix`; `builtins.attrNames (buildNodes { parentGraph = overlays [ (edge "k" "p1") (edge "k" "p2") ]; })` ⇒ threw `gen-scope: node 'k' has 2 parent edges (P must be a partial function, Neron §2.2). …`. With `strict = false`: `attrNames` ⇒ `[ "k" "p1" "p2" ]`, `.k.id` ⇒ `"k"`, `.k.parent` ⇒ threw. Tests: `test-multiple-parent-edges-strict-throws`, `test-multiple-parent-edges-lazy-deferred` (`ci/tests/build-nodes.nix`) |
| `star` is **inverted** relative to Mokhov §5.1 — edges run leaves→center, matching the child→parent P convention | `star` in `lib/graph.nix`; `(s.star "p" [ "a" "b" ]).edges` ⇒ `[ { from = "a"; to = "p"; } { from = "b"; to = "p"; } ]`. Test: `test-star` (`ci/tests/graph.nix`) |
| `buildNodes` always injects `decls.__edges`, so the returned `decls` is never the caller's attrset verbatim | `buildNodes` in `lib/build-nodes.nix`; node `a` was passed `decls.a = { }` yet `(R.node "a").decls` ⇒ keys `[ "__edges" ]`, and `(R.node "c").decls.__edges` ⇒ `{ I = [ ]; uses = [ "b" ]; }` |
| `subtypeOf`'s default `eq` compares **nothing** (`_k: _a: _b: true`) — it is key-containment only; supplying a value-comparing `eq` then drags the synthetic `__edges` into the comparison | `subtypeOf` in `lib/resolve.nix`; two nodes with identical user decls (`k = 1` both) but different import edges (`{ I = [ "n2" ]; }` vs `{ I = [ ]; }`): default ⇒ `true`, `eq = _k: a: b: a == b` ⇒ `false`. Test: `test-subtype-custom-eq` (`ci/tests/neron-semantics.nix`) |
| `followEdge` / `collectByLabel` / `collectionAttr { traverse = "label:X"; }` read a **computed attribute** `edges-X`; `buildNodes` never creates it — it writes targets into `decls.__edges.X` | `followEdge` in `lib/resolve.nix`; with the `uses` edge graph present but no `edges-uses` attribute, `ok (s.followEdge "uses" R "c")` ⇒ `false`. Adding `"edges-uses" = self: id: (self.node id).decls.__edges.uses or [ ]` ⇒ `[ "b" ]`. Test: `test-follow-custom-edge` (`ci/tests/neron-semantics.nix`) |
| The whole `query` family needs a consumer-declared `imports` attribute — import edges are computed, not structural | `query` / `queryAll` in `lib/resolve.nix`; `ok (s.query { dataFilter = n: n.decls.x or null; } Rbare "c")` ⇒ `false`, `ok (s.queryAll … Rbare "c")` ⇒ `false`. Positive control on `R` ⇒ `"R"` |
| `query` returns `null` on a miss, it does not throw | `resolve` in `lib/resolve.nix`; `s.query { dataFilter = _n: null; } R "c"` ⇒ `null`, `s.resolve { }` ⇒ `null`. Test: `test-resolve-all-null` (`ci/tests/resolve.nix`) |
| `nodesByType` is unusable with `evalDebug` — it delegates to `self.nodesOfType`, which only the `eval` record carries | `nodesByType` in `lib/queries.nix`; on an `evalDebug` record ⇒ `error: attribute 'nodesOfType' missing`, which `tryEval` does **not** catch. Record keys observed: `eval` ⇒ `[ "_walkFrom" "allNodes" "allNodesWhere" "get" "node" "nodesOfType" "subtreeOf" ]`, `evalDebug` ⇒ `[ "allNodes" "get" "node" ]`. Positive control on the `eval` record ⇒ `[ "a" "b" ]` |
| `evalDebug.allNodes` is a throw, not a function; and `evalDebug` refuses non-root `node` lookups without `parseParent` | `mkSelf` in `lib/eval.nix`; `d.allNodes` ⇒ threw `gen-scope: evalDebug does not support allNodes (use eval for materialization)`; `node "kid"` without `parseParent` ⇒ threw. Positive control `d.get "root" "imports"` ⇒ succeeded |
| `eval`'s argument pattern has no `...` — an unexpected key is a hard arity error `tryEval` cannot catch. The same closure is what makes `mkDecision` unable to carry a value-bearing field | `eval` in `lib/eval.nix`; `s.eval { roots = {}; attributes = {}; declaredEdges = _: []; }` ⇒ `error: function 'eval' called with unexpected argument 'declaredEdges'` (escapes `tryEval`). Positive control `s.eval { roots = {}; attributes = {}; prior = null; decision = s.coldDecision; }` ⇒ succeeded |
| `recordedDeps` is a pure pass-through with no connection to the evaluator: it applies the caller's function to the caller's id, and neither evaluator consults it | `recordedDeps` in `lib/eval.nix`; `s.recordedDeps { declaredEdges = _: [ "no-such-node" ]; } "also-no-such-node"` ⇒ `[ "no-such-node" ]` with no graph in scope at all; `{ declaredEdges = id: [ (id + "!") ]; } "c"` ⇒ `[ "c!" ]`. An attribute read that no declaration mentions succeeds unremarked: `R.get "c" "imports"` ⇒ `[ ]`. Tests: `test-recordedDeps-declared`, `test-recordedDeps-empty` (`ci/tests/eval.nix`) |
| A mis-pointed `parseParent` fails **two different ways**: naming a resolvable node that lacks the child throws; naming an unresolvable node diverges into a stack overflow | `resolveNode` / `genericResolve` in `lib/eval.nix`. Fixture: roots `r`, `other`; `r`'s `children` ⇒ `kid@r`. `parseParent "kid@r" = "other"` ⇒ `gen-scope: node 'kid@r' not reachable (parent: other)`. `parseParent "kid@r" = "nosuch"` (unresolvable, `parseParent "nosuch" = null`) ⇒ `error: stack overflow; max-call-depth exceeded` — `genericResolve` walks back through `kid@r`, re-entering `parseParent`. Positive controls: correct `parseParent` ⇒ `"k"`, and `parseParent = _: null` (generic walk) ⇒ `"k"` |
| `evalWarm` never reuses ANY structural attribute — `children`, `derived-children`, every `edges-*` label, `includes` — however clean the node and whatever the decision names | `evalAttr`'s first branch tests `structural attrName` (`lib/eval.nix`). Measured across the family: a decision reusing `edges-owns` from a prior answering `[ "POISON" ]` still answers the cold `[ "b" ]`, and the validator fires. Live control in the same matrix: a decision reusing the resolutional `label` IS served the prior's value and the validator stays silent. Tests: `plane-structural-matrix` (`ci/tests/plane.nix`), `test-children-always-recomputed` (`ci/tests/eval.nix`) |
| `circular` defaults to `maxIter = 100` and **throws** rather than returning a partial result | `circular` in `lib/resolve.nix`; `f = _: _: prev: prev + 1` ⇒ threw. Positive control `f = _: _: prev: if prev < 3 then prev + 1 else prev` ⇒ `3`. Test: `test-diverge-throws` (`ci/tests/circular.nix`) |
| `inheritAll` keeps duplicates (ordered-list `++`); `inheritSet` is its dedup sibling. Both are nearest-first | `inheritAll` / `inheritSet` in `lib/resolve.nix`; chain `root` (tag `T`) → `a` (tag `T`) → `c` (tag `C`): `inheritAll` ⇒ `[ "C" "T" "T" ]`, `inheritSet` ⇒ `[ "C" "T" ]`. Test: `test-inheritSet-dedups-what-inheritAll-keeps` (`ci/tests/resolve.nix`) |
| `overlay` does not dedup vertices — dedup is deferred to `buildNodes` | `lib/graph.nix` header comment; `(s.overlay (s.vertex "a") (s.vertex "a")).vertices` ⇒ `[ "a" "a" ]`, while `attrNames (buildNodes { parentGraph = <that>; })` ⇒ `[ "a" ]` |
| `collectionAttr`'s `traverse` is a string-dispatched enum; an unknown value throws at *use*, not at construction | `collectionAttr` in `lib/resolve.nix`; `traverse = "parents"` ⇒ threw `gen-scope: collectionAttr: unknown traverse 'parents'`. Positive control `traverse = "ancestors"` ⇒ `[ "a" "root" ]` |
| `collect` / `collectByType` end at `self` — they take **no** `id` argument, unlike every other combinator | `collect` in `lib/resolve.nix`; on a one-node fixture (`roots = { n = …; }`), `s.collect { } (_self: id: [ id ]) <record>` ⇒ `[ "n" ]` — three arguments, not four |
| The source modules merge flat with **no** shadowing, so the name collisions with other concepts are real exports: `resolve` here is the Neron specificity function (unrelated to the sibling library gen-resolve), and `vertices` is the constructor `[id] -> graph` while `g.vertices` is a field | `lib/default.nix` merges sixteen modules; `nix eval --json .#lib --apply 'builtins.attrNames'` ⇒ 87 names, and the per-module export counts sum to the same figure — so no key is overwritten. `lib/mint.nix` contributes exactly 1 of the 87 |
| ★ A RULE WITH TWO LITERALS CAN STILL BE **UNARY**, and the engine routes it to the closure arm. The discriminator is the greatest **positive** body arity; a negative literal contributes nothing to it | `mkProgram { rules = [ { head="b"; } { head="z"; pos=["b"]; neg=["q"]; } ]; }` ⇒ `bodyArity = 1`, `unaryBodies = true`, `armFor ⇒ "unary"`. Live control in the same suite: adding `{ head="y"; pos=["b" "r"]; }` ⇒ `bodyArity = 2`, `armFor ⇒ "conjunctive"`. Why it is SOUND to compute once: reduction deletes rules and deletes negative literals, and does neither of the two things that could raise the figure. Tests: `engine-program`, `engine-least-model` |
| ★ `mkRule`'s unknown-field refusal is **NOT CATCHABLE** — an argument-arity error kills the evaluation rather than answering `{ success = false; }`, so no nix-unit cell can host it. The same is true of `eval`'s pattern (row above). And `tryEval` DISCARDS a throw's message, so a refusal's TEXT is unreadable in-language even where the throw itself is catchable | `nix-instantiate --argstr arm refuseUnknownField ./ci/bench/engine-ceiling.nix` ⇒ exit 1, `error: function 'mkRule' called with unexpected argument 'negs'`, `Did you mean neg?`. `--argstr arm refuseConjunctiveOnUnaryArm` ⇒ exit 1, message contains `unary-only`. Both are read off the EXIT CODE; `catchControl` in the same sweep returns `{ success = false; }`, so the catcher is live |
| ★ **TWO ABORT SIGNATURES, NOT ONE.** An unforced accumulator field chaining through a FUNCTION APPLICATION exhausts `max-call-depth` first; the same field chaining through a bare `+` has no guard in front of it and goes straight to the C stack. A sweep armed for one label reads the other as green | Measured on one loop over one accumulator, differing only in the link and the forcing (`./ci/bench/engine-ceiling.sh`, nix 2.34.8 · max-call-depth 10000 · `ulimit -s` 8192): `unforcedCall` green 9995 → **CALLDEPTH** 9998; `unforcedOperator` green 45000 → **CSTACK** 45500; `forced` (the same loop under `forceFields`) **green at 50000**, past both; `tryUnforced` (the unforced arm inside `tryEval`) **dies** at 50000 |
| A STRICT READ IS ITSELF A FORCE, but only of the field it reads — so an accumulator whose guard reads one attrset field strictly is force-free on THAT field while every scalar counter beside it still chains. This is how a partial fix arises by construction rather than by omission | The `engine-ceiling.nix` accumulator carries `set` (read strictly by the guard) and `tick` (read by nothing); `set` never chains and `tick` is what aborts. The engine's own alternating fixpoint carries the same shape — `innerConverged` is read by no control flow — which is why `forceFields` derives its forcing from the record rather than from a list of field names |
| The library takes **three** inputs, two of them siblings: `graph` is gen-graph's `.lib` and `schema` is gen-schema's. `lib/graph.nix` (this library's algebraic constructors) is a DIFFERENT thing, bound as `algebraicGraph` inside `lib/default.nix` | `flake.nix` inputs are `gen-prelude` + `gen-graph` + `gen-schema`; `lib/default.nix` takes `{ prelude, graph, schema }`. The engine calls `graph.condensation program.dependency` and reads `.depth`; it partitions nothing itself. Of `schema` only `hashIdentity` is taken, and only `lib/mint.nix` receives it |
| ★ **THE PUBLISHED WIRING RECORD IS TOTAL, AND BOTH REFLEXIVE READS OF IT ARE WRONG.** `resolution.wiring` carries a key for every subject a claim was ABOUT, so a missing key means *never registered* and a present record with `entries = [ ]` means *registered and nothing wired it*. Reading `wiring.<id>.entries` bare **aborts uncatchably** on the first; defaulting the record, `(wiring.<id> or { entries = [ ]; }).entries`, **answers `[ ]` for both** and erases the difference. Test membership, then read | `./ci/bench/wiring-scan.sh`, three arms in one run over a kind whose resolver emits resources and no wiring: `bareReadNeverClaimed` ⇒ exit 1, `error: attribute 'id-never-claimed' missing`; `erasingRead` ⇒ `0` for the registered-but-unwired subject and `0` for the never-claimed one; `safeRead` ⇒ `{"entries":[],"registered":true}` against `{"registered":false}`. Tests: `test-registered-but-unwired-subject-keeps-its-record`, `test-never-claimed-subject-has-no-record`, and the armed control `test-armed-the-erasing-read-loses-the-distinction` (`ci/tests/cascade-helpers.nix`) |
| ★ A relatum that IS minted in the same run refuses anyway if its pass is not STRICTLY EARLIER — "the node exists somewhere in this run" is not the predicate, and the message reads the same as a typo | `mintOne` / `accumulate` in `lib/mint.nix`. Emitters `[ { pass = 0; identifier = "a"; relata.r = "b"; } { pass = 1; identifier = "b"; } ]` ⇒ threw `gen-scope.mintStrata: unresolved relatum 'b' (label 'r', minting kind 'widget', pass 0)`. Positive control, the SAME two emitters with the passes swapped ⇒ evaluated clean |
| ★ A relatum whose LABEL is `identifier` collides with the reserved identity key, and the refusal comes from the AUTHORITY rather than from here — so the message names neither the label nor the emitting site | `identifierKey` / `mintOne` in `lib/mint.nix`. The pass-1 emitter given `relata = { identifier = "b"; }` ⇒ threw `identity: duplicate identity key`, with no gen-scope prefix and no coordinates. Positive control, the same fixture under the label `r` ⇒ evaluated clean |
| Reading ONE field of the result runs the WHOLE mint: the entry deep-forces its result before returning, so a refusal in a stratum the caller never asked about still fires | `builtins.deepSeq result result` at the end of `lib/mint.nix`. `(mintStrata { … }).strata` over a fixture whose pass-1 emitter names a nonexistent relatum ⇒ threw `gen-scope.mintStrata: unresolved relatum 'nosuch' …`, the trace pointing at that final `deepSeq`. Positive control, the same read with that relatum pointed at the pass-0 node ⇒ `2` |
| `strata` counts the DISTINCT DECLARED passes, not the declared maximum plus one — a program declaring passes 0 and 1000000 runs two strata | `schedule = sort ascending (unique (map (e: e.pass) emitters))` in `lib/mint.nix`. Emitters declaring passes 0 and 3 ⇒ `strata` = `2`, `unrun` = `[ ]`, `edges` = `[ { from = "a"; label = "r"; to = "b"; } ]` |
| The conflicting-contribution message orders the two sites by THEIR OWN TEXT, not by the order the emitters were declared in — a message that moved under a permutation would stop being a property of the program | `conflictingContribution` in `lib/mint.nix`. Two same-pass emitters of one identifier disagreeing at key `k`, declared `site-B` then `site-A` ⇒ `… at key 'k' (site-A, site-B)`; declared `site-A` then `site-B` ⇒ the byte-identical message. Both minting refusals are `throw`, so `tryEval` DOES catch them, unlike `mkRule`'s and `eval`'s arity refusals: `{ success = false; }` measured on the same-run-later-pass and nonexistent-relatum fixtures, on a root relatum, on the reserved-label collision and on this conflict, with `tryEval (throw "…")` live in the same run. The message is discarded with the catch, which is why the text cells live in `#testsError` |

## Theory

Claimed in `README.md` under "Theoretical Foundations", which labels each source **Implements**, **Partial**, or **Informed by**, and restated in code comments.

**Implements**

- **Vogt et al. (1989), *Higher-order attribute grammars*** — dynamic node synthesis via `children` / `derived-children` as non-terminal attributes (§2.4); `derived-children` extends this with second-stage stratification.

- **Hedin (2000), *Reference attributed grammars*** — import edges as reference attributes; cross-node attribute access through computed scope references.

- **Neron et al. (2015), *A theory of name resolution*** — scope graph construction, the resolution calculus (`query` / `queryAll`), D < I < P specificity ordering (Fig. 2), path well-formedness (§2.4), seen-imports cycle prevention (rule X), shadowing (§5 Def. 1). The partial-function constraint on P (§2.2) is enforced by `buildNodes`.

- **Mokhov (2017), *Algebraic graphs with class*** — all four construction primitives (`empty` / `vertex` / `overlay` / `connect`) and the derived constructors (`star` / `path` / `clique` / `tree` / …) from §2.1–§5.1; `overlay`'s idempotence is what licenses deferring dedup to `buildNodes`.

- **Sloane et al. (2010), *Kiama: AG embedding*** — the `CachedAttribute` pattern realized as the co-located `_eval` cache; `paramAttr` (§3); `circular` fixed-point attributes (§2.2); collection attributes (§7).

- **Van Gelder, Ross & Schlipf (1991), *The well-founded semantics for general logic programs*** — the well-founded partial model computed at the ATOM level, with `UNDEFINED` a named third verdict for contested atoms; total and equal to the perfect model on locally stratified programs.

- **Van Gelder (1993), *The alternating fixpoint of logic programs with negation*** — the construction: `S(J) = lfp T_{P/J}` antimonotone, `S²` monotone, `W⁺ = lfp(S²)` from ∅, `S(W⁺)` the true-or-undefined set.

- **van Emden & Kowalski (1976), *The semantics of predicate logic as a programming language*** — `T_P` and its least fixpoint as the meaning of a definite program; both `leastModel` arms compute it over the reduct.

**Partial**

- **Gelfond & Lifschitz (1988), *The stable model semantics for logic programming*** — the reduct `P/J` is implemented and iterated. Stable-model EXISTENCE, the companion refusal criterion, is **NOT built**: no construction in this library decides it, and containment (well-founded ⊆ every stable model) is not a decision procedure. Stated so a reader does not infer an oracle from the semantics beside it.
- **Tarjan (1972) / Fleischer, Hendrickson & Pınar (2000)** — CONSUMED, not implemented: the SCC partition and the condensation come from gen-graph's published front door, and the engine reads the reported `depth` and nothing else.
- **van Antwerpen et al. (2018), *Scopes as types*** — custom edge labels via `edgeGraphs` / `followEdge`, structural subtyping (`subtypeOf`), coarse-grained visibility (boolean shadowing flags). README marks the Statix-style constraint patterns partial: custom labelled edges only, and a single `decls` relation per node.

**Informed by** (README's own label; no result claimed): Apt, Blair & Walker (1988) *Towards a theory of declarative knowledge*, at TWO surfaces — for the engine, why the third verdict is needed at all, the stratified semantics admitting positive cycles and leaving a cycle through a negative edge without a meaning; and for `mintStrata`, the standard model of a stratified program being built one stratum at a time with each closed before the next begins (printed p. 108), which is what a minting pass is. The correspondence taken there is the CLOSURE of earlier strata and not the per-stratum fixpoint iteration, and it is why a cycle among minted nodes is inexpressible rather than detected; Hedin & Magnusson (2003) *JastAdd*, for the demand-driven evaluation pattern and the aspect-oriented attribute extension model — the code comment on `queryReverse` cites the same paper's inter-type declarations; Radul & Sussman (2009) *Art of the propagator*, for monotonic convergence in `circular`; Van Wyk et al. (2010) *Silver*, for forwarding and fold operators behind `collectionAttr` / `inheritSet`; Mokhov et al. (2018) *Build systems à la carte*, for demand-driven evaluation as a suspending scheduler (§4.1) — README states gen-scope builds no scheduler, Nix is the scheduler; Acar et al. (2006) *Adaptive functional programming*, for `evalWarm`'s clean-result reuse and `recordedDeps` as the declared read-edge projection of a dynamic dependence graph.

**Standing rulings the minting entry is built against** (cited in `lib/mint.nix` and `lib/default.nix`, where each claim sits beside the construction it governs):

- **ADR-0016 ruling 4** — a binding's identity keys are its relatum labels and their values are the relata's identities. It gives the key set for a binding and refuses a zero-key preimage by name; the reserved key carrying the node's own identifier is what a relatum-free emitter is minted on, and the VALUES clause is untouched.
- **ADR-0016 ruling 5** — identifier ≠ identity, and there is exactly ONE minting authority. Here that is dataflow rather than convention: the module receives `hashIdentity` and holds no library of its own to reach for.
- **ADR-0016 ruling 7** — minting is staged, and a relatum must already be minted in a strictly earlier pass. The frozen set is what makes it by construction: a same-pass relatum cannot be named because it is not in the set.
- **ADR-0014, the CONSTRUCTING arm** — a constructor taking an injected authority mints inside the consumer's own eval, so the value's identity is owned rather than borrowed. The rejected arm is verbatim re-handing, which is why no part of gen-schema is re-exported under this library's name.
- **ADR-0022** — iterative encodings only, every round-loop accumulator field forced per round. Both loops here are folds; a self-applying walk's descent depth would be its iteration count, and past the call-depth guard it ends the evaluation rather than throwing — an abort `tryEval` does not contain.

**Checked invariant**: nixpkgs-lib-freedom (no `lib.`, no `evalModules` / `mkOption`, no `nixpkgs` input — the dependencies are gen-prelude, gen-graph and gen-schema, each nixpkgs-lib-free under its own purity suite rather than under this one) is enforced by `test-library-source-is-nixpkgs-lib-free` (`ci/tests/purity.nix`) over `lib/**.nix` + root `flake.nix` + `default.nix`, on comment-stripped source.

## Drift check

```sh
nix eval --json .#lib --apply 'builtins.attrNames'
```

Current output (verbatim):

```json
["acceptanceSignal","ambiguous","ancestors","armFor","armNames","buildNodes","childBearing","children","childrenIds","circuit","circular","clique","coldDecision","collect","collectByLabel","collectByType","collectImports","collectionAttr","connect","decisionFindings","descendants","edge","edgePrefix","edges","empty","eval","evalDebug","evalWarm","facadeNames","foldContributions","folds","followEdge","forceFields","forest","gmap","hasEdge","hasVertex","induce","inherit'","inheritAll","inheritSet","isAncestor","isDescendant","leastModel","leastModelRounds","leastModelUnary","mintStrata","mkClaim","mkDecision","mkFacade","mkKind","mkKinds","mkProgram","mkRule","nodesByType","overlay","overlays","paramAttr","parent","path","provenanceFor","query","queryAll","queryReverse","recordedDeps","reduct","removeEdge","removeVertex","resolutionalNames","resolve","resolveClaims","shadow","siblings","signalNames","solve","star","stratify","structural","subtypeOf","transpose","tree","verdictNames","verifiedDepth","vertex","vertices","visibleFrom","wellFoundedModel"]
```

**Checks.** Test-runner invocation (from the repo root; CI runs the same command with `working-directory: ci`, `.github/workflows/ci.yml`):

```sh
nix flake check ./ci
```
