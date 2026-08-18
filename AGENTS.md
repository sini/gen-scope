# gen-scope — agent capability sheet

## Scope

Demand-driven higher-order attribute-grammar evaluator over algebraic scope graphs: you supply root node descriptors (`{ id, type, parent, decls }`) and attribute definitions (`self: id: value`), and `eval` returns an accessor record (`node` / `get` / four materializers) whose attributes compute lazily and memoize on an `_eval` cache co-located on each node.

**THREE FURTHER, INDEPENDENT CONCERNS LIVE HERE.** The **well-founded engine** computes the meaning of a rule program with negation — `mkProgram` in, a three-valued model out, with `UNDEFINED` a named verdict for contested atoms. **Staged minting** (`mintStrata`) goes the other way from the evaluator: emitters in, a scope graph out — vertices under their own identifiers, one labelled edge per relatum, each relatum resolved against what strictly earlier passes settled. **The demand cascade** (`resolveClaims`) resolves a claim multiset down a kind registry's depth measure: claims in, provisioned resources and published wiring out, with the record of how. None of the three touches a node, an attribute or a scope graph.

Routing a task: atoms, rules, negation or a fixpoint over a policy program ⇒ the engine. Nodes, attributes or scopes ⇒ the evaluator. Emitters, passes, relata, identifiers or identities ⇒ minting. Claims, kinds, resolvers, resources or wiring ⇒ the demand cascade. ★ **"Strata" alone does NOT route** — the engine's stratum is a layer of a rule program, minting's is a declared pass, and the cascade's is a depth in its kind registry. What these constructions share is ONE module: `lib/least-model.nix`, for the round-loop forcing `forceFields`, which staged minting and the demand cascade each import rather than write a second copy of. Beyond it the assembly hands the stratification driver to staged minting, and no module of one concern reaches another — `grep -rn "import \./" --include="*.nix" lib/` outside `lib/default.nix` returns nine imports across seven files, and the only ones crossing a concern boundary are `mint.nix` → `least-model.nix` and `cascade.nix` → `least-model.nix`.

## Not this library's job

Quoted text is the owner's own `flake.nix` `description` field, verbatim. Grep counts below are `grep -rEl '<pattern>' --include='*.nix' <dir> | wc -l` — files with a match — run from `/home/sini/Documents/repos/sini`. In the patterns, `\|` is markdown table escaping for the ERE alternation `|`. Rows carrying no grep cite attribution from the sibling description alone: the predicates tried for `gen-dispatch` matched nothing in its own `lib/`, so no absence is claimed against it.

| Responsibility | Owner |
|---|---|
| Static read-dependency analysis (`readsAttrs`), attribute stratification, the scheduled convergence fold | `gen-resolve` — "gen-resolve — demand-driven higher-order RAG evaluator over algebraic scope graphs (Knuth 1968 attribute schedule + Vogt 1989 HOAG)". gen-scope ships `circular` as the bare fixed-point loop primitive, and `foldEquations` RECEIVES a schedule as a value rather than building or validating one. Discriminating predicate `readsAttrs\|scheduleWith\|buildSchedule` over `gen-scope/lib` ⇒ **0 files**, same predicate over `gen-resolve/lib` ⇒ **4** (the positive control, and the reason the row is scoped this way). ★ The broad form `readsAttrs\|stratum\|schedule` does NOT discriminate and this row no longer uses it: it returns **7** files here — `stratum` is minting's declared pass and the cascade's own layer, and `schedule` is the argument the cold fold takes — and it returned **5** before that fold arrived, so the `⇒ 0` this row used to claim was already false of the token and only ever true of the ownership |
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
| Selector-driven subject filtering over a demand multiset — `gen-demand`'s `adapters` | **Nobody: it RETIRED rather than moving.** ADR-0008 §4 retired gen-demand as a library into this one — *"gen-resolve and gen-demand as libraries retire into these homes; gen-demand's demand/kind folds re-express over scope"* — and of its eight exports the map records `adapters` as the one that **retires and does not move**, with subject-filtering capability retiring alongside it, because moving it would give the sole evaluator a selector-algebra dependency. gen-scope takes no `gen-select` edge, and that is a dependency fact rather than a token count: `grep -c 'gen-select' flake.nix` ⇒ **0**, against the three live controls `gen-prelude` / `gen-graph` / `gen-schema` ⇒ 5 / 5 / 7 in the same run. ★ Everything else of that library — kinds, claims, the stratified resolution, the fold vocabulary — is **this library's own** and is documented under **The demand cascade** and **The fold vocabulary** in Exports below. This row is the negative space the retirement left, not the surface |
| Aspect traits / classification | `gen-aspects` — "gen-aspects: aspect-oriented composition types (pure-gen, re-hosted on gen-merge)" |
| Channels / dataflow riding over scopes | `gen-pipe` — "gen-pipe — scoped channels + dataflow algebra (map/filter/fold/scan/route/join/tee) with B5 determinism, provenance, dedup, and class-aware contributions"; `gen/lib/mkGenLibs.nix` records its deps as `prelude+select+scope` |
| The nixpkgs boundary: value injection, building systems | `gen-flake` — "gen-flake — the pure composition boundary of the pure-gen module ecosystem" |

## Exports

Entry: `inputs.gen-scope.lib` (flake). Root `default.nix` is a function `{ prelude ? <derived from flake.lock>, graph ? <derived from flake.lock>, schema ? <derived from flake.lock>, ... }` — callable as `import ./gen-scope { }`, which content-addresses gen-prelude, gen-graph and gen-schema out of the pinned lock and needs no `<nixpkgs>`.

`lib/default.nix` is a REFUSING MERGE over seventeen modules — `algebraicGraph`, `buildNodes`, `queries`, `resolve`, `structural`, `interface`, `eval`, `program`, `leastModel`, `wellFounded`, `acceptance`, `engine`, `stratify`, `mint`, `folds`, `cascade`, `foldEquations` — folded by `lib/merge-surface.nix`, which throws naming the key and both contributing modules when one name is contributed twice. It replaced a flat `//` chain, which resolved a duplicate by list position and said nothing. All 88 exports sit at top level; there is no nested namespace and no key is shadowed — and that last is now a property of the assembly rather than of a cell (see traps). ★ In that merge `algebraicGraph` is this library's OWN `lib/graph.nix`; the parameter named `graph` is the **gen-graph library**, and the two are different things. `schema` is the third parameter and is bound to ONE function: `lib/default.nix` passes `hashIdentity` into `lib/mint.nix` and nothing else of that library reaches any module here. ★ Two `lib/` files are NOT in that merge and contribute no export: `lib/merge-surface.nix`, which performs it, and `lib/traversal-names.nix`, the resolver's traversal vocabulary — imported directly by `lib/resolve.nix` and `lib/structural.nix`, so the name the resolver traverses and the name the classifier reserves are one binding rather than two literals that agree by coincidence.

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

Vertices are collected from every edge graph plus the `decls` and `types` key sets, then deduplicated. `parentGraph` becomes the `P` label and `importGraph` the `I` label; all edge targets are written into `decls.__edges` as `{ <label> = [id]; }`. Those two labels are RESERVED — an `edgeGraphs` carrying either is refused by name at the entry (see traps).

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
| `structural` | `name -> bool` — the syntactic partition: `children`, `derived-children`, `edges-*`, the traversal vocabulary's values (`imports`), `includes`. Total on every string |
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

**Attribute-name contract** (consumed, not exported). `children` and `derived-children` are reserved attribute *names* that the evaluator special-cases; `imports` and `edges-<label>` are the names the resolution combinators read. None of the four is supplied for you — the consumer declares them all in `attributes`. ★ All four are STRUCTURAL and so never served from a prior evaluation. `imports` reaches both the resolver and the classifier from one binding (`lib/traversal-names.nix`); a second relation added there is reserved by construction, but a traversal writing its own string literal instead is NOT — a predicate over attribute names cannot read a caller's literals.

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

**The demand cascade** — `lib/cascade.nix`. A kind registry whose depth measure stratifies a run, and the stratified resolution of a claim multiset over it. "Demand" here means demand-driven evaluation and only that; the request value is a CLAIM, named for what it is.

| Export | Signature |
|---|---|
| `mkKind` | `{ name, below ? [ ], resolve, dedupKey ? null, fold ? null } -> kind` |
| `mkKinds` | `[kind] \| { <n> = kind; } -> { _type; kinds; depth; maxDepth; }` |
| `mkClaim` | `{ kind, subject, ...payload } -> claim` |
| `resolveClaims` | `{ kinds, claims, ctx ? { } } -> { resources; wiring; unrun; trace; }` |

`kinds` on the run takes EITHER a registry `mkKinds` built or the raw kinds to build one from, so a caller who already registered pays nothing twice. `claims` is a list. `resources` is `{ <kindName> = { <resourceKey> = value; }; }`, `wiring` is `{ <id_hash> = { subject; byKind; entries = [ { kind; wiring; claim; } ]; }; }`, `trace` is `{ claims; resources; wiring; }`, and `unrun` is the claims the loop created and did not settle.

★ **`lib/cascade.nix` imports ONE sibling module and it is `lib/least-model.nix`**, for the round-loop forcing `forceFields` — the same module staged minting takes it from, rather than either writing a second copy. Nothing else of the evaluator, the engine or staged minting is reached from here, and nothing there reaches this: the cascade receives `{ prelude, graph }` and no more.

**The depth measure and the acyclicity verdict are ONE read, and it is gen-graph's.** `mkKinds` calls the cone-rank surface over the relation the registry already describes and reads the depth map ALONE — not the linearisation beside it, since two topological orders of one relation can differ element for element and both be correct. A cyclic `below` has no producers-first rank and the surface refuses it by name, so acyclicity is what asking for the measure already costs rather than a guard bolted on; the record is `seq`-forced at registration, which is what makes a cyclic set refuse where it is DEFINED. `depth k = 0` for a kind with no registered successor, else `1 + max { depth b : b ∈ below(k) registered }`.

**The schedule is the measure, descending.** `[ maxDepth … 0 ]`, consecutive integers read straight off the map — no sort, no ties, no tie-break — because a kind at depth `d` emits only into strictly smaller depths. Its LENGTH is the loop's bound and that is a theorem rather than a budget: a strictly decreasing natural-number measure exhausts in `maxDepth + 1` rounds by Noetherian induction on ℕ. Nothing tests for convergence and nothing caps the iteration.

**A resolver sees the claim's own fields plus `_path`, and the caller's constant `ctx`.** No resources, no wiring, no trace, no partial view of the run — THEORY: the emission ⊥ consumption invariant of the claim/provide design, which the schedule makes structural rather than a discipline an author keeps, so no resolver's answer can depend on where in a stratum it ran. The engine's `_reserved` channel is stripped; everything else the claim carries, INCLUDING its type marker, is passed through.

**The result is TOTAL on what was declared.** Every registered kind gets a `resources` entry, empty if nothing claimed it; every subject a claim was ABOUT gets a `wiring` key, with `entries = [ ]` if nothing wired it. So a MISSING key means never registered and a present-but-empty record means registered and quiet — two observations the totality exists to keep apart, and nothing else in the result carries the difference. ★ Read it by TESTING the key: a bare `wiring.<id>.entries` aborts uncatchably on an unregistered subject, and the defaulting read `(wiring.<id> or { entries = [ ]; }).entries` answers `[ ]` for BOTH and erases the difference. The traps table below carries both arms with their bench evidence.

**The trace is a record and deliberately not an algebra.** Each resource key maps to the claims that produced it, each wiring entry to the claim that emitted it, each claim to its parent chain. THEORY: why/derivation provenance in the sense of Cheney, Chiticariu & Tan (2009) — named from the literature, not checked against a held copy, as neither this survey nor the semiring paper below is in the project archive. ★ The Green–Karvounarakis–Tannen provenance SEMIRING is DELIBERATELY NOT REALIZED and is not planned — these are records about a run, not annotations carrying a `(+, ×)` algebra, and nothing here computes with them. The rider travels with the citation, because the citation arriving alone reads as a claim that the semiring is implemented.

**What the registry establishes, and where the line is.** `resolve`, `dedupKey` and `fold` are PRESENT on anything that registers and each is APPLICABLE (a function, or a set this evaluator applies — one `__functor` level, because the chain has no bound and can refer to itself). The `dedupKey`/`fold` pairing is a registration-time error. Past that: ARITY is not checked and is not checkable — a one-argument resolver is applied, returns a value, and that value is applied again, failing with the same uncatchable type error a non-function does; and what a resolver's answer CONTAINS is unconstrained, though the answer's own SHAPE is decided where it returns. A `dedupKey`'s return is checked at APPLICATION, where the value first exists.

**Both markers answer PROVENANCE for a cooperative caller, and neither vouches for contents.** A record that came out of `mkKind`/`mkKinds` has been through every refusal; a record that merely writes `_type` has asserted something about its own origin nothing here can check. So the run re-asks the registration door's own question on the door that skips it, and it reads what it SETTLED rather than what the record declared — which is why a depth map that is well-shaped and wrong strands claims into `unrun` instead of silently reporting them as a kind nobody claimed.

**Refusals.** `mkKind`: non-string `name`; a `below` that is not a list, or holds a non-string; `dedupKey` without `fold`; `fold` without `dedupKey`. `mkKinds`: an argument that is neither list nor attribute set; entries that are not kind records, each labelled in the caller's own coordinates (a position for the list form, the attribute name for the set form) and given its own reason; duplicate names; `below` names with no registered kind. `mkClaim`: missing `kind`; missing `subject`; a `kind` that is neither a kind value carrying a string `name` nor a kind-name string; a payload shadowing `_type` / `_path` / `_reserved`. `resolveClaims`: `claims` not a list; a registry defect (no `kinds` or `depth` attribute set, a non-integer `maxDepth`, entries that are not kind records, a registered kind with no `depth` entry); per claim, in order — not a claim, a non-string `kind`, an unknown kind, a non-empty `_reserved`, a subject with no `id_hash`, an `id_hash` that is not a string; a resolver's ANSWER that is not an attribute set, or whose `resources`, `wiring` or `claims` is the wrong container; a `dedupKey` returning a non-string; a sub-claim of a kind outside its emitter's `below`; a resource key contributed by two distinct groups; a wiring entry targeting a subject with no `id_hash` or a non-string one. Every refusal from the per-claim chain onward carries the claim's path, and a sub-claim's also names the emitting claim; the two argument-shape arms — `claims` not a list, and the registry defect — fire before any claim exists and carry neither.

★ **The answer-shape refusal's WORSE half is the record itself.** A resolver returning a list, a number or null is a type error nowhere: all three fields are read through an `or` default, so every default fires and the claim contributes NOTHING — silently, and byte-identically to a resolver that returned an empty set on purpose. Checking only the loud half (a `resources` that is a list, where `attrNames` aborts) would leave the quiet one exactly as it was. The answer is forced to weak head normal form through one binding, so no path reaches a field of it without its shape having been decided.

**What the loop does NOT refuse**, because it is inexpressible: a backward or same-stratum emission. A sub-claim's kind must be a registered member of the emitting kind's `below`, and every such member has strictly smaller depth hence a strictly later position in the schedule. There is no check to meet or miss. ★ And `unrun` is RETURNED, never thrown — for a caller whose registry says something the run cannot honour, a refusal would destroy the information they need. Over a registry this library built it is always empty.

**The fold vocabulary** — `lib/folds.nix`. A value algebra over fragments, under ONE signature: `key: [v]: v`.

| Export | Signature |
|---|---|
| `folds.same` | `key -> [v] -> v` — all fragments agree; returns the first |
| `folds.one` | `key -> [v] -> v` — exactly one contributor |
| `folds.list` | `key -> [v] -> [v]` — the fragments in pinned order |
| `folds.mergeAttrs` | `key -> [attrs] -> attrs` — shallow merge, disjoint sub-keys required |
| `folds.byKey` | `spec -> key -> [attrs] -> attrs` — a fold CONSTRUCTOR: each fragment key `k` folded by `spec.${k}` under the diagnostic sub-key `<key>.<k>` |

`folds` is one top-level export whose value is the five-member vocabulary, and it serves two consumers, BOTH of them caller-side: a kind's resource `fold`, where `key` is the resource key, and a caller's own wiring-splice combine, where `key` is the top-level wiring key. Neither has a vocabulary of its own. The library publishes no splice — `spliceWiring` retired, and the worked form lives in `ci/tests/_fixtures/consumer.nix`. ★ The cascade names this module NOWHERE, and no other `lib/` module imports it either: a kind's fold arrives as a FIELD on the kind, so the vocabulary reaches a run as the author's data rather than as an import.

**Every fold decides its KEY first, `list` included**, even though `list` raises nothing to interpolate. Every refusal that reaches a FRAGMENT names the key; the key check itself cannot, and names the fold and the type it got instead, because interpolating a non-string is a coercion error rather than a refusal — not a value, not held by `tryEval`, and it fires while the message explaining a DIFFERENT refusal is being assembled. The signature belongs to the VOCABULARY, so a member that quietly accepted what the others refuse would make the one contract a caller is given untrue at whichever member they picked. The message names the fold, because a message naming only the vocabulary tells a caller with five folds in a spec nothing about which call to fix.

**`same` refuses its fragments before it compares them, and the guard is a precondition rather than a nicety.** Nix's `==` is not an equivalence over function-bearing values — not even reflexive — so over them the fold would answer "did these arrive as one value slot" instead of "do these agree". A PATH compares perfectly well and cannot be REPORTED: `toJSON` on an absent path aborts uncatchably, and on a present one copies the caller's path into the store. So a function and a path are each refused where they sit, by a scan that descends into attribute sets and lists and stops at a derivation carrying a STRING `outPath` — the three-term skip predicate, deliberately not nixpkgs' `isDerivation`, which tests the marker alone. ★ The path arm is refused even when the fragments AGREE and no message would ever have been built, because a fold whose safety depends on its inputs agreeing has no precondition at all.

**Aggregation's precondition is the CALLER's, and nothing in this file enforces it.** THEORY: Apt, Blair & Walker (1988) — a stratified program's standard model is built stratum by stratum, `M_i = T_{P_i}↑ω(M_{i-1})` (printed p. 108), each stratum reaching its fixed point before the next begins, which is what aggregation classically demands of stratification. These folds are total functions of the list handed to them; no fold can tell a closed fact set from a prefix, and one applied to a prefix returns a confident answer about the prefix. Fragments arrive in pinned order and are never reordered or silently deduplicated, and every fold must handle a singleton, because a group of one is still a group and skipping the fold for it would make an aggregate's SHAPE depend on how many claimants there happened to be.

**Refusals.** `same`: an empty fragment list; a fragment carrying a function or a path, named with its position and its ground; fragments that disagree. `one`: a contributor count other than one. `list`: its key and nothing else. `mergeAttrs`: a fragment that is not an attribute set, named with its position; a sub-key collision. `byKey`: the same non-attrs refusal, and a fragment key the spec does not declare.

**The stratification driver** — `lib/stratify.nix`. A schedule of strata walked once each, taking the instance's own stratum assignment as a parameter. It has ONE instance: staged minting applies it (`lib/mint.nix`). The demand cascade does not — it runs its own bounded loop over its own subject, per the separation the minting entry already states above. The driver knows nothing about what an item is: demands, kinds, minting and nodes occur nowhere in its CODE, only in its commentary, and it imports nothing but the prelude's list primitives and the round-loop forcing it is HANDED.

| Export | Signature |
|---|---|
| `stratify` | `{ schedule, stratumOf, within, seed, advance, describe } -> { settled; unrun; strata; }` |

An instance supplies a run order (`schedule`), a way to place an item in it (`stratumOf`), an order inside one stratum (`within`), a starting set (`seed`), and one function to run a stratum (`advance { stratum, items } -> { emitted; settled; }`). It gets back every stratum's settled output in global schedule order — stratum-major, `within` inside, as the composition of the two rather than a re-sort — the items whose stratum the schedule never named, and how many strata ran.

**`describe` reaches this file and STOPS.** It is handed to no `advance`, appears in no result field, and no line applies it: it declares that an instance placing items in strata owes a way to NAME one, and the live consumer of that obligation is the cascade's `emittedBy`, which writes the site into the instance's own refusals. Totality is the instance's obligation and is checked nowhere here.

**The driver throws NOWHERE, and `unrun` is the whole of what that costs.** An item whose stratum the schedule does not name is returned, not refused. Emission into an already-run stratum is not detected because in the instances this serves it is inexpressible — a well-founded measure that strictly decreases across an emission edge leaves no such emission to write. Any refusal an instance needs is the instance's own and rides on top. ★ ONE refusal IS reachable and it is the EVALUATOR's, outside what "throws nowhere" claims: the argument record is a strict pattern, so a seventh field (or a missing one) is refused at application, naming the function and the field — NAMED and UNCATCHABLE, so no cell can observe it.

**Two preconditions the driver states and does not check.** `schedule`'s members must be DISTINCT: a stratum appearing twice is walked twice and its items settled again, since the loop asks membership questions and never asks whether it has been here before. Both derived instances exclude it by construction rather than by check — the cascade's schedule is consecutive integers from a depth measure, and the minting instance's is the declared passes deduplicated before ordering. A caller whose schedule is neither owes the distinctness itself. And the per-round forcing reaches the accumulator's FIELDS and stops: a list field is forced to its spine, not its elements, so a refusal written as `settled = throw …` ends the run at that round while one written as `settled = [ (throw …) ]` survives it and may never fire.

**Termination is Noetherian induction on the instance's own measure**, and nothing here ceilings it. The loop runs once per element of `schedule`; `strata` is reported and compared against nothing. THEORY — what stratification buys is COMPLETENESS: Apt, Blair & Walker (1988), `M₁ = T_{P₁}↑ω(∅)`, `M_i = T_{P_i}↑ω(M_{i-1})`, `M_P = M_n` (printed p. 108), each stratum reaching its fixed point before the next begins. ★ What is deliberately NOT here is a VISIBILITY RULE. Their strictly-lower indexing (Definition 3, printed p. 96) governs a symbol occurring NEGATIVELY; one occurring positively has its definition within `⋃_{j ≤ i} P_j`, the same stratum included. A driver enforcing the sufficient condition would be stricter than the theorem and would refuse programs it admits. An instance that acquires a NEGATED read acquires their clause 2 with it, and that is a change to this file rather than something it absorbs silently.

**The cold fold** — `lib/fold-equations.nix`. The evaluator's CALLER: it holds no fixpoint of its own and adds the sealing around one.

| Export | Signature |
|---|---|
| `foldEquations` | `{ roots, parseParent, schedule, declaredEdges ? (_: [ ]), settings ? { } } -> ResolveCtx` |

`ResolveCtx` is exactly ten fields — `accessor`, `attributes`, `declaredEdges`, `equations`, `eval`, `parseParent`, `roots`, `schedule`, `settings`, `trace` — and `ci/tests/fold-equations.nix` pins them as an exact set rather than by presence.

**The schedule is a parameter and the equations are read off it** (`equations = schedule.equations`). There is no `equations` formal, so a caller cannot pair a schedule with the equations it was not built from: the seal cannot carry a schedule nobody folded. The schedule is `seq`-forced at the entry, so a caller handing one whose gate refuses is refused where they made the call and not lazily on a first attribute read — binding the equations off it does NOT subsume that forcing, because the binding is consumed lazily through `attributes`.

**What it does NOT hold.** No plane call: the memo context the fold used to build stays with a caller holding both libraries, since building it here would install the incremental plane inside the evaluator. No strata order: the field has no reader, so it is read from nowhere and sealed nowhere, and the order stays with the scheduler that owns its default. `accessor` here is the topology-oracle record `{ nodes; edges; parent; nodeData; }` that gen-graph and the plane consume — a DIFFERENT shape from the accessorRecord `eval` returns, which the ctx carries under `eval`.

## Entry points by task

| Task | Reach for |
|---|---|
| Build a parent/import graph from parts | `overlay` / `overlays` / `edge` / `star` / `tree` |
| Turn graphs into root node descriptors | `buildNodes { parentGraph; importGraph; edgeGraphs; decls; types; }` |
| Evaluate attributes | `eval { roots; attributes; parseParent; }` then `result.get id attrName` |
| Diagnose an "infinite recursion" | `evalDebug` (named cycle trace; no `allNodes`) |
| Re-evaluate incrementally against a prior evaluation | `evalWarm { …; prior; decision = mkDecision { isClean; reusable; }; }` |
| Expose a consumer's declared dependency edges | `recordedDeps { declaredEdges }` |
| Fold a validated schedule's equations into one sealed context | `foldEquations { roots; parseParent; schedule; declaredEdges?; }` — the schedule comes from its own library; this entry forces it and never builds one |
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
| Register a kind, and a set of them | `mkKind { name; below ? [ ]; resolve; dedupKey ? null; fold ? null; }`, then `mkKinds` over the collection — the depth measure and the acyclicity verdict come out of that one call |
| Build a claim | `mkClaim { kind; subject; ...payload }` — `kind` takes a kind record or its name; `subject` needs a string `id_hash` |
| Resolve a claim multiset into resources and wiring | `resolveClaims { kinds; claims; ctx; }` — read `resources`, `wiring` and `trace` |
| Read ONE subject's wiring, in the run's global schedule order | `resolution.wiring.<id>.entries`, each entry `{ kind; claim; wiring; }`. There is no accessor: the run publishes the list, so this is a field read. **Test the key first** — see the totality trap below |
| Splice one subject's wiring into a single record | fold the entries per top-level key with a `key: [v]: v` combine drawn from `folds` — the same vocabulary a kind's resource fold is written against. `ci/tests/_fixtures/consumer.nix` carries the worked form |
| Walk a schedule of strata over items you place yourself | `stratify { schedule; stratumOf; within; seed; advance; describe; }` — read `settled`, `unrun` and `strata`; the argument record is CLOSED at those six |

## Measured traps

Each row verified in this run against `s = import ./. { }`. Shared fixtures: `roots = s.buildNodes { parentGraph = overlays [ (edge "a" "root") (edge "b" "root") (edge "c" "a") ]; importGraph = edge "b" "a"; edgeGraphs.uses = edge "c" "b"; decls = { root = { x = "R"; }; a = { }; b = { x = "B"; }; c = { }; }; types = {…}; }`. `R` = `eval` over those roots declaring both `children` and `imports`; `Rbare` = `eval` over the same roots declaring *neither*; `ok e = (builtins.tryEval e).success`.

| Trap | Evidence |
|---|---|
| `children` / `derived-children` are reserved attribute *names* the evaluator special-cases, but nothing supplies them — a consumer that omits `children` gets a throw from every structural query | `evalAttr` in `lib/eval.nix`; `ok (s.children Rbare "root")` ⇒ `false`, error text `gen-scope: unknown attribute 'children' on node 'root'`. Positive control `s.children R "root"` ⇒ `[ "a" "b" ]` |
| ★ `P` and `I` are reserved *labels* in `edgeGraphs`, and the entry refuses either BY NAME. The caller's labels merge last, so offering one used to replace the argument passed in the same call, silently. The refusal is unconditional — it does not wait for the colliding argument to be non-empty, since a caller's graph PROMOTED to a relation the library privileges is the same defect from the other side | `allEdgeGraphs` in `lib/build-nodes.nix`. Fixture `parentGraph = edge "a" "root"`, `importGraph = edge "a" "lib1"`: `edgeGraphs = { P = edge "a" "HIJACKED"; }` ⇒ threw `` gen-scope.buildNodes: `edgeGraphs` carries reserved label(s) ["P"]: 'P' is the containment relation, whose edges arrive as the `parentGraph` argument… ``; the `I` arm ⇒ the same refusal naming `I` and `importGraph`; both offered at once ⇒ one refusal naming both, in the LIBRARY's order and not the caller's. Positive control, the same fixture under the ordinary label `M` ⇒ `a.parent` = `"root"` and `a.decls.__edges.I` = `[ "lib1" ]`. Cells: `test-reserved-label-P-is-refused` / `test-reserved-label-I-is-refused` and the two `test-control-an-ordinary-label-…` (`ci/tests/build-nodes.nix`), `build-nodes-reserved-labels.*` (`ci/tests-error.nix`) |
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
| `evalWarm` never reuses ANY structural attribute — `children`, `derived-children`, every `edges-*` label, `imports`, `includes` — however clean the node and whatever the decision names | `evalAttr`'s first branch tests `structural attrName` (`lib/eval.nix`). Measured across the family: a decision reusing `edges-owns` from a prior answering `[ "POISON" ]` still answers the cold `[ "b" ]`, and the validator fires. Live control in the same matrix: a decision reusing the resolutional `label` IS served the prior's value and the validator stays silent. Tests: `plane-structural-matrix` (`ci/tests/plane.nix`), `test-children-always-recomputed` (`ci/tests/eval.nix`) |
| ★ The IMPORT RELATION is structural, and what protects it is the NAME. A graph whose imports changed between passes is recomputed under `imports` and served STALE under any other name | `structural` (`lib/structural.nix`) reserves the values of `lib/traversal-names.nix`, which `lib/resolve.nix` also traverses. One construction, two arms, same prior and same decision: under `imports` the warm read answers the current `[ "new" ]`; under `my-imports` — outside the reserved namespace — it answers the prior's `[ "old" ]`, complete and well-typed and wrong. The second arm is the live control: without it the first passes for reasons unrelated to the partition. Test: `test-the-import-relation-is-recomputed-and-the-stale-serve-is-live` (`ci/tests/eval.nix`) |
| `circular` defaults to `maxIter = 100` and **throws** rather than returning a partial result | `circular` in `lib/resolve.nix`; `f = _: _: prev: prev + 1` ⇒ threw. Positive control `f = _: _: prev: if prev < 3 then prev + 1 else prev` ⇒ `3`. Test: `test-diverge-throws` (`ci/tests/circular.nix`) |
| `inheritAll` keeps duplicates (ordered-list `++`); `inheritSet` is its dedup sibling. Both are nearest-first | `inheritAll` / `inheritSet` in `lib/resolve.nix`; chain `root` (tag `T`) → `a` (tag `T`) → `c` (tag `C`): `inheritAll` ⇒ `[ "C" "T" "T" ]`, `inheritSet` ⇒ `[ "C" "T" ]`. Test: `test-inheritSet-dedups-what-inheritAll-keeps` (`ci/tests/resolve.nix`) |
| `overlay` does not dedup vertices — dedup is deferred to `buildNodes` | `lib/graph.nix` header comment; `(s.overlay (s.vertex "a") (s.vertex "a")).vertices` ⇒ `[ "a" "a" ]`, while `attrNames (buildNodes { parentGraph = <that>; })` ⇒ `[ "a" ]` |
| `collectionAttr`'s `traverse` is a string-dispatched enum; an unknown value throws at *use*, not at construction | `collectionAttr` in `lib/resolve.nix`; `traverse = "parents"` ⇒ threw `gen-scope: collectionAttr: unknown traverse 'parents'`. Positive control `traverse = "ancestors"` ⇒ `[ "a" "root" ]` |
| `collect` / `collectByType` end at `self` — they take **no** `id` argument, unlike every other combinator | `collect` in `lib/resolve.nix`; on a one-node fixture (`roots = { n = …; }`), `s.collect { } (_self: id: [ id ]) <record>` ⇒ `[ "n" ]` — three arguments, not four |
| The source modules merge with **no** shadowing, so the name collisions with other concepts are real exports: `resolve` here is the Neron specificity function (unrelated to the sibling library gen-resolve, whose cold fold landed here as `foldEquations` for exactly that reason), and `vertices` is the constructor `[id] -> graph` while `g.vertices` is a field | `lib/default.nix` merges seventeen modules through `lib/merge-surface.nix`, which refuses a duplicate rather than resolving it by position; `nix eval --json .#lib --apply 'builtins.attrNames'` ⇒ 88 names. Renaming `foldEquations` to `resolve` in `lib/fold-equations.nix` ⇒ `error: gen-scope: 'resolve' is exported by both 'foldEquations' and 'resolve', and the library's assembly refuses a duplicate export rather than resolving it by position`, so the guard is armed against the real module set and not only against a synthetic one. `lib/mint.nix` contributes exactly 1 of the 88 |
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

- **Van Gelder (1993), *The alternating fixpoint of logic programs with negation*** — the construction: `S(J) = lfp T_{P/J}` antimonotone, `S²` monotone, `W⁺ = lfp(S²)` from ∅, `S(W⁺)` the true-or-undefined set. ★ ATTRIBUTION UNCHECKED: this project does not hold the paper. It holds Van Gelder, Ross & Schlipf (1991), which is a different paper and does not contain this construction — it cites it as separate work in its own bibliography. The construction is what the code computes and the suites pin; the attribution is what is open.

- **van Emden & Kowalski (1976), *The semantics of predicate logic as a programming language*** — `T_P` and its least fixpoint as the meaning of a definite program; both `leastModel` arms compute it over the reduct. ★ ATTRIBUTION UNCHECKED: this project does not hold the paper. The operator and its least fixpoint are standard and the code computes them; nothing here has been read against the source.

**Partial**

- **Gelfond & Lifschitz (1988), *The stable model semantics for logic programming*** — the reduct `P/J` is implemented and iterated. Stable-model EXISTENCE, the companion refusal criterion, is **NOT built**: no construction in this library decides it, and containment (well-founded ⊆ every stable model) is not a decision procedure. Stated so a reader does not infer an oracle from the semantics beside it.
- **SCC partition and condensation** — CONSUMED, not implemented: they come from gen-graph's published front door, and the engine reads the reported `depth` and nothing else. ★ This entry used to name Tarjan (1972) and Fleischer, Hendrickson & Pınar (2000). Both are struck rather than marked: this project holds neither paper, and a library that runs neither algorithm should not carry them among its foundations at all. What is true here — which door is called and which field is read — needs no primary.
- **van Antwerpen et al. (2018), *Scopes as types*** — custom edge labels via `edgeGraphs` / `followEdge`, structural subtyping (`subtypeOf`), coarse-grained visibility (boolean shadowing flags). README marks the Statix-style constraint patterns partial: custom labelled edges only, and a single `decls` relation per node.

**Informed by** (README's own label; no result claimed): Apt, Blair & Walker (1988) *Towards a theory of declarative knowledge*, at FIVE surfaces — for the engine, why the third verdict is needed at all, the stratified semantics admitting positive cycles and leaving a cycle through a negative edge without a meaning; for `mintStrata`, the standard model of a stratified program being built one stratum at a time with each closed before the next begins (printed p. 108), which is what a minting pass is, where the correspondence taken is the CLOSURE of earlier strata and not the per-stratum fixpoint iteration, and which is why a cycle among minted nodes is inexpressible rather than detected; for the **demand cascade**, completeness ALONE — that construction carries no negation anywhere, so the strictly-lower indexing of their Definition 3 (printed p. 96), which governs the NEGATIVE case, is deliberately not imposed on it; for the **fold vocabulary**, the same completeness as the CALLER's precondition, which no fold in that module enforces; and for the **stratification driver**, the stratum-by-stratum model as what its loop guarantees and the whole of what it guarantees. The five are the constructions that cite the paper beside themselves: `/run/current-system/sw/bin/grep -rl "Apt, Blair" --include="*.nix" lib/` ⇒ seven files, `program.nix` + `least-model.nix` + `well-founded.nix` (the engine's three), `mint.nix`, `cascade.nix`, `folds.nix` and `stratify.nix`; Hedin & Magnusson (2003) *JastAdd*, for the demand-driven evaluation pattern and the aspect-oriented attribute extension model — the code comment on `queryReverse` cites the same paper's inter-type declarations; Radul & Sussman (2009) *Art of the propagator*, for monotonic convergence in `circular`; Van Wyk et al. (2010) *Silver*, for forwarding and fold operators behind `collectionAttr` / `inheritSet`; Mokhov et al. (2018) *Build systems à la carte*, for demand-driven evaluation as a suspending scheduler (§4.1) — README states gen-scope builds no scheduler, Nix is the scheduler; Acar, Blelloch & Harper (2002) *Adaptive functional programming*, for `evalWarm`'s clean-result reuse — that paper's **change propagation** — and `recordedDeps` as the declared read-edge projection of the read structure it propagates over. The year is the edition this project HOLDS: `dynamic dependence graph` and `self-adjusting` are the later editions' vocabulary and appear 0 times in the held PDF, against `change propagation` 35 and `time stamp` 42 in the same `pdftotext` run.

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
["acceptanceSignal","ambiguous","ancestors","armFor","armNames","buildNodes","childBearing","children","childrenIds","circuit","circular","clique","coldDecision","collect","collectByLabel","collectByType","collectImports","collectionAttr","connect","decisionFindings","descendants","edge","edgePrefix","edges","empty","eval","evalDebug","evalWarm","facadeNames","foldContributions","foldEquations","folds","followEdge","forceFields","forest","gmap","hasEdge","hasVertex","induce","inherit'","inheritAll","inheritSet","isAncestor","isDescendant","leastModel","leastModelRounds","leastModelUnary","mintStrata","mkClaim","mkDecision","mkFacade","mkKind","mkKinds","mkProgram","mkRule","nodesByType","overlay","overlays","paramAttr","parent","path","provenanceFor","query","queryAll","queryReverse","recordedDeps","reduct","removeEdge","removeVertex","resolutionalNames","resolve","resolveClaims","shadow","siblings","signalNames","solve","star","stratify","structural","subtypeOf","transpose","tree","verdictNames","verifiedDepth","vertex","vertices","visibleFrom","wellFoundedModel"]
```

**Checks.** Test-runner invocation (from the repo root; CI runs the same command with `working-directory: ci`, `.github/workflows/ci.yml`):

```sh
nix flake check ./ci
```
