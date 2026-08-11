# gen-scope — agent capability sheet

## Scope

Demand-driven higher-order attribute-grammar evaluator over algebraic scope graphs: you supply root node descriptors (`{ id, type, parent, decls }`) and attribute definitions (`self: id: value`), and `eval` returns an accessor record (`node` / `get` / four materializers) whose attributes compute lazily and memoize on an `_eval` cache co-located on each node.

## Not this library's job

Quoted text is the owner's own `flake.nix` `description` field, verbatim. Grep counts below are `grep -rEl '<pattern>' --include='*.nix' <dir> | wc -l` — files with a match — run from `/home/sini/Documents/repos/sini`. In the patterns, `\|` is markdown table escaping for the ERE alternation `|`. Rows carrying no grep cite attribution from the sibling description alone: the predicates tried for `gen-dispatch` matched nothing in its own `lib/`, so no absence is claimed against it.

| Responsibility | Owner |
|---|---|
| Static read-dependency analysis (`readsAttrs`), attribute stratification, the scheduled convergence fold | `gen-resolve` — "gen-resolve — demand-driven higher-order RAG evaluator over algebraic scope graphs (Knuth 1968 attribute schedule + Vogt 1989 HOAG)". gen-scope ships `circular` as the bare fixed-point loop primitive; `readsAttrs\|stratum\|schedule` over `gen-scope/lib` ⇒ 0 files, same predicate over `gen-resolve/lib` ⇒ 6 |
| Graph traversal, SCC/condensation, phase ordering over accessor-graphs | `gen-graph` — "gen-graph: accessor-based graph query combinators". `lib/graph.nix` here is Mokhov *construction* only; `condensation\|stronglyConnected\|topoSort\|topological\|phaseOrder` over `gen-scope/lib` ⇒ 0, control `gen-graph/lib` ⇒ 2 |
| Predicate / selector matching over graph positions | `gen-select` — "gen-select: selector algebra for attributed graph positions". `__sel\|selectorEq` over `gen-scope/lib` ⇒ 0, control `gen-select/lib` ⇒ 3 |
| Minting identity (`id_hash`), kinds, instances, registries | `gen-schema` — "gen-schema: typed record registry with extension points for the pure-gen module system". `id_hash\|hashString\|builtins\.hash` over `gen-scope/lib` ⇒ 0, control `gen-schema/lib` ⇒ 5 |
| Module merge, `evalModules`, option priorities | `gen-merge` — "gen-merge — pure-Nix byte-mode module MERGE engine (evalModuleTree) for the pure-gen module system". Enforced, not merely absent: `test-library-source-is-nixpkgs-lib-free` (`ci/tests/purity.nix`) fails CI on `evalModules` / `mkOption` / `lib.` / `nixpkgs` appearing in `lib/**.nix`, `flake.nix` or `default.nix` |
| Type checking / `verify` | `gen-types` — "gen-types: pure, nixpkgs-lib-free structural type checker for the gen ecosystem" |
| General utilities — gen-scope's *only* dependency; `flake.nix` declares `gen-prelude` alone | `gen-prelude` — "gen-prelude: vendored, nixpkgs-lib-free pure utilities for the gen ecosystem" |
| Graph products, coordinate tuples, slices, fibers | `gen-product` — "gen-product — graph products as first-class operations over accessor-graphs (Cartesian / tensor / strong / lexicographic; cells, slices, fibers, projections, quotients, restriction, containment chains), lazy in and out". `coordsOf\|cartesian\|tensor` over `gen-scope/lib` ⇒ 0, control `gen-product/lib` ⇒ 4 |
| Computing the dirty set / change propagation for an incremental rebuild | `gen-rebuild` — "gen-rebuild: pure-Nix incremental rebuilder core (Mokhov rebuilder dimension)". gen-scope supplies only the consumer-driven hooks: `evalWarm`'s `decision` (`isClean` + `reusable`) over a `prior` accessor, the `facade` the plane reads through, and `recordedDeps` |
| Choosing a winner among matched rules (guard→effect step, ordering, conflict resolution) | `gen-dispatch` — "gen-dispatch: relational rule dispatch over ordered groups (the dispatch STEP)" |
| Layered settings resolution with precedence and structured provenance | `gen-settings` — "gen-settings — stratified settings resolution as a pure layered fold, with refs-as-data, structured provenance, and the graduated injection construct". `stratif\|precedence\|provenance` over `gen-scope/lib` ⇒ 0, control `gen-settings/lib` ⇒ 4 |
| Typed resource demands resolving into resources + wiring — a different sense of "demand" from gen-scope's demand-*driven* evaluation | `gen-demand` — "gen-demand — typed demand cascade (kinds resolve demands into resources + wiring + sub-demands; a stratified, terminating fold resolves the multiset with full provenance)" |
| Aspect traits / classification | `gen-aspects` — "gen-aspects: aspect-oriented composition types (pure-gen, re-hosted on gen-merge)" |
| Channels / dataflow riding over scopes | `gen-pipe` — "gen-pipe — scoped channels + dataflow algebra (map/filter/fold/scan/route/join/tee) with B5 determinism, provenance, dedup, and class-aware contributions"; `gen/lib/mkGenLibs.nix` records its deps as `prelude+select+scope` |
| The nixpkgs boundary: value injection, building systems | `gen-flake` — "gen-flake — the pure composition boundary of the pure-gen module ecosystem" |

## Exports

Entry: `inputs.gen-scope.lib` (flake). Root `default.nix` is a function `{ prelude ? <derived from flake.lock>, ... }` — callable as `import ./gen-scope { }`, which content-addresses gen-prelude out of the pinned lock and needs no `<nixpkgs>`.

`lib/default.nix` is one flat merge — `graph // buildNodes // queries // resolve // structural // interface // eval`. All 63 exports sit at top level; there is no nested namespace and no key is shadowed (see traps).

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
| The five source modules merge flat with **no** shadowing, so the two name collisions with other concepts are real exports: `resolve` here is the Neron specificity function (unrelated to the sibling library gen-resolve), and `vertices` is the constructor `[id] -> graph` while `g.vertices` is a field | `lib/default.nix` is `graph // buildNodes // queries // resolve // eval`; per-module export counts `{ graph = 21; build-nodes = 1; queries = 9; resolve = 19; eval = 4; }` sum to 54, equal to the merged `attrNames` count — so no key is overwritten |

## Theory

Claimed in `README.md` under "Theoretical Foundations", which labels each source **Implements**, **Partial**, or **Informed by**, and restated in code comments.

**Implements**

- **Vogt et al. (1989), *Higher-order attribute grammars*** — dynamic node synthesis via `children` / `derived-children` as non-terminal attributes (§2.4); `derived-children` extends this with second-stage stratification.
- **Hedin (2000), *Reference attributed grammars*** — import edges as reference attributes; cross-node attribute access through computed scope references.
- **Neron et al. (2015), *A theory of name resolution*** — scope graph construction, the resolution calculus (`query` / `queryAll`), D < I < P specificity ordering (Fig. 2), path well-formedness (§2.4), seen-imports cycle prevention (rule X), shadowing (§5 Def. 1). The partial-function constraint on P (§2.2) is enforced by `buildNodes`.
- **Mokhov (2017), *Algebraic graphs with class*** — all four construction primitives (`empty` / `vertex` / `overlay` / `connect`) and the derived constructors (`star` / `path` / `clique` / `tree` / …) from §2.1–§5.1; `overlay`'s idempotence is what licenses deferring dedup to `buildNodes`.
- **Sloane et al. (2010), *Kiama: AG embedding*** — the `CachedAttribute` pattern realized as the co-located `_eval` cache; `paramAttr` (§3); `circular` fixed-point attributes (§2.2); collection attributes (§7).

**Partial**

- **van Antwerpen et al. (2018), *Scopes as types*** — custom edge labels via `edgeGraphs` / `followEdge`, structural subtyping (`subtypeOf`), coarse-grained visibility (boolean shadowing flags). README marks the Statix-style constraint patterns partial: custom labelled edges only, and a single `decls` relation per node.

**Informed by** (README's own label; no result claimed): Hedin & Magnusson (2003) *JastAdd*, for the demand-driven evaluation pattern and the aspect-oriented attribute extension model — the code comment on `queryReverse` cites the same paper's inter-type declarations; Radul & Sussman (2009) *Art of the propagator*, for monotonic convergence in `circular`; Van Wyk et al. (2010) *Silver*, for forwarding and fold operators behind `collectionAttr` / `inheritSet`; Mokhov et al. (2018) *Build systems à la carte*, for demand-driven evaluation as a suspending scheduler (§4.1) — README states gen-scope builds no scheduler, Nix is the scheduler; Acar et al. (2006) *Adaptive functional programming*, for `evalWarm`'s clean-result reuse and `recordedDeps` as the declared read-edge projection of a dynamic dependence graph.

**Checked invariant**: nixpkgs-lib-freedom (dependency on gen-prelude alone, no `lib.`, no `evalModules` / `mkOption`, no `nixpkgs` input) is enforced by `test-library-source-is-nixpkgs-lib-free` (`ci/tests/purity.nix`) over `lib/**.nix` + root `flake.nix` + `default.nix`, on comment-stripped source.

## Drift check

```sh
nix eval --json .#lib --apply 'builtins.attrNames'
```

Current output (verbatim):

```json
["ambiguous","ancestors","buildNodes","children","childrenIds","circuit","circular","clique","collect","collectByLabel","collectByType","collectImports","collectionAttr","connect","descendants","edge","edges","empty","eval","evalDebug","evalWarm","followEdge","forest","gmap","hasEdge","hasVertex","induce","inherit'","inheritAll","inheritSet","isAncestor","isDescendant","nodesByType","overlay","overlays","paramAttr","parent","path","query","queryAll","queryReverse","recordedDeps","removeEdge","removeVertex","resolve","shadow","siblings","star","subtypeOf","transpose","tree","vertex","vertices","visibleFrom"]
```

**Checks.** Test-runner invocation (from the repo root; CI runs the same command with `working-directory: ci`, `.github/workflows/ci.yml`):

```sh
nix flake check ./ci
```
