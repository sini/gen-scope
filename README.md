# gen-scope

[![CI](https://github.com/sini/gen-scope/actions/workflows/ci.yml/badge.svg)](https://github.com/sini/gen-scope/actions/workflows/ci.yml) [![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](https://opensource.org/licenses/MIT) [![Sponsor](https://img.shields.io/badge/Sponsor-%E2%9D%A4-pink?logo=github)](https://github.com/sponsors/sini)

Demand-driven Higher-Order Attribute Grammar evaluator over algebraic scope graphs, implemented as a pure Nix library.

gen-scope is a **hybrid HOAG/RAG** evaluator: Higher-Order Attribute Grammars (Vogt et al., 1989) for dynamic node synthesis, Reference Attribute Grammars (Hedin, 2000) for cross-node references via import edges. It leverages Nix's native lazy evaluation for attribute computation, memoization, and cycle detection — we do not build an AG evaluator, Nix **is** the evaluator.

gen-scope is generic. It has no knowledge of NixOS, aspects, policies, or system configuration. It provides evaluation machinery; consumers define what to compute.

## Table of Contents

- [Overview](#overview)
- [Gen Ecosystem](#gen-ecosystem)
- [Usage](#usage)
- [Core Insight](#core-insight)
- [Terminology](#terminology)
- [Example](#example)
- [HOAG: Dynamic Tree Expansion](#hoag-dynamic-tree-expansion)
- [API Reference](#api-reference)
  - [eval](#eval)
  - [evalDebug](#evaldebug)
  - [evalWarm](#evalwarm)
  - [recordedDeps](#recordeddeps)
  - [buildNodes](#buildnodes)
  - [Algebraic Graph Construction](#algebraic-graph-construction)
  - [Attribute Combinators](#attribute-combinators)
  - [Structural Queries](#structural-queries)
- [Performance](#performance)
- [Testing](#testing)
- [Theoretical Foundations](#theoretical-foundations)

## Overview

gen-scope evaluates **attributes** over a tree of **nodes**. You supply two things: a set of root nodes (minimal descriptors `{ id, type, parent, decls }`) and a set of attribute definitions — each a function `self: id: value` that computes one attribute of one node, free to read other attributes through the `self` accessor. `eval` returns an **accessor record** whose fields destructure the evaluated tree:

| Accessor | Reads | Returns |
|----------|-------|---------|
| `result.node id` | structural data | the node descriptor `{ id, type, parent, decls }` |
| `result.get id attrName` | a computed attribute | the demand-driven, memoized attribute value |
| `result.allNodes` / `allNodesWhere` / `subtreeOf` / `nodesOfType` | the whole tree | flat materializations (Tier 2) |

Evaluation is **demand-driven**: an attribute computes only when `get` reads it, and each result is memoized on a co-located `_eval` cache carried by its own node (see [Core Insight](#core-insight)). Two access tiers matter for cost — **Tier 1** navigation (`node`, `get`) is O(1)/O(depth); **Tier 2** materialization (`allNodes`) forces the full tree at O(n).

The tree is not fixed. The `children` and `derived-children` attributes **synthesize new nodes on demand** (the HOAG half — [HOAG: Dynamic Tree Expansion](#hoag-dynamic-tree-expansion)), and cross-node references travel along **import edges** resolved with scope-graph queries (`query`/`queryAll`/`queryReverse`, the RAG half). The convergence of mutually-recursive attributes is driven by `circular` (fixed-point iteration, Sloane 2010 §2.2) — the loop primitive consumers such as [gen-resolve](https://github.com/sini/gen-resolve) build their fold on top of.

## Gen Ecosystem

| Library | Role |
|---------|------|
| [gen-prelude](https://github.com/sini/gen-prelude) | Pure nixpkgs-lib-free utility base (builtins re-exports + vendored lib utils) |
| [gen-algebra](https://github.com/sini/gen-algebra) | Pure primitives (record, search monad, either, intensional identity) |
| [gen-types](https://github.com/sini/gen-types) | Clean-room MIT structural type checker (leaf/poly checkers; `verify: v → null\|err`) |
| [gen-merge](https://github.com/sini/gen-merge) | Byte-mode module merge engine (`evalModuleTree`, byte-identical to nixpkgs `lib.evalModules` over the priority subset) |
| [gen-schema](https://github.com/sini/gen-schema) | Typed registries (kinds, instances, collections, refs); re-hosted on gen-merge |
| [gen-aspects](https://github.com/sini/gen-aspects) | Aspect type system (traits, classification, dispatch); re-hosted on gen-merge |
| [gen-scope](https://github.com/sini/gen-scope) | **This lib** — HOAG scope-graph evaluator (demand-driven, \_eval memoization, circular attributes) |
| [gen-graph](https://github.com/sini/gen-graph) | Accessor-based graph query combinators (traversal, condensation, phaseOrder) |
| [gen-select](https://github.com/sini/gen-select) | Selector algebra (pattern matching over graph positions) |
| [gen-bind](https://github.com/sini/gen-bind) | Module binding (inject external args into NixOS modules) |
| [gen-dispatch](https://github.com/sini/gen-dispatch) | Relational rule dispatch STEP (stratified phases, conflict resolution) |
| [gen-resolve](https://github.com/sini/gen-resolve) | Demand-driven RAG evaluator over scope graphs (attribute schedule + convergence loop) |
| [gen-rebuild](https://github.com/sini/gen-rebuild) | Pure-Nix incremental rebuilder (change propagation, AFFECTED set) |
| [gen-vars](https://github.com/sini/gen-vars) | Pure-Nix vars/secrets (den-agnostic) |
| [gen-flake](https://github.com/sini/gen-flake) | The nixpkgs boundary — compose purely, inject resolved values, build NixOS systems (value-injection) |

## Usage

gen-scope is **Class B**: nixpkgs-lib-free, depending only on [gen-prelude](https://github.com/sini/gen-prelude) (pure, zero-input). The HOAG evaluator is pure list/attr combinators + builtins — no module system, no `nixpkgs.lib`. The flake exposes a single `.lib` value output.

```nix
# flake.nix
{
  inputs.gen-scope.url = "github:sini/gen-scope";
  outputs = { gen-scope, nixpkgs, ... }:
    let engine = gen-scope.lib;
    in { /* ... */ };
}

# Or without flakes (prelude auto-derived from the pinned flake.lock):
let engine = import ./gen-scope { };
in { /* ... */ }
```

## Core Insight

Nix attrset VALUES are lazy but KEYS are eager. Function application is never memoized. The only way to get O(1) attribute access is an attrset entry.

**The solution:** Co-locate the memoization cache (`_eval`) ON each node. When a parent's `children` attribute materializes child nodes, each child is wrapped with `_eval` — a lazy attrset of that child's attribute computations. The cache is distributed across the tree, not centralized.

## Terminology

| Term | Definition |
|------|-----------|
| Nodes | Minimal descriptors: `{ id, type, parent, decls }` |
| Roots | Entry-point nodes (from `buildNodes` or hand-written) |
| Children | Synthesized nodes produced by the `children` attribute |
| Derived Children | Synthesized nodes from `derived-children` (can read sibling attrs) |
| Attributes | Computed values on nodes — demand-driven, memoized via `_eval` |
| Combinators | Attribute constructors: `inherit'`, `inheritAll`, `inheritSet`, `circular`, `paramAttr`, `collectionAttr`, `query` |
| Tier 1 | Navigation: `self.node id`, `self.get id attrName` — O(1) or O(depth) |
| Tier 2 | Materialization: `self.allNodes` — O(n), forces full tree |

## Example

A hierarchical configuration: environments contain hosts, hosts inherit environment config.

```nix
let
  engine = import ./gen-scope { };   # nixpkgs-lib-free; `lib` below is the consumer's own

  roots = engine.buildNodes {
    parentGraph = engine.overlay
      (engine.star "env:prod" [ "host:web" "host:db" ])
      (engine.star "env:dev" [ "host:dev" ]);
    decls = {
      "env:prod" = { region = "us-east"; isHighSec = true; };
      "env:dev"  = { region = "eu-west"; isHighSec = false; };
      "host:web" = { role = "frontend"; };
      "host:db"  = { role = "database"; };
      "host:dev" = { role = "all"; };
    };
  };

  result = engine.eval {
    inherit roots;
    attributes = {
      # Tree stays flat — no children synthesis in this example
      children = _self: _id: {};

      # Inherited: walks parent chain
      region = engine.inherit' { resolve = n: n.decls.region or null; };

      # Synthesized: computed from node data
      greeting = self: id:
        "hello ${id} in ${self.get id "region"}";
    };
  };
in {
  webRegion = result.get "host:web" "region";     # "us-east"
  webGreeting = result.get "host:web" "greeting"; # "hello host:web in us-east"
  devRegion = result.get "host:dev" "region";     # "eu-west"
}
```

## HOAG: Dynamic Tree Expansion

The `children` attribute synthesizes new nodes on demand. Attribute-dependent — can read other attributes to decide what to create:

```nix
let
  roots = {
    "env:prod" = {
      id = "env:prod"; type = "env"; parent = null;
      decls = { hosts = [ "web-1" "db-1" ]; isHighSec = true; };
    };
  };

  result = engine.eval {
    inherit roots;
    attributes = {
      is-high-sec = self: id: (self.node id).decls.isHighSec or false;

      # Children depend on is-high-sec attribute
      children = self: id:
        let n = self.node id; in
        if n.type == "env" then
          lib.listToAttrs (map (h: {
            name = "host:${h}@${id}";
            value = {
              id = "host:${h}@${id}"; type = "host"; parent = id;
              decls = {
                users = [ "root" ] ++ lib.optional (self.get id "is-high-sec") "auditor";
              };
            };
          }) (n.decls.hosts or []))
        else if n.type == "host" then
          lib.listToAttrs (map (u: {
            name = "user:${u}@${id}";
            value = { id = "user:${u}@${id}"; type = "user"; parent = id; decls = {}; };
          }) (n.decls.users or []))
        else {};

      # Inherited security propagates through synthesized nodes
      inherited-sec = self: id:
        let n = self.node id; in
        if n.decls ? isHighSec then n.decls.isHighSec
        else if n.parent != null then self.get n.parent "inherited-sec"
        else false;
    };
    parseParent = id:
      let parts = lib.splitString "@" id; in
      if builtins.length parts > 1 then lib.concatStringsSep "@" (lib.drop 1 parts)
      else null;
  };
in {
  # Auditor user only on prod (attribute-dependent synthesis)
  prodUsers = builtins.attrNames (result.get "host:web-1@env:prod" "children");
  # → [ "user:auditor@host:web-1@env:prod" "user:root@host:web-1@env:prod" ]

  auditorSec = result.get "user:auditor@host:web-1@env:prod" "inherited-sec";
  # → true
}
```

### `derived-children` — Second-Stage Synthesis

`derived-children` can read attributes of nodes produced by `children` (Vogt 1989 §2.4 NTA stratification):

```nix
attributes = {
  children = self: id: { ... };
  derived-children = self: id:
    let alice = self.get "user:alice@${id}" "resolved-aspects"; in
    if hasAspect "sudo" alice
    then { "user:alice-admin@${id}" = { ... }; }
    else {};
};
```

## API Reference

### `eval`

```nix
eval {
  roots;               # { id = { id, type, parent, decls }; }
  attributes;          # { attrName = self: id: value; }
  parseParent ? null;  # id → parentId | null
}
```

Returns `{ node, get, allNodes, allNodeIds, allNodesWhere, subtreeOf, nodesOfType }`:

| Function | Cost | Description |
|----------|------|-------------|
| `result.node id` | O(1) root, O(depth) synth | Resolve node structural data |
| `result.get id attrName` | O(1) amortized | Demand-driven attribute access (memoized) |
| `result.allNodes` | O(n) | Tier 2: flat map of all reachable nodes |
| `result.allNodeIds` | O(n) | Tier 2: the same node set as an **ordered** id list — see [Materialization order](#materialization-order) |
| `result.allNodesWhere pred` | O(n) | Tier 2: selective materialization filtered by predicate on node data |
| `result.subtreeOf rootId` | O(subtree) | Tier 2: materialize only the subtree rooted at a given node |
| `result.nodesOfType type` | O(n) | Tier 2: all nodes matching a given type string |

**Special attributes:** `children` and `derived-children` are auto-wrapped — their results are node attrsets where each child receives a co-located `_eval` cache.

#### Materialization order

`allNodes` is an attrset, and an attrset is a set: `builtins.attrNames` on it answers in bytewise codepoint order, and the order the walk found the nodes in is not recoverable from that value. `allNodeIds` is the same node set with that order kept:

- **root order, then pre-order depth-first** through `children` / `derived-children`, so a subtree is contiguous and a parent precedes its descendants;
- **root and sibling tie-break — bytewise codepoint order,** which is `attrNames`' order and not dictionary order: `attrNames { z; A; a; _b; "1"; }` is `[ "1" "A" "_b" "a" "z" ]`, uppercase before underscore before lowercase. This is **not** because an attrset "carries no order". The algebraic graph layer carries a declaration-ordered vertex *list* (`lib/graph.nix` — `overlay` and `connect` concatenate), and `lib/build-nodes.nix` collapses it through `listToAttrs` and back out through `attrNames`, the same construction `allNodeIds` exists to stop doing, so `eval` is handed `roots` already set-shaped. The codepoint tie-break is that collapse's residue; recovering the declared order is a change to the constructor, not to this walk. On a flat graph — every node a root with no children, which is what `buildNodes` alone produces — the walk order therefore *is* the codepoint order;
- **`derived-children` interleave:** a derived node does **not** follow its `children` siblings. `_walkFrom` descends `children // derived` as one attrset, so a derived id sorts *into* the sibling run under the same codepoint rule, and nothing in the list marks it as derived. Measured on a root with children `b`, `z` and derived child `aa`: `allNodeIds` is `[ "r" "aa" "b" "z" ]`;
- **repeats dropped first-occurrence-wins**, the same rule `listToAttrs` applies to `allNodes`, so `sort lessThan result.allNodeIds == attrNames result.allNodes`. A node reached both as a root and as another root's child is the ordinary case, so the walk really does repeat.

This is the survey order an attribute-grammar collection or reverse reference attribute is defined over (Hedin & Magnusson 2003; Sloane 2010 §7): contributions combine in a traversal order of the tree, not in a codepoint order of node names. `queryReverse` reads it for exactly that reason.

### `evalDebug`

Same interface as `eval`. Provides structured cycle traces instead of Nix's opaque "infinite recursion." Trade-off: defeats memoization. Use for diagnosing cycles only.

### `evalWarm`

```nix
evalWarm {
  roots;               # { id = { id, type, parent, decls }; }
  attributes;          # { attrName = self: id: value; }
  parseParent ? null;  # id → parentId | null
  priorResults;        # { id = { attrName = cachedValue; }; }
  isClean;             # id → bool
}
```

Warm-cache variant of `eval` for incremental re-evaluation. A leaf attribute of a **clean** node (`isClean id == true`) whose value is present in `priorResults` is served from the cache **without forcing its compute function**; everything else evaluates cold. `children`/`derived-children` are **never** served warm — tree structure is always recomputed, so a dirty descendant stays reachable through freshly-materialized parents. Returns the same shape as `eval`.

With `eval`'s defaults (`priorResults = {}`, `isClean = _: false`) the warm branch never fires, so `eval` and warm-off `evalWarm` are byte-identical — they share a single code path.

```nix
result = engine.evalWarm {
  inherit roots attributes;
  priorResults = { "host:web" = { region = "us-east"; }; };  # from a prior eval
  isClean = id: id != "host:db";                              # only db changed
};
result.get "host:web" "region"   # "us-east" — served warm, compute fn not forced
result.get "host:db"  "region"   # recomputed (db is dirty)
```

### `recordedDeps`

```nix
recordedDeps { declaredEdges } id   # → [id]
```

First-class projection of a consumer's **declared** read-edges: it simply applies `declaredEdges id`. Pure and memo-free — it never runs through `get`. The *dynamic* read-set (the attributes a node actually `self.get`s) is only recoverable via `evalDebug`'s fresh-`self`-per-`get`, which defeats memoization; there is no pure, memo-preserving way to capture it, so the declared edges are the inspectable contract. Useful for incremental consumers that need an explicit dependency edge set (e.g. driving a rebuild).

### `buildNodes`

```nix
buildNodes {
  parentGraph ? empty;   # Algebraic graph for P edges (child → parent)
  importGraph ? empty;   # Algebraic graph for I edges
  edgeGraphs ? {};       # Custom labeled edges: { label → graph }
  decls ? {};            # { nodeId → attrset }
  types ? {};            # { nodeId → string }
  strict ? true;         # true: deepSeq validates parent uniqueness upfront
}
```

Returns minimal root descriptors: `{ id = { id, type, parent, decls }; }`.

Edge data is stored in `decls.__edges`: `{ I = [...]; customLabel = [...]; }`. Consumers define attributes to interpret these edges:

```nix
attributes = {
  imports = self: id: (self.node id).decls.__edges.I or [];
  children = self: id: {};
};
```

### Algebraic Graph Construction

Four core primitives (Mokhov, 2017 §2.1):

| Function | Signature | Description |
|----------|-----------|-------------|
| `empty` | `graph` | Empty graph |
| `vertex` | `string → graph` | Single vertex |
| `overlay` | `graph → graph → graph` | Union (commutative, associative, idempotent) |
| `connect` | `graph → graph → graph` | Overlay + cross-product edges |

Derived constructors (Mokhov, 2017 §2.2, §5.1):

| Function | Description |
|----------|-------------|
| `overlays` | Fold overlay over list of graphs |
| `vertices` | List of isolated vertices |
| `edge` | Single edge from two vertex IDs |
| `edges` | List of `{ from, to }` records |
| `path` | Sequential chain of edges |
| `circuit` | Cycle connecting last to first |
| `star` | Center vertex with leaf edges (inverted: leaves point to center) |
| `clique` | Fully connected subgraph |
| `tree` | Recursive `{ root, children }` structure |
| `forest` | List of trees |

Graph transformations (Mokhov, 2017 §5.2-5.5):

| Function | Description |
|----------|-------------|
| `gmap` | Map function over vertices |
| `induce` | Subgraph matching predicate |
| `transpose` | Flip all edge directions |
| `hasVertex` | Vertex membership test |
| `hasEdge` | Edge membership test |
| `removeVertex` | Remove vertex and incident edges |
| `removeEdge` | Remove a single edge |

### Attribute Combinators

#### `inherit'`

```nix
inherit' { resolve; _visited ? {}; } self id
```

Walks parent chain until `resolve node` returns non-null. Cycle-safe via `_visited`.

#### `inheritAll`

```nix
inheritAll { extract; combine ? a: b: a ++ b; } self id
```

Accumulates values along entire parent chain (ordered-list discipline — keeps duplicates, order-dependent).

#### `inheritSet`

```nix
inheritSet { extract; eq ? a: b: a == b; } self id
```

Set-discipline sibling of `inheritAll`: a node's value = its own contribution ∪ every ancestor's, walking up the P-edge parent chain, **deduplicated** (`eq`, default `==`). Idempotent union — membership is the semantics, order/multiplicity carry none — so a value several ancestors contribute appears once and the set stays bounded along a deep chain. Use for an inherited control-fact set (e.g. suppressed-policy names) that a consumer tests by membership; use `inheritAll` when order and duplicates matter. Delegates the (cycle-safe, demand-driven) parent walk to `inheritAll`.

#### `circular`

```nix
circular { init; eq ? a: b: a == b; maxIter ? 100; } f self id
```

Fixed-point iteration (Sloane 2010 §2.2). `f` receives `self`, `id`, and previous value.

#### `collectionAttr`

```nix
collectionAttr { traverse; extract; combine ? a: b: a ++ b; filter ? _: true; } self id
```

Traverse modes: `"imports"`, `"children"`, `"siblings"`, `"ancestors"`, `"neron"`, `"label:<name>"`, or custom function.

**`"neron"` traverse mode** — Specificity-ordered collection following D over I over P (local shadows import shadows parent) priority. Unlike `query`, which returns a single shadowed result, `"neron"` returns all contributions from reachable scopes in specificity order, suitable for fold-based composition (e.g., collecting all modules, merging config fragments).

Properties: cycle-safe via seen-set tracking, diamond-safe deduplication (each scope visited at most once), recursive parent resolution. Traversal order: self, then unseen imports, then parent — mirroring the Neron (2015) resolution calculus but collecting rather than shadowing.

The neron traversal order (self → imports → parent, imports in declaration order) is a public, stable contract: collection determinism for ordered-list channels rests on this pin plus a left fold, so changing the traversal order is a breaking change.

```nix
# Collect all config fragments from local scope, imports, and ancestors
config-modules = engine.collectionAttr {
  traverse = "neron";
  extract = self: id:
    let n = self.node id; in
    n.decls.modules or null;
  combine = a: b: a ++ b;
};
```

#### `query`

```nix
query { dataFilter; localShadowsImport ? true; importShadowsParent ? true; transitiveImports ? false; } self id
```

Neron (2015) resolution: searches local, imports, parent with specificity D < I < P. Import edges come from `self.get id "imports"` (computed attribute). `_seen` tracks visited scopes to prevent import self-resolution (Neron 2015 §2.4, rule X).

#### `queryAll`

```nix
queryAll { dataFilter; transitiveImports ? false; } self id
```

All reachable results without shadowing (Neron 2015 §2.3, rule R). For ambiguity detection.

#### `queryReverse`

```nix
queryReverse { dataFilter; transitive ? false; } self id   # → [value]
```

Reverse reference attribute — the dual of `queryAll`. Where `queryAll` walks import edges **forward** (the scopes `id` imports), `queryReverse` gathers `dataFilter` over every node that **imports** `id` (the reverse of the `imports` relation — a `neededBy`-style query, Hedin & Magnusson 2003 inter-type declarations). A node cannot see its importers locally, so this forces the full node set via `allNodes` (Tier 2, like `collect`). Gather-all, no shadowing; **direct** importers by default — set `transitive = true` to walk the reverse-import closure (cycle-safe via a seen-set).

**Answer order — reverse-walk discovery order.** The result is emitted in the order the reverse walk reaches its contributors: a pre-order depth-first traversal of the reverse-import relation rooted at `id`, in which a node's importers are enumerated in [materialization order](#materialization-order) (`allNodeIds`), not in the codepoint key order of `attrNames allNodes`. The duality fixes the choice — `queryAll`'s answer order is its traversal order, taken from each node's declared `imports` list, and the reverse relation carries no declared list of its own to walk, so the tree's own traversal supplies it (Hedin & Magnusson 2003; Sloane 2010 §7 collection attributes).

This library **does not sort and does not deduplicate** the answer. A node reachable along two reverse paths contributes twice, because a reverse gather counts contributions. A caller that needs a stable total order regardless of walk shape — or a set — sorts or deduplicates at its own call site and says so there.

```nix
# Which nodes depend on "lib:core"?
dependents = engine.queryReverse {
  dataFilter = n: if (n.decls.__edges.I or []) != [] then n.id else null;
} self "lib:core";
```

#### `paramAttr`

```nix
paramAttr f self id param
```

Parameterized attribute (Sloane 2010 §3).

#### Other Combinators

| Function | Description |
|----------|-------------|
| `shadow inner outer` | Inner shadows outer by key (Neron 2015 §5 Def. 1) |
| `resolve { local?, imported?, inherited? }` | Specificity-ordered resolution (Neron 2015 Fig. 2) |
| `collectImports extract self id` | Collect from imported scopes (Neron 2015 §2.4, rule I) |
| `collect { filter? } extract self` | Global collection (Tier 2, forces `allNodes`) |
| `collectByType type extract self` | Filter by node type (Tier 2) |
| `followEdge label self id` | Custom edge label targets (van Antwerpen 2018 §2.1) |
| `collectByLabel label extract self id` | Collect via custom edges |
| `subtypeOf { eq? } self idA idB` | Structural subtyping (van Antwerpen 2018 §2.3) |
| `ambiguous args self id` | Multiple reachable declarations? (van Antwerpen 2018 §2.3) |
| `visibleFrom dataFilter self id` | Single visible declaration from a scope |

### Structural Queries

Thin wrappers over `self.node` and `self.get`:

| Function | Source | Description |
|----------|--------|-------------|
| `parent self id` | `(self.node id).parent` | Parent node ID |
| `children self id` | `self.get id "children"` | Child nodes attrset |
| `childrenIds self id` | `attrNames (self.get ...)` | Child node IDs |
| `ancestors self id` | Parent chain walk | All ancestor IDs (cycle-safe) |
| `siblings self id` | Parent's other children | Sibling IDs |
| `descendants self id` | Recursive children walk | All descendant IDs (cycle-safe) |
| `isAncestor self ancestorId id` | `elem` check | Whether `ancestorId` is an ancestor of `id` |
| `isDescendant self descendantId id` | `elem` check | Whether `descendantId` is a descendant of `id` |
| `nodesByType self type` | `self.allNodes` filter | Nodes by type (Tier 2) |

## Performance

| Operation | Cost | Memoized? |
|-----------|------|-----------|
| `self.get rootId attrName` | O(1) | Yes — `rootEval.${id}.${attrName}` |
| `self.get synthId attrName` | O(depth) first, O(1) after | Yes — `node._eval.${attrName}` |
| `self.node rootId` | O(1) | Yes — direct roots lookup |
| `self.node synthId` (with parseParent) | O(depth) | Via parent's memoized children |
| `self.node synthId` (generic fallback) | O(n) | Via memoized children along path |
| `self.allNodes` | O(n) | Each node computed once |
| `self.allNodeIds` | O(n) | Shares `allNodes`' walk — asking for both costs one walk |

**`parseParent` is mandatory at scale.** Without it, node resolution walks from ALL roots per unknown node. For 500 roots x 1500 synthesized nodes = 750,000 root checks. With `parseParent`: 1500 x O(1) = 1500.

## Testing

```bash
nix flake check ./ci                       # build + run the full suite
cd ci && just ci                           # run all tests (nix-unit)
cd ci && just ci eval                       # run one suite
cd ci && just ci eval.test-basic-root-attribute  # run one test
```

Requires nix-unit. **174 tests across 20 suites** (13 test files): `eval`, `eval-debug`, `eval-warm`, `build-nodes`, `graph`, `hoag`, `circular`, `collection-attr`, `neron-traverse`, `queries`, `query`, `resolve`, `relations`, `specificity`, `subtype`, `ambiguity`, `custom-edges`, `wf-policy`, `recorded-deps`, and `purity`. The `purity` suite asserts the evaluator never touches `nixpkgs.lib`, enforcing the Class B nixpkgs-lib-free invariant.

## Theoretical Foundations

| Paper | Relationship | Used for |
|-------|-------------|----------|
| Vogt et al. (1989) "Higher-order attribute grammars" | **Implements** | Dynamic node synthesis via `children`/`derived-children` as non-terminal attributes (§2.4); `derived-children` extends this with second-stage stratification |
| Hedin (2000) "Reference attributed grammars" | **Implements** | Import edges as reference attributes; cross-node attribute access via computed scope references |
| Hedin & Magnusson (2003) "JastAdd" | **Informed by** | Demand-driven evaluation pattern; aspect-oriented attribute extension model |
| Neron et al. (2015) "A theory of name resolution" | **Implements** | Scope graph construction, resolution calculus (`query`/`queryAll`), D < I < P specificity ordering (Fig. 2), well-formedness of paths (§2.4), seen-imports cycle prevention (rule X), shadowing (§5 Def. 1) |
| van Antwerpen et al. (2018) "Scopes as types" | **Partial** | Custom edge labels via `edgeGraphs`/`followEdge`, structural subtyping (`subtypeOf`), coarse-grained visibility (boolean shadowing flags); Statix-style constraint patterns (partial: custom labeled edges via `edgeGraphs`, single `decls` relation per node) |
| Mokhov (2017) "Algebraic graphs with class" | **Implements** | All four graph construction primitives (`empty`/`vertex`/`overlay`/`connect`) and derived constructors (`star`/`path`/`clique`/`tree`/etc.) from §2.1-§5.1 |
| Sloane et al. (2010) "Kiama: AG embedding" | **Implements** | `CachedAttribute` pattern realized as `_eval` co-located cache; `paramAttr` (§3); `circular` fixed-point attributes (§2.2); collection attributes (§7) |
| Radul & Sussman (2009) "Art of the propagator" | **Informed by** | Monotonic convergence concept for `circular` attribute iteration; cells accepting information from multiple sources as design influence on scope graph merging |
| Van Wyk et al. (2010) "Silver: extensible AG" | **Informed by** | Forwarding concept (productions defining default attribute values via translation); collection attributes with fold operators as design influence on `collectionAttr` |
| Mokhov et al. (2018) "Build systems a la carte" | **Informed by** | Demand-driven evaluation as suspending scheduler (§4.1); Nix's lazy evaluation recognized as the scheduling mechanism — we do not build a scheduler, Nix is the scheduler |
| Acar et al. (2006) "Adaptive functional programming" | **Informed by** | Warm-cache incremental re-evaluation (`evalWarm`): reusing clean prior results and recomputing only dirty nodes; `recordedDeps` as the declared read-edge projection of a dynamic dependence graph |
