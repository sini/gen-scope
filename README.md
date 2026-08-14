# gen-scope

[![CI](https://github.com/sini/gen-scope/actions/workflows/ci.yml/badge.svg)](https://github.com/sini/gen-scope/actions/workflows/ci.yml) [![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](https://opensource.org/licenses/MIT) [![Sponsor](https://img.shields.io/badge/Sponsor-%E2%9D%A4-pink?logo=github)](https://github.com/sponsors/sini)

Demand-driven Higher-Order Attribute Grammar evaluator over algebraic scope graphs, implemented as a pure Nix library.

gen-scope is a **hybrid HOAG/RAG** evaluator: Higher-Order Attribute Grammars (Vogt et al., 1989) for dynamic node synthesis, Reference Attribute Grammars (Hedin, 2000) for cross-node references via import edges. It leverages Nix's native lazy evaluation for attribute computation, memoization, and cycle detection — we do not build an AG evaluator, Nix **is** the evaluator.

gen-scope is generic. It has no knowledge of NixOS, aspects, policies, or system configuration. It provides evaluation machinery; consumers define what to compute.

Beside the evaluator it carries a second, independent concern: **the well-founded engine**, which computes the meaning of a rule program with negation (Van Gelder, Ross & Schlipf 1991) — including the third verdict, `UNDEFINED`, for the contested cycles a stratified semantics leaves without one. See [The well-founded engine](#the-well-founded-engine).

It also carries the **staged minting entry**, which builds a scope graph rather than evaluating one: a fixed emitter list in, vertices under their own identifiers and one labelled edge per relatum out, each relatum resolved against the identities that strictly earlier passes settled. See [Staged minting](#staged-minting).

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
  - [The structural partition](#the-structural-partition)
  - [recordedDeps](#recordeddeps)
  - [buildNodes](#buildnodes)
  - [Algebraic Graph Construction](#algebraic-graph-construction)
  - [Attribute Combinators](#attribute-combinators)
  - [Structural Queries](#structural-queries)
- [The well-founded engine](#the-well-founded-engine)
  - [The construction, and the two arms behind the door](#the-construction-and-the-two-arms-behind-the-door)
  - [Iterative encodings, and the accumulator discipline](#iterative-encodings-and-the-accumulator-discipline)
  - [Ceilings](#ceilings)
  - [The partition, the bound, and the warning the result carries](#the-partition-the-bound-and-the-warning-the-result-carries)
  - [The ordered fold](#the-ordered-fold)
- [Staged minting](#staged-minting)
  - [The three vocabularies](#the-three-vocabularies)
  - [The identity key set](#the-identity-key-set)
  - [A pass is a stratum, and the set it resolves against is frozen](#a-pass-is-a-stratum-and-the-set-it-resolves-against-is-frozen)
  - [The two refusals](#the-two-refusals)
  - [What the entry does not do](#what-the-entry-does-not-do)
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

gen-scope is **Class B**: nixpkgs-lib-free, depending on [gen-prelude](https://github.com/sini/gen-prelude) (pure, zero-input), [gen-graph](https://github.com/sini/gen-graph) and [gen-schema](https://github.com/sini/gen-schema). Every concern here is pure list/attr combinators + builtins — no module system, no `nixpkgs.lib`, enforced by the `purity` suite over the library source. The flake exposes a single `.lib` value output.

Neither of the two siblings is the evaluator's. The **gen-graph** dependency is the engine's: the well-founded engine consumes that library's one published SCC-partition front door rather than carrying a second partitioner, because reverse reachability and the condensation are its concern. The **gen-schema** dependency is [staged minting](#staged-minting)'s: that library is the identity authority's home, and the one function it supplies reaches the minting module by injection from `lib/default.nix` rather than by that module importing a library of its own. Both sibling declarations carry a `follows` collapsing the inputs they share with this one, because two instances of a library in one evaluation are two formulas for the same node.

```nix
# flake.nix
{
  inputs.gen-scope.url = "github:sini/gen-scope";
  outputs = { gen-scope, nixpkgs, ... }:
    let engine = gen-scope.lib;
    in { /* ... */ };
}

# Or without flakes (all three inputs auto-derived from the pinned flake.lock):
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
  prior ? null;        # a prior EVALUATION's accessor — not a result map
  decision ? coldDecision;  # { isClean; reusable; } — see `evalWarm`
  provenance ? [ ];    # plain data carried back to the caller on the result
}
```

Returns `{ node, get, allNodes, allNodeIds, allNodesWhere, subtreeOf, nodesOfType, facade, resolutional, served, structuralEdges, decisionFindings, provenance }`:

| Function | Cost | Description |
|----------|------|-------------|
| `result.node id` | O(1) root, O(depth) synth | Resolve node structural data |
| `result.get id attrName` | O(1) amortized | Demand-driven attribute access (memoized) |
| `result.allNodes` | O(n) | Tier 2: flat map of all reachable nodes |
| `result.allNodeIds` | O(n) | Tier 2: the same node set as an **ordered** id list — see [Materialization order](#materialization-order) |
| `result.allNodesWhere pred` | O(n) | Tier 2: selective materialization filtered by predicate on node data |
| `result.subtreeOf rootId` | O(subtree) | Tier 2: materialize only the subtree rooted at a given node |
| `result.nodesOfType type` | O(n) | Tier 2: all nodes matching a given type string |
| `result.facade` | O(1) | The restricted read record an incremental plane is handed — see [`evalWarm`](#evalwarm) |
| `result.resolutional id` | O(a) | The reuse vocabulary at a node: this attribute set minus the structural partition |
| `result.served id` | O(a·r) | What the decision asked to reuse, intersected with that vocabulary |
| `result.structuralEdges id` | O(1) + per entry | The structural relation the substrate constructed, readable without forcing any resolutional attribute |
| `result.decisionFindings` | O(n·r), only if forced | Debug-mode validator: every attribute a decision named that the node's vocabulary does not contain |
| `result.provenance` | O(1) | The provenance the caller supplied, carried back on the result rather than dropped |

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

The trace is a **returned value**, not text inside an error. Alongside `node` and `get`, the accessor carries:

| Function | Description |
|----------|-------------|
| `d.trace` | The read path this accessor was reached along |
| `d.getTraced id attrName` | `{ value; trace; }` — the path is readable **without forcing the value**, so it survives the cycle and unknown-attribute cases where the value throws |

`get` is `getTraced` with the path dropped, so the two cannot drift apart. What is recorded is the **path** from the root read to this one; the union of reads across sibling branches is not recoverable, because the thread runs downward into the consumer's attribute functions and their results are values.

### `evalWarm`

```nix
evalWarm {
  roots;               # { id = { id, type, parent, decls }; }
  attributes;          # { attrName = self: id: value; }
  parseParent ? null;  # id → parentId | null
  prior;               # a prior EVALUATION's accessor
  decision;            # mkDecision { isClean; reusable; }
  provenance ? [ ];
}
```

Reuse-driven variant of `eval`. Both plane arguments are **mandatory**: an evaluation that means to reuse says which prior it reuses from and which decision authorises it, rather than inheriting a default that decides for it. Returns the same shape as `eval`.

**The interface is a DECISION interface.** The plane takes the current program, a prior evaluation and the graph, and returns a `Decision` — a predicate over nodes and a projection over the prior evaluation's results. The evaluator consumes it and does all recomputation. A `Decision` is two total functions and carries **no values**, so a plane that accumulates its own evaluation state has nowhere to put a result; `mkDecision`'s argument set is closed, so a field holding values is refused by name at construction rather than added silently.

**The prior is an accessor, not a result map.** Reuse is intra-evaluation: the prior is another evaluation live inside the same one, so there is nothing to materialize and nothing persists from one invocation to the next.

**Structure is never reused.** `children`, `derived-children`, every `edges-*` label and `includes` are decided by one syntactic predicate (`structural`) and always recomputed — the branch that does so fires before the decision is consulted at all, so a decision naming a structural attribute is inconsequential rather than dangerous. A dirty descendant therefore stays reachable through freshly-materialized parents, and a labelled reachability relation is never read stale. The cost is real and taken deliberately: a reuse-driven evaluation pays edge-set recomputation.

**What the plane is handed** is `result.facade` — exactly `{ get; nodeIds; resolutional; }`, and that **key set is closed and checkable**: no `node` entry, no materialization surfaces, no combinator entries, and a read outside those three names is an attribute that does not exist rather than one that is refused.

**What that does *not* close, stated because it would otherwise read as containment.** Closing the key set bounds the names the plane can ask this record for; it does not bound what is reachable through the values `get` returns. Two channels, both measured:

- `get id "children"` answers **node records**, each carrying `id` / `type` / `parent` / `decls` and the co-located `_eval` cache — so `(get id "children").<kid>._eval.<attr>` evaluates without passing through `get`, and `decls` / `parent` are read straight off the record. Raw node records are **reachable**.
- `get` accepts **any string**. Withholding the combinators withholds the combinators; it does not stop a caller building `"edges-" + label` and passing it in.

This is the same shape as the fact that there is no single read choke point anywhere in this library, and the facade cells pin it as measured fact rather than arguing it away. So the facade bounds one consumer's **entry points**; it does not make gen-scope single-choke-point, because the evaluator's own attribute functions keep every read channel they have. What survives the residual is the property reuse actually rests on: **no structural value is ever served from a prior evaluation**, which is a property of the evaluator's branch order and not of this record.

Under `coldDecision` — nothing clean, nothing reusable — the reuse branch never fires, so `eval` and cold-decision `evalWarm` are byte-identical; they share a single code path.

```nix
prior = engine.eval { inherit roots attributes; };   # the previous evaluation
result = engine.evalWarm {
  inherit roots attributes prior;
  decision = engine.mkDecision {
    isClean = id: id != "host:db";      # only db changed
    reusable = _: [ "region" ];         # and this is what may be reused
  };
};
result.get "host:web" "region"   # reused from `prior`, compute fn not forced
result.get "host:db"  "region"   # recomputed (db is dirty)
```

### The structural partition

```nix
structural name          # → bool, total on every string
resolutionalNames names  # → the complement over a list of names
edgePrefix               # "edges-" — the reserved structural namespace
```

An attribute is **structural** when the graph's shape depends on it: `children`, `derived-children`, anything under `edges-`, and `includes`. The predicate is over the **name** rather than an enumeration because `edges-<label>` is an open family whose members are built during evaluation, so no list could be complete — and an under-inclusive partition would admit a structural name into the reuse vocabulary, where reusing it serves a stale edge relation.

**Its stated domain.** The predicate is decidable and total, but its faithfulness rests on consumers naming structural attributes inside the reserved namespace. An attribute that is structural in *meaning* under a name outside it — `myEdges` — classifies resolutional and may be reused. Semantic structurality is undecidable, so that residual is real and is not closed here; what catches it is the byte-parity oracle, since a stale structural value is a parity failure.

Containment needs no term: a node's parent rides the node record's `.parent` field and never reaches the evaluator as an attribute name.

### `recordedDeps`

```nix
recordedDeps { declaredEdges } id   # → [id]
```

First-class projection of a consumer's **declared** read-edges: it simply applies `declaredEdges id`. Pure and memo-free — it never runs through `get`. The *dynamic* read-set (the attributes a node actually `self.get`s) is only recoverable via `evalDebug`'s fresh-`self`-per-`get` — `getTraced` returns that recording as a value — and that construction defeats memoization; there is no pure, memo-preserving way to capture it, so the declared edges are the inspectable contract. Useful for incremental consumers that need an explicit dependency edge set (e.g. driving a rebuild).

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

## The well-founded engine

A second concern lives in this library beside the attribute evaluator: an engine that computes the meaning of a **rule program with negation**. It shares the evaluator's substrate and nothing else — no node, no attribute, no scope graph. What it computes is the **well-founded partial model** (Van Gelder, Ross & Schlipf 1991), and the reason it exists is the third value.

```nix
program = engine.mkProgram {
  rules = [
    { head = "t"; }                                    # a fact
    { head = "u1"; neg = [ "u2" ]; }                   # u1 :- not u2
    { head = "u2"; neg = [ "u1" ]; }                   # u2 :- not u1
    { head = "c1"; pos = [ "c2" ]; }                   # c1 :- c2
    { head = "c2"; pos = [ "c1" ]; }                   # c2 :- c1
  ];
};
model = engine.wellFoundedModel program;

model.trueAtoms       # [ "t" ]         — derived
model.undefinedAtoms  # [ "u1" "u2" ]   — CONTESTED: a cycle through a negative edge
model.falseAtoms      # [ "c1" "c2" ]   — UNFOUNDED: a positive cycle with no support
model.verdict "nothing-mentions-this"   # "false" — total on every string
```

**Why a third value.** A cycle through a negative edge has no meaning under the stratified semantics — Apt, Blair & Walker 1988 admit positive cycles and leave that shape without one. `UNDEFINED` is what the well-founded model gives it, and it is a **named verdict**, never a silence: `verdict` is total on every string, and an atom no rule mentions comes back `"false"` rather than as an absence the caller has to interpret. On locally stratified programs the model is total and equal to the perfect model, so nothing that already had a meaning acquires a different one.

**Stable-model existence is the refusal oracle, and it is NOT built here.** The engine constructs the well-founded model; deciding whether a program has a stable model is a harder problem and this library supplies no construction for it. Containment (well-founded ⊆ every stable model) is what keeps the pair coherent; it is not a decision procedure. Stated so a reader does not infer an oracle from the semantics it accompanies.

### The construction, and the two arms behind the door

`S(J) = lfp T_{P/J}` over the Gelfond–Lifschitz reduct is antimonotone, so `S²` is monotone; `W⁺ = lfp(S²)` from ∅ is the true set and `S(W⁺)` is the true-or-undefined set. The inner least fixpoint has two constructions and the door routes between them:

| arm | construction | expresses | round count |
|---|---|---|---|
| `leastModelUnary` | `builtins.genericClosure` — a C-level worklist, no accumulator, no recursion | **unary bodies only**; refuses conjunctive input by name | not observable (the done-set is C++-side) |
| `leastModelRounds` | one `T_P` application per round over a flat fold | every program | reported |

```nix
engine.armFor program        # "unary" | "conjunctive" — computed from the program
engine.leastModel program    # the door: routes, then delegates
```

**The routing is a property of the program, never a caller-selected mode.** A mode would let a caller select the engine that cannot express their program. The discriminator is the greatest **positive** body arity, and reading only the positive body is what makes computing it *once* sound: reduction deletes whole rules and deletes negative literals, and does neither of the two things that could raise that number — so a program routed once routes the same way for every reduct taken of it. A rule with one positive and one negative literal is therefore **unary**, which is worth stating because it does not look it.

**The price of conjunctivity is the loss of the closure arm**, and it is measurable: on unary input the two arms agree on the answer while the round loop costs a growing multiple of the closure, and on conjunctive input the closure arm cannot express the program at all.

### Iterative encodings, and the accumulator discipline

Two constructions are excluded outright rather than merely not chosen, because both fail as **aborts** rather than as errors — `tryEval` does not contain either, so no in-language assertion can observe one and no caller can recover.

- **Per-atom recursion.** A self-applying loop costs one evaluator frame per iteration, so its descent depth is its iteration count. Every loop here is flat: a C-level closure or a C-level fold.
- **A partially-forced round accumulator.** `foldl'` forces its accumulator to weak head normal form — for a record, the record and not its fields — so a field written every round and read in none chains one update thunk per round.

`forceFields` is the answer, and it is derived from the accumulator's **own fields** rather than from a maintained list of them, so a field added later is forced without the discipline being re-applied:

```nix
engine.forceFields acc   # seq over every value in the record; a partial fix is no fix
```

**There are TWO abort signatures, and an engine armed for one misses the other.** Where the chain passes through a function application the descent exhausts the evaluator's call-depth guard first; where it is a bare operator there is no guard in front of it at all and it goes straight to the C stack. Measured on this host (nix 2.34.8 · `max-call-depth` 10000 · `ulimit -s` 8192 KB), on one loop over one accumulator at one round count, differing only in whether the forcing is applied:

| arm | boundary | signature |
|---|---|---|
| `unforcedCall` — the counter chains through a function application | green 9995, aborts 9998 | `CALLDEPTH` (`max-call-depth exceeded`) |
| `unforcedOperator` — the counter chains through `+` | green 45000, aborts 45500 | `CSTACK` (`stack overflow`) |
| `forced` — the same loop under `forceFields` | **green at 50000**, past both | — |
| `tryUnforced` — the unforced arm wrapped in `tryEval` | **dies** at 50000 | the abort is uncatchable |

Re-run: `./ci/bench/engine-ceiling.sh`. A sweep in which a signature does not fire reports `INVALID` rather than passing: a green row from an evaluation that could not have observed an abort says nothing.

**The round bound is a theorem, not a cap.** `T_P` is monotone and its iteration from ∅ is increasing, so at most one round per atom can be productive and one further round observes that none was. `|atoms| + 1` is the number of steps the recursion would itself have taken. Nothing refuses at it, and `converged` rides every result so an unconverged answer is visible rather than inferred.

**And the loops are flat, which is a measurement rather than a reading of the source.** A self-applying loop cannot pass `max-call-depth` at all — its descent depth *is* its iteration count. Both loops are green **past** that guard: `leastModelRounds` at **12001 rounds** and `wellFoundedModel`'s outer loop at **10002 outer rounds**, against a guard of 10000. The first is an arm of `./ci/bench/engine-ceiling.sh`; the second costs minutes (outer rounds × two least-model passes × ~20000 atoms) and is run on its own rather than in the sweep.

### Ceilings

| surface | ceiling | disposition |
|---|---|---|
| `leastModelUnary` | none found | states no ceiling; refuses nothing on size |
| `leastModelRounds` | none found to 12001 rounds — past the call-depth guard | states no ceiling; refuses nothing |
| `wellFoundedModel` outer loop | none found to 10002 outer rounds — past the same guard | states no ceiling; refuses nothing |
| `leastModelUnary` on conjunctive input | not a ceiling — a **refusal by name**, since the arm cannot express the program | throws, naming the arm and the offending rule's head and arity |

The round counts above are where the loops were **run**, not where they were pushed to failure — but they are past the **call-depth guard**, which is the reading that settles the encoding. Neither is near the **C-stack** boundary at ~45500 and neither can cheaply be: cost is rounds × rules, and the outer cell already costs 465 s at 10002 rounds. What carries the construction claim there is the controlled forced/unforced comparison above, not a cliff-region reading of the engine itself.

### The partition, the bound, and the warning the result carries

The engine does not partition. Strongly connected components and the condensation are [gen-graph](https://github.com/sini/gen-graph)'s concern, and this engine **consumes that library's one published front door**:

```nix
solved = engine.solve program;
solved.condensationDepth   # read from the door, reported as the door reports it
solved.provenance          # [ ] inside the verified bound; one plain-data entry past it
```

What the door is handed is the **unsigned** dependency accessor (`program.dependency`), because mutual reachability is a property of the unsigned relation; the sign labels sit beside it (`program.signs`) as the labelled view, and nothing here asks the door to carry a label.

**The engine constrains nothing on cost.** It accepts any program the semantics does not refuse and costs what it costs: no depth, size or shape makes a program inadmissible. `verifiedDepth` is an **acceptance** bound — what has been verified, never what the engine permits — and past it the engine **warns**; it does not refuse. A runtime refusal past a stated depth would make cost into correctness.

**The depth is paid only if the warning is read.** Measured on one 2049-atom chain: forcing `solve`'s `trueAtoms` costs 679 ms, forcing its `provenance` costs 2765 ms. The difference is the condensation, and it is demand-driven like everything else in this substrate — the field is on the result and cannot be dropped, but nothing computes it until something reads it.

**The warning rides the result.** It is a value the caller receives, never a side channel: a printed warning goes to stderr, which the evaluation cache swallows after the first run, and a debug-only field is invisible in ordinary use. A field that *is* the result survives caching because it is what was cached. It is plain data, so it crosses an evaluation boundary as itself. It is **not** the semantics' third value — `UNDEFINED` is a verdict on an atom inside the model; this accompanies a successful operation.

```nix
engine.verifiedDepth
# { depth = 2049;
#   derivation = "the greatest condensation depth at which every arm of
#                 ci/bench/cost-classes.nix completed with converged=true, …";
#   fixtures = [ "chain" "cycle" "blocks" "blocksWide" "deepContested" "layers" ];
#   environment = { nix = "2.34.8"; maxCallDepth = 10000; stackLimitKb = 8192; };
#   reDerivationOwedOn = [ … ]; }
```

**The figure is never a bare number.** It is derived at implementation from the engine's own measured cost curve, recorded with its derivation, and re-derived whenever the engine changes — `reDerivationOwedOn` names the four constructions whose editing owes one. Re-run: `./ci/bench/cost-classes.sh`, whose default ladder is what produced the figure. The ladder as measured, wall ms, most expensive arm per rung:

| rung `d` | chain | blocks | deepContested | layers | greatest condensation depth |
|---|---|---|---|---|---|
| 128 | 430 | 432 | 503 | 641 | 129 |
| 512 | 569 | 589 | 1524 | 3643 | 513 |
| 1024 | 1014 | 1144 | 5020 | 13807 | 1025 |
| 2048 | 2740 | 3152 | 20335 | 58590 | **2049** |

Each cell is a separate `nix-instantiate`, so every figure carries the evaluator's startup — around 250 ms, which is most of the 128 rung and none of the 2048 one. The ladder is read for **what completed**, not as a cost model. The `model` arm is the engine's own cost; the `depth` arm is the model **plus** the door, so the door's price is the difference between them and never the `depth` reading.

No figure here is a budget and none is offered as one. Whether a curve is adequate for the fleet the engine is for is a judgement, made by a person reading it, and no threshold is manufactured to make it runnable.

**The detector detects; it does not act.** A bound derived from the measured curve cannot be failed by that curve, so the signal is not "the benchmark exceeded the figure" — it is a re-derivation moving the verified depth **downward**, compared under three pinned terms:

```nix
engine.acceptanceSignal { baseline = <recorded>; reading = <fresh>; }
# → { signal = "unbaselined" | "voided" | "fired" | "steady"; reason = "…"; }
```

A change to the fixture families, the derivation function, or the environment terms **voids** the comparison rather than passing or failing it, and a fresh baseline is owed. A fired detector is a **signal to a judge**, who takes the retreat or declines it; nothing here executes anything. And it detects **regression, never inadequacy** — an engine whose first verified depth is far too low regresses against nothing and this stays silent, which is why the first run reports `unbaselined` and why the judge is a person.

### The ordered fold

```nix
engine.foldContributions { model; contributions; op; init; }
# → { value; admitted; contested; }
```

Contributions combine in the order they were **declared**, and the fold reads no strength annotation: positional authority is the substrate's, and a priority algebra is the module system's own. A priority is content — a value carrying meaning — which the substrate must not interpret and which may not cross an evaluation boundary; an ordered contribution list is plain data. Nothing is sorted, deduped, or filtered by rank, because the list's order *is* the authority.

A contribution whose gating atom is **UNDEFINED** is not admitted and is not dropped either: it comes back in `contested`. A gate that is FALSE is neither — it did not happen, which is a different fact from being undecided.

## Staged minting

A third concern, and the only one that **builds** a graph rather than reading one. `mintStrata` takes the emitters a program declared and returns the scope graph they describe: a node map keyed by identifier, one labelled edge per relatum, the number of strata the run walked, and the driver's leftover partition carried through.

```nix
mintStrata {
  emitters;   # [ { pass; identifier; kind; relata; content; site; } ] — the fixed item set
  kinds;      # the schema stratum's already-evaluated output
}
# → { nodes  = { <identifier> = { identity; kind; content; }; };
#     edges  = [ { from; to; label; } ];   # one per relatum, carrying the identity's own label
#     strata;                              # the number of distinct declared passes the run walked
#     unrun; }                             # the driver's leftovers — empty on every run, by theorem
```

**Neither the identity authority nor a frozen set is an argument, and both absences are load-bearing.** `hashIdentity` is [gen-schema](https://github.com/sini/gen-schema)'s and reaches the minting module by injection from `lib/default.nix`, which is what makes the count of minting authorities a fact about the dataflow rather than a rule an author obeys (ADR-0016 ruling 5) — the module has no library of its own to reach for and no second derivation to drift. Identity is minted inside the evaluation doing the constructing, which is ADR-0014's **constructing** arm: a constructor taking an authority as a parameter owns the value it emits rather than borrowing it. The rejected arm of the same ruling is why nothing of gen-schema is re-exported under this library's name — re-exporting another library's value re-exports *its* build — so what the seam adds to the export surface is this entry and nothing else. A caller-supplied frozen set is absent for a different reason: it would be forgeable, and a forgeable frozen set is a rule authors must obey rather than a construction. Stratum 0 therefore resolves against `{ }`.

### The three vocabularies

ADR-0016 ruling 5 separates them and the entry never merges them:

| Term | What it is |
|---|---|
| **identifier** | A string — the scope graph's own vertex name. It is what an emitter writes when it names a relatum, what keys the node map, and what an edge endpoint names. The root has one and has no identity. |
| **identity** | The authority's output, `"<kind>:" + digest`. Minted once per identifier, by `hashIdentity` and by nothing here. |
| **label** | A relatum's role in the relation. It keys the identity *and* is the token the incident edge carries, so choosing a label is choosing a traversal token. |

### The identity key set

**The keys are the relatum labels plus the node's own identifier**, under a reserved label, and the second half is forced rather than chosen. ADR-0016 ruling 4 gives the binding case whole — *a kind whose identity keys are its relatum labels and whose values are the relata's identities* — and the authority refuses a preimage with no keys by name. But **not every vertex of a scope graph is a binding**: an emitter with no relata is admissible, is most of a real emitter set, and under the relatum-labels-only reading has no identity to mint at all — while a relatum-free node that other emitters name must have one to resolve to. So some key is owed. Two readings are refused with their reasons, so neither is re-proposed:

- **Key the content.** Refused because it is the one thing the staged construction forbids: a later pass contributes content to an already-minted identity, so an identity that moved when content arrived would re-mint on every contribution. Content-independence is exactly what lets two emitters of one relation reach one node.
- **Key the kind alone.** Total, and refused on ADR-0016's own ground for the zero-relatum binding: it would collapse every relatum-free node of a kind onto one identity, which makes the identifier→identity map many-to-one and takes the information out of resolution — the map's whole job.

The one property ruling 4 states about **values** is untouched: every relatum's value is that relatum's resolved identity and never its identifier, because hashing a relatum's declared name would make one node's identity a function of another's spelling.

### A pass is a stratum, and the set it resolves against is frozen

Apt, Blair & Walker (1988) build the standard model of a stratified program one stratum at a time, each closed before the next begins. A minting pass is that stratum: when pass N runs, every earlier pass has finished and the identities it settled are closed, and a relatum resolves against **that** set and no other. ADR-0016 ruling 7 is the consequence a reader feels — **a cycle among minted nodes is inexpressible**, because writing one would require a pass to see its own output. There is nothing to detect because there is nothing to express.

The schedule is the **distinct declared passes, ascending** — not a range over the declared maximum and not a topological sort. A program declaring passes 0 and 1000000 runs two strata, not a million empty ones. `strata` is reported and compared against nothing.

### The two refusals

They are different in kind, and both are `throw`, so both are catchable — a refusal a caller cannot catch is a refusal no test can assert on.

- **An identifier that does not resolve** is refused at **mint** time, naming the relatum, its label, the kind being minted and the emitting pass. Three failures reach it and they differ only in why the lookup missed: a same-pass relatum (not in the set, which holds strictly earlier passes only), the root (an identifier with no identity), and a name with no entry.
- **Contributions that disagree** are refused at **merge** time, after minting has already succeeded, exactly as a module system refuses two conflicting definitions of one option. That message names the identity, the key and both emitters' sites — ordered by their own text rather than by the order the emitters arrived in, since within a pass there is no order and a message that moved under a permutation would stop being a property of the program.

Within a pass there is no order at all (ADR-0022), so the only outcomes an unordered fold may have are agreement and refusal. Each emitter naming an identifier contributes an identity and a set of content keys, and both merge by one rule: identical collapses, conflicting refuses. Because the identity is a total function of the kind, the identifier and the resolved relata, agreement on the identity **is** agreement on the kind and the relata, so no separate check for either exists to drift.

★ **The cross-pass arm of that rule is PROPOSED rather than settled, and a reader must not take it for ruled law.** A later pass naming an already-frozen identifier contributes content and never yields a second node — that half is settled, and where the contribution agrees or adds a key the behaviour is indistinguishable from same-pass agreement. What is not settled is a later pass **disagreeing** about a key an earlier pass had already settled. ADR-0016 leaves it open in its own words: two emitters of one identity yield one node with contributions from both, and how those contributions compose *is not settled here — that is the substrate's general content rule*. The entry refuses there **as a proposal pending that rule**. The argument for it, offered rather than asserted: the freeze ranges over membership while the map's values may be revisited, but a stratum's output is closed when the next begins and the standard model only ever grows, so a later pass *adding* a key is revision while a later pass *replacing* one is retraction — and retraction is what stratification exists to keep out of a fold. The argument against is equally available and is why this is not stated as law: pass order **is** contribution order, so a later contribution is an ordered one, and the module-system analogy admits a later definition winning. Whoever rules the general content rule rules this line, and if it goes the other way the change is the merge's disagreement branch and nothing else.

### What the entry does not do

- **It refuses nothing for being large.** No cap, no ceiling, no budget: the schedule is what the emitters declared and no number here refuses a program for its size. The frozen set is an attrset rather than a list of records because resolution is a membership test plus a lookup per relatum, and over a list that is a scan inside the pass loop — a cost argument, deliberately not a refusal.
- **It does not rewire the kind cascade.** `resolveClaims` and the wiring surface run their own bounded loop over their own subject; nothing here calls them and nothing there calls this. The two are separate constructions that happen to share a library.
- **It asks the graph nothing.** The `graph` formal reaches the module and stops — no line applies it. What the entry publishes is the graph's **content** as plain data; answering reachability and partition questions about a graph already built is a different phase's work, and the emptiness is what says the minting run asks none of them.
- **It is not lazy in its result.** The whole result is forced before it is returned, and each stratum's output is forced in the round that produced it, so a refusal is a property of the **call** rather than of a consumer's reading pattern. A caller reading one field gets the same answer as a caller reading all of them.

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

Requires nix-unit. **623 tests across 45 suites** (30 suite files under `ci/tests/`; two further files sit in `ci/tests/_fixtures/`, which the tree importer does not import: the two files contribute no suite, and 45 suites come from the 30 files outside that directory). The evaluator's: `eval`, `eval-debug`, `eval-debug-trace`, `eval-warm`, `build-nodes`, `graph`, `hoag`, `circular`, `collection-attr`, `neron-traverse`, `queries`, `query`, `resolve`, `relations`, `specificity`, `subtype`, `ambiguity`, `custom-edges`, `wf-policy`, `recorded-deps`, `structural`, and the six `plane-*` suites. The engine's: `engine-program`, `engine-least-model`, `engine-well-founded`, `engine-door`. Staged minting's: `minting`, plus `stratify`, `stratify-non-refusals` and `stratum-aggregation` for the driver it runs on. Nine further suites — `folds`, `dedup` and the seven `cascade-*` — cover the fold vocabulary and the kind cascade. The `purity` suite asserts the library source never touches `nixpkgs.lib`, enforcing the Class B nixpkgs-lib-free invariant.

A cell whose subject is a refusal **message** cannot live under `flake.tests`: the batch asserter behind `checks.default` quantifies over that option and forces every `expr` unconditionally, so a throwing one crashes the gate instead of failing a cell. Those cells have their own output — **34 tests across `cascade-refusals`, `folds-refusals` and `minting-refusals`**, run with `nix-unit --flake ./ci#testsError`. Both minting refusals are asserted there — each of the unresolved-relatum causes and the merge conflict against its own message text, anchored end to end rather than checked for being non-empty, so neither cell can be satisfied by the other's refusal.

**Two things the suite structurally cannot host**, and both are read off exit codes instead:

```bash
./ci/bench/engine-ceiling.sh    # the abort controls, both signatures, and the refusals
./ci/bench/cost-classes.sh      # the cost curve the acceptance bound derives from
```

A stack overflow is an abort rather than a throw, so `tryEval` does not contain one and no in-language assertion can observe it — and an argument-arity refusal is not catchable either, while a throw's *message* is discarded by `tryEval`. `engine-ceiling.sh` reports `INVALID` when a signature fails to fire, because a green row from an evaluation that could not have observed an abort is not a pass.

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
| Van Gelder, Ross & Schlipf (1991) "The well-founded semantics for general logic programs" | **Implements** | The well-founded partial model at the ATOM level; `UNDEFINED` as a named third verdict for contested atoms; totality on locally stratified programs |
| Van Gelder (1993) "The alternating fixpoint of logic programs with negation" | **Implements** | The construction: `S(J) = lfp T_{P/J}` antimonotone, `S²` monotone, `W⁺ = lfp(S²)` from ∅, `S(W⁺)` the true-or-undefined set |
| Gelfond & Lifschitz (1988) "The stable model semantics for logic programming" | **Partial** | The reduct `P/J` the alternating fixpoint iterates over. Stable-model EXISTENCE as the refusal oracle is adopted as the companion criterion and is **not built here** — no construction in this library decides it |
| Apt, Blair & Walker (1988) "Towards a theory of declarative knowledge" | **Informed by** | Two uses at one label. For the engine: why the third value is needed at all — the stratified semantics admits positive cycles and leaves a cycle through a negative edge without a meaning. For [staged minting](#staged-minting): the standard model of a stratified program is built one stratum at a time, each closed before the next begins, and a minting pass is that stratum — which is what makes a cycle among minted nodes inexpressible rather than detected. The correspondence taken is the closure of earlier strata, not the per-stratum fixpoint iteration |
| van Emden & Kowalski (1976) "The semantics of predicate logic as a programming language" | **Implements** | `T_P` and its least fixpoint as the meaning of a definite program — what both `leastModel` arms compute over the reduct |
| Tarjan (1972) / Fleischer, Hendrickson & Pınar (2000) | **Consumes** | Strongly connected components and the condensation, through gen-graph's published partition front door. Not re-implemented here: the engine reads the reported condensation depth and nothing else |
| Acar et al. (2006) "Adaptive functional programming" | **Informed by** | Warm-cache incremental re-evaluation (`evalWarm`): reusing clean prior results and recomputing only dirty nodes; `recordedDeps` as the declared read-edge projection of a dynamic dependence graph |
