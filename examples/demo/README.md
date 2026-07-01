# gen-scope demo

A tour of `gen-scope`: algebraic graph construction (Mokhov 2017), scope-graph
name resolution (Neron 2015, van Antwerpen 2018), and higher-order attribute
grammar (HOAG) evaluation (Vogt 1989, Sloane 2010).

Every attribute in `flake.nix` is a self-contained, evaluatable example whose
inline `# ->` comment states the expected result.

## Layout

The single-file flake exposes one output attribute per concept:

| Output | Concept |
| --- | --- |
| `graphPrimitives` | Core algebra: `empty`, `vertex`, `overlay`, `connect` |
| `graphDerived` | Derived constructors: `star`, `path`, `circuit`, `clique`, `tree`, `forest`, `edges`, `overlays` |
| `graphTransformations` | `gmap`, `transpose`, `induce`, `removeVertex`, `removeEdge` |
| `scopeGraphBasic` | `buildNodes` + `eval`: parents, decls, imports, types |
| `structuralQueries` | ancestors, descendants, siblings, children |
| `nameResolution` | lexical/import resolution, shadowing, deep inheritance |
| `ambiguityDetection` | multiple reaching declarations |
| `visibilityPolicies` | transitive vs non-transitive import visibility |
| `seenImports` | seen-set cycle guarding during resolution |
| `demandDrivenEval` | lazy, memoized attribute demand |
| `hoagSynthesis` | dynamic node synthesis (higher-order AG) |
| `circularAttributes` | fixpoint `circular` attributes (Sloane 2010 §2.2) |
| `importCollection` | import-scoped collection (Neron 2015) |
| `structuralSubtyping` | `subtypeOf` record subtyping |
| `customEdgeLabels` | custom edge labels: `followEdge`, `collectByLabel` |
| `scopedRelations` | multiple relation namespaces on one scope |
| `evalDebugDemo` | structured cycle tracing via `evalDebug` |
| `globalCollection` | `collect` / `collectByType` global queries |

## Run

Each output evaluates to a plain attrset of results:

```sh
nix eval .#graphPrimitives --json
nix eval .#circularAttributes --json    # { "converged": 95 }
nix eval .#hoagSynthesis --json
```

Compare any output against the `# ->` comments next to its definition in
`flake.nix` to confirm the demonstrated behavior.

## Inputs

Pinned to the published `github:sini/gen-scope`. The library is consumed through
its single `.lib` value:

```nix
genScope = gen-scope.lib;
```
