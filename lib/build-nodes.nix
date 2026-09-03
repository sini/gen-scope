# Scope graph construction: produces the node set AND the declared vertex order.
#
# Output shape: { nodes = { id = { id, type, parent, decls }; }; nodeOrder = [ id … ]; }
# No pre-indexed edges — relationships are computed via attributes.
# Edge declarations stored in decls.__edges for consumers to use in attribute definitions.
#
# ── WHY A RECORD AND NOT A BARE NODE MAP ──
# The algebraic graph layer carries vertices as a LIST (`lib/graph.nix`, where `overlay` and
# `connect` concatenate), and an attrset is a SET: collapsing that list through `listToAttrs` and
# back out through `attrNames` computes a declared order and then discards it, leaving bytewise
# codepoint order as the residue. The order is not absent from the substrate; it is destroyed by
# THAT COLLAPSE, which is the shape this constructor does not have. `nodeOrder` is that order,
# kept. It is a list of strings — plain data, so it crosses a library boundary as a value rather
# than as a re-handed build.
#
# The order cannot live INSIDE the node attrset: a reserved top-level key would be enumerated as a
# node by every consumer that reads `attrNames`, and a Nix attrset has no other channel.
#
# `edgeGraphs` is an ORDERED LIST of `{ label, graph }` rather than a label-keyed attrset, because
# an attrset has no order to carry: enumerating a label space with `attrNames` makes the order in
# which edge graphs contribute a function of alphabetical label spelling. A list has somewhere for
# the caller's declared order to live. It is the caller's OWN label space, open on every label
# except `P` and `I`, which are this constructor's names for the containment and import relations
# and are refused by name at the entry — see the reservation below.
{ prelude }:
let
  graph = import ./graph.nix;

  # ── THE RESERVED LABELS, REFUSED BY NAME ──
  # `P` and `I` are this constructor's OWN names for containment and import. Neither is an ordinary
  # label — the partial-function guard is stated of `P` by name (Neron 2015 §2.2), and the label
  # index is built from every label except it — so a caller's graph arriving under one of these
  # names is read as a relation this library privileges rather than as the labelled edges the
  # caller declared. The reservation is a refusal AT THE ENTRY rather than a convention a caller is
  # trusted to know, and it is unconditional: a reservation that lapsed when `parentGraph` happened
  # to be empty would leave the caller's graph silently PROMOTED to the privileged relation instead
  # of silently displacing it, which is the same defect entered from the other side.
  reservedLabels = [
    {
      label = "P";
      relation = "the containment relation, whose edges arrive as the `parentGraph` argument";
    }
    {
      label = "I";
      relation = "the import relation, whose edges arrive as the `importGraph` argument";
    }
  ];

  nonEmpty = g: g.vertices != [ ] || g.edges != [ ];

  # ── NODE KINDS REGISTER ──
  # `type` used to be `types.${id} or null` and nothing else: a per-id, free-form string with no
  # registry behind it and no validation in front of it. Any spelling was a kind, an id absent from
  # `types` was a node of no kind at all, and a node minted during evaluation carried whatever its
  # producer wrote — so the kind set grew as freely as the node set, and neither growth was
  # observable from anywhere. A well-founded order over kinds cannot live on a set like that: an
  # order needs a domain, and this one had none.
  #
  # So a caller that declares kinds declares them AGAINST A REGISTRY, and an unregistered name is
  # refused BY NAME. The formal is sentinel-guarded rather than required, and the rule underneath it
  # is total in both directions: declaring a `type` with no registry is refused just as an
  # unregistered spelling is. It is the absent-declaration case that the free-form version got
  # wrong, and defaulting it to "anything goes" is the same defect wearing a default.
  #
  # A caller declaring NO types is unaffected and pays nothing — there is no kind to be unregistered,
  # and the kind order over an empty vocabulary is trivially well founded. What such a caller cannot
  # do is spawn, because an expansion descends a rank and a node with no kind has none.
  unregisteredKinds =
    kinds: types:
    let
      declared = prelude.filter (t: t != null) (builtins.attrValues types);
      registered = builtins.attrNames (kinds.kinds or { });
    in
    prelude.unique (prelude.filter (t: !(builtins.elem t registered)) declared);

  buildRoots =
    {
      parentGraph ? graph.empty,
      importGraph ? graph.empty,
      edgeGraphs ? [ ],
      decls ? { },
      types ? { },
      kinds ? null,
      strict ? true,
    }:
    let
      reservedOffenders = prelude.filter (
        r: prelude.any (c: c.label == r.label) edgeGraphs
      ) reservedLabels;

      declaredTypes = prelude.filter (t: t != null) (builtins.attrValues types);
      unregistered = if kinds == null then [ ] else unregisteredKinds kinds types;

      # A label names a DIMENSION, not a node, so two contributions claiming one label is a genuine
      # collision with no order semantics to resolve it. The list form makes that expressible where
      # the attrset could not, so the list form owes the refusal: unguarded, the second contributor's
      # vertices survive into the node set while its edges are silently emptied, leaving nodes whose
      # declared relations are blank and undetectable from outside.
      duplicateLabels =
        let
          byLabel = builtins.groupBy (c: c.label) edgeGraphs;
        in
        prelude.filter (l: builtins.length byLabel.${l} > 1) (builtins.attrNames byLabel);

      contributions =
        if kinds == null && declaredTypes != [ ] then
          throw "gen-scope.buildRoots: `types` declares kind(s) ${builtins.toJSON (prelude.unique declaredTypes)} but no `kinds` registry was supplied. A kind is a name in a registered vocabulary, not a free string: without the registry there is no order for the kinds to be ranked in, so nothing can say that an expansion descends and every spelling is its own kind. Register them with `mkKinds` and pass the result as `kinds`, or declare no types."
        else if unregistered != [ ] then
          throw "gen-scope.buildRoots: `types` declares kind(s) ${builtins.toJSON unregistered} that the supplied `kinds` registry does not carry. An unregistered kind has no rank, so nothing can decide whether an expansion into or out of it descends — register the kind, or use one that is registered."
        else if reservedOffenders != [ ] then
          throw "gen-scope.buildRoots: `edgeGraphs` carries reserved label(s) ${
            builtins.toJSON (map (r: r.label) reservedOffenders)
          }: ${
            prelude.concatMapStringsSep "; " (r: "'${r.label}' is ${r.relation}") reservedOffenders
          }. A reserved label is this library's own name for a relation it privileges, and `edgeGraphs` does not extend to it — supply those edges as the argument named, or relabel them."
        else if duplicateLabels != [ ] then
          throw "gen-scope.buildRoots: `edgeGraphs` claims label(s) ${builtins.toJSON duplicateLabels} more than once. A label names a dimension, not a node, so two contributions under one label is a collision with no order semantics to resolve it — merge them with `overlay` before contributing, or give each its own label."
        else
          # `P` and `I` become contributions IFF their graph is non-empty. Including them
          # unconditionally would emit `decls.__edges.I = [ ]` on every node of every import-free
          # graph — a node-value divergence under an identical id set.
          prelude.optional (nonEmpty parentGraph) {
            label = "P";
            graph = parentGraph;
          }
          ++ prelude.optional (nonEmpty importGraph) {
            label = "I";
            graph = importGraph;
          }
          ++ edgeGraphs;

      # ── THE DECLARED SEQUENCE ──
      # Segments, each ordered by something written down. `parentGraph` and `importGraph` lead
      # because they are the two relations this constructor privileges by name, and their position
      # is THIS SIGNATURE's declaration, fixed for every caller rather than an enumeration artefact.
      # `decls` and `types` are attrset formals, so a vertex known only from their keys has no
      # declared position anywhere: it takes the codepoint TAIL, which is stated rather than left to
      # be whatever `attrNames` happened to return. No sort is introduced — the tail is already in
      # `attrNames` order and the leading segments preserve.
      declaredSequence =
        prelude.concatMap (c: c.graph.vertices) contributions
        ++ builtins.attrNames decls
        ++ builtins.attrNames types;

      # First-occurrence dedup, INDEX-BASED: one `listToAttrs` recording first positions, one pass
      # reading them back. A fold carrying a `seen` attrset copies that attrset per element and is
      # quadratic on both the list and the set axes, while being CHEAPER on lookups — so a
      # lookup-only budget certifies the quadratic form and rejects this one.
      nodeOrder =
        let
          n = builtins.length declaredSequence;
          firstAt = prelude.listToAttrs (
            prelude.genList (i: {
              name = builtins.elemAt declaredSequence i;
              value = i;
            }) n
          );
        in
        prelude.concatMap (
          i:
          let
            v = builtins.elemAt declaredSequence i;
          in
          prelude.optional (firstAt.${v} == i) v
        ) (prelude.genList (i: i) n);

      # The `P` contribution's edges, found by label in the list. There is no label-keyed attrset to
      # subtract from, so `I` reaches `decls.__edges` by the same path as an ordinary label.
      parentEdges =
        let
          ps = prelude.filter (c: c.label == "P") contributions;
        in
        if ps == [ ] then [ ] else (builtins.head ps).graph.edges;

      # Pre-index P edges by source (child → parent), then validate the partial-function constraint.
      # strict=true: deepSeq forces all validations upfront (errors surface immediately).
      # strict=false: validation is lazy (errors surface only when a conflicting node's parent is read).
      parentIndex =
        let
          grouped = builtins.groupBy (e: e.from) parentEdges;
          validated = prelude.mapAttrs (
            from: edges:
            if builtins.length edges > 1 then
              throw "gen-scope: node '${from}' has ${toString (builtins.length edges)} parent edges (P must be a partial function, Neron §2.2). If this node should exist under multiple parents, use distinct IDs (e.g., '${from}@parent1', '${from}@parent2')."
            else
              (builtins.head edges).to
          ) grouped;
        in
        if strict then builtins.deepSeq validated validated else validated;

      # Every contribution except `P`, in contribution order. Duplicate labels are refused above, so
      # this `listToAttrs` cannot collide.
      edgeIndex = prelude.listToAttrs (
        map (c: {
          name = c.label;
          value = builtins.mapAttrs (_: es: map (e: e.to) es) (builtins.groupBy (e: e.from) c.graph.edges);
        }) (prelude.filter (c: c.label != "P") contributions)
      );
    in
    builtins.seq parentIndex {
      inherit nodeOrder;
      # The registry travels WITH the node set, because the evaluator needs the same vocabulary
      # this constructor validated against and a second formal there would be a second declaration.
      # `null` is the no-kinds case and reads as one: an evaluator handed it runs no spawn channel,
      # which is exactly right for a scope whose nodes have no kinds to descend from.
      inherit kinds;
      nodes = prelude.genAttrs nodeOrder (id: {
        inherit id;
        # Checked above against the registry, so this is a lookup rather than an admission.
        type = types.${id} or null;
        parent = parentIndex.${id} or null;
        decls = (decls.${id} or { }) // {
          # Store edge declarations for consumers to build computed attributes from
          __edges = prelude.mapAttrs (_label: idx: idx.${id} or [ ]) edgeIndex;
        };
      });
    };

  # ── THE RETIRED NAME ──
  # A tombstone rather than a silent redirect. `buildRoots` returns a record where this returned a
  # bare node map, so a caller that kept calling the old name would hand a record to an argument
  # expecting a node map — and every ENUMERATING read of that (`allNodes`, `allNodeIds`,
  # `allNodesWhere`) answers `[ "nodeOrder" "nodes" ]` with no error at all. Refusing the name means
  # that call cannot be written, rather than being detected after it is.
  buildNodes = throw "gen-scope: `buildNodes` is retired. Use `buildRoots`, which returns `{ nodes, nodeOrder }` — the node set together with its declared vertex order. Renaming the call is NOT sufficient: the evaluators take that whole record as `scope`, not a bare node map as `roots`, so `eval { roots = buildRoots {…}; }` is refused too.";
in
{
  inherit buildRoots buildNodes;
}
