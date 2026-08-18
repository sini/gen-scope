# Scope graph construction: produces minimal root descriptors from algebraic graphs.
#
# Output shape: { id = { id, type, parent, decls }; }
# No pre-indexed edges — relationships are computed via attributes.
# Edge declarations stored in decls.__edges for consumers to use in attribute definitions.
#
# `edgeGraphs` is the caller's OWN label space and it is open on every label except `P` and `I`,
# which are this constructor's names for the containment and import relations. Those two are refused
# by name at the entry — see the reservation below.
{ prelude }:
let
  graph = import ./graph.nix;

  buildNodes =
    {
      parentGraph ? graph.empty,
      importGraph ? graph.empty,
      edgeGraphs ? { },
      decls ? { },
      types ? { },
      strict ? true,
    }:
    let
      # ── THE RESERVED LABELS, REFUSED BY NAME ──
      # `P` and `I` are this constructor's OWN names for containment and import, and the merge below
      # is last-wins: a caller offering either label would REPLACE the argument it passed in the same
      # call, silently and with nothing said. Neither is an ordinary label — the partial-function
      # guard is stated of `P` by name (Neron 2015 §2.2), and the label index is built from every
      # label except it — so a caller's graph arriving under one of these names is read as a relation
      # this library privileges rather than as the labelled edges the caller declared. A relation
      # important enough to carry a named arity refusal is important enough to refuse being
      # overwritten, so the reservation is a refusal AT THE ENTRY rather than a convention a caller is
      # trusted to know. It is unconditional: a reservation that lapsed when `parentGraph` happened to
      # be empty would leave the caller's graph silently PROMOTED to the privileged relation instead
      # of silently replacing it, which is the same defect entered from the other side.
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
      reservedOffenders = prelude.filter (r: edgeGraphs ? ${r.label}) reservedLabels;

      # Merge all edge graphs for vertex collection. The caller's labels merge LAST, which is what
      # the refusal above answers: this `//` settles a collision by position and reports nothing.
      allEdgeGraphs =
        if reservedOffenders != [ ] then
          throw "gen-scope.buildNodes: `edgeGraphs` carries reserved label(s) ${
            builtins.toJSON (map (r: r.label) reservedOffenders)
          }: ${
            prelude.concatMapStringsSep "; " (r: "'${r.label}' is ${r.relation}") reservedOffenders
          }. A reserved label is this library's own name for a relation it privileges, and `edgeGraphs` does not extend to it — supply those edges as the argument named, or relabel them."
        else
          (prelude.optionalAttrs (parentGraph.vertices != [ ] || parentGraph.edges != [ ]) {
            P = parentGraph;
          })
          // (prelude.optionalAttrs (importGraph.vertices != [ ] || importGraph.edges != [ ]) {
            I = importGraph;
          })
          // edgeGraphs;

      # Collect all vertices: from edge graphs + decls + types keys (O(n) dedup via attrset)
      allVertices = builtins.attrNames (
        builtins.listToAttrs (
          prelude.concatMap (
            label:
            map (v: {
              name = v;
              value = true;
            }) allEdgeGraphs.${label}.vertices
          ) (builtins.attrNames allEdgeGraphs)
          ++ map (v: {
            name = v;
            value = true;
          }) (builtins.attrNames decls)
          ++ map (v: {
            name = v;
            value = true;
          }) (builtins.attrNames types)
        )
      );

      # Pre-index P edges by source (child → parent).
      # Uses groupBy (O(E)) then validates partial function constraint.
      # strict=true: deepSeq forces all validations upfront (errors surface immediately).
      # strict=false: validation is lazy (errors surface only when conflicting node's parent is accessed).
      parentIndex =
        let
          grouped = builtins.groupBy (e: e.from) (allEdgeGraphs.P.edges or [ ]);
          validated = prelude.mapAttrs (
            from: edges:
            if builtins.length edges > 1 then
              throw "gen-scope: node '${from}' has ${toString (builtins.length edges)} parent edges (P must be a partial function, Neron §2.2). If this node should exist under multiple parents, use distinct IDs (e.g., '${from}@parent1', '${from}@parent2')."
            else
              (builtins.head edges).to
          ) grouped;
        in
        if strict then builtins.deepSeq validated validated else validated;

      # Pre-index all non-P edges by source, grouped by label.
      # Uses groupBy (O(E)) instead of foldl'+// (O(E²)).
      edgeIndex = prelude.mapAttrs (
        _label: g:
        let
          grouped = builtins.groupBy (e: e.from) g.edges;
        in
        builtins.mapAttrs (_: es: map (e: e.to) es) grouped
      ) (builtins.removeAttrs allEdgeGraphs [ "P" ]);
    in
    builtins.seq parentIndex (
      prelude.genAttrs allVertices (id: {
        inherit id;
        type = types.${id} or null;
        parent = parentIndex.${id} or null;
        decls = (decls.${id} or { }) // {
          # Store edge declarations for consumers to build computed attributes from
          __edges = prelude.mapAttrs (label: idx: idx.${id} or [ ]) edgeIndex;
        };
      })
    );
in
{
  inherit buildNodes;
}
