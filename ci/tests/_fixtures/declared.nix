# A CONTRACTED DECLARED RELATION over a materialized scope, from the `node -> [ ids ]` map a fixture
# writes.
#
# Every entry taking a declared relation admits only what `gen-graph.mkDeclaredEdges` minted, so a
# fixture cannot hand one in as a bare function. What it writes instead is the index the constructor
# normalizes to, and this is the ONE place the suite turns such a map into a contracted value: a
# second construction idiom would be a second reading of the same contract, free to drift from this
# one while both suites stayed green.
#
# THE MEMBERSHIP AUTHORITY IS THE SCOPE'S OWN NODE MAP, so these fixtures go THROUGH the
# constructor's registration check rather than around it — a target no `buildRoots` call declared is
# refused at construction here exactly as it would be in a consumer. A fixture declaring an edge to
# a SPAWNED node cannot use this helper and should not: such a node is absent from the registration
# set by definition, and `mkSpawnedNodeRef` is its route (`_fixtures/circular-nta.nix`).
{ genGraph, scope }:
rel:
genGraph.mkDeclaredEdges (
  builtins.mapAttrs (
    _: ids: map (genGraph.mkNodeRef { isRegistered = id: scope.nodes ? ${id}; }) ids
  ) rel
)
