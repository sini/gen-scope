{
  prelude,
  graph,
  identity,
  algebra,
}@args:
let
  modules = import ./modules.nix args;
in
{
  inherit (modules.acceptance)
    acceptanceSignal
    signalNames
    verifiedDepth
    ;
  inherit (modules.algebraicGraph)
    circuit
    clique
    connect
    edge
    edges
    empty
    forest
    gmap
    hasEdge
    hasVertex
    induce
    overlay
    overlays
    path
    removeEdge
    removeVertex
    star
    transpose
    tree
    vertex
    vertices
    ;
  inherit (modules.ascent)
    ascend
    ;
  inherit (modules.buildRoots)
    buildNodes
    buildRoots
    mintAttachmentId
    parseParent
    ;
  inherit (modules.calculus)
    labelOrder
    neron
    resolve
    wellFormed
    wfl
    ;
  inherit (modules.cascade)
    mkClaim
    mkKind
    mkKinds
    resolveClaims
    ;
  inherit (modules.engine)
    foldContributions
    provenanceFor
    solve
    ;
  inherit (modules.eval)
    decodeNta
    eval
    evalDebug
    evalWarm
    mintNtaId
    seamAcquisitionDefect
    ;
  inherit (modules.foldEquations)
    foldEquations
    ;
  inherit (modules.folds)
    folds
    ;
  inherit (modules.interface)
    coldDecision
    decisionFindings
    facadeNames
    mkDecision
    mkFacade
    ;
  inherit (modules.leastModel)
    armFor
    armNames
    forceFields
    leastModel
    leastModelRounds
    leastModelUnary
    ;
  inherit (modules.mint)
    argumentBinding
    mintStrata
    ;
  inherit (modules.program)
    mkProgram
    mkRule
    ;
  inherit (modules.queries)
    ancestors
    children
    childrenIds
    descendants
    isAncestor
    isDescendant
    nodesByType
    parent
    siblings
    ;
  inherit (modules.resolve)
    ambiguous
    circular
    collect
    collectByLabel
    collectByType
    collectImports
    collectionAttr
    followEdge
    inherit'
    inheritAll
    inheritSet
    query
    queryAll
    queryReverse
    shadow
    subtypeOf
    visibleFrom
    ;
  inherit (modules.stratify)
    stratify
    ;
  inherit (modules.structural)
    childBearing
    childDepth
    edgePrefix
    flattenChildren
    resolutionalNames
    structural
    ;
  inherit (modules.wellFounded)
    Pos
    reduct
    verdictNames
    wellFoundedModel
    ;
}
