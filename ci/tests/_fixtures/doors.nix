# THE CLOSED DOORS' FIELD TABLE (den-hoag-7gp66 P1, §v1.2) — every published door whose argument was
# a native closed formal set at b0aea00, with its required and optional fields as that revision's
# `builtins.functionArgs` read them, both lists in codepoint order (the order the shared checks quote
# them in). It is transcribed rather than read off the library on purpose: the cells compare what the
# checked doors do against the surface as it was published, so a door whose fields drifted in the
# migration reds instead of agreeing with itself. 15 record, 5 options, 14 mixed; the minting entry's
# emitter record is the 35th, reached one position in.
#
# `args` supplies every field as a throw naming it, so a door that admits the record and then reads a
# field says which one, and a refusal from the check reads no field at all. `unknown` is built from
# the door's own accepted set, so it cannot be one of them.
let
  doors = {
    acceptanceSignal.required = [
      "baseline"
      "reading"
    ];
    ascend.required = [
      "advance"
      "bottomOf"
      "bound"
      "members"
      "settledBy"
    ];
    buildRoots.optional = [
      "decls"
      "edgeGraphs"
      "importGraph"
      "kinds"
      "parentGraph"
      "strict"
      "types"
    ];
    circular.optional = [ "carrier" ];
    collect.optional = [ "filter" ];
    collectionAttr = {
      required = [
        "extract"
        "traverse"
      ];
      optional = [
        "combine"
        "filter"
      ];
    };
    decisionFindings.required = [
      "decision"
      "nodeIds"
      "resolutional"
    ];
    eval = {
      required = [
        "attributes"
        "scope"
      ];
      optional = [
        "decision"
        "declaredDependencies"
        "parseParent"
        "prior"
        "provenance"
      ];
    };
    evalDebug = {
      required = [
        "attributes"
        "scope"
      ];
      optional = [ "parseParent" ];
    };
    evalWarm = {
      required = [
        "attributes"
        "decision"
        "prior"
        "scope"
      ];
      optional = [
        "parseParent"
        "provenance"
      ];
    };
    foldContributions.required = [
      "contributions"
      "init"
      "model"
      "op"
    ];
    foldEquations = {
      required = [
        "declaredDependencies"
        "parseParent"
        "schedule"
        "scope"
      ];
      optional = [ "settings" ];
    };
    "inherit'" = {
      required = [ "resolve" ];
      optional = [ "_visited" ];
    };
    inheritAll = {
      required = [ "extract" ];
      optional = [
        "_visited"
        "combine"
      ];
    };
    inheritSet = {
      required = [ "extract" ];
      optional = [
        "_visited"
        "eq"
      ];
    };
    leastModel.required = [
      "program"
      "seed"
    ];
    leastModelRounds.required = [
      "program"
      "seed"
    ];
    leastModelUnary.required = [
      "program"
      "seed"
    ];
    mintStrata.required = [
      "emitters"
      "kinds"
    ];
    mkDecision.required = [
      "isClean"
      "reusable"
    ];
    mkFacade.required = [
      "get"
      "nodeIds"
      "resolutional"
    ];
    mkKind = {
      required = [ "name" ];
      optional = [
        "below"
        "dedupKey"
        "fold"
        "nta"
        "resolve"
        "spawns"
      ];
    };
    mkProgram.required = [ "rules" ];
    mkRule = {
      required = [ "head" ];
      optional = [
        "neg"
        "pos"
      ];
    };
    query = {
      required = [ "dataFilter" ];
      optional = [
        "_seen"
        "importShadowsParent"
        "localShadowsImport"
        "transitiveImports"
      ];
    };
    queryAll = {
      required = [ "dataFilter" ];
      optional = [
        "_seen"
        "transitiveImports"
      ];
    };
    queryReverse = {
      required = [ "dataFilter" ];
      optional = [
        "_seen"
        "transitive"
      ];
    };
    resolve.optional = [
      "importShadowsParent"
      "imported"
      "inherited"
      "local"
      "localShadowsImport"
    ];
    resolveClaims = {
      required = [
        "claims"
        "kinds"
      ];
      optional = [ "ctx" ];
    };
    seamAcquisitionDefect.required = [
      "declared"
      "reader"
      "target"
    ];
    solve.required = [
      "interpretation"
      "program"
    ];
    stratify.required = [
      "advance"
      "describe"
      "schedule"
      "seed"
      "stratumOf"
      "within"
    ];
    subtypeOf.optional = [ "eq" ];
    wellFoundedModel.required = [
      "interpretation"
      "program"
    ];
  };
in
builtins.mapAttrs (
  name: d:
  let
    required = d.required or [ ];
    optional = d.optional or [ ];
    accepted = builtins.sort builtins.lessThan (required ++ optional);
    reach = f: throw "reached:${f}";
  in
  rec {
    inherit required optional accepted;
    class =
      if optional == [ ] then
        "record"
      else if required == [ ] then
        "options"
      else
        "mixed";
    door = "gen-scope.${name}";
    unknown = "_" + builtins.concatStringsSep "_" accepted + "_";
    args = builtins.listToAttrs (
      map (f: {
        name = f;
        value = reach f;
      }) accepted
    );
    missing = builtins.head required;
    withoutMissing = builtins.removeAttrs args [ missing ];
    withUnknown = args // {
      ${unknown} = reach unknown;
    };
  }
) doors
