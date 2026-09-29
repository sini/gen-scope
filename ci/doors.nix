# THE DOOR TABLE (den-hoag-7gp66 P2 — `prelude.door`, R7 argument structure / R5 field closure) —
# every published step of gen-scope that takes a RECORD, read by `ci/tests/door-checks.nix`
# (catchability, contracts, the guard, G3) and `ci/tests-error.nix`'s `door-checks` (the refusal
# bytes). It lives outside ./tests so the harness does not collect it as a test module.
#
# After P2 a door is one of two steps (R7). An OPTIONS step is a closed set, first in the call: a
# row is the door and its `optional` names. A RECORD step is an open data record (R5): a row is the
# step as applied (every earlier operand already supplied), its `required` fields, a `good` record,
# the field `drop` removes for the missing-field cell, and — for a record behind an options step —
# `guardedBy`, the options row whose names the record refuses (`optionsStep`, G10). `step good` must
# answer: that is each row's live control, so a refusal below is the check firing and not a broken
# fixture.
#
# The positional entries (`solve`, `wellFoundedModel`, `leastModel`, `leastModelUnary`,
# `leastModelRounds`, `mkProgram`, `mintStrata`, `foldContributions`) carry no row: their arity is
# structural and they have no field check.
{ genScope, genGraph }:
let
  S = genScope;

  # a imports b, b imports c; a's parent is root. The query family's options are read over it.
  roots = S.buildRoots {
    parentGraph = S.edge {
      from = "a";
      to = "root";
    };
    importGraph = S.overlays [
      (S.edge {
        from = "a";
        to = "b";
      })
      (S.edge {
        from = "b";
        to = "c";
      })
    ];
    decls = {
      root.val = "from-root";
      a = { };
      b.val = "from-b";
      c = {
        val = "from-c";
        extra = "c-extra";
      };
    };
    types = { };
  };
  attributes = {
    children = _: id: if id == "root" then { inherit (roots.nodes) a; } else { };
    imports = self: id: (self.node id).decls.__edges.I or [ ];
  };
  ev = S.eval { } attributes roots;

  # The cold fold's operands, over a one-node scope and the empty declared relation.
  foldScope = S.buildRoots {
    parentGraph = S.vertex "n";
    decls.n.v = 1;
    types.n = "host";
    kinds = S.mkKinds [ (S.mkKind { } "host") ];
  };
  foldRecord = {
    scope = foldScope;
    parseParent = _: null;
    schedule.equations.v = {
      name = "v";
      kind = "synthesized";
      readsAttrs = [ ];
      stratum = "resolution";
      compute = self: id: (self.node id).decls.v;
    };
    declaredDependencies = import ./tests/_fixtures/declared.nix {
      inherit genGraph;
      scope = foldScope;
    } { };
  };

  warmRecord = {
    scope = roots;
    inherit attributes;
    prior = null;
    decision = S.coldDecision;
  };
in
{
  inherit
    ev
    roots
    attributes
    foldRecord
    warmRecord
    ;

  options = {
    ambiguous.optional = [
      "_seen"
      "transitiveImports"
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
    collectionAttr.optional = [
      "combine"
      "filter"
    ];
    eval.optional = [
      "decision"
      "declaredDependencies"
      "parseParent"
      "prior"
      "provenance"
    ];
    evalDebug.optional = [ "parseParent" ];
    evalWarm.optional = [
      "parseParent"
      "provenance"
    ];
    foldEquations.optional = [ "settings" ];
    "inherit'".optional = [ "_visited" ];
    inheritAll.optional = [
      "_visited"
      "combine"
    ];
    inheritSet.optional = [
      "_visited"
      "eq"
    ];
    mkKind.optional = [
      "below"
      "dedupKey"
      "fold"
      "kindValue"
      "nta"
      "resolve"
      "spawns"
    ];
    mkRule.optional = [
      "neg"
      "pos"
    ];
    query.optional = [
      "_seen"
      "importShadowsParent"
      "localShadowsImport"
      "transitiveImports"
    ];
    queryAll.optional = [
      "_seen"
      "transitiveImports"
    ];
    queryReverse.optional = [
      "_seen"
      "transitive"
    ];
    resolve.optional = [
      "importShadowsParent"
      "imported"
      "inherited"
      "local"
      "localShadowsImport"
    ];
    resolveClaims.optional = [ "ctx" ];
    subtypeOf.optional = [ "eq" ];
  };

  # The options doors whose next step is not a record: positional operands (or nothing) follow.
  notChained = [
    "ambiguous"
    "buildRoots"
    "circular"
    "collect"
    "collectionAttr"
    "eval"
    "evalDebug"
    "inherit'"
    "inheritAll"
    "inheritSet"
    "mkKind"
    "mkRule"
    "query"
    "queryAll"
    "queryReverse"
    "resolve"
    "resolveClaims"
    "subtypeOf"
  ];

  records = {
    acceptanceSignal = {
      step = S.acceptanceSignal;
      required = [
        "baseline"
        "reading"
      ];
      good = {
        baseline = null;
        reading = null;
      };
      drop = "reading";
    };
    ascend = {
      step = S.ascend;
      required = [
        "advance"
        "bottomOf"
        "bound"
        "members"
        "settledBy"
      ];
      good = {
        members = [ ];
        bottomOf = _: 0;
        advance = v: v;
        settledBy =
          _: _: _:
          true;
        bound = [ ];
      };
      drop = "bound";
    };
    connect = {
      step = S.connect;
      required = [
        "from"
        "to"
      ];
      good = {
        from = S.vertex "a";
        to = S.vertex "b";
      };
      drop = "to";
    };
    decisionFindings = {
      step = S.decisionFindings;
      required = [
        "decision"
        "nodeIds"
        "resolutional"
      ];
      good = {
        decision = S.coldDecision;
        nodeIds = [ ];
        resolutional = _: [ ];
      };
      drop = "nodeIds";
    };
    edge = {
      step = S.edge;
      required = [
        "from"
        "to"
      ];
      good = {
        from = "a";
        to = "b";
      };
      drop = "from";
    };
    evalWarm = {
      step = S.evalWarm { };
      required = [
        "attributes"
        "decision"
        "prior"
        "scope"
      ];
      good = warmRecord;
      drop = "decision";
      guardedBy = "evalWarm";
    };
    foldEquations = {
      step = S.foldEquations { };
      required = [
        "declaredDependencies"
        "parseParent"
        "schedule"
        "scope"
      ];
      good = foldRecord;
      drop = "schedule";
      guardedBy = "foldEquations";
    };
    mintNtaId = {
      step = S.mintNtaId;
      required = [
        "host"
        "name"
        "group"
        "key"
      ];
      good = {
        host = "h";
        name = "n";
        group = "g";
        key = "k";
      };
      drop = "group";
    };
    mkDecision = {
      step = S.mkDecision;
      required = [
        "isClean"
        "reusable"
      ];
      good = S.coldDecision;
      drop = "reusable";
    };
    mkFacade = {
      step = S.mkFacade;
      required = [
        "get"
        "nodeIds"
        "resolutional"
      ];
      good = {
        get = null;
        nodeIds = null;
        resolutional = null;
      };
      drop = "get";
    };
    seamAcquisitionDefect = {
      step = S.seamAcquisitionDefect;
      required = [
        "declared"
        "reader"
        "target"
      ];
      good = {
        reader = "a";
        target = "a";
        declared = [ ];
      };
      drop = "target";
    };
    shadow = {
      step = S.shadow;
      required = [
        "inner"
        "outer"
      ];
      good = {
        inner = { };
        outer = { };
      };
      drop = "outer";
    };
    stratify = {
      step = S.stratify;
      required = [
        "advance"
        "describe"
        "schedule"
        "seed"
        "stratumOf"
        "within"
      ];
      good = {
        schedule = [ ];
        stratumOf = _: 0;
        within = _: _: true;
        seed = [ ];
        advance = _: {
          emitted = [ ];
          settled = [ ];
        };
        describe = _: "";
      };
      drop = "seed";
    };
  };
}
