# THE REGISTRATION FORCE'S SUBJECT — O10, O11, O12.
#
# `gen-graph.mkDeclaredEdges` deep-forces the relation it is handed, and the depth is its contract. The
# force's SUBJECT is the relation and nothing else: node content, a caller's configuration and the
# content a delivery class carries live in the same evaluation, beside the relation, and must never be
# reached by it. A landing that deep-forced the context instead would change the cost class of the
# whole evaluation, silently until benchmarked, so the boundary is pinned here rather than argued.
#
# EACH CELL IS A PAIR, AND THE PAIR IS WHAT MAKES IT A MEASUREMENT. The boundary cell puts a throw in
# a value the relation sits beside and asserts the fold answers. Its control puts THE SAME throw in an
# edge-list entry, in a field the accept-list does not read, and asserts the fold refuses at
# registration: the force is live exactly where it is owed. A third cell asserts the throw is
# reachable from the fold's own context, so a force applied to the context would meet it. Without
# that, a green boundary cell could be a seed nothing could reach.
#
# Both declared forms are covered: the attrset form through the suite's one construction idiom
# (`_fixtures/declared.nix`), the list form through the constructor directly.
{
  genScope,
  genGraph,
  ...
}:
let
  inherit (genGraph) mkDeclaredEdges mkNodeRef declaredEdgesFindings;

  # Deep-forces a value: does anything below it throw?
  didThrow = v: !(builtins.tryEval (builtins.deepSeq v true)).success;

  forced = throw "forced-content";

  # THE THREE CARRIERS, each a value a node holds and the relation does not.
  carriers = {
    # O10: node content is a throwing thunk.
    content = {
      content = forced;
    };
    # O11: a user-config-shaped attrset whose throw sits below its top level.
    config = {
      config = {
        name = "parent";
        enable = true;
        secret.deep = forced;
      };
    };
    # O12: content carried by a delivery class, as a list of modules.
    delivery = {
      classes.nixos = [ { imports = [ forced ]; } ];
    };
  };

  scopeWith =
    carrier:
    genScope.buildRoots {
      kinds = genScope.mkKinds [ (genScope.mkKind { } "host") ];
      parentGraph = genScope.edge {
        from = "child";
        to = "parent";
      };
      decls = {
        parent.v = 10;
        child = {
          v = 1;
        }
        // carrier;
      };
      types = {
        parent = "host";
        child = "host";
      };
    };

  equations = {
    self-v = {
      name = "self-v";
      kind = "synthesized";
      readsAttrs = [ ];
      stratum = "resolution";
      compute = self: id: (self.node id).decls.v;
    };
    children = {
      name = "children";
      kind = "nta";
      readsAttrs = [ ];
      stratum = "structural";
      compute = _self: _id: { };
    };
  };

  fold =
    scope: declaredDependencies:
    genScope.foldEquations { } {
      inherit scope declaredDependencies;
      schedule = { inherit equations; };
      parseParent = id: scope.nodes.${id}.parent or null;
    };

  ref = scope: mkNodeRef (id: scope.nodes ? ${id});

  # The two declared forms of the honest relation `child -> parent`.
  attrsetForm =
    scope: import ./_fixtures/declared.nix { inherit genGraph scope; } { child = [ "parent" ]; };
  listForm =
    scope:
    mkDeclaredEdges [
      {
        from = ref scope "child";
        to = ref scope "parent";
      }
    ];

  # The fold answers: a node attribute, the gate's relation and the accessor's union, all read.
  answers =
    ctx:
    let
      v = [
        (ctx.eval.get "child" "self-v")
        (ctx.declaredDependencies.dependencies "child")
        (ctx.accessor.dependencies "child")
      ];
    in
    builtins.tryEval (builtins.deepSeq v v);

  answered = {
    success = true;
    value = [
      1
      [ "parent" ]
      [ "parent" ]
    ];
  };

  # The same carrier moved INTO an edge-list entry, in a field the accept-list does not read, so the
  # constructor's force is the only thing that can reach it. List form: an extra field on the element.
  # Attrset form: an extra field on the reference.
  inListForm = scope: carrier: [
    (
      {
        from = ref scope "child";
        to = ref scope "parent";
      }
      // carrier
    )
  ];
  inAttrsetForm = scope: carrier: { child = [ (ref scope "parent" // carrier) ]; };

  # The edge-list control: the accept-list admits the relation, and the fold refuses at registration.
  firesInEdgeList = scope: raw: {
    findings = declaredEdgesFindings raw;
    folds = (builtins.tryEval (builtins.seq (fold scope (mkDeclaredEdges raw)) true)).success;
  };
  fired = {
    findings = [ ];
    folds = false;
  };

  cellsFor =
    o: carrierName:
    let
      carrier = carriers.${carrierName};
      scope = scopeWith carrier;
    in
    {
      "test-${o}-a-${carrierName}-throw-folds-green-attrset-form" = {
        expr = answers (fold scope (attrsetForm scope));
        expected = answered;
      };
      "test-${o}-a-${carrierName}-throw-folds-green-list-form" = {
        expr = answers (fold scope (listForm scope));
        expected = answered;
      };
      "test-control-${o}-throw-in-edge-list-fires-attrset-form" = {
        expr = firesInEdgeList scope (inAttrsetForm scope carrier);
        expected = fired;
      };
      "test-control-${o}-throw-in-edge-list-fires-list-form" = {
        expr = firesInEdgeList scope (inListForm scope carrier);
        expected = fired;
      };
      # The seed is live: a force over the fold's own context, which the relation sits beside, would
      # meet it.
      "test-control-${o}-the-${carrierName}-throw-is-reachable-from-the-context" = {
        expr = didThrow (fold scope (attrsetForm scope)).roots;
        expected = true;
      };
    };
in
{
  flake.tests.thunk-boundary =
    cellsFor "o10" "content" // cellsFor "o11" "config" // cellsFor "o12" "delivery";
}
