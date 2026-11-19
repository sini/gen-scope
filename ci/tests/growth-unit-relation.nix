# THE REUSE RELATION OVER GROWTH UNITS — what `accessor.dependencies` answers for a node the substrate
# grows from a host (an `nta` child, an on-demand `nta` child, a `spawns` child), and what the
# evaluator's reuse vocabulary answers for a node outside the enumerated set.
#
# A grown child's record is a function of its host's evaluation: an `nta` seed is a sub-value of a
# host attribute, and a spawn builder reads through the host's handle. So the child depends on its
# host, and the host's structural edge to it is not an edge (an armed reader hands the host the record
# its own evaluation built). A registered child keeps the parent -> child edge it always had.
#
# The cycle cells read `graph.cycles` over the published relation under four declaration variants:
#   hr   a host reads its own `nta` child through `getNta` and declares host -> child;
#   c6   a grown child reads its host and declares child -> host;
#   all  both;
#   ae   a host `r2` reads `z`, and `z` reads `r2`'s grown child. The attribute instances are acyclic,
#        but no node-level relation is both sound and acyclic: an edit to `z` must reach `r2`, and an
#        edit to `r2` moves the child `z` reads. The relation carries that cycle and names it, and an
#        acyclic consumer refuses it by name; the consumer's own suite pins the refusal.
#
# The consumer's warm plane (warm against a fresh fold) is the consumer's suite; these cells pin the
# relation it is handed.
{
  genScope,
  genGraph,
  genPreludeLib,
  ...
}:
let
  prelude = genPreludeLib;
  inherit (builtins) head isAttrs;
  addr = def: at: {
    attr = "defs";
    inherit def at;
  };
  nta =
    host: name:
    genScope.mintNtaId {
      inherit host name;
      group = "g";
      key = "k";
    };
  grow =
    self: id:
    let
      d = self.get id "defs";
    in
    if d != [ ] && isAttrs (head d) && head d ? s then { g.k = [ (addr 0 [ "s" ]) ]; } else { };
  copy = h: id: { "${id}-c".decls.defs = (h.node id).decls.defs; };
  kinds = genScope.mkKinds [
    (genScope.mkKind { } "plain")
    (genScope.mkKind { nta.x = grow; } "host")
    (genScope.mkKind {
      nta.y = grow;
      ntaOnDemand = [ "y" ];
    } "lazy")
    (genScope.mkKind {
      below = [ "plain" ];
      spawns.plain = copy;
    } "sp")
  ];
  res = name: compute: {
    inherit name compute;
    kind = "synthesized";
    readsAttrs = [ ];
    stratum = "resolution";
  };
  rootsParent = {
    "p@c" = "p";
  };
  parseParent =
    id:
    let
      d = genScope.decodeNta id;
      m = builtins.match "(.*)-c" id;
    in
    if d != null then
      d.host
    else if m != null then
      head m
    else
      rootsParent.${id} or null;
  hChild = nta "h" "x";
  hrChild = nta "hr" "x";
  zChild = nta "r2" "x";
  equations = variant: roots: {
    children = {
      name = "children";
      kind = "nta";
      readsAttrs = [ ];
      stratum = "structural";
      compute = _: id: prelude.filterAttrs (_: n: (n.parent or null) == id) roots.nodes;
    };
    imports = {
      name = "imports";
      kind = "synthesized";
      readsAttrs = [ ];
      stratum = "structural";
      compute = _: _: [ ];
    };
    defs = res "defs" (
      self: id:
      let
        d = (self.node id).decls;
      in
      if d ? seed then map (e: e.value) d.seed else d.defs or [ ]
    );
    hostDefs = res "hostDefs" (
      self: id:
      if id == hChild && (variant == "c6" || variant == "all") then self.get "h" "defs" else null
    );
    hostAgg = res "hostAgg" (
      self: id:
      if id == "hr" && (variant == "hr" || variant == "all") then self.getNta "x" "g" "k" "defs" else null
    );
    zRead = res "zRead" (self: id: if id == "z" then self.get zChild "defs" else null);
    aRead = res "aRead" (
      self: id: if id == "r2" && variant == "ae" then self.get "z" "zRead" else null
    );
  };
  declsAt =
    e:
    {
      r.defs = [ { s = 1; } ];
      o.defs = [ { s = 1; } ];
      q.defs = [ 1 ];
      p.defs = [ 1 ];
      "p@c".defs = [ 5 ];
      h.defs = [ { s = 1; } ];
      hr.defs = [ { s = 1; } ];
      r2.defs = [ { s = 1; } ];
      z.defs = [ 0 ];
    }
    // e;
  types = {
    r = "host";
    o = "lazy";
    q = "sp";
    p = "plain";
    "p@c" = "plain";
    h = "host";
    hr = "host";
    r2 = "host";
    z = "plain";
  };
  scopeAt =
    e:
    genScope.buildRoots {
      inherit kinds types;
      decls = declsAt e;
      parentGraph = genScope.overlay (genScope.vertex "r") (
        genScope.edge {
          from = "p@c";
          to = "p";
        }
      );
    };
  declaredFor =
    variant:
    genGraph.mkDeclaredEdges (
      builtins.mapAttrs (_: map (genGraph.mkNodeRef (_: true))) (
        {
          z = [ zChild ];
        }
        // (if variant == "c6" || variant == "all" then { ${hChild} = [ "h" ]; } else { })
        // (if variant == "hr" || variant == "all" then { hr = [ hrChild ]; } else { })
        // (if variant == "ae" then { r2 = [ "z" ]; } else { })
      )
    );
  foldAt =
    variant: e:
    let
      s = scopeAt e;
    in
    genScope.foldEquations { } {
      scope = s;
      schedule.equations = equations variant s;
      inherit parseParent;
      declaredDependencies = declaredFor variant;
    };
  cold = variant: foldAt variant { };
  deps = variant: (cold variant).accessor.dependencies;
  cyclesOf =
    variant:
    let
      a = (cold variant).accessor;
    in
    genGraph.cycles (a // { edges = a.dependencies; });
  onDemand = nta "o" "y";
in
{
  flake.tests.growth-unit-relation = {
    # A grown child depends on its host; the host does not depend on it.
    test-an-nta-child-depends-on-its-host = {
      expr = deps "all" (nta "r" "x");
      expected = [ "r" ];
    };
    test-a-host-does-not-depend-on-its-grown-child = {
      expr = deps "all" "r";
      expected = [ ];
    };
    test-a-spawned-child-depends-on-its-host = {
      expr = deps "all" "q-c";
      expected = [ "q" ];
    };
    # The control: a registered child keeps the parent -> child edge.
    test-a-registered-child-keeps-its-parent-edge = {
      expr = deps "all" "p";
      expected = [ "p@c" ];
    };
    # A node outside the enumerated set is in no published relation, so nothing of it is reusable.
    test-an-on-demand-child-has-no-reuse-vocabulary = {
      expr = (cold "all").eval.resolutional onDemand;
      expected = [ ];
    };
    test-an-enumerated-node-keeps-the-full-reuse-vocabulary = {
      expr = (cold "all").eval.resolutional "o";
      expected = [
        "aRead"
        "defs"
        "hostAgg"
        "hostDefs"
        "zRead"
      ];
    };
    # A decision that calls every node but the edited host clean, and reuses whatever the prior's
    # vocabulary admits: the on-demand child recomputes from the moved host.
    test-an-on-demand-child-recomputes-under-a-warm-decision = {
      expr =
        let
          prior = (cold "all").eval;
        in
        (genScope.evalWarm { } {
          scope = scopeAt { o.defs = [ { s = 2; } ]; };
          inherit (cold "all") attributes;
          inherit prior;
          decision = genScope.mkDecision {
            isClean = id: id != "o";
            reusable = prior.resolutional;
          };
        }).get
          onDemand
          "defs";
      expected = [ 2 ];
    };
    # Host reads child (declared host -> child), child reads host (declared child -> host), and both:
    # inside a growth unit the relation points only up, so none of the three is cyclic.
    test-a-host-reading-its-child-is-acyclic = {
      expr = cyclesOf "hr";
      expected = [ ];
    };
    test-a-child-reading-its-host-is-acyclic = {
      expr = cyclesOf "c6";
      expected = [ ];
    };
    test-host-and-child-reading-each-other-is-acyclic = {
      expr = cyclesOf "all";
      expected = [ ];
    };
    # The host's declared read of its child is reach, not an edge to the child.
    test-a-host-reading-its-child-carries-no-edge-down = {
      expr = {
        child = deps "hr" hrChild;
        host = deps "hr" "hr";
      };
      expected = {
        child = [ "hr" ];
        host = [ ];
      };
    };
    # The price: a cycle the attribute instances do not have, carried and named rather than dropped.
    test-a-host-reading-a-reader-of-its-child-is-a-named-cycle = {
      expr = cyclesOf "ae";
      expected = [
        zChild
        "r2"
        "z"
      ];
    };
    # The control for the reserved `nta` key space: a spawned key that does not decode builds.
    test-a-spawned-key-outside-the-nta-space-builds = {
      expr =
        (genScope.eval { } (cold "all").attributes (
          genScope.buildRoots {
            kinds = genScope.mkKinds [
              (genScope.mkKind { } "plain")
              (genScope.mkKind {
                below = [ "plain" ];
                spawns.plain = _: id: { "${id}-c".decls.defs = [ 1 ]; };
              } "spn")
            ];
            types.sn = "spn";
            decls.sn.defs = [ 0 ];
            parentGraph = genScope.vertex "sn";
          }
        )).allNodeIds;
      expected = [
        "sn"
        "sn-c"
      ];
    };
  };
}
