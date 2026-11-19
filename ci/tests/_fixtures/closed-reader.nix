# THE CLOSED BODY READER'S ROUTE TABLES — the fixtures `tests/codomain-closed-reader.nix` asserts.
#
# Every route is one verdict, classified without aborting: "ABSENT" (the reader lacks the name, `?`),
# "REFUSED" (`tryEval` caught a throw), "NO_EVAL" / "NO_MEMO" (a record carries no such field), else
# the value. A route is read in six modes: cold, warm after its target's edit, and a fresh cold fold
# of the edited scope, each under the empty and under the declared relation. Warm parity holds where
# the warm column equals the fresh cold one; a stale serve is a warm column equal to the cold one.
#
# THE WARM PASS is `evalWarm`, armed with the fold's relation, over the cold fold's facade, with the
# decision an incremental plane derives: the edited roots and their reverse cone over the fold's own
# dependency union (`accessor.dependencies`, declared ∪ structural) are dirty, every other node is
# clean and serves the prior's resolutional attributes. A clean reader serves its prior answer, so an
# undeclared read the cold fold refused is refused warm, and one it admitted would be served stale.
{ genScope, genGraph }:
let
  try =
    v:
    let
      r = builtins.tryEval (builtins.deepSeq v v);
    in
    if r.success then r.value else "REFUSED";
  has = s: n: s ? ${n};
  res = name: compute: {
    inherit name compute;
    kind = "synthesized";
    readsAttrs = [ ];
    stratum = "resolution";
  };
  kept = [
    "_childOrder"
    "allNodeIds"
    "get"
    "getHostAt"
    "getNta"
    "getRepresentative"
    "node"
  ];
  marker = [ "reader" ];
  tombs = [
    "_childRecords"
    "_childSet"
    "_walkFrom"
    "allNodes"
    "allNodesWhere"
    "decisionFindings"
    "facade"
    "nodesOfType"
    "projectionFindings"
    "provenance"
    "resolutional"
    "served"
    "structuralAttributes"
    "structuralEdges"
    "subtreeOf"
  ];
  # Per name: on the reader (`?`), and readable to WHNF (`tryEval` of `typeOf`).
  probeNames =
    self:
    builtins.listToAttrs (
      map (n: {
        name = n;
        value = {
          present = has self n;
          readable = if has self n then (builtins.tryEval (builtins.typeOf self.${n})).success else "ABSENT";
        };
      }) (kept ++ marker ++ tombs)
    );
  rel = r: genGraph.mkDeclaredEdges (builtins.mapAttrs (_: map (genGraph.mkNodeRef (_: true))) r);
  emptyRel = rel { };

  # The warm pass over a fold `ctx`, its roots edited by `edits` (`id -> decls overlay`).
  warmOf =
    ctx: edits:
    let
      deps = ctx.accessor.dependencies;
      grow =
        d:
        let
          d' = prelude.unique (
            d ++ builtins.filter (n: builtins.any (t: builtins.elem t d) (deps n)) ctx.accessor.nodes
          );
        in
        if builtins.length d' == builtins.length d then d else grow d';
      prelude = {
        unique = builtins.foldl' (acc: x: if builtins.elem x acc then acc else acc ++ [ x ]) [ ];
      };
      dirty = grow (builtins.attrNames edits);
      scope' = ctx.scope // {
        nodes = builtins.mapAttrs (
          id: n: if edits ? ${id} then n // { decls = (n.decls or { }) // edits.${id}; } else n
        ) ctx.scope.nodes;
      };
    in
    genScope.evalWarm
      {
        inherit (ctx) parseParent declaredDependencies;
      }
      {
        scope = scope';
        inherit (ctx) attributes;
        prior = ctx.eval;
        decision = genScope.mkDecision {
          isClean = id: !(builtins.elem id dirty);
          reusable = ctx.eval.facade.resolutional;
        };
      };

  # ── fixture F: flat roots plus a parent → kid → gk chain of `children` records ──
  kinds = genScope.mkKinds [ (genScope.mkKind { } "host") ];
  ids = [
    "producer"
    "consumer"
    "parent"
    "kid"
    "gk"
    "kid2"
  ];
  # `kid`, `kid2` and `gk` are registered with parent edges, so `children` SELECTS them; a selected
  # record is inert (reads answer from the registered roots), and its co-located `_eval` is the cache.
  scopeAt =
    edits:
    genScope.buildRoots {
      inherit kinds;
      parentGraph = genScope.overlays (
        map genScope.edge [
          {
            from = "kid";
            to = "parent";
          }
          {
            from = "kid2";
            to = "parent";
          }
          {
            from = "gk";
            to = "kid";
          }
        ]
      );
      decls = {
        producer.v = 1;
        consumer = { };
        parent = { };
        kid.v = 1;
        kid2.v = 2;
        gk.v = 1;
      }
      // edits;
      types = builtins.listToAttrs (
        map (n: {
          name = n;
          value = "host";
        }) ids
      );
    };
  routes = {
    # kept names
    get = {
      r = "consumer";
      t = "producer";
      f = s: s.get "producer" "val";
    };
    node-decls = {
      r = "consumer";
      t = "producer";
      f = s: (s.node "producer").decls.v;
    };
    self-get = {
      r = "consumer";
      t = "consumer";
      f = s: s.get "consumer" "val";
    };
    childOrder = {
      r = "consumer";
      t = "parent";
      f = s: if has s "_childOrder" then s._childOrder "parent" else "ABSENT";
    };
    childOrder-self = {
      r = "parent";
      t = "parent";
      f = s: if has s "_childOrder" then s._childOrder "parent" else "ABSENT";
    };
    allNodeIds = {
      r = "consumer";
      t = "parent";
      f = s: if has s "allNodeIds" then s.allNodeIds else "ABSENT";
    };
    # nested `_eval` escapes, each through a kept name
    node-kid-eval-gk = {
      r = "consumer";
      t = "gk";
      f = s: ((s.node "kid")._eval or { }).children.nodes.gk._eval.val or "NO_EVAL";
    };
    self-node-eval-gk = {
      r = "kid";
      t = "gk";
      f = s: ((s.node "kid")._eval or { }).children.nodes.gk._eval.val or "NO_EVAL";
    };
    get-children-eval-gk = {
      r = "consumer";
      t = "gk";
      f = s: (s.get "kid" "children").gk._eval.val or "NO_EVAL";
    };
    own-children-eval = {
      r = "parent";
      t = "kid";
      f = s: (s.get "parent" "children").kid._eval.val or "NO_EVAL";
    };
    # the 15 tombstoned fields, each through its strongest read
    childSet = {
      r = "consumer";
      t = "producer";
      f = s: if has s "_childSet" then s._childSet "producer" "val" else "ABSENT";
    };
    childRecords = {
      r = "consumer";
      t = "kid";
      f =
        s:
        if has s "_childRecords" then (s._childRecords "parent").kid._eval.val or "NO_EVAL" else "ABSENT";
    };
    walkFrom = {
      r = "consumer";
      t = "producer";
      f =
        s: if has s "_walkFrom" then (builtins.head (s._walkFrom "producer")).value.decls.v else "ABSENT";
    };
    subtreeOf = {
      r = "consumer";
      t = "producer";
      f = s: if has s "subtreeOf" then (s.subtreeOf "producer").producer.decls.v else "ABSENT";
    };
    allNodes = {
      r = "consumer";
      t = "producer";
      f = s: if has s "allNodes" then s.allNodes.producer.decls.v else "ABSENT";
    };
    allNodesWhere = {
      r = "consumer";
      t = "producer";
      f = s: if has s "allNodesWhere" then (s.allNodesWhere (_: true)).producer.decls.v else "ABSENT";
    };
    nodesOfType = {
      r = "consumer";
      t = "producer";
      f = s: if has s "nodesOfType" then (s.nodesOfType "host").producer.decls.v else "ABSENT";
    };
    facade = {
      r = "consumer";
      t = "producer";
      f = s: if has s "facade" then s.facade.get "producer" "val" else "ABSENT";
    };
    structuralAttributes = {
      r = "consumer";
      t = "kid";
      f =
        s:
        if has s "structuralAttributes" then
          builtins.attrNames (s.structuralAttributes "parent")
        else
          "ABSENT";
    };
    structuralEdges = {
      r = "consumer";
      t = "parent";
      f = s: if has s "structuralEdges" then s.structuralEdges "parent" else "ABSENT";
    };
    projectionFindings = {
      r = "consumer";
      t = "parent";
      f = s: if has s "projectionFindings" then s.projectionFindings "parent" else "ABSENT";
    };
    decisionFindings = {
      r = "consumer";
      t = "producer";
      f = s: if has s "decisionFindings" then s.decisionFindings else "ABSENT";
    };
    resolutional = {
      r = "consumer";
      t = "producer";
      f = s: if has s "resolutional" then s.resolutional "producer" else "ABSENT";
    };
    served = {
      r = "consumer";
      t = "producer";
      f = s: if has s "served" then s.served "producer" else "ABSENT";
    };
    provenance = {
      r = "consumer";
      t = "producer";
      f = s: if has s "provenance" then s.provenance else "ABSENT";
    };
    # armed helpers
    q-children = {
      r = "consumer";
      t = "kid";
      f = s: builtins.attrNames (genScope.children s "parent");
    };
    q-childrenIds = {
      r = "consumer";
      t = "kid";
      f = s: genScope.childrenIds s "parent";
    };
    q-children-v = {
      r = "consumer";
      t = "kid";
      f = s: builtins.mapAttrs (_: r: r.decls.v or "NO_DECLS") (genScope.children s "parent");
    };
    q-siblings = {
      r = "kid";
      t = "kid2";
      f = s: genScope.siblings s "kid";
    };
    q-descendants = {
      r = "consumer";
      t = "gk";
      f = s: genScope.descendants s "parent";
    };
    q-parent = {
      r = "consumer";
      t = "kid";
      f = s: genScope.parent s "kid";
    };
    q-nodesByType = {
      r = "consumer";
      t = "producer";
      f = s: builtins.attrNames (genScope.nodesByType s "host");
    };
    collection-children = {
      r = "parent";
      t = "kid";
      f = s: genScope.collectionAttr { } "children" (s': id: [ (s'.node id).decls.v ]) s "parent";
    };
  };
  equations = {
    children = {
      name = "children";
      kind = "nta";
      readsAttrs = [ ];
      stratum = "structural";
      compute =
        self: id:
        builtins.listToAttrs (
          map
            (k: {
              name = k;
              value = {
                id = k;
              };
            })
            (
              if id == "parent" then
                (self.node id).decls.kids or [ "kid" ]
              else if id == "kid" then
                [ "gk" ]
              else
                [ ]
            )
        );
    };
    imports = {
      name = "imports";
      kind = "synthesized";
      readsAttrs = [ ];
      stratum = "structural";
      compute = _: _: [ ];
    };
    val = res "val" (self: id: (self.node id).decls.v or 0);
    names = res "names" (self: _: probeNames self);
  }
  // builtins.listToAttrs (
    builtins.attrValues (
      builtins.mapAttrs (n: rt: {
        name = "via-${n}";
        value = res "via-${n}" (self: id: if id == rt.r then rt.f self else 0);
      }) routes
    )
  );
  declRel = rel {
    consumer = [
      "producer"
      "parent"
      "kid"
    ];
    parent = [ "kid" ];
    kid = [
      "parent"
      "kid2"
    ];
  };
  parseParent =
    id:
    if id == "kid" || id == "kid2" then
      "parent"
    else if id == "gk" then
      "kid"
    else
      null;
  foldWith =
    eqs: relation: edits:
    genScope.foldEquations { } {
      scope = scopeAt edits;
      schedule.equations = eqs;
      declaredDependencies = relation;
      inherit parseParent;
    };
  fold = foldWith equations;
  # The target edit: a root is re-declared; `kid` and `gk` are children of `parent`, whose decls
  # carry no per-child data, so for `parent` the edit is a membership change (a second kid).
  editOf =
    t:
    if t == "parent" then
      {
        parent.kids = [
          "kid"
          "kid2"
        ];
      }
    else
      { ${t}.v = 9; };
  cell =
    name: rt:
    let
      a = "via-${name}";
      modes = relation: {
        cold = try ((fold relation { }).eval.get rt.r a);
        warm = try ((warmOf (fold relation { }) (editOf rt.t)).get rt.r a);
        freshcold = try ((fold relation (editOf rt.t)).eval.get rt.r a);
      };
    in
    {
      undeclared = modes emptyRel;
      declared = modes declRel;
    };

  # ── fixture N: the `nest` nta graph (r → a, b; a → k), cold and warm (the host edited) ──
  fx = import ./nta.nix { inherit genScope; };
  childA = genScope.mintNtaId {
    host = "r";
    name = "sub";
    group = "g";
    key = "a";
  };
  childB = genScope.mintNtaId {
    host = "r";
    name = "sub";
    group = "g";
    key = "b";
  };
  ntaExtra = {
    inherit (fx) pos;
    hp = self: _: if has self "getHostAt" then self.getHostAt "pos" else "ABSENT";
    readA = self: _: self.getNta "sub" "g" "a" "v";
    # depth 3: the host's own `nta-children` product, then a child's co-located cache
    own-nta-eval = self: id: (self.get id "nta-children").sub.g.a._eval.v or "NO_EVAL";
    # through `getNta`, the child's own `nta-children`, then the grandchild's cache
    getNta-nta-eval = self: _: (self.getNta "sub" "g" "a" "nta-children").sub.g.k._eval.v or "NO_EVAL";
    # the child's record through `node`, then its cache
    node-child-eval = self: _: ((self.node childA)._eval or { }).v or "NO_EVAL";
    names = self: _: probeNames self;
    # a host attribute that moves with the host's data, read by the child at its coordinates
    posv = self: id: {
      sub.g =
        if id == "r" then
          builtins.mapAttrs (_: d: d.v or 0) (builtins.head (self.get id "defs"))
        else
          { k = 0; };
    };
    hpv = self: _: self.getHostAt "posv";
    nids = self: _: builtins.length self.allNodeIds;
  };
  nestCapt = fx.nestWith (_: attrs: sc: { inherit attrs sc; }) ntaExtra;
  nestEdit.defs = [
    {
      a = {
        v = 9;
        s.v = 3;
      };
      b.v = 2;
      c.v = 4;
    }
  ];
  nKind =
    n:
    if
      builtins.elem n [
        "children"
        "defs"
      ]
    then
      "nta"
    else
      "synthesized";
  nFold =
    relation: sc:
    genScope.foldEquations { } {
      scope = sc;
      declaredDependencies = relation;
      schedule.equations = builtins.mapAttrs (name: compute: {
        inherit name compute;
        kind = nKind name;
        readsAttrs = [ ];
        stratum = if name == "children" then "structural" else "resolution";
      }) nestCapt.attrs;
      parseParent = _: null;
    };
  editedScope = nestCapt.sc // {
    nodes = nestCapt.sc.nodes // {
      r = nestCapt.sc.nodes.r // {
        decls = nestEdit;
      };
    };
  };
  nWarmRows =
    relation:
    builtins.listToAttrs (
      map
        (c: {
          name = c.n;
          value = {
            cold = try ((nFold relation nestCapt.sc).eval.get c.r c.a);
            warm = try ((warmOf (nFold relation nestCapt.sc) { r = nestEdit; }).get c.r c.a);
            freshcold = try ((nFold relation editedScope).eval.get c.r c.a);
          };
        })
        [
          {
            n = "getHostAt-child-reads-host";
            r = childA;
            a = "hpv";
          }
          {
            n = "getNta-host-reads-child";
            r = "r";
            a = "readA";
          }
          {
            n = "allNodeIds-membership";
            r = childB;
            a = "nids";
          }
        ]
    );
  ntaRun =
    r:
    fx.nestWith (
      _: attrs: sc:
      genScope.eval { declaredDependencies = rel r; } attrs sc
    ) ntaExtra;
  ntaRows = ev: {
    getNta-host-reads-child = try (ev.get "r" "readA");
    getHostAt-child-reads-host = try (ev.get childA "hp");
    own-nta-eval = try (ev.get "r" "own-nta-eval");
    getNta-nta-eval = try (ev.get "r" "getNta-nta-eval");
    node-child-eval = try (ev.get "r" "node-child-eval");
    childNames = try (ev.get childA "names");
  };
  ntaDeclared = {
    r = [ childA ];
    ${childA} = [ "r" ];
  };

  # ── fixture Q: getRepresentative, and the circular steps' readers (shared round, nested ascent) ──
  peerOf = id: if id == "a" then "b" else "a";
  carrierWith = quotient: {
    bottom = 0;
    leq = x: y: x <= y;
    height = 100;
    inherit quotient;
  };
  # The step reader's names, as one number: 1000 × present + readable, over the kept and the
  # tombstoned names.
  stepProbe =
    self:
    builtins.length (builtins.filter (has self) (kept ++ marker ++ tombs)) * 1000
    + builtins.length (
      builtins.filter (n: has self n && (builtins.tryEval (builtins.typeOf self.${n})).success) (
        kept ++ marker ++ tombs
      )
    );
  qAttrs = {
    children = _: _: { };
    imports = _: _: [ ];
    own-v = self: id: (self.node id).decls.v;
    own-rep = genScope.circular { carrier = carrierWith true; } (
      self: id: _prev:
      (self.node id).decls.v
    );
    peer-rep = self: id: (self.getRepresentative (peerOf id) "own-rep").representative;
    step-shared = genScope.circular { carrier = carrierWith false; } (
      self: _: _prev:
      stepProbe self
    );
    step-nested = genScope.circular { carrier = carrierWith true; } (
      self: _: _prev:
      stepProbe self
    );
  };
  qKind =
    n:
    if n == "children" then
      "nta"
    else if
      builtins.elem n [
        "own-rep"
        "step-shared"
        "step-nested"
      ]
    then
      "circular"
    else
      "synthesized";
  qFold =
    relation: edits:
    genScope.foldEquations { } {
      scope = genScope.buildRoots {
        decls = {
          a.v = 1;
          b.v = 2;
        }
        // edits;
        types = { };
      };
      declaredDependencies = relation;
      schedule.equations = builtins.mapAttrs (name: compute: {
        inherit name compute;
        kind = qKind name;
        readsAttrs = [ ];
        stratum = if name == "children" then "structural" else "resolution";
      }) qAttrs;
      parseParent = _: null;
    };
  qRows = relation: {
    peer-rep-cold = try ((qFold relation { }).eval.get "a" "peer-rep");
    peer-rep-warm = try ((warmOf (qFold relation { }) { b.v = 7; }).get "a" "peer-rep");
    peer-rep-freshcold = try ((qFold relation { b.v = 7; }).eval.get "a" "peer-rep");
    step-shared = try ((qFold relation { }).eval.get "a" "step-shared");
    step-nested = try ((qFold relation { }).eval.getRepresentative "a" "step-nested").representative;
  };

  # ── K3: the published helpers over a fully declared range, cold, warm and fresh ──
  k3eq = equations // {
    bytype = res "bytype" (
      self: id:
      if id == "consumer" then
        builtins.mapAttrs (_: r: r.decls.v or "NO_DECLS") (genScope.nodesByType self "host")
      else
        { }
    );
    kids = res "kids" (
      self: id:
      if id == "consumer" then
        builtins.mapAttrs (_: r: r.decls.v or "NO_DECLS") (genScope.children self "parent")
      else
        { }
    );
    # the key set of each record the helpers return
    shape = res "shape" (
      self: id:
      if id == "consumer" then
        {
          children = builtins.mapAttrs (_: builtins.attrNames) (genScope.children self "parent");
          bytype = builtins.mapAttrs (_: builtins.attrNames) (genScope.nodesByType self "host");
        }
      else
        { }
    );
  };
  declAll = rel { consumer = ids; };
  k3six = a: t: {
    cold = try ((foldWith k3eq declAll { }).eval.get "consumer" a);
    warm = try ((warmOf (foldWith k3eq declAll { }) { ${t}.v = 9; }).get "consumer" a);
    freshcold = try ((foldWith k3eq declAll { ${t}.v = 9; }).eval.get "consumer" a);
    undeclared = try ((foldWith k3eq emptyRel { }).eval.get "consumer" a);
  };
  unarmedK3 = genScope.eval { } (builtins.mapAttrs (_: e: e.compute) k3eq) (scopeAt { });

  # ── naked reads: a body that writes the read with no classification ──
  nakedOf =
    f:
    (genScope.foldEquations { } {
      scope = scopeAt { };
      schedule.equations = equations // {
        naked = res "naked" (self: id: if id == "consumer" then f self else 0);
      };
      declaredDependencies = emptyRel;
      inherit parseParent;
    }).eval.get
      "consumer"
      "naked";
in
{
  inherit
    kept
    marker
    tombs
    childA
    nakedOf
    ;
  # unclassified reads, for the cells that pin the text a refusal raises
  rawCold = name: (fold emptyRel { }).eval.get routes.${name}.r "via-${name}";
  ntaUndeclared = ntaRun { };
  names = {
    armed = try ((fold emptyRel { }).eval.get "consumer" "names");
    unarmed = try (
      (genScope.eval { } (builtins.mapAttrs (_: e: e.compute) equations) (scopeAt { })).get "consumer"
        "names"
    );
  };
  cells = builtins.mapAttrs cell routes;
  nta = {
    undeclared = ntaRows (ntaRun { });
    declared = ntaRows (ntaRun ntaDeclared);
    unarmed = ntaRows (fx.nestWith genScope.eval ntaExtra);
  };
  ntawarm = {
    undeclared = nWarmRows emptyRel;
    declared = nWarmRows (rel ntaDeclared);
  };
  q = {
    undeclared = qRows emptyRel;
    declared = qRows (rel {
      a = [ "b" ];
      b = [ "a" ];
    });
  };
  k3 = {
    bytype = k3six "bytype" "producer";
    kids = k3six "kids" "kid";
    unarmed-shape = try (unarmedK3.get "consumer" "shape");
    unarmed-kids = try (unarmedK3.get "consumer" "kids");
  };
}
