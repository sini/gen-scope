# A READER HANDED OUT AS A VALUE — producer-bounded delegation (den-hoag-9pt45, ruled arm (a)).
#
# A body's reader is a value like any other: a declared node's attribute may return it, directly,
# inside a record or list, or captured by a closure, and another node may forward it. The guard
# checks the relation of the node the reader was BOUND to (its producer), never the node whose body
# holds it, so a consumer reads what the producer declared through its own declared dependency path,
# without declaring the producer's targets itself. The bound: a target the producer did not declare
# stays refused, and so does the consumer's own undeclared read. This is the evaluator's behaviour
# stated as semantics, not a security boundary (spec §2.5 item 6, §2.12).
#
# Each consumer's `out` reads its route inside `try`, so one value per route: the answer, or
# "REFUSED". The nta route (a host's reader carried in a child's seed) is not here: it is stale
# warm for a reason that needs no reader (den-hoag-h7w6l), and nothing in these cells depends on it.
{ genScope, genGraph }:
let
  try =
    v:
    let
      r = builtins.tryEval (builtins.deepSeq v v);
    in
    if r.success then r.value else "REFUSED";
  res = name: compute: {
    inherit name compute;
    kind = "synthesized";
    readsAttrs = [ ];
    stratum = "resolution";
  };
  rel = r: genGraph.mkDeclaredEdges (builtins.mapAttrs (_: map (genGraph.mkNodeRef (_: true))) r);

  consumers = [
    "cDirect"
    "cFwd"
    "cFwd2"
    "cRec"
    "cFn"
    "cOwn"
    "cBeyond"
    "cGkOwn"
  ];
  ids = [
    "producer"
    "relay"
    "relay2"
    "kid"
    "gk"
  ]
  ++ consumers;
  scopeAt =
    edits:
    genScope.buildRoots {
      kinds = genScope.mkKinds [ (genScope.mkKind { } "host") ];
      decls =
        builtins.listToAttrs (
          map (n: {
            name = n;
            value = { };
          }) ids
        )
        // {
          kid.v = 1;
          gk.v = 5;
        }
        // edits;
      types = builtins.listToAttrs (
        map (n: {
          name = n;
          value = "host";
        }) ids
      );
    };

  is =
    want: id: v:
    if id == want then v else null;
  val = self: k: self.get k "val";
  equations = {
    children = {
      name = "children";
      kind = "nta";
      readsAttrs = [ ];
      stratum = "structural";
      compute = _: _: { };
    };
    imports = {
      name = "imports";
      kind = "synthesized";
      readsAttrs = [ ];
      stratum = "structural";
      compute = _: _: [ ];
    };
    val = res "val" (self: id: (self.node id).decls.v or 0);
    # the producer hands out its own reader: directly, in a record and a list, and in a closure
    leak = res "leak" (self: id: is "producer" id self);
    rec_ = res "rec_" (
      self: id:
      is "producer" id {
        inner.r = self;
        l = [ self ];
      }
    );
    fn = res "fn" (self: id: is "producer" id (k: val self k));
    # forwarding: relay passes the producer's reader on, relay2 passes relay's on
    fwd = res "fwd" (self: id: is "relay" id (self.get "producer" "leak"));
    fwd2 = res "fwd2" (self: id: is "relay2" id (self.get "relay" "fwd"));
    # untried reads, for the error plane: the refusal names whose relation the guard consulted
    rawBeyond = res "rawBeyond" (
      self: id: is "cBeyond" id ((self.get "producer" "leak").get "gk" "val")
    );
    rawOwn = res "rawOwn" (self: id: is "cOwn" id (self.get "kid" "val"));
    out = res "out" (
      self: id:
      let
        t = try;
        leak = self.get "producer" "leak";
      in
      if id == "cDirect" then
        {
          node = t (leak.node "kid").decls.v;
          get = t (leak.get "kid" "val");
        }
      else if id == "cFwd" then
        {
          node = t ((self.get "relay" "fwd").node "kid").decls.v;
          get = t ((self.get "relay" "fwd").get "kid" "val");
        }
      else if id == "cFwd2" then
        { get = t ((self.get "relay2" "fwd2").get "kid" "val"); }
      else if id == "cRec" then
        {
          inner = t ((self.get "producer" "rec_").inner.r.get "kid" "val");
          list = t ((builtins.head (self.get "producer" "rec_").l).get "kid" "val");
        }
      else if id == "cFn" then
        { call = t ((self.get "producer" "fn") "kid"); }
      else if id == "cOwn" then
        {
          node = t (self.node "kid").decls.v;
          get = t (self.get "kid" "val");
        }
      else if id == "cBeyond" then
        {
          node = t (leak.node "gk").decls.v;
          get = t (leak.get "gk" "val");
        }
      else if id == "cGkOwn" then
        { get = t (self.get "gk" "val"); }
      else
        null
    );
  };

  # cFwd declares relay only, cFwd2 relay2 only: neither declares the producer or kid
  live = {
    producer = [ "kid" ];
    relay = [ "producer" ];
    relay2 = [ "relay" ];
    cDirect = [ "producer" ];
    cFwd = [ "relay" ];
    cFwd2 = [ "relay2" ];
    cRec = [ "producer" ];
    cFn = [ "producer" ];
    cOwn = [ "producer" ];
    cBeyond = [ "producer" ];
    cGkOwn = [ "gk" ];
  };
  fold =
    relation: edits:
    genScope.foldEquations { } {
      scope = scopeAt edits;
      schedule = { inherit equations; };
      declaredDependencies = rel relation;
      parseParent = _: null;
    };
  rows =
    ev:
    builtins.listToAttrs (
      map (c: {
        name = c;
        value = try (ev.get c "out");
      }) consumers
    );
in
{
  inherit consumers live;
  cold = rows (fold live { }).eval;
  empty = rows (fold { } { }).eval;
  # the raw refusals, untried, for the error plane's message cells
  beyondGet = (fold live { }).eval.get "cBeyond" "rawBeyond";
  ownGet = (fold live { }).eval.get "cOwn" "rawOwn";
  inherit fold equations;
}
