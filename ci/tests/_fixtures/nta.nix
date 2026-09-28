# THE `nta` WITNESSES — one fixture shared by the value suite (`tests/nta.nix`) and the refusal
# cells in `tests-error.nix`, so the graph a refusal is earned on and the graph the clean path
# answers over are one value.
#
# Every kind here grows its OWN kind through `nta`, which `spawns` cannot express (a kind naming
# itself in `below` is refused by `mkKinds`). The host's definitions are the attribute `defs`: a
# registered root carries them in `decls.defs`, and an `nta` child's definitions are its seed's
# values — the inherited regime, under which each branch descends and the expansion is finite.
{ genScope }:
let
  inherit (genScope) mkKind mkKinds mintNtaId;
  inherit (builtins) head isAttrs attrNames;

  # A seed address into definition `def` of the host's `defs`, along `at`.
  addr = def: at: {
    attr = "defs";
    inherit def at;
  };

  defs =
    self: id:
    let
      d = (self.node id).decls;
    in
    if d ? seed then map (e: e.value) d.seed else d.defs or [ ];

  first = self: id: head (self.get id "defs");

  # `tree`: one child per level while the first definition carries `s` — same-kind growth whose key
  # set reads an evaluated attribute.
  tree = mkKind {
    nta.sub =
      self: id:
      let
        d = first self id;
      in
      {
        g = if isAttrs d && d ? s then { k = [ (addr 0 [ "s" ]) ]; } else { };
      };
  } "tree";

  # `pick`: the key set is the host's evaluated `selector` — a value, which `spawnHandle` cannot read.
  pick = mkKind {
    nta.hosts = self: id: {
      hosts = builtins.listToAttrs (
        map (k: {
          name = k;
          value = [
            (addr 0 [
              "hosts"
              k
            ])
          ];
        }) (self.get id "selector")
      );
    };
  } "pick";

  # `fam`: group `second`'s KEY is group `first`'s child's evaluated `label` — interleaved families.
  fam = mkKind {
    nta.fam =
      self: id:
      let
        d = first self id;
      in
      {
        first = if d ? first then { seed = [ (addr 0 [ "first" ]) ]; } else { };
        second =
          if d ? second then
            {
              ${
                self.get (mintNtaId {
                  host = id;
                  name = "fam";
                  group = "first";
                  key = "seed";
                }) "label"
              } =
                [ (addr 0 [ "second" ]) ];
            }
          else
            { };
      };
  } "fam";

  # `nest`: the root grows one child per key of its first definition, and a child whose seed
  # carries `s` grows one grandchild under group `g` key `k` — the two depths at which a host reads
  # its own children through `getNta`.
  nest = mkKind {
    nta.sub =
      self: id:
      let
        d = first self id;
      in
      {
        g =
          if id == "r" then
            builtins.mapAttrs (k: _: [ (addr 0 [ k ]) ]) d
          else if isAttrs d && d ? s then
            { k = [ (addr 0 [ "s" ]) ]; }
          else
            { };
      };
  } "nest";

  # `raw`: the builder is a parameter, so one kind carries every refusal and every address case. It
  # grows from the root only, so an enumeration over it is finite whatever the builder yields.
  rawWith =
    builder:
    mkKind {
      nta.x = self: id: if id == "r" then builder self id else { };
    } "raw";

  attributes = {
    children = _: _: { };
    inherit defs;
    selector = self: id: (self.node id).decls.selector or [ ];
    label = self: id: (first self id).label or "none";
    n = _: _: 3;
    # Definitions computed from another attribute's value, beside data ones: an address reads the
    # EVALUATED definition, so a computed one is as addressable as a written one.
    computed = self: id: [
      { value.s.x = 1; }
      (({ ... }: { value.s.x = 2; }) { })
      { value.s.x = self.get id "n" + 1; }
      { value.l = [ { x = 5; } ]; }
      { value.s = null; }
    ];
    notAList = _: _: { };
  };

  root = type: decls: {
    r = {
      id = "r";
      inherit type decls;
      parent = null;
    };
  };

  scopeOf = kinds: nodes: {
    inherit nodes kinds;
    nodeOrder = attrNames nodes;
  };

  evalWith = kinds: nodes: genScope.eval { } attributes (scopeOf kinds nodes);

  treeWith = data: evalWith (mkKinds [ tree ]) (root "tree" { defs = [ data ]; });
  pickScope =
    selector:
    scopeOf (mkKinds [ pick ]) (
      root "pick" {
        defs = [
          {
            hosts = {
              alpha.x = 1;
              beta.x = 2;
              gamma.x = 3;
            };
          }
        ];
        inherit selector;
      }
    );
  pickWith = selector: genScope.eval { } attributes (pickScope selector);
  rawRun =
    builder: evalWith (mkKinds [ (rawWith builder) ]) (root "raw" { defs = [ { s = { }; } ]; });
  rawNodes =
    builder: extra:
    evalWith (mkKinds [ (rawWith builder) ]) (root "raw" { defs = [ { s = { }; } ]; } // extra);

  # The `nest` graph: child `a` carries grandchild `k`, child `b` carries none. `extra` adds the
  # attributes a cell reads through; `evaluator` is `eval` or `evalDebug`.
  nestWith =
    evaluator: extra:
    evaluator { } (attributes // { v = self: id: (first self id).v; } // extra) (
      scopeOf (mkKinds [ nest ]) (
        root "nest" {
          defs = [
            {
              a = {
                v = 1;
                s.v = 3;
              };
              b.v = 2;
            }
          ];
        }
      )
    );

  # The host's equation for each of its `nest` children, by the child's coordinates: the attribute
  # a child reads through `getHostAt` (den-hoag-n6dh7 U2.0′).
  pos = self: id: {
    sub.g =
      if id == "r" then builtins.mapAttrs (k: _: "${id}/${k}") (first self id) else { k = "${id}/k"; };
  };

  # The one `raw` child under group `g` key `k`, its seed the given list.
  seeded = seed: rawRun (_: _: { g.k = seed; });
  child = mintNtaId {
    host = "r";
    name = "x";
    group = "g";
    key = "k";
  };
  seedOfChild = ev: (ev.node child).decls.seed;
in
{
  inherit
    addr
    attributes
    tree
    treeWith
    pickWith
    pickScope
    rawWith
    rawRun
    rawNodes
    nestWith
    pos
    seeded
    child
    seedOfChild
    scopeOf
    root
    ;

  famRun = evalWith (mkKinds [ fam ]) (
    root "fam" {
      defs = [
        {
          first.label = "from-seed";
          second.label = "x";
        }
      ];
    }
  );

  # The host plus three levels of data: the expansion ends where the data does.
  threeLevels = treeWith { s.s.s = { }; };
}
