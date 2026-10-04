# A NODE IDENTIFIER CARRYING STORE-PATH STRING CONTEXT (den-hoag-di165).
#
# `baseNameOf pkgs.hello` is a string with a store path in its context set, and Nix aborts — past
# `tryEval` — on `{ ${thatString} = …; }` and on `set ? ${thatString}`. Every table this library keys
# by node id is therefore keyed by the id's TEXT, while the record, the edge target and the answer
# keep the id as the caller wrote it. One cell per site that used the id as an attribute name; each
# answers a value, so the site that regresses turns ITS cell red with the abort and no other.
#
# ★ THE ID IS A REAL `builtins.toFile` OUTPUT. A fabricated store path makes the evaluator try to
# build it (den-hoag-we7kr), and a context-free spelling of one is not the shape under test.
#
# The scope: `root` contains `ctx`, which contains `leaf`; the `a` edges run root -> ctx -> leaf.
# `ctx` is the node under test, `plain` its context-free spelling (the only spelling an attribute
# name can take).
{
  genScope,
  genGraph,
  ...
}:
let
  S = genScope;
  ctx = builtins.baseNameOf (builtins.toFile "di165-ctx-node" "x");
  plain = builtins.unsafeDiscardStringContext ctx;
  has = builtins.hasContext;
  sorted = builtins.sort builtins.lessThan;

  roots = S.buildRoots {
    parentGraph = S.overlays [
      (S.edge {
        from = ctx;
        to = "root";
      })
      (S.edge {
        from = "leaf";
        to = ctx;
      })
      (S.vertex "root")
    ];
    edgeGraphs = [
      {
        label = "a";
        graph = S.overlays [
          (S.edge {
            from = "root";
            to = ctx;
          })
          (S.edge {
            from = ctx;
            to = "leaf";
          })
        ];
      }
    ];
    decls.${plain}.v = 7;
  };

  parseParent = id: roots.nodes.${builtins.unsafeDiscardStringContext id}.parent or null;
  attributes = {
    children =
      _: id:
      if id == "root" then
        { ${plain} = roots.nodes.${plain}; }
      else if id == ctx then
        { leaf = roots.nodes.leaf; }
      else
        { };
    imports = _: _: [ ];
    marks = _: _: [ ];
    edges-a =
      _: id:
      if id == "root" then
        [ ctx ]
      else if id == ctx then
        [ "leaf" ]
      else
        [ ];
    v = self: id: (self.node id).decls.v or 0;
    count =
      S.circular
        {
          carrier = {
            bottom = 0;
            height = 3;
            leq = a: b: a <= b;
            quotient = false;
          };
        }
        (
          _self: _id: prev:
          if prev >= 3 then prev else prev + 1
        );
  };
  ev = S.eval { inherit parseParent; } attributes roots;
  evDebug = S.evalDebug { inherit parseParent; } attributes roots;

  wf = S.wellFormed {
    alphabet = [
      "a"
      "parent"
    ];
    expression = "a* | parent*";
  };
  walk =
    extra: from:
    map (a: a.node)
      (S.resolve (
        {
          inherit wf;
          mode = "reachable";
          dataFilter = n: n.id;
        }
        // extra
      ) ev from).answers;
  # `resolve` reports each answer's node as the id the caller wrote: `==` ignores context, `hasContext`
  # does not, so the answer's context is what a cell reads.
  ctxIn = ids: map has ids;

  minted = S.mintStrata { widget = { }; } [
    {
      pass = 0;
      identifier = ctx;
      kind = "widget";
      relata = { };
      content = { };
      site = "s0";
    }
    {
      pass = 1;
      identifier = "top";
      kind = "widget";
      relata.r = ctx;
      content = { };
      site = "s1";
    }
  ];

  folded =
    let
      contracted = import ./_fixtures/declared.nix {
        inherit genGraph;
        scope = roots;
      };
    in
    S.foldEquations { } {
      scope = roots;
      schedule.equations = {
        children = {
          name = "children";
          kind = "nta";
          readsAttrs = [ ];
          stratum = "structural";
          compute = _: _: { };
        };
      };
      inherit parseParent;
      declaredDependencies = contracted { };
    };
in
{
  flake.tests.context-node-id = {
    # ── build-nodes.nix: the node set ──
    test-buildRoots-keys-by-text-and-keeps-the-id = {
      expr = {
        order = ctxIn roots.nodeOrder;
        keys = sorted (builtins.attrNames roots.nodes);
        id = has roots.nodes.${plain}.id;
        parent = roots.nodes.${plain}.parent;
        childParent = has roots.nodes.leaf.parent;
        edges = roots.nodes.root.decls.__edges.a == [ ctx ];
        decls = roots.nodes.${plain}.decls.v;
      };
      expected = {
        order = [
          true
          false
          false
        ];
        keys = sorted [
          plain
          "leaf"
          "root"
        ];
        id = true;
        parent = "root";
        childParent = true;
        edges = true;
        decls = 7;
      };
    };

    # ── eval.nix: the accessors, the walk and the circular round ──
    test-node-and-get-resolve-the-id = {
      expr = {
        v = ev.get ctx "v";
        id = has (ev.node ctx).id;
        byText = (ev.node plain).decls.v;
      };
      expected = {
        v = 7;
        id = true;
        byText = 7;
      };
    };
    test-allNodeIds-keeps-context-and-the-maps-key-by-text = {
      expr = {
        ids = ctxIn ev.allNodeIds;
        all = sorted (builtins.attrNames ev.allNodes);
        subtree = builtins.attrNames (ev.subtreeOf ctx);
        where = sorted (builtins.attrNames (ev.allNodesWhere (_: true)));
      };
      expected = {
        ids = [
          true
          false
          false
        ];
        all = sorted [
          plain
          "leaf"
          "root"
        ];
        subtree = sorted [
          plain
          "leaf"
        ];
        where = sorted [
          plain
          "leaf"
          "root"
        ];
      };
    };
    test-circular-attribute-at-the-id = {
      expr = ev.get ctx "count";
      expected = 3;
    };
    test-evalDebug-reads-the-id = {
      expr = {
        node = has (evDebug.node ctx).id;
        get = evDebug.get ctx "v";
        traced = (evDebug.getTraced ctx "v").value;
      };
      expected = {
        node = true;
        get = 7;
        traced = 7;
      };
    };

    # ── queries.nix ──
    test-queries-walk-through-the-id = {
      expr = {
        ancestors = map has (S.ancestors ev "leaf");
        descendants = sorted (S.descendants ev "root");
        isAncestor = S.isAncestor ev "root" ctx;
        siblings = S.siblings ev ctx;
      };
      expected = {
        ancestors = [
          true
          false
        ];
        descendants = sorted [
          plain
          "leaf"
        ];
        isAncestor = true;
        siblings = [ ];
      };
    };

    # ── resolve.nix: `inheritAll` / `inheritSet` ──
    test-inherit-accumulators-at-the-id = {
      expr = {
        all = S.inheritAll { } (n: n.decls.v or null) ev ctx;
        set = S.inheritSet { } (n: n.decls.v or null) ev ctx;
      };
      expected = {
        all = [ 7 ];
        set = [ 7 ];
      };
    };

    # ── calculus.nix, through `resolve`: the shape gen-demo's C46 reads ──
    test-resolve-walks-a-store-named-node = {
      expr = {
        from = ctxIn (walk { } ctx);
        to = ctxIn (walk { } "root");
        inbound = ctxIn (walk { direction = "inbound"; } ctx);
        witnesses = ctxIn (walk { mode = "witnesses"; } "root");
      };
      expected = {
        from = [
          true
          false
          false
        ];
        to = [
          false
          true
          false
        ];
        inbound = [
          true
          false
          false
        ];
        witnesses = [
          false
          true
          false
        ];
      };
    };

    # ── mint.nix ──
    test-mintStrata-keys-by-text-and-keeps-the-identifier = {
      expr = {
        nodes = sorted (builtins.attrNames minted.nodes);
        from = map (e: has e.from) minted.edges;
        to = map (e: has e.to) minted.edges;
      };
      expected = {
        nodes = sorted [
          plain
          "top"
        ];
        from = [ false ];
        to = [ true ];
      };
    };

    # ── fold-equations.nix ──
    test-foldEquations-trace-reads-the-id = {
      expr = (folded.accessor.trace ctx).deps;
      expected = [ ];
    };
  };
}
