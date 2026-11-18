# THE CLOSED BODY READER — R§2.4 under the arm-(b) construction.
#
# An armed body's reader is a closed record: the guarded demand forms (`node`, `get`,
# `getRepresentative`, `getNta`, `getHostAt`, `_childOrder`), the one enumeration `allNodeIds`, and a
# named refusal at each field the substrate accessor carried before it closed. A field the substrate
# gains later is ABSENT from it. The records a body receives are the records as authored: no wrapper
# field (the co-located `_eval` cache, or any other a wrap site adds) reaches a body through a kept name.
#
# THE PLANTED-FIELD CONTROL. The evaluator is re-instantiated here from a copy of this tree's own
# `lib/eval.nix` with one field planted on the substrate accessor — a reader of another node with no
# edge consulted. Under the closed reader it is absent from an armed body's view; an unarmed body sees
# it (the live control that the plant wrote and reaches the substrate). A reader that only removes the
# names it knows (a deny-list) hands the plant to every armed body, so this cell is what tells the
# closed reader from one. The copy is made in this file; nothing is planted in `lib/`.
#
# THE ROUTE CELLS (C1–C13) read the tables of `_fixtures/closed-reader.nix`: every route a body can
# take to another node through the reader, kept or tombstoned, nested or not, in six modes (cold,
# warm after the target's edit, a fresh cold fold of the edited scope; under the empty and the
# declared relation). A refusal is a `tryEval` fact here; the text each raises is pinned in
# `../tests-error.nix` (`codomain-closed-reader-refusals`).
{
  genScope,
  genGraph,
  genPreludeLib,
  genAlgebra,
  ...
}:
let
  prelude = genPreludeLib;
  cr = import ./_fixtures/closed-reader.nix { inherit genScope genGraph; };
  r3 = v: {
    cold = v;
    warm = v;
    freshcold = v;
  };
  # warm parity: the warm read equals a fresh cold fold of the edited scope, not the prior cold read
  parity = cold: fresh: {
    inherit cold;
    warm = fresh;
    freshcold = fresh;
  };
  REF = r3 "REFUSED";
  both = v: {
    undeclared = v;
    declared = v;
  };
  pick = names: t: prelude.genAttrs names (n: t.${n});
  readable = t: builtins.mapAttrs (_: v: v.readable) t;
  # the reader's names as the closed record carries them: the seven kept readable, the fifteen
  # tombstoned present and refusing at WHNF
  closedNames =
    prelude.genAttrs cr.kept (_: {
      present = true;
      readable = true;
    })
    // prelude.genAttrs cr.tombs (_: {
      present = true;
      readable = false;
    });
  openNames = prelude.genAttrs (cr.kept ++ cr.tombs) (_: {
    present = true;
    readable = true;
  });
  validator =
    through:
    genScope.seamAcquisitionDefect {
      reader = null;
      target = null;
      declared = [ ];
      inherit through;
    };
  mentions = n: msg: builtins.length (builtins.split "`self\\.${n}`" msg) > 1;
  refused = v: !(builtins.tryEval (builtins.deepSeq v v)).success;

  # ── the planted evaluator ──
  anchor = "            _childSet = id: attrName: demand \"self.get\" id attrName;\n";
  source = builtins.readFile ../../lib/eval.nix;
  planted =
    let
      text =
        builtins.replaceStrings
          [ anchor "import ./" ]
          [
            (anchor + "            _zzPlanted = id: attrName: demand \"self.get\" id attrName;\n")
            "import ${../../lib}/"
          ]
          source;
    in
    assert text != source;
    # one plant: `split` answers the text either side of the one match, and the match
    assert builtins.length (builtins.split "_zzPlanted" text) == 3;
    text;
  cascade = import ../../lib/cascade.nix {
    inherit prelude;
    algebra = genAlgebra;
  };
  plantedEval =
    (import (builtins.toFile "eval-planted.nix" planted) {
      inherit prelude;
      graph = genGraph;
      inherit
        (import ../../lib/require-scope.nix {
          inherit prelude;
          inherit (cascade) kindSetDefect sameKindValue;
        })
        requireScope
        ;
      inherit (import ../../lib/require-declared-dependencies.nix { graph = genGraph; })
        requireDeclaredDependencies
        ;
    }).eval;

  # ── fixture: siblings `a`, `b` under `root`, and `kid` selected by `root` ──
  scopeAt =
    edits:
    genScope.buildRoots {
      parentGraph = genScope.overlays [
        (genScope.edge {
          from = "a";
          to = "root";
        })
        (genScope.edge {
          from = "b";
          to = "root";
        })
        (genScope.edge {
          from = "kid";
          to = "a";
        })
      ];
      kinds = genScope.mkKinds [ (genScope.mkKind { } "host") ];
      decls = {
        root = { };
        a.v = 1;
        b.v = 2;
        kid.v = 3;
      }
      // edits;
      types = {
        root = "host";
        a = "host";
        b = "host";
        kid = "host";
      };
    };
  scope = scopeAt { };
  contracted = import ./_fixtures/declared.nix { inherit genGraph scope; };
  rel = r: contracted r;
  attrs = {
    children =
      _: id:
      if id == "a" then
        {
          kid = {
            id = "kid";
          };
        }
      else
        { };
    imports = _: _: [ ];
    own-v = self: id: (self.node id).decls.v or 0;
    planted-seen = self: id: if id == "a" then self ? _zzPlanted else false;
    planted-read =
      self: id: if id == "a" && self ? _zzPlanted then self._zzPlanted "b" "own-v" else "ABSENT";
    # K3: the published helpers, read from `root`
    kids =
      self: id:
      if id == "root" then
        builtins.mapAttrs (_: r: r.decls.v or "NO_DECLS") (genScope.children self "a")
      else
        { };
    kid-keys = self: id: if id == "root" then builtins.attrNames (genScope.children self "a") else [ ];
    by-type =
      self: id: if id == "root" then builtins.attrNames (genScope.nodesByType self "host") else [ ];
    # the record a body receives through a child-bearing read: the authored record, never its wrapper
    received =
      self: id:
      if id == "root" then
        let
          r = (self.get "a" "children").kid;
        in
        {
          keys = builtins.attrNames r;
          wrapperField = r ? raw;
          cache = r ? _eval;
        }
      else
        { };
  };
  armedEval = relation: plantedEval { declaredDependencies = rel relation; } attrs scope;
  unarmedEval = plantedEval { } attrs scope;
  allDeclared = {
    root = [
      "a"
      "b"
      "kid"
    ];
    a = [ "b" ];
  };

  # ── fixture: the `nest` nta graph; `childA`'s own child `gk` is never declared ──
  fx = import ./_fixtures/nta.nix { inherit genScope; };
  childA = genScope.mintNtaId {
    host = "r";
    name = "sub";
    group = "g";
    key = "a";
  };
  extra = {
    inherit (fx) pos;
    # through the host's equation at the reader's own coordinates, the reader's own nta child's cache
    host-gk-eval =
      self: id:
      if id == childA then
        ((self.getHostAt "nta-children")._eval or { })."nta-children".sub.g.k._eval.v or "NO_EVAL"
      else
        0;
    host-has-eval = self: id: if id == childA then (self.getHostAt "nta-children") ? _eval else false;
    host-own-id = self: id: if id == childA then (self.getHostAt "nta-children").id else "";
    host-pos = self: id: if id == childA then self.getHostAt "pos" else "";
  };
  ntaRun =
    r:
    fx.nestWith (
      _: a: sc:
      genScope.eval {
        declaredDependencies = genGraph.mkDeclaredEdges (
          builtins.mapAttrs (_: map (genGraph.mkNodeRef (_: true))) r
        );
      } a sc
    ) extra;
  hostOnly = ntaRun {
    r = [ childA ];
    ${childA} = [ "r" ];
  };
  unarmedNta = fx.nestWith genScope.eval extra;
in
{
  flake.tests."codomain-closed-reader" = {
    # N1: the planted field is absent from an armed body's reader, under any relation
    test-N1-planted-field-is-absent-armed = {
      expr = [
        ((armedEval { }).get "a" "planted-seen")
        ((armedEval allDeclared).get "a" "planted-seen")
        ((armedEval allDeclared).get "a" "planted-read")
      ];
      expected = [
        false
        false
        "ABSENT"
      ];
    };
    test-control-N1-the-plant-reaches-an-unarmed-body = {
      expr = [
        (unarmedEval.get "a" "planted-seen")
        (unarmedEval.get "a" "planted-read")
      ];
      expected = [
        true
        2
      ];
    };
    # K1: getHostAt on a child-bearing attribute hands out the authored record, never the wrapper
    test-K1-getHostAt-hands-no-wrapper = {
      expr = [
        (hostOnly.get childA "host-gk-eval")
        (hostOnly.get childA "host-has-eval")
      ];
      expected = [
        "NO_EVAL"
        false
      ];
    };
    test-control-K1-getHostAt-answers-the-authored-record-and-values = {
      expr = [
        (hostOnly.get childA "host-own-id")
        (hostOnly.get childA "host-pos")
      ];
      expected = [
        childA
        "r/a"
      ];
    };
    test-control-K1-unarmed-getHostAt-is-unchanged = {
      expr = [
        (unarmedNta.get childA "host-gk-eval")
        (unarmedNta.get childA "host-has-eval")
      ];
      expected = [
        3
        true
      ];
    };
    test-K1-undeclared-host-is-refused = {
      expr = refused ((ntaRun { }).get childA "host-own-id");
      expected = true;
    };
    # The wrap seam keeps the record it wrapped under `raw` (armed only), and an armed body is handed
    # that record: the authored `{ id = "kid"; }`, carrying neither the wrapper's field nor its cache.
    test-the-armed-body-receives-the-authored-record = {
      expr = (armedEval allDeclared).get "root" "received";
      expected = {
        keys = [ "id" ];
        wrapperField = false;
        cache = false;
      };
    };
    test-control-the-unarmed-body-receives-the-wrapper = {
      expr = unarmedEval.get "root" "received";
      expected = {
        keys = [
          "_eval"
          "id"
        ];
        wrapperField = false;
        cache = true;
      };
    };
    # K3: a fully declared read through the published helpers is preserved on the armed reader
    test-K3-declared-children-answers-armed = {
      expr = [
        ((armedEval allDeclared).get "root" "kid-keys")
        ((armedEval allDeclared).get "root" "kids")
      ];
      expected = [
        [ "kid" ]
        { kid = 3; }
      ];
    };
    test-K3-declared-nodesByType-answers-armed = {
      expr = (armedEval allDeclared).get "root" "by-type";
      expected = [
        "a"
        "b"
        "kid"
        "root"
      ];
    };
    # `a` is declared, so its child ids are a declared read of `a`'s structure; the child's record is not
    test-K3-undeclared-child-is-refused = {
      expr = [
        (refused ((armedEval { root = [ "a" ]; }).get "root" "kids"))
        (refused ((armedEval { root = [ "a" ]; }).get "root" "by-type"))
      ];
      expected = [
        true
        true
      ];
    };
    test-control-K3-an-undeclared-child-s-id-is-a-declared-read-of-its-parent = {
      expr = (armedEval { root = [ "a" ]; }).get "root" "kid-keys";
      expected = [ "kid" ];
    };
    test-control-K3-unarmed-helpers-answer = {
      expr = [
        (unarmedEval.get "root" "kid-keys")
        (unarmedEval.get "root" "by-type")
      ];
      expected = [
        [ "kid" ]
        [
          "a"
          "b"
          "kid"
          "root"
        ]
      ];
    };
    # ── THE ROUTE CELLS ──
    # C1: the seven kept names are present and readable, beside the fifteen tombstones, at every
    # entry a body is handed a reader by: the ordinary application, an `nta` child's reader, and
    # both circular ascents' step readers (22 present, 7 readable, as `1000 × present + readable`)
    test-C1-the-closed-key-set-at-every-entry = {
      expr = [
        cr.names.armed
        cr.nta.declared.childNames
        cr.nta.undeclared.childNames
        cr.q.declared.step-shared
        cr.q.declared.step-nested
        cr.q.undeclared.step-shared
        cr.q.undeclared.step-nested
      ];
      expected = [
        closedNames
        closedNames
        closedNames
        22007
        22007
        22007
        22007
      ];
    };
    # C2: each tombstone refuses CATCHABLY, and the evaluation continues
    test-C2-each-tombstone-is-a-catchable-refusal = {
      expr = map (n: cr.nakedOf (self: (builtins.tryEval self.${n}).success)) cr.tombs;
      expected = map (_: false) cr.tombs;
    };
    # C3: the validator's capability mode: a message naming `self.<n>` for the fifteen, null for the
    # seven kept names and for a name the reader never carried
    test-C3-the-validator-names-each-tombstoned-capability = {
      expr = map (n: mentions n (validator n)) cr.tombs;
      expected = map (_: true) cr.tombs;
    };
    test-C3-the-validator-is-null-for-a-kept-or-unknown-name = {
      expr = map validator (
        cr.kept
        ++ [
          "_zzPlanted"
          "zzFuture"
        ]
      );
      expected = map (_: null) (
        cr.kept
        ++ [
          0
          0
        ]
      );
    };
    # C4: a name the substrate never published is ABSENT, not tombstoned (its abort is in tests-error)
    test-C4-a-future-name-is-absent = {
      expr = cr.nakedOf (self: self ? zzFuture);
      expected = false;
    };
    # C5 / C5′: `getNta` (host → child) and `getHostAt` (child → host), the host edited
    test-C5-undeclared-getNta-and-getHostAt-refuse-cold-warm-and-fresh = {
      expr = pick [ "getHostAt-child-reads-host" "getNta-host-reads-child" ] cr.ntawarm.undeclared;
      expected = {
        getHostAt-child-reads-host = REF;
        getNta-host-reads-child = REF;
      };
    };
    test-C5prime-declared-getNta-and-getHostAt-hold-warm-parity = {
      expr = pick [ "getHostAt-child-reads-host" "getNta-host-reads-child" ] cr.ntawarm.declared;
      expected = {
        getHostAt-child-reads-host = parity 1 9;
        getNta-host-reads-child = parity 1 9;
      };
    };
    test-control-C5-the-undeclared-host-read-is-refused-and-the-declared-answers = {
      expr = [
        cr.nta.undeclared.getHostAt-child-reads-host
        cr.nta.undeclared.getNta-host-reads-child
        cr.nta.declared.getHostAt-child-reads-host
        cr.nta.declared.getNta-host-reads-child
      ];
      expected = [
        "REFUSED"
        "REFUSED"
        "r/a"
        1
      ];
    };
    # C6: depth 3 — the host's own `nta-children` product, and `getNta` to a grandchild — carries
    # no child's cache
    test-C6-no-cache-at-depth-three = {
      expr = pick [ "own-nta-eval" "getNta-nta-eval" ] cr.nta.declared;
      expected = {
        own-nta-eval = "NO_EVAL";
        getNta-nta-eval = "NO_EVAL";
      };
    };
    # C7: no cache through a kept name: a reader's own children, a declared node's children to an
    # undeclared grandchild, a node's record, an `nta` child's record
    test-C7-no-cache-through-a-kept-name = {
      expr = [
        (pick [
          "own-children-eval"
          "self-node-eval-gk"
          "get-children-eval-gk"
          "node-kid-eval-gk"
        ] cr.cells)
        cr.nta.declared.node-child-eval
      ];
      expected = [
        {
          own-children-eval = both (r3 "NO_EVAL");
          self-node-eval-gk = both (r3 "NO_EVAL");
          get-children-eval-gk = {
            undeclared = REF;
            declared = r3 "NO_EVAL";
          };
          node-kid-eval-gk = {
            undeclared = REF;
            declared = r3 "NO_EVAL";
          };
        }
        "NO_EVAL"
      ];
    };
    # C8: `_childOrder` is guarded; declared and self reads hold warm parity over a membership edit
    test-C8-childOrder-is-guarded = {
      expr = pick [ "childOrder" "childOrder-self" ] cr.cells;
      expected = {
        childOrder = {
          undeclared = REF;
          declared = parity [ "kid" ] [ "kid" "kid2" ];
        };
        childOrder-self = both (parity [ "kid" ] [ "kid" "kid2" ]);
      };
    };
    # C8′: `allNodeIds` is the one unguarded name: it answers undeclared, in every mode (F2)
    test-C8prime-allNodeIds-answers-undeclared = {
      expr = builtins.mapAttrs (
        _: builtins.mapAttrs (_: builtins.sort builtins.lessThan)
      ) cr.cells.allNodeIds;
      expected = both (r3 [
        "consumer"
        "gk"
        "kid"
        "kid2"
        "parent"
        "producer"
      ]);
    };
    # C9: `getRepresentative` refuses undeclared, and holds warm parity declared
    test-C9-getRepresentative-guarded-with-warm-parity = {
      expr = [
        (pick [ "peer-rep-cold" "peer-rep-warm" "peer-rep-freshcold" ] cr.q.undeclared)
        (pick [ "peer-rep-cold" "peer-rep-warm" "peer-rep-freshcold" ] cr.q.declared)
      ];
      expected = [
        {
          peer-rep-cold = "REFUSED";
          peer-rep-warm = "REFUSED";
          peer-rep-freshcold = "REFUSED";
        }
        {
          peer-rep-cold = 2;
          peer-rep-warm = 7;
          peer-rep-freshcold = 7;
        }
      ];
    };
    # C10: the published helpers refuse undeclared and answer declared; `nodesByType` over a range
    # not fully declared refuses
    test-C10-armed-helpers = {
      expr = pick [
        "q-children"
        "q-children-v"
        "q-childrenIds"
        "q-siblings"
        "q-parent"
        "q-descendants"
        "q-nodesByType"
        "collection-children"
      ] cr.cells;
      expected = {
        q-children = {
          undeclared = REF;
          declared = r3 [ "kid" ];
        };
        q-children-v = {
          undeclared = REF;
          declared = parity { kid = 1; } { kid = 9; };
        };
        q-childrenIds = {
          undeclared = REF;
          declared = r3 [ "kid" ];
        };
        q-siblings = {
          undeclared = REF;
          declared = r3 [ ];
        };
        q-parent = {
          undeclared = REF;
          declared = r3 "parent";
        };
        q-descendants = both REF;
        q-nodesByType = both REF;
        collection-children = {
          undeclared = REF;
          declared = parity [ 1 ] [ 9 ];
        };
      };
    };
    # K3 cold/warm: a fully declared range through the helpers holds warm parity
    test-K3-declared-helpers-hold-warm-parity = {
      expr = [
        cr.k3.kids
        cr.k3.bytype
      ];
      expected = [
        {
          cold.kid = 1;
          warm.kid = 9;
          freshcold.kid = 9;
          undeclared = "REFUSED";
        }
        (
          let
            at = p: {
              consumer = "NO_DECLS";
              gk = 1;
              kid = 1;
              kid2 = 2;
              parent = "NO_DECLS";
              producer = p;
            };
          in
          {
            cold = at 1;
            warm = at 9;
            freshcold = at 9;
            undeclared = "REFUSED";
          }
        )
      ];
    };
    # C11: the fifteen removed routes refuse in all six modes
    test-C11-the-fifteen-removed-routes-refuse = {
      expr = pick [
        "childSet"
        "childRecords"
        "walkFrom"
        "subtreeOf"
        "allNodes"
        "allNodesWhere"
        "nodesOfType"
        "facade"
        "structuralAttributes"
        "structuralEdges"
        "projectionFindings"
        "decisionFindings"
        "resolutional"
        "served"
        "provenance"
      ] cr.cells;
      expected = prelude.genAttrs [
        "childSet"
        "childRecords"
        "walkFrom"
        "subtreeOf"
        "allNodes"
        "allNodesWhere"
        "nodesOfType"
        "facade"
        "structuralAttributes"
        "structuralEdges"
        "projectionFindings"
        "decisionFindings"
        "resolutional"
        "served"
        "provenance"
      ] (_: both REF);
    };
    # C12: unarmed, the reader is the substrate accessor, and every `nta` route answers as before
    test-C12-unarmed-is-unchanged = {
      expr = [
        cr.names.unarmed
        cr.nta.unarmed.childNames
        (removeAttrs cr.nta.unarmed [ "childNames" ])
        cr.k3.unarmed-shape
        cr.k3.unarmed-kids
      ];
      expected = [
        openNames
        openNames
        {
          getHostAt-child-reads-host = "r/a";
          getNta-host-reads-child = 1;
          getNta-nta-eval = 3;
          node-child-eval = 1;
          own-nta-eval = 1;
        }
        {
          children.kid = [
            "_eval"
            "id"
          ];
          bytype = prelude.genAttrs [ "consumer" "gk" "kid" "kid2" "parent" "producer" ] (_: [
            "decls"
            "id"
            "parent"
            "type"
          ]);
        }
        { kid = "NO_DECLS"; }
      ];
    };
    # C13: the read seam's own guard, as a control: `get` / `node` refuse undeclared and hold warm
    # parity declared; a self-read answers under either relation
    test-C13-get-and-node-guarded-with-warm-parity = {
      expr = pick [ "get" "node-decls" "self-get" ] cr.cells;
      expected = {
        get = {
          undeclared = REF;
          declared = parity 1 9;
        };
        node-decls = {
          undeclared = REF;
          declared = parity 1 9;
        };
        self-get = both (parity 0 9);
      };
    };
  };
}
