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
{
  genScope,
  genGraph,
  genPreludeLib,
  genAlgebra,
  ...
}:
let
  prelude = genPreludeLib;
  refused = v: !(builtins.tryEval (builtins.deepSeq v v)).success;

  # ── the planted evaluator ──
  anchor = "            _childSet = id: attrName: demand \"self.get\" id attrName;\n";
  source = builtins.readFile ../../lib/eval.nix;
  planted =
    let
      text = builtins.replaceStrings [ anchor "import ./" ] [
        (anchor + "            _zzPlanted = id: attrName: demand \"self.get\" id attrName;\n")
        "import ${../../lib}/"
      ] source;
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
    planted-read = self: id: if id == "a" && self ? _zzPlanted then self._zzPlanted "b" "own-v" else "ABSENT";
    # K3: the published helpers, read from `root`
    kids = self: id: if id == "root" then builtins.mapAttrs (_: r: r.decls.v) (genScope.children self "a") else { };
    kid-keys = self: id: if id == "root" then builtins.attrNames (genScope.children self "a") else [ ];
    by-type = self: id: if id == "root" then builtins.attrNames (genScope.nodesByType self "host") else [ ];
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
  };
}
