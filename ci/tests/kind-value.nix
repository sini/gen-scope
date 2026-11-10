# A KIND CARRIES ITS KIND VALUE, AND EVERY NODE OF THAT KIND CARRIES IT (den-hoag-l0y, arm (B′)).
# The refusals are message cells in `ci/tests-error.nix`'s `kind-value-refusals`; these are the
# admitting half over the same fixtures.
#
# The kind values here are SHAPE fixtures: records carrying gen-schema's tagged sum
# (`kind`, `__mint.minted`) and its total `__sealed` without having been minted. That is the whole
# of what gen-scope reads — it takes no gen-schema input; its door asks `__mint ? minted`, and two
# values at one mark are decided over `__sealed` (den-hoag-gzjf7) — so a minted value and this
# fixture cross the door identically. The minted value's behaviour at `sel.kind` is gen-select's to
# test.
{ genScope, genGraph, ... }:
let
  S = genScope;
  # den-hoag-25mup: one root's read beside an incoherent root (`_fixtures/kind-value-read.nix`).
  kr = import ./_fixtures/kind-value-read.nix { inherit genScope genGraph; };
  inherit (kr) planted unplanted;
  # The walk and the by-id read hand out one record. `hand` builds a host-kinded hand record; `attrs`
  # the attribute set every walk fixture below evaluates.
  hand = id: parent: {
    inherit id parent;
    type = "host";
    decls = { };
  };
  attrs = {
    children = _: _: { };
    probe = _self: _id: 3;
  };
  kidOf =
    spawn:
    S.mkKinds [
      (S.mkKind { } "kid")
      (S.mkKind {
        below = [ "kid" ];
        spawns.kid = spawn;
      } "host")
    ];
  # W1: p's body selects the registered c under its key, handing a DIFFERENT record.
  bodyEv =
    S.eval { }
      {
        children =
          _: id:
          if id == "p" then
            {
              c = hand "c" "p" // {
                marker = "BODY";
              };
            }
          else
            { };
      }
      {
        nodes = {
          p = hand "p" null;
          c = hand "c" "p";
        };
        nodeOrder = [ "p" ];
      };
  # W3: h0 and h1 both spawn the key `h0/m` (markers H0 / H1); `parseParent` places it under h0, and
  # the walk reaches h1 first.
  xppEv =
    S.eval
      {
        parseParent = id: if id == "h0/m" then "h0" else null;
      }
      attrs
      {
        nodes = {
          h0 = hand "h0" null;
          h1 = hand "h1" null;
        };
        nodeOrder = [
          "h1"
          "h0"
        ];
        kinds = kidOf (
          _: id: {
            "h0/m" = {
              decls = { };
              marker = if id == "h1" then "H1" else "H0";
            };
          }
        );
      };
  # W4: no `parseParent`; roots b and a each spawn the key `m`, and the walk reaches b first.
  dupeEv = S.eval { } attrs {
    nodes = {
      a = hand "a" null;
      b = hand "b" null;
    };
    nodeOrder = [
      "b"
      "a"
    ];
    kinds = kidOf (_: _: { m.decls = { }; });
  };
  # D2: root h spawns `h/kids/k`; `evalDebug` with no `parseParent` cannot place k.
  kScope = {
    nodes.h = hand "h" null;
    nodeOrder = [ "h" ];
    kinds = kidOf (_: id: { "${id}/kids/k".decls = { }; });
  };
  valueOf = name: mark: {
    kind = name;
    __mint.minted = mark;
    __sealed = { };
  };
  hostA = valueOf "host" "host:a";
  # The shape a gen-schema kind with an option default has: a mark beside a sealed component.
  sealedHost = hostA // {
    __sealed."open.options.port.default" = 22;
  };
  sealedReg = S.mkKinds [ (S.mkKind { kindValue = sealedHost; } "host") ];
  leafV = valueOf "leaf" "leaf:l";

  scopeWith =
    kinds:
    S.buildRoots {
      parentGraph = S.vertex "a";
      types.a = "host";
      inherit kinds;
    };
  declared = scopeWith (S.mkKinds [ (S.mkKind { kindValue = hostA; } "host") ]);
  bare = scopeWith (S.mkKinds [ (S.mkKind { } "host") ]);
  kindless = S.buildRoots { parentGraph = S.vertex "a"; };

  # A `//`-merged registry whose two records under `host` carry the SAME value: coherent.
  plain = S.mkKinds [
    (S.mkKind { } "host")
    (S.mkKind { below = [ "host" ]; } "leaf")
  ];
  withValue = r: v: r // { kindValue = v; };
  mergedCoherent = {
    kinds = {
      host = withValue plain.kinds.host hostA;
      leaf = plain.kinds.leaf // {
        belowKinds.host = withValue plain.kinds.host hostA;
      };
    };
  };

  mergedSealed = {
    kinds = {
      host = withValue plain.kinds.host sealedHost;
      leaf = plain.kinds.leaf // {
        belowKinds.host = withValue plain.kinds.host sealedHost;
      };
    };
  };

  # Hand-built records crossing the eval door: coherent with the registry, omitting the field, and
  # carrying a value in a scope whose registry declares none.
  handBuilt =
    kinds: node:
    (S.eval { } { children = _self: _id: { }; } {
      inherit kinds;
      nodeOrder = [ "a" ];
      nodes.a = {
        id = "a";
        type = "host";
        parent = null;
        decls = { };
      }
      // node;
    }).allNodeIds;
  valuedReg = S.mkKinds [ (S.mkKind { kindValue = hostA; } "host") ];
  bareReg = S.mkKinds [ (S.mkKind { } "host") ];

  # `host` spawns `leaf` children; both kinds declare a value.
  spawnScope = S.buildRoots {
    parentGraph = S.vertex "a";
    types.a = "host";
    kinds = S.mkKinds [
      (S.mkKind { kindValue = leafV; } "leaf")
      (S.mkKind {
        below = [ "leaf" ];
        kindValue = hostA;
        spawns.leaf = _self: id: {
          sprout = {
            id = "sprout";
            parent = id;
            decls = { };
          };
        };
      } "host")
    ];
  };
  sprout =
    (S.eval { } {
      children = _self: _id: { };
    } spawnScope).get
      "a"
      "derived-children";
in
{
  flake.tests.kind-value = {
    # ── den-hoag-25mup: THE CONJUNCT IS DECIDED AT THE NODE'S OWN READ ──
    # Every read below does not reach the incoherent `h1`'s record, and serves its value on the
    # coherent twin (each RED: the scope door's entry scan, which refused them all).
    test-25mup-A1-a-root-read-serves-beside-an-incoherent-root = {
      expr = map (g: (g.ev.node "h0").id) [
        planted
        unplanted
      ];
      expected = [
        "h0"
        "h0"
      ];
    };
    test-25mup-A2-a-roots-get-serves-beside-an-incoherent-root = {
      expr = planted.ev.get "h0" "children";
      expected = unplanted.ev.get "h0" "children";
    };
    test-25mup-A3-a-nested-read-serves-beside-an-incoherent-root = {
      expr = (planted.ev.node "h0/needles/h0-m").id;
      expected = "h0/needles/h0-m";
    };
    # The read a per-node kind test makes (gen-select's `sel.kind` reads the node's copy).
    test-25mup-A4-a-roots-kind-value-serves-beside-an-incoherent-root = {
      expr = (planted.ev.node "h0").kindValue.__mint.minted;
      expected = "thimble:t";
    };
    test-25mup-A5-a-roots-children-ids-serve-beside-an-incoherent-root = {
      expr = S.childrenIds planted.ev "h0";
      expected = [ "h0/needles/h0-m" ];
    };
    test-25mup-A6-the-folds-node-data-serves-beside-an-incoherent-root = {
      expr = builtins.attrNames (planted.fold.accessor.nodeData "h0");
      expected = [ "def" ];
    };
    test-25mup-A7-the-debug-lookup-serves-beside-an-incoherent-root = {
      expr = (planted.dbg.node "h0").id;
      expected = "h0";
    };
    # The selection's KEYS are a key test; only the incoherent record refuses (R10).
    test-25mup-A8-a-selection-of-an-incoherent-root-serves-its-keys = {
      expr = builtins.attrNames (planted.sel.get "h0" "children");
      expected = [ "h1" ];
    };
    # The live control of every refusal in `kind-value-refusals`' 25mup cells: the same reads on the
    # coherent twin serve, so each refusal is the plant's.
    test-25mup-the-coherent-twin-serves-every-read-the-planted-scope-refuses = {
      expr = {
        node = (unplanted.ev.node "h1").id;
        nested = (unplanted.ev.node "h1/needles/h1-m").id;
        get = unplanted.ev.get "h1" "children";
        universe = builtins.length unplanted.ev.allNodeIds;
        dbgNode = (unplanted.dbg.node "h1").id;
        dbgGet = unplanted.dbg.get "h1" "children";
        dbgNested = unplanted.dbg.get "h1/needles/h1-m" "children";
        fold = unplanted.fold.roots.h1.kindValue == kr.thimbleV;
        selection = (unplanted.sel.get "h0" "children").h1.kindValue == kr.thimbleV;
      };
      expected = {
        node = "h1";
        nested = "h1/needles/h1-m";
        get = { };
        universe = 8;
        dbgNode = "h1";
        dbgGet = { };
        dbgNested = { };
        fold = true;
        selection = true;
      };
    };
    # ── THE WALK HANDS OUT THE RECORD A BY-ID READ ANSWERS ──
    # W1: a registered child is the scope's record, whatever record a body selects it with.
    test-25mup-W1-the-walk-hands-out-a-registered-childs-own-record = {
      expr = [
        (bodyEv.allNodes.c.marker or "ROOTS")
        ((bodyEv.node "c").marker or "ROOTS")
      ];
      expected = [
        "ROOTS"
        "ROOTS"
      ];
    };
    # W3: a key two parents spawn is the record of the parent `parseParent` places it under.
    test-25mup-W3-a-key-two-parents-spawn-is-the-placed-parents-record = {
      expr = {
        walk = xppEv.allNodes."h0/m".marker;
        node = (xppEv.node "h0/m").marker;
        parent = xppEv.allNodes."h0/m".parent;
      };
      expected = {
        walk = "H0";
        node = "H0";
        parent = "h0";
      };
    };
    # W4: with no `parseParent` the walk resolves every child by id, so it agrees with `node`.
    test-25mup-W4-an-unplaced-duplicate-key-is-the-by-id-record = {
      expr = dupeEv.allNodes.m.parent == (dupeEv.node "m").parent;
      expected = true;
    };
    # D2: `evalDebug` with no `parseParent` decides a non-root read as the scope door did — every
    # root's record — and serves it on a coherent scope, as `eval` does.
    test-25mup-D2-a-debug-read-it-cannot-place-serves-on-a-coherent-scope = {
      expr = [
        ((S.evalDebug { } attrs kScope).get "h/kids/k" "probe")
        ((S.eval { } attrs kScope).get "h/kids/k" "probe")
      ];
      expected = [
        3
        3
      ];
    };
    # c7: a scope with no kinds keeps the node record it always had, field for field.
    test-c7-a-kindless-node-carries-no-kind-value = {
      expr = builtins.attrNames kindless.nodes.a;
      expected = [
        "decls"
        "id"
        "parent"
        "type"
      ];
    };
    # c13: and so does a kinded scope whose kinds declare no value — the per-scope choice.
    test-c13-a-kinded-scope-declaring-no-value-keeps-the-record = {
      expr = builtins.attrNames bare.nodes.a;
      expected = [
        "decls"
        "id"
        "parent"
        "type"
      ];
    };
    # The node carries its kind's value itself — the same reference: one mark, one sealed subject.
    test-a-node-carries-its-kinds-value = {
      expr = declared.nodes.a.kindValue.__mint.minted;
      expected = "host:a";
    };
    test-a-kind-carries-the-value-it-declared = {
      expr = declared.kinds.kinds.host.kindValue.__mint.minted;
      expected = "host:a";
    };
    # c11b: a merge whose records under one name carry one value is admitted.
    test-c11b-a-coherent-merged-registry-is-admitted = {
      expr =
        builtins.attrNames
          (S.buildRoots {
            types.a = "host";
            kinds = mergedCoherent;
          }).nodes;
      expected = [ "a" ];
    };
    # C2's admitting half: a hand-built node carrying its kind's own value, one omitting the field
    # (kind-blind, refused by name at `sel.kind`), and one carrying a value in a scope whose registry
    # declares none (the node's own declaration, authoritative there).
    test-C2-a-hand-built-node-carrying-its-kinds-value-is-admitted = {
      expr = handBuilt valuedReg { kindValue = hostA; };
      expected = [ "a" ];
    };
    test-C2-a-hand-built-node-omitting-the-value-is-admitted = {
      expr = handBuilt valuedReg { };
      expected = [ "a" ];
    };
    test-C2-a-node-carried-value-in-a-scope-declaring-none-is-admitted = {
      expr = handBuilt bareReg { kindValue = hostA; };
      expected = [ "a" ];
    };
    # den-hoag-dg8d1: a kind value beside sealed components is admitted and bucketed by its MARK
    # (gen-algebra's `hasMark`/`markOf`), where `identityOf` answers the compared arm for it. Both
    # doors read it: `mkKinds` admission and the eval door's node-against-registry comparison, whose
    # live arm is a node carrying a different kind's value.
    test-dg8d1-a-sealed-kind-value-is-admitted-and-bucketed-by-its-mark = {
      expr = {
        declared = (scopeWith sealedReg).nodes.a.type;
        coherent = handBuilt sealedReg { kindValue = sealedHost; };
        contradicting = (builtins.tryEval (handBuilt sealedReg { kindValue = leafV; })).success;
      };
      expected = {
        declared = "host";
        coherent = [ "a" ];
        contradicting = false;
      };
    };
    # gzjf7: at one mark the sealed subjects decide, so a node carrying its kind's OWN sealed value
    # is admitted, and so is a `//` merge whose two records carry that one value.
    test-gzjf7-one-sealed-value-at-one-mark-is-one-kind = {
      expr = {
        node = handBuilt sealedReg { kindValue = sealedHost; };
        merge = (scopeWith mergedSealed).nodes.a.type;
      };
      expected = {
        node = [ "a" ];
        merge = "host";
      };
    };
    # c14: a spawned child carries its PRODUCED kind's value, stamped with its `type`.
    test-c14-a-spawned-child-carries-its-kinds-value = {
      expr = {
        inherit (sprout.sprout) type;
        mark = sprout.sprout.kindValue.__mint.minted;
      };
      expected = {
        type = "leaf";
        mark = "leaf:l";
      };
    };
  };
}
