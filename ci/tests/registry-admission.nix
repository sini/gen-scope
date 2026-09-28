# THE KIND DOMAIN, BY CONSTRUCTION — that a kind outside the domain cannot be minted, that the
# evaluator's spawn chain follows minted records, and that the registry doors decide a TYPE.
#
# ── WHY THE ASSERTION IS `tryEval` AND NOT A MESSAGE ──
# What these cells hold is not that a refusal is worded well; `tests-error.nix` holds that. It is
# that a refusal EXISTS AT ALL where previously there was none — and the state it replaced was not
# a wrong answer but an UNCATCHABLE ABORT. A spawn chain that does not descend expands without
# bound and the evaluation dies `stack overflow; max-call-depth exceeded`, which `builtins.tryEval`
# DOES NOT CONTAIN: the whole evaluation goes, and a caller gets no value to act on, not even a
# `false`. So `{ success = false; }` here is the entire content of a refusal cell.
#
# ── THE TWO WITNESSES, AND WHY NEITHER IS A KIND ──
# W1 names ITSELF in its own `below` set. W2 is a two-cycle in which NEITHER record names itself.
# `mkKind` builds both, and what it builds is a DECLARATION: the fold in `mkKinds` is the sole
# producer of a kind, and it resolves each `below` name against the kinds minted strictly earlier,
# so neither witness can be minted in any order. There is no cycle check to meet or miss.
#
# ── THE MERGE, AND WHY TERMINATION DOES NOT REST ON THE DOOR ──
# Two registries `mkKinds` built from declarations that disagree — `host` above `item` in one,
# `item` above `host` in the other — merged with `//`. Looked up by name, a spawned node's kind
# re-routes through the other registry and the chain cycles. The evaluator follows the RECORDS each
# kind resolved when it was minted, so the chain descends a `depth` fixed at minting whatever the
# registry value; the door refuses the merge anyway, by name, because it files two different kinds
# under one name and a reader looking a kind up by name would silently get the other one.
{ genScope, ... }:
let
  inherit (genScope) mkKind mkKinds;

  # One spawn per host, keyed by the produced id so each level mints a fresh node.
  spawnOf = suffix: _self: id: {
    "${id}-${suffix}" = {
      id = "${id}-${suffix}";
      parent = id;
      decls = { };
    };
  };

  # ── W1 — self-naming. A declaration; `mkKinds` cannot mint it.
  w1 = mkKind {
    below = [ "k" ];
    spawns.k = spawnOf "k";
  } "k";

  # ── W2 — a two-cycle. Both halves are declarations and NEITHER names itself.
  w2a = mkKind {
    below = [ "b" ];
    spawns.b = spawnOf "i";
  } "a";
  w2b = mkKind {
    below = [ "a" ];
    spawns.a = spawnOf "i";
  } "b";

  # ── THE CONTROL REGISTRY — `host` ranks above `item` and `item` spawns nothing, so the
  # expansion is one level deep. Declared leaf first: a kind follows the kinds its `below` names.
  itemDecl = mkKind { } "item";
  hostDecl = mkKind {
    below = [ "item" ];
    spawns.item = spawnOf "i";
  } "host";
  okKinds = mkKinds [
    itemDecl
    hostDecl
  ];

  # ── G3 — two honest registries whose declarations disagree, merged with `//`.
  upKinds = mkKinds [
    (mkKind { } "host")
    (mkKind {
      below = [ "host" ];
      spawns.host = spawnOf "i";
    } "item")
  ];
  merged = okKinds // {
    kinds = okKinds.kinds // {
      inherit (upKinds.kinds) item;
    };
  };

  # ── C1's admitted arm — two registries sharing an IDENTICAL leaf, merged. Every name maps to
  # one kind, so the merge is coherent and admitted.
  leafDecl = mkKind { } "leaf";
  leftKinds = mkKinds [
    leafDecl
    (mkKind {
      below = [ "leaf" ];
      spawns.leaf = spawnOf "l";
    } "left")
  ];
  rightKinds = mkKinds [
    leafDecl
    (mkKind {
      below = [ "leaf" ];
      spawns.leaf = spawnOf "r";
    } "right")
  ];
  sharedLeaf = leftKinds // {
    kinds = leftKinds.kinds // rightKinds.kinds;
  };

  # ── C5 — which record the evaluator follows, made observable. The door compares two kinds on
  # `name`, `below`, `depth` and their key sets, and NOT on builder bodies, so two registries whose
  # `mid` differs only in its builder merge coherently. A spawned `mid` node then spawns through the
  # builder of the `mid` record its host resolved — `-x` — and a by-name read would give `-y`.
  midDecl =
    suffix:
    mkKind {
      below = [ "leaf" ];
      spawns.leaf = spawnOf suffix;
    } "mid";
  topKinds = mkKinds [
    leafDecl
    (midDecl "x")
    (mkKind {
      below = [ "mid" ];
      spawns.mid = spawnOf "m";
    } "top")
  ];
  otherMid = mkKinds [
    leafDecl
    (midDecl "y")
  ];
  builderSplit = topKinds // {
    kinds = topKinds.kinds // {
      inherit (otherMid.kinds) mid;
    };
  };

  # ── C4 — a minted host updated with `//`. The gate's literal edit adds a spawn key alone; the
  # second also extends `below`, which is the edit that passes the door's per-entry type check and
  # reaches the evaluator, where the key has no resolved record to stamp.
  editedSpawnOnly = okKinds // {
    kinds = okKinds.kinds // {
      host = okKinds.kinds.host // {
        spawns = okKinds.kinds.host.spawns // {
          extra = spawnOf "e";
        };
      };
    };
  };
  editedBelowAndSpawn = okKinds // {
    kinds = okKinds.kinds // {
      host = okKinds.kinds.host // {
        below = okKinds.kinds.host.below ++ [ "extra" ];
        spawns = okKinds.kinds.host.spawns // {
          extra = spawnOf "e";
        };
      };
    };
  };

  # ── C3 — one declaration set in two admissible orders, and reversed.
  diamondA = [
    (mkKind { } "leaf")
    (mkKind {
      below = [ "leaf" ];
    } "a")
    (mkKind {
      below = [ "leaf" ];
    } "b")
    (mkKind {
      below = [
        "a"
        "b"
      ];
    } "top")
  ];
  diamondB = [
    (builtins.elemAt diamondA 0)
    (builtins.elemAt diamondA 2)
    (builtins.elemAt diamondA 1)
    (builtins.elemAt diamondA 3)
  ];
  measured = ks: {
    inherit (ks) maxDepth;
    depth = builtins.mapAttrs (_: k: k.depth) ks.kinds;
    below = builtins.mapAttrs (_: k: k.below) ks.kinds;
  };

  buildScope =
    kinds: rootKind:
    genScope.buildRoots {
      parentGraph = genScope.vertex "root";
      types.root = rootKind;
      decls.root = { };
      inherit kinds;
    };

  # The hand-built record: the route `buildRoots` does not stand in front of.
  handBuilt = kinds: type: {
    nodes.root = {
      id = "root";
      inherit type;
      parent = null;
      decls = { };
    };
    nodeOrder = [ "root" ];
    inherit kinds;
  };

  attributes.children = _self: _id: { };
  runEval = scope: (genScope.eval { } attributes scope).allNodeIds;

  # Forced, because a refusal on the far side of a lazy field is a refusal nothing reached.
  caught = e: builtins.tryEval (builtins.deepSeq e "ADMITTED");
  refused = {
    success = false;
    value = false;
  };
in
{
  flake.tests.registry-admission = {
    # ── G1 / G2 — NO KIND OUTSIDE THE DOMAIN EXISTS ──
    # `mkKind` returns a declaration, and the fold cannot mint either witness.
    test-G1-a-self-naming-declaration-is-not-a-kind = {
      expr = w1._type;
      expected = "gen-scope/kind-declaration";
    };
    test-G1-mkKinds-refuses-a-self-naming-declaration-catchably = {
      expr = caught (mkKinds [ w1 ]);
      expected = refused;
    };
    test-G2-neither-half-of-a-two-cycle-is-a-kind = {
      expr = [
        w2a._type
        w2b._type
      ];
      expected = [
        "gen-scope/kind-declaration"
        "gen-scope/kind-declaration"
      ];
    };
    test-G2-mkKinds-refuses-a-two-cycle-in-either-order-catchably = {
      expr = [
        (caught (mkKinds [
          w2a
          w2b
        ]))
        (caught (mkKinds [
          w2b
          w2a
        ]))
      ];
      expected = [
        refused
        refused
      ];
    };

    # ── G3 / C1 — THE MERGE IS REFUSED AT BOTH DOORS, BY NAME AND CATCHABLY ──
    test-G3-eval-refuses-a-merge-that-files-two-kinds-under-one-name = {
      expr = caught (runEval (handBuilt merged "host"));
      expected = refused;
    };
    test-G3-buildRoots-refuses-the-same-merge = {
      expr = caught (buildScope merged "host");
      expected = refused;
    };
    # C1's admitted arm: a merge in which every name denotes one kind evaluates, both spawns firing.
    test-C1-a-coherent-shared-leaf-merge-is-admitted = {
      expr = [
        (runEval (buildScope sharedLeaf "left"))
        (runEval (buildScope sharedLeaf "right"))
      ];
      expected = [
        [
          "root"
          "root-l"
        ]
        [
          "root"
          "root-r"
        ]
      ];
    };

    # ── C5 — A SPAWNED NODE'S KIND IS THE STAMPED RECORD ──
    # The `mid` node is spawned from `top`, and its own spawn runs the builder of the `mid` record
    # `top` resolved (`-x`), not the one the registry files under `mid` (`-y`).
    test-C5-a-spawned-node-spawns-through-the-record-its-host-resolved = {
      expr = runEval (buildScope builderSplit "top");
      expected = [
        "root"
        "root-m"
        "root-m-x"
      ];
    };
    test-C5-the-stamped-kind-is-the-spawn-keys-record = {
      expr =
        let
          ev = genScope.eval { } attributes (buildScope topKinds "top");
        in
        {
          inherit ((ev.node "root-m")._kind) name depth below;
        };
      expected = {
        name = "mid";
        depth = 1;
        below = [ "leaf" ];
      };
    };

    # ── G4 — A HAND-BUILT REGISTRY OF DECLARATIONS IS A TYPE REFUSAL ──
    test-G4-eval-refuses-a-registry-of-declarations-catchably = {
      expr = caught (runEval (handBuilt { kinds.k = w1; } "k"));
      expected = refused;
    };
    test-G4-buildRoots-refuses-a-registry-of-declarations-catchably = {
      expr = caught (buildScope { kinds.k = w1; } "k");
      expected = refused;
    };
    # A hand-built registry of MINTED kinds is admitted: every minted kind is in the domain.
    test-G4-a-hand-built-registry-of-minted-kinds-is-admitted = {
      expr = runEval (handBuilt { inherit (okKinds) kinds; } "host");
      expected = [
        "root"
        "root-i"
      ];
    };

    # ── C2 — A DUPLICATE NAME IS REFUSED BEFORE THE FOLD ──
    test-C2-two-same-name-declarations-are-refused = {
      expr = caught (mkKinds [
        itemDecl
        itemDecl
      ]);
      expected = refused;
    };

    # ── C3 — ADR-0016 RULING 7: THE MINTED REGISTRY IS INVARIANT UNDER ADMISSIBLE ORDER ──
    test-C3-two-admissible-orders-mint-the-same-registry = {
      expr = measured (mkKinds diamondA) == measured (mkKinds diamondB);
      expected = true;
    };
    test-C3-the-control-measure = {
      expr = measured (mkKinds diamondA);
      expected = {
        maxDepth = 2;
        depth = {
          leaf = 0;
          a = 1;
          b = 1;
          top = 2;
        };
        below = {
          leaf = [ ];
          a = [ "leaf" ];
          b = [ "leaf" ];
          top = [
            "a"
            "b"
          ];
        };
      };
    };
    # Admissibility is NOT invariant: the same set reversed is refused, by name.
    test-C3-the-reversed-order-is-refused = {
      expr = caught (mkKinds (builtins.genList (i: builtins.elemAt diamondA (3 - i)) 4));
      expected = refused;
    };

    # ── C4 — A `//`-EDITED MINTED HOST IS REFUSED BY NAME, CATCHABLY ──
    # The spawn key alone: refused at the door, a spawn outside the entry's own `below`.
    test-C4-an-extra-spawn-key-is-refused-at-the-door = {
      expr = caught (runEval (handBuilt editedSpawnOnly "host"));
      expected = refused;
    };
    # The key with its `below` name: the door admits the entry, and the evaluator finds no resolved
    # record to stamp for the key.
    test-C4-an-extra-spawn-with-no-resolved-kind-is-refused-at-the-spawn = {
      expr = caught (runEval (handBuilt editedBelowAndSpawn "host"));
      expected = refused;
    };

    # ── THE CONTROLS — that the doors are not refusing everything ──
    test-control-a-minted-registry-builds-and-evaluates = {
      expr = runEval (buildScope okKinds "host");
      expected = [
        "root"
        "root-i"
      ];
    };
    test-control-a-minted-registry-passes-the-hand-built-route = {
      expr = runEval (handBuilt okKinds "host");
      expected = [
        "root"
        "root-i"
      ];
    };

    # ── THE NO-KINDS CASES, WHICH ARE NOT A DEGENERATE CORNER ──
    # `buildRoots`' own default is `null` and `gen-link` calls it with no `kinds` at all. Absent and
    # `null` are the same case and both pass.
    test-control-an-explicitly-null-registry-passes = {
      expr = runEval (handBuilt null null);
      expected = [ "root" ];
    };
    test-control-a-record-with-no-kinds-field-passes = {
      expr = runEval {
        nodes.root = {
          id = "root";
          type = null;
          parent = null;
          decls = { };
        };
        nodeOrder = [ "root" ];
      };
      expected = [ "root" ];
    };
    test-control-buildRoots-with-no-registry-still-builds = {
      expr = runEval (
        genScope.buildRoots {
          parentGraph = genScope.vertex "root";
          decls.root = { };
        }
      );
      expected = [ "root" ];
    };

    # ── THE RETIRED PREDICATE ──
    # `isKindSet` answered provenance by a tag `//` preserves; it left the surface.
    test-isKindSet-is-not-published = {
      expr = genScope ? isKindSet;
      expected = false;
    };
  };
}
