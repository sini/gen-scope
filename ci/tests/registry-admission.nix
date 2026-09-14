# THE REGISTRY ADMISSION DOOR — that the evaluator and the constructor admit only a registry
# `mkKinds` built, and that refusing it yields a VALUE the caller can act on.
#
# ── WHY THE ASSERTION IS `tryEval` AND NOT A MESSAGE ──
# What these cells hold is not that a refusal is worded well; `tests-error.nix` holds that. It is
# that a refusal EXISTS AT ALL where previously there was none — and the state it replaced was not
# a wrong answer but an UNCATCHABLE ABORT. Handed a registry whose `below` relation names itself,
# the spawn channel in `eval.nix` expands without bound and the evaluation dies `stack overflow;
# max-call-depth exceeded`, which `builtins.tryEval` DOES NOT CONTAIN: the whole evaluation goes,
# and a caller gets no value to act on, not even a `false`.
#
# So `{ success = false; }` here is the entire content of the change. A cell asserting only "the
# node list is right" would pass over a library that still overflowed on the forged input, and a
# cell asserting only a message would pass over one that printed the right words on its way down.
#
# ── THE TWO WITNESSES, AND WHY BOTH ──
# W1 names ITSELF in its own `below` set. W2 is a two-cycle in which NEITHER record names itself,
# and it is the one that settles the design: the strongest refusal a single kind record could carry
# — `mkKind` rejecting `name ∈ below` — leaves W2 untouched, because acyclicity is a property of
# the SET and no member can see the set. That is why the verdict lives at `mkKinds` and why
# admission is a question about PROVENANCE, answered by a tag at a door.
#
# ── AND WHY BOTH DOORS ──
# `buildRoots` refuses at CONSTRUCTION, so the malformed scope record never forms. `requireScope`
# refuses at the EVALUATOR, covering the one route that skips the constructor — a hand-built record,
# which this suite itself uses and the published surface permits. Neither subsumes the other.
{ genScope, ... }:
let
  # One spawn per host, keyed by the produced id so each level mints a fresh node. Under a
  # descending registry this fires once; under W1 or W2 it is what expands without bound.
  spawnOf = _self: id: {
    "${id}-i" = {
      id = "${id}-i";
      parent = id;
      decls = { };
    };
  };

  # ── W1 — self-naming. `mkKind` BUILDS this record (rc 0): the per-record checks are
  # `spawns ⊆ below` and the field shapes, and `spawns.k` with `below = [ "k" ]` satisfies both.
  # `mkKinds` is what refuses it, and nothing required `mkKinds` to have run.
  w1 = {
    kinds.k = genScope.mkKind {
      name = "k";
      below = [ "k" ];
      spawns.k = spawnOf;
    };
  };

  # ── W2 — a two-cycle. BOTH records build and NEITHER names itself.
  w2 = {
    kinds = {
      a = genScope.mkKind {
        name = "a";
        below = [ "b" ];
        spawns.b = spawnOf;
      };
      b = genScope.mkKind {
        name = "b";
        below = [ "a" ];
        spawns.a = spawnOf;
      };
    };
  };

  # ── THE CONTROL REGISTRY — the same shape, through `mkKinds`, descending.
  # `host` ranks above `item` and `item` spawns nothing, so the expansion is one level deep.
  okKinds = genScope.mkKinds [
    (genScope.mkKind {
      name = "host";
      below = [ "item" ];
      spawns.item = spawnOf;
    })
    (genScope.mkKind { name = "item"; })
  ];

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
  runEval = scope: (genScope.eval { inherit scope attributes; }).allNodeIds;

  # Forced, because a refusal on the far side of a lazy field is a refusal nothing reached: an
  # `attrNames` read of a record the constructor refuses can return before the guard runs.
  caught = e: builtins.tryEval (builtins.deepSeq e "ADMITTED");
in
{
  flake.tests.registry-admission = {
    # ── (a) THE EVALUATOR'S DOOR — what `requireScope`'s fifth conjunct buys ──
    # Before it, each of these exited `stack overflow; max-call-depth exceeded` THROUGH this
    # `tryEval`, which is what makes `success = false` the measurement rather than the formality.
    test-eval-refuses-a-self-naming-registry-catchably = {
      expr = caught (runEval (handBuilt w1 "k"));
      expected = {
        success = false;
        value = false;
      };
    };

    # The witness no record-level check could reach.
    test-eval-refuses-a-two-cycle-registry-catchably = {
      expr = caught (runEval (handBuilt w2 "a"));
      expected = {
        success = false;
        value = false;
      };
    };

    # ── (b) THE CONSTRUCTOR'S DOOR — the record never forms ──
    # The arm DOMINATES the unregistered-kind arm beside it, and the order is load-bearing:
    # `unregisteredKinds` reads `kinds.kinds or { }`, and that read IS the unvalidated read.
    test-buildRoots-refuses-a-self-naming-registry-at-construction = {
      expr = caught (buildScope w1 "k");
      expected = {
        success = false;
        value = false;
      };
    };

    test-buildRoots-refuses-a-two-cycle-registry-at-construction = {
      expr = caught (buildScope w2 "a");
      expected = {
        success = false;
        value = false;
      };
    };

    # ── (c) THE CONTROLS — that the doors are not refusing everything ──
    # A registry that DID pass `mkKinds`, through the constructor and then the evaluator, spawn and
    # all. Without this the four cells above are equally satisfied by a library that refuses every
    # registry there is.
    test-control-a-minted-registry-builds-and-evaluates = {
      expr = runEval (buildScope okKinds "host");
      expected = [
        "root"
        "root-i"
      ];
    };

    # The same registry on the hand-built route, so the evaluator's guard is shown to ADMIT on the
    # very path the two cells in (a) refuse on. Same door, same shape, opposite verdict.
    test-control-a-minted-registry-passes-the-hand-built-route = {
      expr = runEval (handBuilt okKinds "host");
      expected = [
        "root"
        "root-i"
      ];
    };

    # ── (d) THE NO-KINDS CASES, WHICH ARE NOT A DEGENERATE CORNER ──
    # `buildRoots`' own default is `null` and `gen-link` calls it with no `kinds` at all, so an
    # admit-set reading "require `isKindSet`" would break most callers in the ecosystem. Absent and
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

    # ── (e) THE DISCRIMINATOR ITSELF ──
    # Both arms, so the predicate is shown to separate rather than to answer one way. This is the
    # whole of what the two doors ask, and publishing it is what keeps ONE spelling of the tag: a
    # second copy inlined at a door is the drift `require-declared-dependencies.nix` exists to
    # prevent.
    test-isKindSet-admits-what-mkKinds-built = {
      expr = genScope.isKindSet okKinds;
      expected = true;
    };

    test-isKindSet-refuses-a-record-that-merely-has-kinds = {
      expr = genScope.isKindSet w1;
      expected = false;
    };

    # It is NOMINAL, which is the point: a forged record carrying the tag is admitted, and nothing
    # at a door can check that the `below` relation behind the tag was ever ranked. That is the
    # cooperative-caller bargain `kindMarker` and `claimMarker` already make, stated here so it is
    # measured rather than assumed unbroken.
    test-isKindSet-is-nominal-not-structural = {
      expr = genScope.isKindSet (w1 // { _type = "gen-scope/kind-set"; });
      expected = true;
    };

    test-isKindSet-refuses-a-non-attrset = {
      expr = [
        (genScope.isKindSet null)
        (genScope.isKindSet [ ])
        (genScope.isKindSet "kinds")
      ];
      expected = [
        false
        false
        false
      ];
    };
  };
}
