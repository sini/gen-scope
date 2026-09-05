# THE RELATION A REUSE LAYER READS — the accessor's dependency union, its normalization, and its
# direction.
#
# The seal carries TWO dependency relations and they are no longer one value under two names: the
# formal `declaredDependencies` is the contracted relation a grammar gate runs over, and
# `accessor.dependencies` is the union that relation induces together with the substrate's own
# structural edges. What these cells hold is that the two really are two, that the union is
# normalized at the single site that builds it, and that it points the way a staleness cone needs it
# to point.
#
# THE GATE'S FIELD IS READ AT `declaredDependencies.dependencies <id>` because it is sealed as the
# CONTRACTED VALUE `gen-graph.mkDeclaredEdges` returns rather than as a bare function — which is what
# lets a consumer hand the field straight back to the entry it must call. The relation these cells
# assert is the same relation; only the door to it is named.
#
# ── WHY THE FIXTURE PUTS A NODE IN BOTH HALVES, AND WHY THAT IS THE LOAD-BEARING CHOICE ──
# A fixture carrying only a STRUCTURAL-ONLY edge cannot see the normalization defect at all: with no
# node in both relations the union has no duplicate, so the raw union and the deduped one coincide
# and a suite built on that fixture goes green against an unnormalized construction. The overlapping
# node is what makes these cells discriminating, and the structural-only node is kept beside it as
# the control that demonstrates the blindness rather than merely asserting it.
#
# ── WHAT THESE CELLS CANNOT REACH, STATED RATHER THAN SIMULATED ──
# The consumer's reuse predicate lives in another library and is not an input to this suite. What is
# reproduced here is the one line of normalization that consumer applies to whatever it receives,
# so the identity is measured against the shape it actually compares — but a run of that predicate,
# and its clean-reuses / dirty-refuses control pair, belong to the consumer's own suite.
{
  genScope,
  genGraph,
  genPreludeLib,
  lib,
  ...
}:
let
  inherit (genScope) foldEquations;

  flatKinds = names: genScope.mkKinds (map (name: genScope.mkKind { inherit name; }) names);

  # Four nodes, one containment edge. `kid` is `host`'s child, so it is in the structural relation
  # for `host`; `alpha` and `solo` are in no structural relation at all, which is what lets one of
  # them carry a declared-only edge and the other stand as the unrelated control.
  #
  # `alpha` is named so that it sorts BEFORE `kid` in codepoint order. That is deliberate: the union
  # is built structural-first, so a fixture whose declared member sorts after the structural one
  # would produce an already-sorted list and an order cell over it would be unable to tell a
  # first-occurrence order from a canonical one.
  roots = genScope.buildRoots {
    kinds = flatKinds [ "host" ];
    parentGraph = genScope.edge "kid" "host";
    decls = {
      host = {
        v = 10;
      };
      kid = {
        v = 1;
      };
      alpha = {
        v = 2;
      };
      solo = {
        v = 3;
      };
    };
    types = {
      host = "host";
      kid = "host";
      alpha = "host";
      solo = "host";
    };
  };

  equations = {
    self-v = {
      name = "self-v";
      kind = "synthesized";
      readsAttrs = [ ];
      stratum = "resolution";
      compute = self: id: (self.node id).decls.v;
    };
    children = {
      name = "children";
      kind = "nta";
      readsAttrs = [ ];
      stratum = "structural";
      compute = self: id: lib.filterAttrs (_: n: n.parent == id) roots.nodes;
    };
  };

  schedule = {
    inherit equations;
  };

  fold =
    declaredDependencies:
    foldEquations {
      scope = roots;
      inherit schedule declaredDependencies;
      parseParent = id: roots.nodes.${id}.parent or null;
    };

  # The entry admits only what `gen-graph.mkDeclaredEdges` minted, so the three arms below hand it
  # the contracted value rather than a bare function. The relation each arm declares is unchanged.
  contracted = import ./_fixtures/declared.nix {
    inherit genGraph;
    scope = roots;
  };

  # ── THE THREE ARMS, one per member of the identity ──
  # (a) STRUCTURAL-ONLY: `host` reaches `kid` and declares nothing.
  structuralOnly = fold (contracted { });
  # (b) DECLARED ∩ STRUCTURAL: `host` declares the very child it already reaches. The ordinary case,
  # and the only one in which the union can produce a duplicate.
  overlapping = fold (contracted {
    host = [ "kid" ];
  });
  # (c) ORDER: the two halves contribute different members, so the union carries both and its
  # first-occurrence order is observable.
  ordered = fold (contracted {
    host = [ "alpha" ];
  });

  nodes = structuralOnly.accessor.nodes;

  # THE CONSUMER'S NORMALIZATION, reproduced as the one line it is. A reuse layer dedups the relation
  # it is handed before comparing, so the identity must be measured against THAT shape and not
  # against the raw list — which is exactly the asymmetry the union introduced and the alias hid.
  planeNormalizes = deps: genPreludeLib.unique deps;

  # The comparison a reuse decision makes: what the seal recorded against what the accessor hands
  # back, as LISTS. Same members, same multiplicity, same order — set equality would not do.
  depsMatch = ctx: id: ctx.trace.${id}.deps == planeNormalizes (ctx.accessor.dependencies id);

  # THE SEEDED CONSTRUCTION: the union as it would be built with the normalization omitted. This is
  # the defect the site's `unique` refuses, expressed here so the refusal can be measured firing
  # rather than assumed.
  rawUnion =
    ctx: declared: id:
    ctx.eval.structuralEdges id ++ declared id;
  rawOverlapping = rawUnion overlapping (id: if id == "host" then [ "kid" ] else [ ]);
  rawStructuralOnly = rawUnion structuralOnly (_: [ ]);

  # One hop of the inversion a staleness cone is the closure of, taken over the SAME relation the
  # accessor publishes. Computing it here is what makes the direction cells a measurement of the
  # published relation rather than a restatement of the projection's own documentation.
  dependentsOf = deps: target: builtins.filter (n: builtins.elem target (deps n)) nodes;

  # THE TRANSPOSITION SEED: the projection with `from` and `to` swapped, so it answers child→parent.
  # It is deliberately built to look healthy — it returns a populated, plausible list for the very
  # node the correct relation reports on — because a cone computed from it is populated too, and
  # that is why nothing but a direction cell would catch it.
  transposed =
    id: builtins.filter (n: builtins.elem id (structuralOnly.eval.structuralEdges n)) nodes;
in
{
  flake.tests.dependency-union = {

    # ══ THE TWO FIELDS ARE TWO — the gate's relation is not the plane's ══
    # THE LEAK CHECK, AS A CELL. `declaredDependencies` is what a grammar gate reads and it must
    # carry exactly what the caller contracted; `accessor.dependencies` is what a reuse cone is taken
    # over and it must carry the union. Here the caller declared NOTHING, so the two fields differ,
    # and a change that leaked the union back into the formal would collapse them.
    test-the-gate-field-and-the-plane-field-are-not-the-same-relation = {
      expr = {
        gate = structuralOnly.declaredDependencies.dependencies "host";
        plane = structuralOnly.accessor.dependencies "host";
      };
      expected = {
        gate = [ ];
        plane = [ "kid" ];
      };
    };
    # ★ THE DISCRIMINATION CONTROL the cell above rests on: the two fields are not unconditionally
    # different. On a node with no structural edge they agree, so the cell measures a divergence
    # where one is owed rather than a blanket inequality that would hold under any wiring.
    test-control-the-two-fields-agree-where-there-is-no-structural-edge = {
      expr = {
        gate = overlapping.declaredDependencies.dependencies "kid";
        plane = overlapping.accessor.dependencies "kid";
      };
      expected = {
        gate = [ ];
        plane = [ ];
      };
    };
    # The formal is sealed under its own name and is untouched by the union: what the caller handed
    # in is what a gate reads back out, for the overlapping node too.
    test-the-sealed-formal-is-the-callers-own-relation = {
      expr = overlapping.declaredDependencies.dependencies "host";
      expected = [ "kid" ];
    };

    # ══ MEMBER (a) — THE STRUCTURAL-ONLY EDGE REACHES THE RELATION ══
    test-a-structural-only-edge-is-in-the-union = {
      expr = structuralOnly.accessor.dependencies "host";
      expected = [ "kid" ];
    };
    # THE SEED, MEASURED: the relation this field used to hold — the declared one alone — drops the
    # edge entirely. Same fixture, same run, so the cell above is a measurement of the union and not
    # of a graph that happened to declare its own topology.
    test-seed-the-declared-relation-alone-drops-the-structural-edge = {
      expr = structuralOnly.declaredDependencies.dependencies "host";
      expected = [ ];
    };
    # And it reaches the TRACE, which is the surface a reuse layer actually records.
    test-a-structural-only-edge-reaches-the-trace = {
      expr = structuralOnly.trace.host.deps;
      expected = [ "kid" ];
    };

    # ══ MEMBER (b) — THE OVERLAPPING NODE, AND THE NORMALIZATION ══
    # THE SEED, MEASURED AND NOT ARGUED: with the normalization omitted the union really does carry
    # the node twice. The duplicate is what a list-equality reuse predicate trips over.
    test-seed-the-unnormalized-union-carries-the-duplicate = {
      expr = rawOverlapping "host";
      expected = [
        "kid"
        "kid"
      ];
    };
    # THE SEED'S CONSEQUENCE: the seal would record the raw list while the consumer dedups what it is
    # handed, so the two sides disagree for exactly this node — and disagree permanently, because
    # nothing about the node ever changes to make them agree again.
    test-seed-the-unnormalized-union-fails-the-identity = {
      expr = rawOverlapping "host" == planeNormalizes (rawOverlapping "host");
      expected = false;
    };
    # THE OTHER HALF OF THE BIDIRECTIONAL REQUIREMENT: with the normalization applied at the site,
    # the same node passes. A cell measuring only this half cannot tell a working mechanism from a
    # fixture that never exercised one.
    test-the-normalized-union-holds-the-identity = {
      expr = depsMatch overlapping "host";
      expected = true;
    };
    test-the-normalized-union-emits-the-node-once = {
      expr = overlapping.accessor.dependencies "host";
      expected = [ "kid" ];
    };
    # ★ THE CONTROL THAT EXPLAINS WHY MEMBER (b) IS REQUIRED, and it is a measurement rather than a
    # caution: on the STRUCTURAL-ONLY node the seeded construction and the normalized one coincide,
    # so the identity holds even unnormalized. A suite whose fixture carried only that shape would
    # pass against the broken construction and report nothing.
    test-control-a-structural-only-fixture-cannot-see-the-normalization-defect = {
      expr = rawStructuralOnly "host" == planeNormalizes (rawStructuralOnly "host");
      expected = true;
    };

    # ══ MEMBER (c) — ORDER, DEFENSIVE ══
    # The reuse predicate is LIST equality, so order is part of the contract. It is not defended here
    # by a sort: the union is built at ONE site and the consumer receives that list, so there is no
    # second derivation for an order to diverge from. This member is DEFENSIVE for that reason and
    # RE-ARMS AS REQUIRED the moment a second construction site for the union appears anywhere — a
    # second derivation is the trigger, not any change in what the comparison means.
    test-the-union-carries-first-occurrence-order = {
      expr = ordered.accessor.dependencies "host";
      expected = [
        "kid"
        "alpha"
      ];
    };
    # THE CONSUMER CANNOT REORDER WHAT IT IS HANDED: its dedup is idempotent on an already-deduped
    # list, so the single construction site really is what fixes the order on both sides.
    test-the-consumers-dedup-is-idempotent-on-the-union = {
      expr =
        planeNormalizes (ordered.accessor.dependencies "host") == ordered.accessor.dependencies "host";
      expected = true;
    };
    # THE SEED: the same members in a different order — what a canonical sort applied on one side
    # only would produce. It fails the identity, which is what makes the two cells above load-bearing
    # rather than incidental.
    test-seed-the-same-members-permuted-fail-the-identity = {
      expr =
        ordered.accessor.dependencies "host"
        == builtins.sort builtins.lessThan (ordered.accessor.dependencies "host");
      expected = false;
    };
    test-the-ordered-union-holds-the-identity = {
      expr = depsMatch ordered "host";
      expected = true;
    };

    # ══ THE DIRECTION IS PARENT→CHILD ══
    # A changed CHILD must dirty its PARENT, so the parent has to appear in the inversion of the
    # published relation at the child. Getting this backwards inverts every cone silently.
    test-the-cone-of-a-changed-child-contains-its-parent = {
      expr = dependentsOf structuralOnly.accessor.dependencies "kid";
      expected = [ "host" ];
    };
    # ★ THE CONTROL WITHOUT WHICH A ⊤ RELATION PASSES: an unrelated node dirties nobody. The cell
    # above alone is satisfied by a relation that returns every node for every query.
    test-control-an-unrelated-node-dirties-nobody = {
      expr = dependentsOf structuralOnly.accessor.dependencies "solo";
      expected = [ ];
    };
    # THE TRANSPOSITION SEED, and the reason it needs a cell of its own: it is a one-character-class
    # error that produces a POPULATED, entirely plausible answer at the node under test …
    test-control-the-transposed-projection-looks-healthy = {
      expr = transposed "kid";
      expected = [ "host" ];
    };
    # … and yet the cone taken over it does not contain the parent. Nothing but a direction cell
    # separates these two facts.
    test-seed-the-transposed-projection-loses-the-parent-from-the-cone = {
      expr = dependentsOf transposed "kid";
      expected = [ ];
    };

    # ══ THE RECORD THE CONSUMER READS THROUGH ══
    # The accessor's field set, pinned as an EXACT set: a field added, dropped or renamed here is
    # a change to the interface a consumer binds against, and it should redden a cell rather than
    # surface as a missing attribute inside somebody else's fold. The fifth field is the guarded
    # trace lookup — the by-name refusal the sealed `trace.<id>` selection cannot carry.
    test-the-accessor-publishes-exactly-its-five-fields = {
      expr = builtins.attrNames structuralOnly.accessor;
      expected = [
        "dependencies"
        "nodeData"
        "nodes"
        "parent"
        "trace"
      ];
    };
    # The relation is total over the node set: every node the accessor enumerates answers, so a
    # consumer folding over `nodes` cannot meet a gap.
    test-the-union-is-total-over-the-accessors-node-set = {
      expr = map (id: builtins.isList (structuralOnly.accessor.dependencies id)) nodes;
      expected = [
        true
        true
        true
        true
      ];
    };
    # ★ ARMED: the node set really is the four-node one the cell above folds over, so an empty or
    # truncated enumeration cannot pass it by having nothing to check.
    test-control-the-accessors-node-set-is-the-whole-graph = {
      expr = nodes;
      expected = [
        "alpha"
        "host"
        "kid"
        "solo"
      ];
    };
  };
}
