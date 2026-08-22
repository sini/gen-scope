# The demand cascade's kind registry: what the measure is, what the registry refuses, and in what
# order it refuses it.
#
# ★ THE DEPTH CELLS ARE AN IDENTITY ORACLE AND THEY CANNOT PIN A RECURRENCE. The expected values
# below are the output of the previous construction, read at its own pins, on four shapes — the
# diamond is the discriminating one, since a chain agrees under a construction that re-walks
# shared producers and under one that does not. Four equalities over finite fixtures say nothing
# about a fifth shape, so the strict-decrease cells further down are quantified over the registry
# and over generated lattices instead.
#
# ★★ THE REFUSAL CELLS CARRY ARMED NEGATIVE CONTROLS, because two of them are about ORDER and an
# order cannot be observed from a cell that exercises one check on its own. The graph library's
# rank surface drops an edge leaving its cone silently, so a registry that checks unregistered
# names beside the measure rather than ahead of it answers depth 0 with no diagnostic — and an
# isolated refusal cell passes against exactly that registry. The `nonDominating` variant below IS
# that registry, built here so the cells can be measured against something that must fail them.
{
  genScope,
  genGraph,
  genPreludeLib,
  lib,
  ...
}:
let
  inherit (genScope) mkKind mkKinds;

  didThrow = e: !(builtins.tryEval (builtins.deepSeq e null)).success;
  succeeds = e: (builtins.tryEval (builtins.deepSeq e null)).success;

  leaf =
    name:
    mkKind {
      inherit name;
      resolve = _: _: { };
    };
  node =
    name: below:
    mkKind {
      inherit name below;
      resolve = _: _: { };
    };

  # ── FIXTURES ──
  # `levels` × `width`, every node at level i pointing at EVERY node at level i−1. Generated
  # rather than hand-written, so the shapes are not chosen to agree: `maxDepth == levels - 1` is
  # asserted separately, which is the independent check that the generator built the lattice it
  # claims and not a degenerate one.
  latticeNames = l: w: builtins.genList (i: "n${toString l}_${toString i}") w;
  lattice =
    levels: width:
    builtins.concatLists (
      builtins.genList (
        l: map (n: if l == 0 then leaf n else node n (latticeNames (l - 1) width)) (latticeNames l width)
      ) levels
    );

  chain = [
    (leaf "l0")
    (node "l1" [ "l0" ])
    (node "l2" [ "l1" ])
    (node "l3" [ "l2" ])
    (node "l4" [ "l3" ])
  ];
  diamond = [
    (leaf "leaf")
    (node "a" [ "leaf" ])
    (node "b" [ "leaf" ])
    (node "top" [
      "a"
      "b"
    ])
  ];
  fan = [
    (leaf "f0")
    (leaf "f1")
    (leaf "f2")
    (leaf "f3")
    (node "hub" [
      "f0"
      "f1"
      "f2"
      "f3"
    ])
  ];
  lattice43 = lattice 4 3;

  # The k8s registry, read for its measure only. The generated shapes above are chosen to
  # discriminate constructions; this one is the shape a consumer actually writes, and its depth map
  # is a golden carried over from the retiring library rather than derived here.
  k8s = import ./_fixtures/k8s.nix { inherit genScope; };

  ghost = [ (node "a" [ "ghost" ]) ];
  twoCycle = [
    (node "a" [ "b" ])
    (node "b" [ "a" ])
  ];
  selfLoop = [ (node "a" [ "a" ]) ];
  duplicated = [
    (leaf "a")
    (leaf "a")
  ];

  # ── FORGED KIND RECORDS: REACHING THE FIELD ARMS AT ALL ──
  # The intake predicate decides IN ORDER, and the marker arm sits ahead of every field arm. A bare
  # record is therefore refused for its PROVENANCE, and a cell built from one is green whatever the
  # arm it is named for does — measured, not argued: deleting `isString name` outright left such a
  # cell passing and the suite whole. Forging the marker is what puts the field arms on the path.
  #
  # ★ AND THE REST OF THE RECORD HAS TO BE WHOLE, which is the half that is easy to miss. The arms
  # BELOW the field checks ask for `resolve`, `dedupKey` and `fold` by presence, so a forged record
  # that stops at the marker is refused THERE instead — the same defect wearing a later arm, and
  # measurably so: with the provenance arm deleted the old bare records were still refused, two
  # arms further down, for carrying no `resolve`. Every field except the one under test is supplied
  # and well-formed here, which leaves exactly one thing wrong with the record and exactly one arm
  # that can answer for it.
  #
  # The marker is written as a LITERAL rather than read off the library. A forgery that imported
  # the constant it forges would agree with the library by construction and could not detect a
  # record the library refuses to recognise.
  forgedKind =
    fields:
    {
      _type = "gen-scope/kind";
      name = "ghost";
      below = [ ];
      resolve = _: _: { };
      dedupKey = null;
      fold = null;
    }
    // fields;

  # The same whole record with the marker WITHHELD: nothing else about it is wrong, so provenance
  # is the only arm that can refuse it, and deleting that arm has to let it register.
  unmarkedKind = removeAttrs (forgedKind { name = "a"; }) [ "_type" ];

  # ── THE ARMED VARIANT ──
  # The registry built the way the domination requirement forbids: the unregistered-name check is
  # a sibling binding that reading the measure never forces. Everything else is identical. It is
  # here to be measured, never to be used.
  nonDominating =
    kindList:
    let
      names = map (k: k.name) kindList;
      kinds = builtins.listToAttrs (
        map (k: {
          inherit (k) name;
          value = k;
        }) kindList
      );
      allBelow = lib.unique (builtins.concatLists (map (k: k.below) kindList));
      unresolved = builtins.filter (b: !(kinds ? ${b})) allBelow;
      ranked = genGraph.coneRank {
        nodes = names;
        edges = n: kinds.${n}.below;
      } names;
    in
    {
      inherit unresolved;
      inherit (ranked) depth;
    };

  # The composed predicate: does the registry refuse an unregistered `below` name ON THE PATH THAT
  # ALSO READS THE MEASURE? Applied to both constructions in the same run.
  refusesOnTheDepthPath = mk: didThrow (mk ghost).depth;

  # ── THE STRICT-DECREASE PREDICATE ──
  # Domain: every registered kind name, and for each, every one of its `below` names that is
  # itself registered. Parameterised on the depth map so the same predicate can be aimed at a map
  # known to violate it.
  strictDecrease =
    {
      names,
      belowOf,
      depth,
    }:
    builtins.all (
      k: builtins.all (b: depth.${k} > depth.${b}) (builtins.filter (b: depth ? ${b}) (belowOf k))
    ) names;

  overRegistry =
    kindList: depthOf:
    let
      ks = mkKinds kindList;
      names = map (k: k.name) kindList;
    in
    strictDecrease {
      inherit names;
      belowOf = n: ks.kinds.${n}.below;
      depth = depthOf ks;
    };

  asBuilt = ks: ks.depth;
  allZero = ks: lib.genAttrs (builtins.attrNames ks.depth) (_: 0);
  reversed = ks: lib.mapAttrs (_: d: ks.maxDepth - d) ks.depth;

  registeredNames = kindList: builtins.attrNames (lib.genAttrs (map (k: k.name) kindList) (_: null));
  namesOf = kindList: builtins.attrNames (mkKinds kindList).depth;

  # ── THE POISONED RANK SURFACE ──
  # A source scan cannot decide consumption: it needs a case per syntactic form, and a form it has
  # no case for reads as absence. This is the semantic instrument instead. The depth map is the
  # real one; the linearisation throws on contact. The library is instantiated against it, so the
  # cell goes red if ANY path reads that field, by projection, by `inherit`, by `getAttr`, or by
  # a form nobody thought to write a case for.
  poisoned = genGraph // {
    coneRank =
      accessor: cone:
      genGraph.coneRank accessor cone // { order = throw "the rank linearisation was consumed"; };
  };
  # The graph surface is the ONLY substituted one: the cascade takes the prelude and this, so a
  # reading here cannot be a second injection's doing.
  cascadeUnderPoison = import ../../lib/cascade.nix {
    prelude = genPreludeLib;
    graph = poisoned;
  };

  # The same substitution aimed at the field the registry DOES read. Without this arm the cell
  # above would pass just as happily against an instantiation that never consulted the injected
  # surface at all, which is the one way a substitution oracle goes quietly vacuous.
  depthPoisoned = genGraph // {
    coneRank =
      accessor: cone:
      genGraph.coneRank accessor cone // { depth = throw "the rank measure was consumed"; };
  };
  cascadeUnderDepthPoison = import ../../lib/cascade.nix {
    prelude = genPreludeLib;
    graph = depthPoisoned;
  };

  # The accessor the registry builds, rebuilt here so the poison can be aimed at the surface
  # directly and shown to fire.
  accessorFor = kindList: {
    nodes = map (k: k.name) kindList;
    edges =
      n:
      (builtins.listToAttrs (
        map (k: {
          inherit (k) name;
          value = k;
        }) kindList
      )).${n}.below;
  };
  rankOf = graph: kindList: graph.coneRank (accessorFor kindList) (map (k: k.name) kindList);

  # ARMED: a registry that DOES consume the linearisation, written in the `inherit`-from form a
  # substring scan for a dotted projection is blind to. Under the poison it must fail the cell the
  # real construction passes.
  consumingRegistry = graph: kindList: { inherit (rankOf graph kindList) depth order; };
in
{
  flake.tests.cascade-kinds = {
    # ── (a) THE MEASURE, BYTE-EQUAL TO THE PREVIOUS CONSTRUCTION'S ──
    # Expected values are `builtins.toJSON` of the previous construction's own depth map, so the
    # comparison is over bytes and not over a structural equality that could agree on a rounded
    # reading.
    test-depth-map-chain-byte-equal = {
      expr = builtins.toJSON (mkKinds chain).depth;
      expected = "{\"l0\":0,\"l1\":1,\"l2\":2,\"l3\":3,\"l4\":4}";
    };
    test-depth-map-diamond-byte-equal = {
      expr = builtins.toJSON (mkKinds diamond).depth;
      expected = "{\"a\":1,\"b\":1,\"leaf\":0,\"top\":2}";
    };
    test-depth-map-fan-byte-equal = {
      expr = builtins.toJSON (mkKinds fan).depth;
      expected = "{\"f0\":0,\"f1\":0,\"f2\":0,\"f3\":0,\"hub\":1}";
    };
    test-depth-map-shared-producer-lattice-byte-equal = {
      expr = builtins.toJSON (mkKinds lattice43).depth;
      expected = "{\"n0_0\":0,\"n0_1\":0,\"n0_2\":0,\"n1_0\":1,\"n1_1\":1,\"n1_2\":1,\"n2_0\":2,\"n2_1\":2,\"n2_2\":2,\"n3_0\":3,\"n3_1\":3,\"n3_2\":3}";
    };

    # ── (b) ACYCLICITY IS REACHABLE, WITH A LIVE ACYCLIC CONTROL ──
    # The refusal's MESSAGE belongs to the graph library now, and the sweep that reads its text is
    # an exit-code run; what these cells pin is that the refusal is reached at all, and that the
    # instrument is not one that refuses everything.
    test-two-cycle-refused = {
      expr = didThrow (mkKinds twoCycle);
      expected = true;
    };
    test-self-loop-refused = {
      expr = didThrow (mkKinds selfLoop);
      expected = true;
    };
    test-long-cycle-refused = {
      expr = didThrow (mkKinds [
        (node "a" [ "b" ])
        (node "b" [ "c" ])
        (node "c" [ "a" ])
      ]);
      expected = true;
    };
    test-acyclic-control-registers = {
      expr = succeeds (mkKinds diamond);
      expected = true;
    };
    # The refusal is a DEFINITION-TIME error: it fires on the registry record itself, without a
    # reader ever asking for a field.
    test-cycle-refused-at-the-registration-site = {
      expr = didThrow (builtins.seq (mkKinds twoCycle) null);
      expected = true;
    };

    # ── (c) THE PREVIOUS CONSTRUCTION'S ABORT IS GONE ──
    # The exact shape that terminates evaluation under the retiring library at this graph
    # revision. In-suite this can only say "returns"; the abort's uncatchability is why the
    # companion arm is an exit-code sweep.
    test-registry-returns-against-the-current-graph-record = {
      expr = (mkKinds diamond).depth.top;
      expected = 2;
    };
    test-registry-returns-under-a-catcher = {
      expr = succeeds (mkKinds diamond).depth;
      expected = true;
    };

    # ── (d) THE UNREGISTERED-NAME REFUSAL DOMINATES THE PATH TO THE MEASURE ──
    # Composed, not isolated: the predicate reads `.depth`, which is the path the refusal has to
    # dominate. The armed variant is the same predicate against a registry whose check is a
    # sibling — it MUST fail the cell above, and the two cells below are that failure measured.
    test-unregistered-below-name-refuses-on-the-depth-path = {
      expr = refusesOnTheDepthPath mkKinds;
      expected = true;
    };
    test-armed-non-dominating-variant-fails-the-domination-cell = {
      expr = refusesOnTheDepthPath nonDominating;
      expected = false;
    };
    test-armed-non-dominating-variant-answers-depth-zero-silently = {
      expr = (nonDominating ghost).depth;
      expected = {
        a = 0;
      };
    };
    # The armed variant is otherwise a working registry, so its failure above is about ORDER and
    # not about it being broken.
    test-armed-variant-agrees-on-a-well-formed-registry = {
      expr = (nonDominating diamond).depth;
      expected = {
        leaf = 0;
        a = 1;
        b = 1;
        top = 2;
      };
    };

    # ── (e) THE RANK SURFACE'S LINEARISATION IS NOT CONSUMED ──
    # Two topological linearisations of one relation can differ element for element and both be
    # correct; the depth map admits no such freedom. The positive control is in the same run and
    # over the same stripped source, so a scan that could not see either token fails visibly.
    test-rank-linearisation-not-consumed = {
      expr = succeeds (cascadeUnderPoison.mkKinds diamond);
      expected = true;
    };
    # The poisoned instantiation is the same library doing the same work, so the cell above is not
    # passing against something that quietly did nothing.
    test-control-poisoned-instantiation-still-computes-the-measure = {
      expr = (cascadeUnderPoison.mkKinds diamond).depth == (mkKinds diamond).depth;
      expected = true;
    };
    # ARMED, three ways. The poison fires on contact; it fires through the `inherit`-from form;
    # and the field is otherwise perfectly readable, so the throw is the poison and not an absence.
    test-armed-the-poisoned-linearisation-throws-on-contact = {
      expr = didThrow (rankOf poisoned diamond).order;
      expected = true;
    };
    test-armed-a-registry-consuming-the-linearisation-fails-the-cell = {
      expr = succeeds (consumingRegistry poisoned diamond);
      expected = false;
    };
    test-armed-the-same-consuming-registry-passes-against-the-real-surface = {
      expr = succeeds (consumingRegistry genGraph diamond);
      expected = true;
    };
    test-armed-the-injected-surface-is-the-one-the-registry-reads = {
      expr = didThrow (cascadeUnderDepthPoison.mkKinds diamond);
      expected = true;
    };
    test-control-the-poison-leaves-the-measure-alone = {
      expr = (rankOf poisoned diamond).depth;
      expected = {
        leaf = 0;
        a = 1;
        b = 1;
        top = 2;
      };
    };

    # ── INTAKE: EVERY ENTRY IS A KIND RECORD, AND THE REFUSAL IS CATCHABLE ──
    # `didThrow` is the discriminating predicate here: a refusal by name is a caught throw, while
    # a type error reaching an attribute position terminates the evaluation and reports as a
    # runner-level crash rather than a failed cell. Both are counted.
    test-entry-that-is-not-an-attrset-refused = {
      expr = didThrow (mkKinds [ "a" ]);
      expected = true;
    };
    test-entry-not-built-by-the-constructor-refused = {
      expr = didThrow (mkKinds [ unmarkedKind ]);
      expected = true;
    };
    test-entry-with-a-non-string-name-refused = {
      expr = didThrow (mkKinds [ (forgedKind { name = 42; }) ]);
      expected = true;
    };
    test-entry-with-no-below-field-refused = {
      expr = didThrow (mkKinds [ (removeAttrs (forgedKind { }) [ "below" ]) ]);
      expected = true;
    };
    # The `below` arms are reached through a forged record and not through the constructor: the
    # constructor screens both shapes itself, so a fixture built with it is refused before the
    # registry's own arm is ever consulted.
    test-below-holding-a-non-string-refused = {
      expr = didThrow (mkKinds [ (forgedKind { below = [ 42 ]; }) ]);
      expected = true;
    };
    test-below-that-is-not-a-list-refused = {
      expr = didThrow (mkKinds [ (forgedKind { below = "b"; }) ]);
      expected = true;
    };
    test-argument-that-is-neither-list-nor-attrset-refused = {
      expr = didThrow (mkKinds "a");
      expected = true;
    };
    # Composed, like the unregistered-name cell: the intake refusal has to dominate the path to
    # the measure, not merely exist beside it.
    test-intake-refusal-dominates-the-depth-path = {
      expr = didThrow (mkKinds [ (forgedKind { name = 42; }) ]).depth;
      expected = true;
    };

    # ── (f) THE CARRIED ITEMS, ONE CELL EACH ──
    # Item 1 — name uniqueness, with a live control that distinct names register.
    test-duplicate-name-refused = {
      expr = didThrow (mkKinds duplicated);
      expected = true;
    };
    test-control-distinct-names-register = {
      expr = succeeds (mkKinds [
        (leaf "a")
        (leaf "b")
      ]);
      expected = true;
    };
    # Item 2 — `below`-name resolution, refused on its own as well as on the measure's path.
    test-unregistered-below-name-refused = {
      expr = didThrow (mkKinds ghost);
      expected = true;
    };
    # Item 3 — acyclicity: the cells above.
    # Item 4 — the per-kind measure: the byte-equalities above, and the registry field is present
    # and typed.
    test-registry-publishes-a-per-kind-depth-map = {
      expr = builtins.isAttrs (mkKinds diamond).depth;
      expected = true;
    };
    # Item 5 — `maxDepth`, over the same map, on every shape.
    test-max-depth-chain = {
      expr = (mkKinds chain).maxDepth;
      expected = 4;
    };
    test-max-depth-diamond = {
      expr = (mkKinds diamond).maxDepth;
      expected = 2;
    };
    test-max-depth-fan = {
      expr = (mkKinds fan).maxDepth;
      expected = 1;
    };
    test-max-depth-shared-producer-lattice = {
      expr = (mkKinds lattice43).maxDepth;
      expected = 3;
    };
    # The same two fields over the k8s registry: leaves at 0, composites at 1, `maxDepth` 1. The
    # leaf and composite cells are separate because a construction answering a constant 0 passes
    # the first and fails the second, which one merged cell would not distinguish.
    test-k8s-depth-leaves = {
      expr = {
        inherit (k8s.kinds.depth) connect secret storage;
      };
      expected = {
        connect = 0;
        secret = 0;
        storage = 0;
      };
    };
    test-k8s-depth-composites = {
      expr = {
        inherit (k8s.kinds.depth) database route;
      };
      expected = {
        database = 1;
        route = 1;
      };
    };
    test-k8s-max-depth = {
      expr = k8s.kinds.maxDepth;
      expected = 1;
    };
    # Item 6 — strict decrease: the property cells below.
    # And the record's other carried shapes: the registration-time pairing check and the input
    # form the previous construction accepted.
    test-dedup-key-without-fold-refused = {
      expr = didThrow (mkKind {
        name = "x";
        dedupKey = _: "k";
        resolve = _: _: { };
      });
      expected = true;
    };
    test-fold-without-dedup-key-refused = {
      expr = didThrow (mkKind {
        name = "x";
        fold = _: vs: builtins.head vs;
        resolve = _: _: { };
      });
      expected = true;
    };
    test-control-both-dedup-key-and-fold-register = {
      expr = succeeds (mkKind {
        name = "x";
        dedupKey = _: "k";
        fold = _: vs: builtins.head vs;
        resolve = _: _: { };
      });
      expected = true;
    };
    test-attrset-input-form-accepted = {
      expr = succeeds (mkKinds {
        b = leaf "b";
        a = node "a" [ "b" ];
      });
      expected = true;
    };

    # ── (g) STRICT DECREASE, QUANTIFIED OVER THE REGISTRY ──
    # ∀ registered k. ∀ registered b ∈ below(k). depth k > depth b — over the four fixtures above
    # and over three generated lattices, so the property is not read off hand-picked shapes.
    test-strict-decrease-chain = {
      expr = overRegistry chain asBuilt;
      expected = true;
    };
    test-strict-decrease-diamond = {
      expr = overRegistry diamond asBuilt;
      expected = true;
    };
    test-strict-decrease-fan = {
      expr = overRegistry fan asBuilt;
      expected = true;
    };
    test-strict-decrease-shared-producer-lattice = {
      expr = overRegistry lattice43 asBuilt;
      expected = true;
    };
    test-strict-decrease-lattice-6x4 = {
      expr = overRegistry (lattice 6 4) asBuilt;
      expected = true;
    };
    test-strict-decrease-lattice-10x3 = {
      expr = overRegistry (lattice 10 3) asBuilt;
      expected = true;
    };
    test-strict-decrease-lattice-3x7 = {
      expr = overRegistry (lattice 3 7) asBuilt;
      expected = true;
    };
    # The generators built the shapes they claim: maxDepth is levels − 1 on each.
    test-generated-lattice-6x4-has-max-depth-5 = {
      expr = (mkKinds (lattice 6 4)).maxDepth;
      expected = 5;
    };
    test-generated-lattice-10x3-has-max-depth-9 = {
      expr = (mkKinds (lattice 10 3)).maxDepth;
      expected = 9;
    };
    test-generated-lattice-3x7-has-max-depth-2 = {
      expr = (mkKinds (lattice 3 7)).maxDepth;
      expected = 2;
    };
    # ARMED: the same predicate on maps measured to violate it. Without these the property cell
    # would pass against a predicate that cannot say no.
    test-armed-all-zero-depth-map-violates-strict-decrease = {
      expr = overRegistry diamond allZero;
      expected = false;
    };
    test-armed-reversed-depth-map-violates-strict-decrease = {
      expr = overRegistry diamond reversed;
      expected = false;
    };
    test-armed-all-zero-depth-map-violates-on-a-lattice = {
      expr = overRegistry (lattice 6 4) allZero;
      expected = false;
    };
    test-armed-reversed-depth-map-violates-on-a-lattice = {
      expr = overRegistry (lattice 6 4) reversed;
      expected = false;
    };

    # ── (h) THE MEASURE IS TOTAL ON THE REGISTERED NAMES ──
    # Compared against the names read off the fixture's own kind list, not off a field the same
    # call produced.
    test-depth-total-on-names-chain = {
      expr = namesOf chain;
      expected = registeredNames chain;
    };
    test-depth-total-on-names-diamond = {
      expr = namesOf diamond;
      expected = registeredNames diamond;
    };
    test-depth-total-on-names-fan = {
      expr = namesOf fan;
      expected = registeredNames fan;
    };
    test-depth-total-on-names-shared-producer-lattice = {
      expr = namesOf lattice43;
      expected = registeredNames lattice43;
    };
    test-depth-total-on-names-lattice-6x4 = {
      expr = namesOf (lattice 6 4);
      expected = registeredNames (lattice 6 4);
    };
    test-depth-total-on-names-lattice-10x3 = {
      expr = namesOf (lattice 10 3);
      expected = registeredNames (lattice 10 3);
    };
    test-depth-total-on-names-lattice-3x7 = {
      expr = namesOf (lattice 3 7);
      expected = registeredNames (lattice 3 7);
    };

    # ── THE REGISTRY IS THE SUBSTRATE'S, NOT THE CASCADE'S ──
    # `resolve` used to be total at the door, which made this registry unusable as the home of the
    # node kind order: a structural kind has no demand semantics to supply. These cells are the
    # generalization from the other side — a kind with NO resolver registers, ranks and orders
    # exactly like one that carries it, so the two vocabularies really do share one relation and one
    # acyclicity verdict. What such a kind cannot do is answer a demand, and `../tests-error.nix`
    # asserts that refusal by its text.
    test-a-kind-with-no-resolver-registers = {
      expr =
        builtins.attrNames
          (genScope.mkKinds [
            (genScope.mkKind { name = "structural"; })
            (genScope.mkKind {
              name = "host";
              below = [ "structural" ];
            })
          ]).kinds;
      expected = [
        "host"
        "structural"
      ];
    };
    test-a-kind-with-no-resolver-takes-a-rank-like-any-other = {
      expr =
        (genScope.mkKinds [
          (genScope.mkKind { name = "structural"; })
          (genScope.mkKind {
            name = "host";
            below = [ "structural" ];
          })
        ]).depth;
      expected = {
        host = 1;
        structural = 0;
      };
    };
    # A DEMAND kind and a STRUCTURAL one rank in the SAME relation — which is the whole content of
    # there being one registry rather than two. Without this cell the two above are equally
    # consistent with a registry that quietly partitions them.
    test-control-demand-and-structural-kinds-rank-in-one-order = {
      expr =
        (genScope.mkKinds [
          (genScope.mkKind { name = "leaf"; })
          (genScope.mkKind {
            name = "structural";
            below = [ "leaf" ];
          })
          (genScope.mkKind {
            name = "demanding";
            below = [ "structural" ];
            resolve = _: _: { };
          })
        ]).depth;
      expected = {
        demanding = 2;
        leaf = 0;
        structural = 1;
      };
    };

    # ── THE SPAWN DECLARATION RIDES THE SAME RECORD ──
    # A declared spawn is admitted only where its produced kind is already `below` the host, so the
    # descent is a property of the record rather than of the run. The refusal is asserted by text
    # next door; this is its clean path, and without it that refusal is consistent with a
    # constructor that refuses every `spawns` it is given.
    test-control-a-descending-spawn-is-admitted = {
      expr =
        builtins.attrNames
          (genScope.mkKind {
            name = "host";
            below = [ "child" ];
            spawns.child = _self: _id: { };
          }).spawns;
      expected = [ "child" ];
    };
    # The refusal as a BOOLEAN, beside the message cell next door, because the two suites are read
    # by different gates: the batch asserter behind `checks.default` quantifies over `flake.tests`
    # and never sees `flake.testsError`, so a guard pinned only by its text is unguarded on the gate
    # CI actually builds. Measured: with the descent check disabled, `#tests` stayed green at 732
    # and only the message cells fired.
    test-a-spawn-outside-the-hosts-below-set-is-refused = {
      expr =
        !(builtins.tryEval (
          builtins.deepSeq (genScope.mkKind {
            name = "host";
            below = [ "low" ];
            spawns.sideways = _self: _id: { };
          }) null
        )).success;
      expected = true;
    };
    test-a-spawn-declared-with-no-below-at-all-is-refused = {
      expr =
        !(builtins.tryEval (
          builtins.deepSeq (genScope.mkKind {
            name = "host";
            spawns.child = _self: _id: { };
          }) null
        )).success;
      expected = true;
    };
  };
}
