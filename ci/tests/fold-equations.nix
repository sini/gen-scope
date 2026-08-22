# The cold fold: what the entry seals, what it forces, and what it refuses to let a caller express.
#
# THE SCHEDULE IS A FIXTURE RECORD RATHER THAN A SCHEDULER'S OUTPUT, and that is the honest shape for
# this suite: the entry reads exactly one field off it and forces the value itself, so a fixture
# carrying that field exercises everything the entry does with a schedule. What validated the grammar
# is the scheduler's own concern and is asserted where the scheduler lives.
{
  lib,
  genScope,
  genPreludeLib,
  ...
}:
let
  # A FLAT kind vocabulary: names, and no order between them, so no kind expands into another.
  # These fixtures declare types and never spawn, which is exactly what an empty `below` says.
  flatKinds = names: genScope.mkKinds (map (name: genScope.mkKind { inherit name; }) names);

  inherit (genScope) foldEquations;

  roots = genScope.buildRoots {
    kinds = flatKinds [ "host" ];
    parentGraph = genScope.edge "child" "parent";
    decls = {
      parent = {
        v = 10;
      };
      child = {
        v = 1;
      };
      # A node in NEITHER half of the dependency union: nothing declares an edge to it and it has no
      # structural descendant. Since the accessor's relation became a union, `parent` is no longer
      # such a node — it reaches `child` structurally — so the empty case needs a node that is
      # genuinely outside both halves, or the cell asserting emptiness is asserting it of nothing.
      orphan = {
        v = 0;
      };
    };
    types = {
      parent = "host";
      child = "host";
      orphan = "host";
    };
  };

  # An Equation is `{ name; kind; compute; readsAttrs; stratum }` at the authoring surface; the fold
  # reads `compute` and nothing else, which is why these fixtures carry the whole record and the
  # cells below turn only on the compute functions.
  equations = {
    self-v = {
      name = "self-v";
      kind = "synthesized";
      readsAttrs = [ ];
      stratum = "resolution";
      compute = self: id: (self.node id).decls.v;
    };
    plus-one = {
      name = "plus-one";
      kind = "synthesized";
      readsAttrs = [ "self-v" ];
      stratum = "resolution";
      compute = self: id: self.get id "self-v" + 1;
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

  ctx = foldEquations {
    scope = roots;
    inherit schedule;
    parseParent = id: roots.nodes.${id}.parent or null;
    declaredDependencies = _: [ ];
  };

  # The same fold over a NON-EMPTY relation, which is what makes the trace cells below
  # discriminating: against the empty relation every deps list is empty and a derivation that
  # dropped its argument entirely would read identically to one that used it.
  edgedCtx = foldEquations {
    scope = roots;
    inherit schedule;
    parseParent = id: roots.nodes.${id}.parent or null;
    declaredDependencies = id: if id == "child" then [ "parent" ] else [ ];
  };

  # ── (g) THE COLLISION SET ──
  # The comparand is the library's exports MINUS this module's own, so the check is about what was
  # already there and not about the name this module just added.
  foldNames = builtins.attrNames (
    import ../../lib/fold-equations.nix {
      prelude = genPreludeLib;
      inherit (genScope) eval;
      inherit (import ../../lib/require-scope.nix { prelude = genPreludeLib; }) requireScope;
    }
  );
  incumbentNames = builtins.filter (n: !(builtins.elem n foldNames)) (builtins.attrNames genScope);
  collidesWith = names: builtins.filter (n: builtins.elem n incumbentNames) names;
in
{
  flake.tests.fold-equations = {
    # A demanded leaf value flows from the decls through the equation's own compute.
    test-project-leaf = {
      expr = ctx.eval.get "child" "self-v";
      expected = 1;
    };
    # A derived attribute reads another attribute through the demand fixpoint.
    test-project-derived = {
      expr = ctx.eval.get "parent" "plus-one";
      expected = 11;
    };
    # The sealed context, asserted as an EXACT SET rather than as presence: a presence check is
    # satisfied by any context containing those names and is silent about everything else, which is
    # how a seal comes to carry a field nobody put there. Compared on NAMES, so a widening, a
    # narrowing or a rename each fail this cell.
    test-ctx-sealed = {
      expr = builtins.attrNames ctx;
      expected = [
        "accessor"
        "attributes"
        "declaredDependencies"
        "equations"
        "eval"
        "parseParent"
        "roots"
        "schedule"
        "scope"
        "settings"
        "trace"
      ];
    };

    # ── THE SEALED RECORD, AND WHY IT IS SEALED WHOLE ──
    # `roots` is the node map; `scope` is the record that CONTAINS it, together with the declared
    # vertex order and the kind registry. The distinction is the whole reason for the second field:
    # a consumer that must call an evaluator needs the order and the registry, and neither is
    # recoverable from the node map — so publishing only `roots` refused such a consumer by name
    # (the input-type guard) while leaving it nowhere to be redirected.
    test-scope-is-sealed-whole = {
      expr = builtins.attrNames ctx.scope;
      expected = [
        "kinds"
        "nodeOrder"
        "nodes"
      ];
    };

    # ── THE TWO FIELDS AGREE, AND THAT IS AN INVARIANT RATHER THAN A COINCIDENCE ──
    # Publishing the same node map under two names is exactly the shape that goes stale silently:
    # nothing in the record's type says they are the same object, so a later edit that rebuilds one
    # and not the other leaves a consumer reading whichever it happened to pick. Both come off
    # `checked` here, so this cell states the property the seal is relied on for rather than
    # re-testing the constructor.
    test-sealed-roots-is-the-sealed-scopes-node-map = {
      expr = ctx.roots == ctx.scope.nodes;
      expected = true;
    };
    # The equations the seal carries are the SCHEDULE'S OWN, which is what makes a schedule paired
    # with a foreign equation set inexpressible: there is no second argument to disagree with.
    test-the-sealed-equations-are-the-schedules-own = {
      expr = ctx.equations == schedule.equations;
      expected = true;
    };
    # ── THE TRACE'S DEPS ARE DERIVED, NOT DECLARED ──
    # There is no read-set construct between the relation and the trace: the body is the read set,
    # so the deps a consumer reads off the seal are the accessor's dependencies for that node and
    # nothing else. Asserted THROUGH the fold rather than against a naked projection, which is what
    # the retired surface's own cells could not do.
    test-trace-deps-are-the-accessor-dependencies = {
      expr = edgedCtx.trace.child.deps;
      expected = edgedCtx.accessor.dependencies "child";
    };
    # Pinned against a LITERAL as well, so the cell above cannot pass by comparing two calls to one
    # broken function.
    test-trace-deps-literal = {
      expr = edgedCtx.trace.child.deps;
      expected = [ "parent" ];
    };
    # The STRUCTURAL half reaches the trace on its own: `parent` declares nothing at all and still
    # traces its child, which is the unsoundness the union closes — a parent is stale when its child
    # changes whether or not an author wrote that edge down.
    test-trace-deps-carry-the-structural-half-where-nothing-is-declared = {
      expr = edgedCtx.trace.parent.deps;
      expected = [ "child" ];
    };
    # A node in neither half traces empty — and this is the discriminating TRIPLE with the two cells
    # above: all three nodes exist, all three are traced, and only the relation separates them.
    # `child` carries a declared edge and no descendant, `parent` a descendant and no declared edge,
    # `orphan` neither. Without this cell the two above are satisfied by a relation that answers
    # non-empty for everything.
    test-trace-deps-empty-where-neither-half-of-the-union-holds-an-edge = {
      expr = edgedCtx.trace.orphan.deps;
      expected = [ ];
    };
    # Every traced node carries the pair the seal promises; a derivation that skipped a node would
    # leave a `deps` missing rather than empty.
    test-trace-entry-shape = {
      expr = builtins.attrNames edgedCtx.trace.child;
      expected = [
        "deps"
        "hash"
      ];
    };
    # The declared dependencies are the topology consumers' oracle and nothing on the cold path
    # walks them, so a CYCLIC declaration resolves exactly as an acyclic one does.
    test-cyclic-declared-dependencies-leave-the-cold-path-alone = {
      expr =
        (foldEquations {
          scope = roots;
          inherit schedule;
          parseParent = id: roots.nodes.${id}.parent or null;
          declaredDependencies = id: if id == "child" then [ "parent" ] else [ "child" ];
        }).eval.get
          "child"
          "self-v";
      expected = 1;
    };
    # THE SCHEDULE IS FORCED AT THE ENTRY, not lazily on a first attribute read: a caller handing a
    # schedule whose gate refuses gets the refusal here, where they made the call.
    test-a-throwing-schedule-is-refused-at-the-entry = {
      expr =
        (builtins.tryEval (foldEquations {
          scope = roots;
          parseParent = _: null;
          declaredDependencies = _: [ ];
          schedule = throw "the gate refused this grammar";
        })).success;
      expected = false;
    };
    # The control beside it: the same expression against a schedule that does not throw. Without it
    # the cell above passes against an entry that refuses everything.
    test-control-a-schedule-that-does-not-throw-is-not-refused = {
      expr =
        (builtins.tryEval (foldEquations {
          scope = roots;
          inherit schedule;
          parseParent = _: null;
          declaredDependencies = _: [ ];
        })).success;
      expected = true;
    };

    # ── (g) THE ARRIVING SURFACE AGAINST THE LIBRARY IT LANDS IN ──
    test-the-arriving-surface-collides-with-nothing = {
      expr = collidesWith foldNames;
      expected = [ ];
    };
    # ARMED: the predicate fires on names that ARE in the comparand, so an empty result above is a
    # measurement rather than a predicate that could not match.
    test-armed-the-collision-predicate-fires = {
      expr = collidesWith [
        "resolve"
        "eval"
      ];
      expected = [
        "resolve"
        "eval"
      ];
    };
    # The library's surface minus this module's one name. The figure is a baseline over the export
    # surface and re-derives whenever that surface grows.
    test-the-comparand-is-the-library-without-this-module = {
      expr = builtins.length incumbentNames;
      expected = 88;
    };
    # One: the fold's entry, and nothing else. This cell is the module's inventory, and an export it
    # does not list is an export nothing measured.
    test-this-module-exports-exactly-its-one-name = {
      expr = foldNames;
      expected = [ "foldEquations" ];
    };
  };
}
