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
  inherit (genScope) foldEquations;

  roots = genScope.buildRoots {
    parentGraph = genScope.edge "child" "parent";
    decls = {
      parent = {
        v = 10;
      };
      child = {
        v = 1;
      };
    };
    types = {
      parent = "host";
      child = "host";
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
  };

  # ── (g) THE COLLISION SET ──
  # The comparand is the library's exports MINUS this module's own, so the check is about what was
  # already there and not about the name this module just added.
  foldNames = builtins.attrNames (
    import ../../lib/fold-equations.nix {
      prelude = genPreludeLib;
      inherit (genScope) eval recordedDeps;
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
        "declaredEdges"
        "equations"
        "eval"
        "parseParent"
        "roots"
        "schedule"
        "settings"
        "trace"
      ];
    };
    # The equations the seal carries are the SCHEDULE'S OWN, which is what makes a schedule paired
    # with a foreign equation set inexpressible: there is no second argument to disagree with.
    test-the-sealed-equations-are-the-schedules-own = {
      expr = ctx.equations == schedule.equations;
      expected = true;
    };
    # The declared edges are the topology consumers' oracle and nothing on the cold path walks them,
    # so a CYCLIC declaration resolves exactly as an acyclic one does.
    test-cyclic-declared-edges-leave-the-cold-path-alone = {
      expr =
        (foldEquations {
          scope = roots;
          inherit schedule;
          parseParent = id: roots.nodes.${id}.parent or null;
          declaredEdges = id: if id == "child" then [ "parent" ] else [ "child" ];
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
      expected = 89;
    };
    # One: the fold's entry, and nothing else. This cell is the module's inventory, and an export it
    # does not list is an export nothing measured.
    test-this-module-exports-exactly-its-one-name = {
      expr = foldNames;
      expected = [ "foldEquations" ];
    };
  };
}
