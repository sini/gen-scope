# SPAWNED-NODE VISIBILITY AT THE QUERY AND TRAVERSAL SURFACES.
#
# One graph, one node notion (ADR-0012): a spawned node carries an identity, attributes and a
# parent edge exactly as a declared one does, so a query surface that reads the declared
# `children` half alone answers about a DIFFERENT node set than the evaluator materializes.
# These cells pin the composed read (`self._childRecords`) at every site that used to read the
# declared half directly: the five child-direction query entries, the two resolver traversals,
# and the debug evaluator's half of the same surface.
#
# The fixture is shared with the refusal cell in `tests-error.nix` — see
# `_fixtures/spawned-visibility.nix` for why it carries one declared and TWO spawned children.
{ lib, genScope, ... }:
let
  fixture = import ./_fixtures/spawned-visibility.nix { inherit lib genScope; };
  inherit (fixture) result debugWithParse;
  inherit (genScope)
    children
    childrenIds
    siblings
    descendants
    isDescendant
    ;
  sorted = builtins.sort builtins.lessThan;
in
{
  flake.tests."spawned-visibility" = {
    # ★ THE CONTROL, and it is the load-bearing half: the spawn channel really materializes both
    # spawned ids in this run. If the channel were misconfigured, every cell below would go green
    # over an empty question — this one failing beside them is what separates "the query now
    # answers" from "the fixture spawns nothing".
    test-control-spawned-node-materialized = {
      expr = builtins.elem "winnow" result.allNodeIds && builtins.elem "groat" result.allNodeIds;
      expected = true;
    };

    # ── the spawned node appears in structural queries ──
    test-childrenIds-includes-spawned = {
      expr = childrenIds result "millstone";
      expected = [
        "groat"
        "husk"
        "winnow"
      ];
    };
    test-children-record-includes-spawned = {
      expr = builtins.attrNames (children result "millstone");
      expected = [
        "groat"
        "husk"
        "winnow"
      ];
    };
    test-descendants-includes-spawned = {
      expr = sorted (descendants result "millstone");
      expected = [
        "groat"
        "husk"
        "winnow"
      ];
    };
    test-isDescendant-reaches-spawned = {
      expr = isDescendant result "winnow" "millstone";
      expected = true;
    };

    # ── the sibling relation, on the asymmetry it actually has ──
    # The declared child gains its spawned siblings (pre-fix: [ ]).
    test-siblings-declared-child-gains-spawned = {
      expr = siblings result "husk";
      expected = [
        "groat"
        "winnow"
      ];
    };
    # A spawned child already saw its DECLARED sibling (it reads the parent's children, and the
    # parent is declared); what it gains is its OTHER SPAWNED sibling — the cell that can only
    # fail because the fixture carries two. Pre-fix: [ "husk" ].
    test-siblings-spawned-child-gains-other-spawned = {
      expr = siblings result "winnow";
      expected = [
        "groat"
        "husk"
      ];
    };

    # ── the resolver's traversals compose (sites unreachable from any query cell) ──
    test-collection-children-gathers-spawned = {
      expr = sorted (result.get "millstone" "gather-children");
      expected = [
        "groat"
        "husk"
        "winnow"
      ];
    };
    test-collection-siblings-gathers-spawned = {
      expr = sorted (result.get "husk" "gather-siblings");
      expected = [
        "groat"
        "winnow"
      ];
    };

    # ── the debug evaluator keeps the query surface ──
    # Two regressions in one cell: the forgotten debug half (`_childRecords` missing from the
    # debug accessor throws on ANY fixture), and the newly-forced node acquisition — the composed
    # read forces `(ev.node id).type` through the spawn channel, which on a debug accessor needs
    # `parseParent` for a non-root id and is INVISIBLE on a kindless fixture, which every other
    # debug fixture in this suite tree is. The refusal arm (no `parseParent`, by name) is the
    # message cell in `tests-error.nix`.
    test-debug-query-surface-answers-with-spawned = {
      expr = {
        children = builtins.attrNames (children debugWithParse "millstone");
        childrenIds = childrenIds debugWithParse "millstone";
        siblings = siblings debugWithParse "husk";
        descendants = sorted (descendants debugWithParse "millstone");
        isDescendant = isDescendant debugWithParse "winnow" "millstone";
      };
      expected = {
        children = [
          "groat"
          "husk"
          "winnow"
        ];
        childrenIds = [
          "groat"
          "husk"
          "winnow"
        ];
        siblings = [
          "groat"
          "winnow"
        ];
        descendants = [
          "groat"
          "husk"
          "winnow"
        ];
        isDescendant = true;
      };
    };

    # ── the kindless scope still answers ──
    # The guard that makes the composed read safe is `attributes ? "derived-children"`, a test on
    # the RUNNING attribute set: on a kindless scope the spawn channel does not exist and an
    # unguarded read would throw `unknown attribute 'derived-children'` from a query that answers
    # fine. Seeded-defect form: drop the guard in `childRecordsOf`'s derived half and these two
    # go red while every cell above stays green.
    test-kindless-scope-childrenIds-answers =
      let
        kindlessRoots = genScope.buildRoots {
          parentGraph = genScope.edge "kid" "top";
          importGraph = genScope.empty;
          decls = {
            top = { };
            kid = { };
          };
          types = { };
        };
        kindless = genScope.eval {
          scope = kindlessRoots;
          attributes = {
            children = _self: id: lib.filterAttrs (_: n: n.parent == id) kindlessRoots.nodes;
            imports = _self: _id: [ ];
          };
        };
      in
      {
        expr = {
          childrenIds = childrenIds kindless "top";
          descendants = descendants kindless "top";
        };
        expected = {
          childrenIds = [ "kid" ];
          descendants = [ "kid" ];
        };
      };
  };
}
