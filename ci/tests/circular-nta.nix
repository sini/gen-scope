# CIRCULAR ATTRIBUTES OVER A SPAWNED SUBTREE — the two carriers composed, end to end.
#
# The grammar, the carrier and the two seeded variants live in `_fixtures/circular-nta.nix`, which
# states what the combination is and why its lattice has the shape it has. What is here is what can
# be asserted as a VALUE: the ranks the expansions descend, the subtree they grow, the fixed point
# taken over it, and the clean path beside each seeded refusal. WHICH refusal fires is a claim about
# a message, so those cells live in `../tests-error.nix` where `expectedError` can read the text.
#
# ★ THE VACUITY GUARD IS THE POINT OF THE TWO STRUCTURAL CELLS. A fixed point over an EMPTY index
# set converges immediately and to a value a cell can be written against, so a suite that asserted
# convergence alone would be equally satisfied by a spawn that produced nothing at all. The cells
# that pin the materialized subtree and the cell that ties the lattice's index set to it are what
# make the convergence cell a statement about a grown node set.
{ lib, genScope, ... }:
let
  fixture = import ./_fixtures/circular-nta.nix { inherit genScope; };
  inherit (fixture)
    kinds
    ev
    ctx
    converged
    step
    ;

  # Tag sets are attribute sets used as sets; comparing their key lists is what makes the expected
  # value below readable as the set it stands for.
  tagsOf = builtins.mapAttrs (_: v: builtins.attrNames v);

  # THE FIXED POINT, COMPUTED BY HAND. From the empty map, a tag travels one `needs` edge per step
  # around the 3-cycle c-a → c-b → c-c → c-a:
  #
  #   x0 = { }
  #   x1 = { c-a = {a};     c-b = {b};     c-c = {c};     }   each member's own endpoint seed
  #   x2 = { c-a = {a,b};   c-b = {b,c};   c-c = {c,a};   }   one edge travelled
  #   x3 = { c-a = {a,b,c}; c-b = {a,b,c}; c-c = {a,b,c}; }   two edges: the cycle is closed
  #   x4 = x3
  #
  # Three strict ascents, and the fourth step is the one that observes none — `h + 1` step
  # evaluations on a declared height of three, which is the bound the declaration derives rather
  # than a budget anyone chose.
  closed = [
    "a"
    "b"
    "c"
  ];
in
{
  flake.tests."circular-nta" = {
    # ── THE DOMAIN CARRIER ──
    # The rank each expansion descends, published by the registry. Two spawns, two strictly
    # decreasing steps, and a `maxDepth` that bounds the chain.
    test-control-the-kind-order-ranks-each-expansion-below-its-host = {
      expr = kinds.depth;
      expected = {
        cluster = 2;
        member = 1;
        endpoint = 0;
      };
    };

    # One declared root, six spawned nodes, each carrying the kind its builder was declared under.
    # Nothing in any builder body chose a kind: the substrate stamps it from the key.
    test-control-the-spawned-subtree-materializes-under-its-declared-kinds = {
      expr = builtins.mapAttrs (_: n: n.type) ev.allNodes;
      expected = {
        c = "cluster";
        "c-a" = "member";
        "c-a-ep" = "endpoint";
        "c-b" = "member";
        "c-b-ep" = "endpoint";
        "c-c" = "member";
        "c-c-ep" = "endpoint";
      };
    };

    # ── WHERE THE TWO CARRIERS MEET ──
    # The lattice is indexed by exactly the nodes the spawn produced at the member rank, derived
    # here from the materialized node set rather than restated, so the two sides cannot drift into
    # agreeing by coincidence.
    test-control-the-lattices-index-set-is-the-spawned-member-set = {
      expr = builtins.attrNames converged;
      expected = builtins.attrNames (lib.filterAttrs (_: n: n.type == "member") ev.allNodes);
    };

    # ── THE FIXED POINT ──
    test-the-closure-converges-to-the-hand-computed-fixpoint = {
      expr = tagsOf converged;
      expected = {
        "c-a" = closed;
        "c-b" = closed;
        "c-c" = closed;
      };
    };

    # AND IT IS A FIXED POINT OF THE STEP, not merely a value some convergence test accepted. A
    # combinator whose convergence predicate is unrelated to its ascent can return a value its own
    # step moves; applying the step to the answer is what separates the two, and the declared order
    # is what makes them the same question here.
    test-control-the-converged-value-is-a-fixpoint-of-its-own-step = {
      expr = step ev "c" converged == converged;
      expected = true;
    };

    # ── THE TWO SEEDED VIOLATIONS ──
    # A height one short of the chain. The step is unchanged and perfectly monotone, so the
    # declaration is what this refutes.
    test-a-height-one-short-of-the-chain-is-refused = {
      expr = builtins.tryEval fixture.shortHeight;
      expected = {
        success = false;
        value = false;
      };
    };

    # A member's neighbours REPLACING its own seed rather than joining it: the same boolean as the
    # cell above and a different fact, which is why both messages are asserted next door.
    test-a-non-monotone-contribution-from-the-spawned-subtree-is-refused = {
      expr = builtins.tryEval fixture.nonMonotone;
      expected = {
        success = false;
        value = false;
      };
    };

    # ── THE SAME COMBINATION AT THE ENTRY A SCHEDULE'S EQUATIONS ARRIVE AT ──
    # The cold fold binds the equations off the schedule it is handed and holds no fixpoint of its
    # own, so what these two cells add is that the circular equation and the registry-declared
    # expansion compose through it unchanged.
    test-the-cold-fold-runs-the-combined-grammar-to-the-same-fixpoint = {
      expr = tagsOf (ctx.eval.get "c" "closure");
      expected = {
        "c-a" = closed;
        "c-b" = closed;
        "c-c" = closed;
      };
    };

    # The sealed accessor's node list is read off the evaluator AFTER materialization, which is the
    # reason a spawned node is in it at all: a list taken from the roots would carry one id.
    test-control-the-sealed-accessor-carries-the-spawned-subtree = {
      expr = ctx.accessor.nodes;
      expected = [
        "c"
        "c-a"
        "c-a-ep"
        "c-b"
        "c-b-ep"
        "c-c"
        "c-c-ep"
      ];
    };
  };
}
