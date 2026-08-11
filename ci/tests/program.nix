# The program's shape: its Herbrand base, its routing discriminator, and the two views of its
# dependency relation.
#
# The cells below pin the three properties the rest of the engine rests on. The atom list is
# CLOSED (every atom the rules mention is in it) and in DECLARATION ORDER, because the ordered
# fold over contributions is defined against that order. The routing discriminator reads the
# POSITIVE body only, which is what makes computing it once sound across every reduct. And the
# accessor handed to the partition door carries NO sign label, while the labelled view sits
# beside it — one relation, two readings, and the door reads the one mutual reachability is a
# property of.
{ genScope, ... }:
let
  p = genScope.mkProgram {
    rules = [
      {
        head = "z";
        pos = [ "b" ];
        neg = [ "q" ];
      }
      { head = "b"; }
      {
        head = "z";
        pos = [
          "b"
          "r"
        ];
      }
    ];
  };
in
{
  flake.tests."engine-program" = {
    # Closed and in declaration order: heads first, then bodies, first occurrence winning. `q`
    # and `r` head no rule and are atoms all the same — an atom nothing derives is FALSE, and it
    # has to be in the base for the model to be able to say so.
    test-atoms-are-closed-and-in-declaration-order = {
      expr = p.atoms;
      expected = [
        "z"
        "b"
        "q"
        "r"
      ];
    };
    # The greatest POSITIVE body arity. The first rule has two literals and a positive arity of
    # one; the third has a positive arity of two, and that is the figure.
    test-body-arity-reads-the-positive-body-only = {
      expr = p.bodyArity;
      expected = 2;
    };
    test-routing-follows-the-arity = {
      expr = p.unaryBodies;
      expected = false;
    };
    # ★ THE LIVE CONTROL for the cell above: the same shape with the conjunctive rule removed
    # routes the other way, so the discriminator is being read rather than a constant returned.
    test-a-two-literal-rule-with-one-positive-literal-is-unary = {
      expr =
        (genScope.mkProgram {
          rules = [
            { head = "b"; }
            {
              head = "z";
              pos = [ "b" ];
              neg = [ "q" ];
            }
          ];
        }).unaryBodies;
      expected = true;
    };
    # The door's accessor: nodes, and an edge function carrying BOTH bodies unsigned and deduped
    # across the rules that share a head.
    test-dependency-nodes-are-the-atoms = {
      expr = p.dependency.nodes;
      expected = p.atoms;
    };
    test-dependency-edges-are-unsigned-and-deduped = {
      expr = p.dependency.edges "z";
      expected = [
        "b"
        "q"
        "r"
      ];
    };
    # Total: an atom that heads no rule has no edges rather than an absence to test for.
    test-dependency-edges-are-total = {
      expr = p.dependency.edges "q";
      expected = [ ];
    };
    test-signs-separate-the-two-labels = {
      expr = p.signs "z";
      expected = {
        positive = [
          "b"
          "r"
        ];
        negative = [ "q" ];
      };
    };
    test-signs-are-total = {
      expr = p.signs "nothing-heads-this";
      expected = {
        positive = [ ];
        negative = [ ];
      };
    };
    # Both bodies default to empty because a rule with neither is a FACT — the base case of the
    # least model, not an omission.
    test-a-bodyless-rule-is-a-fact = {
      expr = genScope.mkRule { head = "f"; };
      expected = {
        head = "f";
        pos = [ ];
        neg = [ ];
      };
    };
    # ★ THE UNKNOWN-FIELD REFUSAL HAS NO CELL HERE, and the reason is a measured fact rather than
    # an omission: an argument-arity error is NOT contained by `tryEval` — the evaluation dies
    # rather than answering `{ success = false; }` — so no in-language assertion can observe one.
    # It is read where an abort is read, off the exit code of a separate evaluation:
    # `ci/bench/engine-ceiling.sh`, the `refuseUnknownField` arm. A cell here would have to
    # pretend the error is catchable, which is the thing it would then be pinning.
  };
}
