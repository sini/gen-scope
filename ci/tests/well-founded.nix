# The well-founded partial model, and the third value that is the reason it exists.
#
# ★ THE THREE-VERDICT ORACLE IS ONE PROGRAM, ONE RUN, and it covers every failure direction the
# semantics has. A fact must come out TRUE; a negative two-cycle must come out UNDEFINED — the
# shape the stratified semantics leaves without a meaning at all; and a positive cycle with
# nothing supporting it must come out FALSE, which is the unfounded-set half and the one a
# derivation-only engine gets wrong by returning nothing rather than by returning UNDEFINED. A
# suite carrying only the first two would pass against an engine that never says FALSE.
#
# ★ AND THE VERDICT FUNCTION IS TOTAL, which is the same property read from the other side: an
# atom outside the program is FALSE and says so, rather than answering with an absence the caller
# has to interpret. UNDEFINED is a value this function returns, never a silence it falls into.
{ genScope, ... }:
let
  # These cells are about the UN-INTERPRETED semantics, so the empty interpretation is written
  # once here rather than at every call. The interpreted case is ci/tests/interpretation.nix.
  wf =
    program:
    genScope.wellFoundedModel {
      inherit program;
      interpretation = [ ];
    };

  oracle = genScope.mkProgram {
    rules = [
      { head = "t"; }
      {
        head = "u1";
        neg = [ "u2" ];
      }
      {
        head = "u2";
        neg = [ "u1" ];
      }
      {
        head = "c1";
        pos = [ "c2" ];
      }
      {
        head = "c2";
        pos = [ "c1" ];
      }
    ];
  };
  m = wf oracle;

  # a0 a fact, a_i :- not a_{i-1}: a chain of negative edges, TOTAL at every atom, alternating
  # true and false. It is locally stratified, so the well-founded model is the perfect model and
  # nothing here acquires a meaning it did not already have.
  negChain =
    d:
    wf (
      genScope.mkProgram {
        rules = builtins.genList (
          i:
          if i == 0 then
            { head = "a${toString i}"; }
          else
            {
              head = "a${toString i}";
              neg = [ "a${toString (i - 1)}" ];
            }
        ) (d + 1);
      }
    );

  # The stratified fragment: a program with no negative cycle, where the model must be total.
  stratified = wf (
    genScope.mkProgram {
      rules = [
        { head = "p"; }
        {
          head = "q";
          pos = [ "p" ];
        }
        {
          head = "r";
          neg = [ "q" ];
        }
      ];
    }
  );
in
{
  flake.tests."engine-well-founded" = {
    test-a-fact-is-true = {
      expr = m.trueAtoms;
      expected = [ "t" ];
    };
    test-a-negative-two-cycle-is-undefined = {
      expr = m.undefinedAtoms;
      expected = [
        "u1"
        "u2"
      ];
    };
    test-an-unsupported-positive-cycle-is-false = {
      expr = m.falseAtoms;
      expected = [
        "c1"
        "c2"
      ];
    };
    test-the-three-verdicts-partition-the-atoms = {
      expr = builtins.sort builtins.lessThan (m.trueAtoms ++ m.undefinedAtoms ++ m.falseAtoms);
      expected = builtins.sort builtins.lessThan oracle.atoms;
    };
    # Total on every string, including one no rule mentions.
    test-the-verdict-is-total = {
      expr = map m.verdict [
        "t"
        "u1"
        "c1"
        "nothing-mentions-this"
      ];
      expected = [
        "true"
        "undefined"
        "false"
        "false"
      ];
    };
    test-verdict-names-are-a-closed-enumeration = {
      expr = genScope.verdictNames;
      expected = [
        "true"
        "undefined"
        "false"
      ];
    };
    test-the-model-converges = {
      expr = m.converged;
      expected = true;
    };
    # The atoms come back in DECLARATION order rather than in the codepoint order an attribute
    # walk would give, because that order is what the ordered fold over contributions is defined
    # against. `u1`/`u2` sort the same either way; `t` before them does not.
    test-atoms-are-emitted-in-declaration-order = {
      expr =
        (wf (
          genScope.mkProgram {
            rules = [
              { head = "zebra"; }
              { head = "alpha"; }
            ];
          }
        )).trueAtoms;
      expected = [
        "zebra"
        "alpha"
      ];
    };

    # ── THE REDUCT ──
    # Rules with a negative literal in the guess are DELETED; the survivors lose their negative
    # bodies and keep their positive ones. What comes out is definite, which is the only thing
    # the least-model door ever sees.
    test-the-reduct-deletes-rules-gated-on-the-guess = {
      expr = map (r: r.head) (genScope.reduct oracle { u1 = true; }).rules;
      expected = [
        "t"
        "u1"
        "c1"
        "c2"
      ];
    };
    test-the-reduct-is-definite = {
      expr = builtins.all (r: r.neg == [ ]) (genScope.reduct oracle { }).rules;
      expected = true;
    };
    # Reduction deletes rules and deletes negative literals; it does neither of the two things
    # that could raise the positive arity. That is what makes routing computed ONCE sound.
    test-the-reduct-carries-the-routing-figure = {
      expr = (genScope.reduct oracle { u1 = true; }).unaryBodies;
      expected = oracle.unaryBodies;
    };

    # ── THE OUTER LOOP ──
    # On a negation chain of depth d the alternating fixpoint settles in d/2 + 2 rounds, and the
    # model is total: no atom is undefined anywhere on it.
    test-a-negation-chain-is-total = {
      expr = (negChain 16).undefinedAtoms;
      expected = [ ];
    };
    test-outer-rounds-track-the-chain-depth = {
      expr = map (d: (negChain d).outerRounds) [
        8
        16
        32
      ];
      expected = [
        6
        10
        18
      ];
    };
    # Locally stratified, so the model is total and equal to the perfect model: nothing that
    # already had a meaning acquires a different one.
    test-a-stratified-program-has-a-total-model = {
      expr = {
        inherit (stratified) trueAtoms undefinedAtoms falseAtoms;
      };
      expected = {
        trueAtoms = [
          "p"
          "q"
        ];
        undefinedAtoms = [ ];
        falseAtoms = [ "r" ];
      };
    };
  };
}
