# The program the engine computes over, and the dependency graph its semantics is stated on.
#
# A PROGRAM IS RULES OVER ATOMS. A rule is `head :- p₁ … pₙ, not q₁ … not qₘ`: a head atom, a
# positive body and a negative body. It is plain data — strings and lists of strings — so a
# program is the same value on either side of an evaluation boundary, and nothing in it is a
# function whose identity was minted by the build that made it.
#
# THE ATOM IS THE UNIT. The well-founded model is computed at the ATOM level rather than at the
# relation-symbol level, which is what lets one contested pair be contested while its neighbours
# in the same relation settle. Van Gelder, Ross & Schlipf 1991 state the semantics over the
# Herbrand base; here that base is `atoms`, and it is closed by construction — every atom the
# rules mention is in it, whether or not any rule has it as a head.
#
# ★★ AND UNDER THE ENGINE'S INTERPRETATION PARAMETER THAT BASE IS THE PROGRAM'S HALF OF A LARGER
# ONE, WHICH IS SAID HERE RATHER THAN LEFT TO CONTRADICT THE SENTENCE ABOVE. `atoms` is still
# closed by construction over the RULES; nothing in the paragraph above weakens. But a caller may
# carry a verdict for an atom this program never mentions, so the base the model is computed and
# REPORTED over is `atoms ∪ dom(interpretation)` — partly closed by construction, partly DECLARED
# by the caller. The engine keeps the two halves in that order: program atoms first in declaration
# order, then interpretation atoms not already present. A header claiming a closure the code no
# longer delivers is the silent-drift class this repository exists to close, so the claim is scoped
# rather than left standing.
# ★ `bodyArity`, `unaryBodies` and the routing are untouched: an interpretation adds no rules, so
# it cannot raise the greatest positive body arity.
#
# THE DEPENDENCY GRAPH IS SIGN-LABELLED, AND THE LABELS ARE WHY THE SEMANTICS IS NEEDED AT ALL.
# Apt, Blair & Walker 1988 give a meaning to a program whose cycles are all positive, and give a
# cycle through a negative edge nothing; the well-founded model is what supplies one. So the
# label is not decoration on the relation — it is the discriminator between the fragment ABW
# covers and the fragment it does not.
#
# THE LABELS LIVE BESIDE THE UNSIGNED RELATION, NEVER ON IT, and the split is deliberate. Mutual
# reachability — the relation whose equivalence classes are the strongly connected components —
# is a property of the UNSIGNED edge set: two atoms are in one component when each reaches the
# other, and by what sign is not part of that question. So `dependency` is the accessor the
# partition door is handed and `signs` is the labelled view read beside it. Composing a labelled
# edge set with a partitioner is a separate surface with a separate open defect, and it is not
# this one: nothing here asks the door to carry a label.
{ prelude }:
let
  # First-occurrence-wins dedup over names, INDEX-BASED. Two constructions are excluded rather
  # than merely not chosen: a fold carrying a `seen` attrset copies that attrset once per
  # element, which is quadratic on the atom axis; and a self-recursive walk spends one evaluator
  # frame per element, which is the per-atom recursion this engine forbids outright and which
  # aborts uncatchably past the call-depth guard. One `listToAttrs` recording first positions
  # and one pass reading them back is linear and flat, and it keeps DECLARATION ORDER — which
  # the ordered fold over contributions then depends on, so the order is load-bearing and not a
  # nicety.
  firstOccurrence =
    names:
    let
      n = prelude.length names;
      firstAt = prelude.listToAttrs (
        prelude.genList (i: {
          name = prelude.elemAt names i;
          value = i;
        }) n
      );
    in
    prelude.concatMap (
      i:
      let
        name = prelude.elemAt names i;
      in
      prelude.optional (firstAt.${name} == i) name
    ) (prelude.genList (i: i) n);

  # A rule, and the pattern is the refusal. An unknown field is rejected BY NAME at
  # construction by the interpreter itself, so a caller who misspells `neg` learns it at the
  # rule rather than through a model that quietly lost a negative literal. Both bodies default
  # to empty because a rule with neither is a FACT, which is the base case of the least model
  # and not an omission.
  mkRule =
    {
      head,
      pos ? [ ],
      neg ? [ ],
    }:
    {
      inherit head pos neg;
    };

  mkProgram =
    { rules }:
    let
      normalized = map mkRule rules;
      # The Herbrand base: every atom the rules mention, in declaration order. Heads first,
      # then each rule's positive then negative body — so an atom's position is where it was
      # first written, and the order is a function of the program text rather than of a
      # codepoint sort applied to it later.
      atoms = firstOccurrence (
        map (r: r.head) normalized ++ prelude.concatMap (r: r.pos ++ r.neg) normalized
      );
      # The ROUTING DISCRIMINATOR, computed ONCE, on the program. It is the greatest POSITIVE
      # body arity, and reading only the positive body is what makes "once" sound: the reduct
      # against any guess deletes whole rules and deletes negative literals, and does neither
      # of the two things that could raise this number. So a program routed by this figure
      # routes the same way for every reduct the alternating fixpoint will take of it, and no
      # re-derivation per round is owed.
      bodyArity = prelude.foldl' prelude.max 0 (map (r: prelude.length r.pos) normalized);
    in
    {
      inherit atoms bodyArity;
      rules = normalized;
      # A property of the PROGRAM, never a mode a caller selects. A caller-selected mode would
      # let a caller select the engine that cannot express their program; this cannot be
      # selected at all, only computed.
      unaryBodies = bodyArity <= 1;

      # The unsigned dependency accessor, in the shape the partition door reads: `nodes` and an
      # `edges` function. An edge runs HEAD → BODY ATOM — "this atom's meaning depends on
      # that one" — so a longest path over the condensation is a dependency depth read the way
      # a stratification is read, deepest consumer to its ultimate producers.
      dependency = {
        nodes = atoms;
        edges =
          let
            byHead = prelude.mapAttrs (_: rs: firstOccurrence (prelude.concatMap (r: r.pos ++ r.neg) rs)) (
              builtins.groupBy (r: r.head) normalized
            );
          in
          atom: byHead.${atom} or [ ];
      };

      # The SIGN-LABELLED view, read beside the unsigned relation rather than through it. Total
      # on every string: an atom no rule heads has two empty label sets, which says there is no
      # edge, rather than answering with a value that has to be tested for absence.
      signs =
        let
          byHead = prelude.mapAttrs (_: rs: {
            positive = firstOccurrence (prelude.concatMap (r: r.pos) rs);
            negative = firstOccurrence (prelude.concatMap (r: r.neg) rs);
          }) (builtins.groupBy (r: r.head) normalized);
        in
        atom:
        byHead.${atom} or {
          positive = [ ];
          negative = [ ];
        };
    };
in
{
  inherit mkRule mkProgram;
}
