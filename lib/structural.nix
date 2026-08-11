# The structural partition: ONE syntactic predicate over attribute NAMES.
#
# An attribute is STRUCTURAL when the graph's shape depends on it, and RESOLUTIONAL
# otherwise. The partition decides what may be reused from a prior evaluation: a structural
# value is always recomputed, so a dirty descendant stays reachable and a labelled
# reachability relation is never read stale.
#
# WHY A PREDICATE OVER THE NAME AND NOT AN ENUMERATION. `edges-<label>` is an OPEN FAMILY
# whose members are constructed during evaluation (`self.get id "edges-${label}"`, see
# `followEdge` and `collectionAttr`'s `label:` traversal in resolve.nix), so no list of names
# can be complete. An under-inclusive partition admits a structural name into the reuse
# vocabulary, where a consumer naming it is served a STALE STRUCTURAL VALUE — a wrong answer
# reachable without malice, through nothing worse than a classifier that missed a label. A
# predicate over the name is TOTAL over any attribute set, including a caller's, which is the
# property an enumeration cannot have.
#
# WHY THE PREDICATE IS DERIVED AND NOT DECLARED. A declared classification (an author-supplied
# stratum) answers the same question, and the derived form governs: the burden of proof falls
# on the declaration, which must carry an argument that derivation is impossible. Derivation
# is available — this is it — so no such argument can be given.
#
# THE STATED DOMAIN, because a syntactic classifier has one. `structural` is decidable and
# total, but its FAITHFULNESS rests on consumers naming structural attributes inside the
# reserved namespace. A consumer that invents a structurally-meaningful attribute under a name
# outside the namespace is classified resolutional and may be reused. The substrate cannot
# detect semantic structurality — that is undecidable — so this residual is real and is NOT
# closed here. What catches it is the byte-parity oracle: a stale structural value is a parity
# failure. Three instruments, each with its own domain: the syntactic classifier for the
# decidable half, the reserved namespace for naming, the parity oracle for the residual.
#
# CONTAINMENT NEEDS NO TERM. The third boundary family — a node's parent — rides the node
# record's `.parent` field (`queries.nix`), so it never reaches the evaluator as an attribute
# name at all. An attribute-name predicate is total over the names that reach it, and
# containment is not one of them.
{ prelude }:
let
  # The reserved structural namespace. Every attribute named into it is structural, and
  # therefore always recomputed and never reused.
  edgePrefix = "edges-";

  structural =
    name:
    name == "children"
    || name == "derived-children"
    || prelude.hasPrefix edgePrefix name
    # A consumer-level name: the imports relation is declared by the caller, not by this
    # library, so the partition is partly defined by the caller's attribute set. Naming it in
    # the substrate's own vocabulary is what puts a caller's boundary mark inside a rule the
    # substrate can apply.
    || name == "includes";

  # The complement over a set of names. The reuse vocabulary is this projection and nothing
  # else, so a structural name contributes nothing to what may be served — not because a guard
  # rejected it, but because there is nothing for it to intersect with.
  resolutionalNames = names: builtins.filter (name: !(structural name)) names;

  # The two attributes whose values are child-node records: the evaluator materializes their
  # children rather than returning the raw value. A materialization concern, not a partition
  # concern — both are structural, and so is every other member of the partition.
  childBearing = name: name == "children" || name == "derived-children";
in
{
  inherit
    edgePrefix
    structural
    resolutionalNames
    childBearing
    ;
}
