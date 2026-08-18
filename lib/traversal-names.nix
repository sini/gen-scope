# The traversal vocabulary: the attribute NAMES under which this library's resolver reaches a
# scope-graph edge relation. ONE binding, read by the resolver that traverses the relation and by
# the classifier that must reserve it, so the two cannot come to hold different names.
#
# WHAT IS BOUND HERE. Neron et al. (2015) give a scope graph labelled edges and rank resolution
# D < I < P (Fig. 2); van Antwerpen et al. (2018 §2.1) generalize the query over those labels. The
# I edges reach this evaluator as a COMPUTED ATTRIBUTE rather than as a field on the node record,
# which is what admits an import relation resolved during evaluation — and a computed attribute is
# reached by NAME. The name is therefore the thing two modules have to agree on, and agreement
# between two written-down literals is a coincidence rather than a property.
#
# WHY THAT COINCIDENCE IS THE DANGEROUS KIND. The resolver traverses the relation; the structural
# partition must reserve it, because a relation classified resolutional MAY be served from a prior
# evaluation. Let the two literals drift and the reserved-but-untraversed name reserves nothing
# while the traversed-but-unreserved name is served warm — and neither says so. The value is
# well-typed, the evaluation completes, and the answer is computed over a STALE import relation.
# Nothing in the result distinguishes it from a correct one.
#
# WHY THE CLASSIFIER READS THE SET AND NOT A MEMBER. `structural` reserves the VALUES of this set
# rather than naming `imports` for itself, so it holds no relation name of its own: a relation
# added here is reserved BY CONSTRUCTION rather than by a second edit some later author has to
# remember. An enumeration maintained on the classifier's side would answer today's question and
# leave tomorrow's traversal able to miss the join, which is the shape `structural`'s own header
# argues against where it explains why `edges-` is a prefix predicate and not a list.
#
# WHAT THIS DOES NOT CLOSE, stated because the wide reading of it would be false. It does not make
# the vocabulary complete. A traversal that writes its own string literal instead of taking a
# member from here still escapes, and no predicate over attribute names can catch that: the
# traversed names live inside `self.get id "…"` call sites, and a classifier reading names has no
# access to a caller's literals. This closes the drift between the two consumers that DO read the
# binding, and closes nothing beyond them — the residual belongs to `structural`'s stated domain,
# where it is already named and where the byte-parity oracle is its instrument.
{
  # The import relation I (Neron et al. 2015, Fig. 2; van Antwerpen et al. 2018 §2.1). Declared by
  # the consumer in its own attribute set, like every attribute here — what this library owns is
  # the NAME it reaches for, which is exactly what has to be reserved.
  imports = "imports";
}
