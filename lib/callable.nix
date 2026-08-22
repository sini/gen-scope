# Whether a value can be APPLIED — approximated, because the exact property is not decidable by
# any terminating predicate and the approximation is chosen to err in the safe direction.
#
# `isFunction` alone is too NARROW: it is false for an attribute set carrying `__functor`, which
# this evaluator applies perfectly well. Carrying the attribute is too WIDE: applying such a set
# evaluates `v.__functor v arg`, so what gets applied is the attribute's VALUE, and a `__functor`
# holding an integer aborts at the call site exactly as a bare integer would. Both are the same
# defect — a predicate that does not decide the property it is named for — pointed in opposite
# directions.
#
# ★ WHY ONE LEVEL AND NOT A WALK. The `__functor` chain has no bound, and it can refer to itself:
# `let f = { __functor = f; }; in f` is a value whose application diverges, so a predicate that
# followed the chain would diverge deciding it. A depth ceiling would be a number nobody can
# justify. One level is what terminates on every input.
#
# WHAT THAT COSTS: a NESTED functor applies, and this admits only the first level, so it refuses
# the deeper ones. Measured at TWO, THREE AND FOUR levels — each evaluates to its innermost
# function — which is a sample and not an induction; nothing here claims a depth that was not run.
# The approximation therefore errs toward refusing working input rather than admitting input that
# aborts, which is the direction where the caller gets a name instead of a dead evaluation.
#
# ★★ ONE BINDING, TWO CALLERS, AND THAT IS WHY IT LIVES IN A FILE OF ITS OWN. The kind registry
# decides this of a `resolve` and the circular carrier decides it of a `leq`. Two copies of a
# discipline agree only for as long as someone keeps them in step, and an APPROXIMATION is exactly
# the kind of thing that drifts: a carrier admitting a `__functor` order while the registry refused
# a `__functor` resolver would be two different answers to one question, each defensible alone. The
# module takes no argument — it depends on nothing and names no prelude, like the algebraic graph
# core and the traversal vocabulary beside it.
v: builtins.isFunction v || (builtins.isAttrs v && v ? __functor && builtins.isFunction v.__functor)
