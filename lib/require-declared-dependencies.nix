# The declared relation every entry taking one demands, and its refusal.
#
# It lives in its own module for `require-scope.nix`'s reason and is INTERNAL in the same way: two
# modules need it — the evaluator and the cold fold — and the assembly point binds it and hands it
# on rather than merging it into the published surface. A guard is not a consumer-facing construct.
#
# ── THE TYPE IS `gen-graph`'s AND THE REFUSAL IS THIS LIBRARY'S ──
# The contract on a declared relation lives at its CONSTRUCTOR — `gen-graph.mkDeclaredEdges` — where
# the accept-list, the endpoint check and the deep force all run, because a construct's contract
# belongs at its construction site. What is left for a consumer is to ADMIT ONLY WHAT THAT
# CONSTRUCTOR MINTED: a contract enforced inside the fold that reads the relation is bypassed by any
# caller who hand-assembles the context, and callers do exactly that.
#
# ★ SO THE DISCRIMINATOR IS SHARED AND THE MESSAGE IS NOT. `gen-graph.isDeclaredEdges` answers the
# one question a consumer cannot answer for itself — does this value carry the tag only those
# constructors write — and the refusal is minted HERE, naming THIS library's entry point, because
# the defect is at this library's door and a refusal minted in `gen-graph` would name `gen-graph`
# for it. That is the whole reason no `requireDeclaredEdges` ships beside the constructor, and it is
# why a discriminator with no consumer calling it would be a guard nobody calls.
#
# ★ THE PREDICATE IS NOMINAL, WHICH IS WHAT MAKES THE TWO-ARMED DETAIL LOAD-BEARING. A
# hand-assembled attrset carrying an `index` and a `dependencies` has the right SHAPE and is
# precisely the bypass — of it `builtins.typeOf` says `set`, which tells a reader nothing they did
# not already know. That arm names the CONSTRUCTOR that was missed instead, so the reader is told
# the door they walked past; only the arm where no constructor is plausibly in play falls back to
# the type.
#
# ★ AND IT IS AN ACCEPT-LIST. The minted value is admitted first and everything else is refused, so
# a shape nobody thought to enumerate is refused rather than admitted — `require-scope.nix` states
# the same convention for the scope guard, and `declared-edges.nix` for the constructor.
{ graph }:
{
  requireDeclaredDependencies =
    entry: declared:
    let
      must = "gen-scope.${entry}: `declaredDependencies` must be the relation `gen-graph.mkDeclaredEdges` returns";
      pass = "Build it with `gen-graph.mkDeclaredEdges` and pass the result: the relation is contracted where it is constructed, so a value this entry cannot tell apart from a contracted one is one it must refuse.";
      bad = detail: throw "${must}; ${detail}. ${pass}";
    in
    if graph.isDeclaredEdges declared then
      declared
    else if builtins.isAttrs declared then
      bad "received an attrset that `mkDeclaredEdges` did not build"
    else
      bad "received a ${builtins.typeOf declared}";
}
