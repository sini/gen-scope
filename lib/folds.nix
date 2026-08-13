# THE STOCK FOLDS — the vocabulary an aggregation is written in, under ONE signature: `key: [v]: v`.
#
# The same shape serves both consumers: a kind's resource `fold`, where `key` is the resource key
# and the fragments are what the claimants of one dedup group contributed under it, and a wiring
# splice's combine, where `key` is the top-level wiring key. A fold written for either is usable at
# the other, and neither consumer has a vocabulary of its own.
#
# ── A VALUE ALGEBRA, WHICH IS WHY IT IS A MODULE AND NOT A SECTION ──
# Nothing here knows about kinds, claims, strata or the run that schedules them. A fold is handed a
# key and a list, and returns the one value that stands for the list. It depends on the prelude and
# on nothing else, and two independent consumers reach it — which is what makes it a module rather
# than a paragraph inside whichever of them was written first.
#
# ── WHAT AGGREGATION RESTS ON, AND WHERE THAT GUARANTEE IS ACTUALLY MADE ──
# An aggregate is meaningful over a COMPLETE fact set. THEORY: Apt, Blair & Walker (1988),
# "Stratified Programs" — a stratified program's standard model is built stratum by stratum,
# `M_i = T_{P_i}↑ω(M_{i-1})` (printed p. 108), each stratum reaching its own fixed point before the
# next begins. That completeness is what aggregation classically demands of stratification, and it
# is NOT a restriction on what a stratum may read: strictly-lower indexing is ABW's rule for the
# NEGATIVE case (Definition 3, printed p. 96) and a sufficient condition for completeness rather
# than the property itself.
#
# ★ AND NOTHING IN THIS FILE ENFORCES IT, WHICH IS THE POINT OF SAYING IT HERE. These are total
# functions of the list they are handed; no fold can tell a closed fact set from a prefix of one,
# and a fold applied to a prefix returns a confident answer about the prefix. The guarantee belongs
# to the caller's schedule — the cascade folds a kind's fragments only once that kind's stratum has
# finished — so a consumer that folds outside such a schedule has not weakened a check here, it has
# stepped outside the only thing that made the answer mean what it reads as.
#
# ── EVERY FOLD REFUSES ITS PRECONDITION BY NAME ──
# A fold's fragments are values a caller chose, and each fold below is defined only over some of
# them: `same` needs its fragments to be comparable, `mergeAttrs` and `byKey` need attribute sets.
# The alternative to refusing by name is not a milder failure, it is a WORSE one — an evaluator type
# error, or a `toJSON` that cannot render what it was asked to. Neither is a value: `tryEval` does
# not hold either, so what surfaces terminates the evaluation and carries no fold, no key and no
# fragment position in it. So each precondition is decided where the fragments are in hand, and the
# refusal names the fold, the key and the position in the fragment list.
#
# ── ORDER AND ARITY ──
# Fragments arrive in the caller's pinned order and are never reordered or silently deduplicated
# here; a fold wanting a canonical order imposes one itself. Every fold must handle a one-element
# list, because a kind's fold is applied to singleton groups too: a group of one is still a group,
# and skipping the fold for it would make an aggregate's SHAPE depend on how many claimants there
# happened to be.
{ prelude }:
let
  inherit (builtins)
    attrNames
    isAttrs
    isFunction
    isList
    toJSON
    typeOf
    ;
  inherit (prelude)
    all
    concatMap
    filter
    foldl'
    head
    imap0
    length
    listToAttrs
    map
    nameValuePair
    unique
    ;

  # ── WHERE A FUNCTION SITS INSIDE A VALUE ──
  # The position of the first function anywhere in a value, rendered as a path expression, or null
  # if there is none. Written as a pair of mutually recursive scans whose frame depth is the value's
  # NESTING DEPTH and not its size: siblings are independent applications that do not nest, and the
  # fold over them stops descending as soon as a site is found.
  #
  # It stops at `outPath`, because that is where both readers of these values already stop:
  # `toJSON` renders a store-path carrier by its path, and `==` compares two derivations by theirs.
  # A scan that walked inside one would answer a question neither the comparison nor the diagnostic
  # ever asks.
  siteIn =
    where: v:
    if isFunction v then
      where
    else if isAttrs v then
      if v ? outPath then
        null
      else
        firstSite (
          map (n: {
            w = "${where}.${n}";
            v = v.${n};
          }) (attrNames v)
        )
    else if isList v then
      firstSite (
        imap0 (i: e: {
          w = "${where}[${toString i}]";
          v = e;
        }) v
      )
    else
      null;

  firstSite = items: foldl' (found: it: if found != null then found else siteIn it.w it.v) null items;

  # The fragment-list position of the first function in a fragment list, or null.
  functionSite =
    vs:
    firstSite (
      imap0 (i: v: {
        w = "[${toString i}]";
        inherit v;
      }) vs
    );

  # The fragment-list position of the first fragment that is not an attribute set, or null. Kept as
  # a position rather than as the value, because the value is the thing that cannot be rendered.
  nonAttrsSite =
    vs:
    let
      bad = filter (e: !isAttrs e.v) (imap0 (i: v: { inherit i v; }) vs);
    in
    if bad == [ ] then null else head bad;

  # ── `same`: ALL FRAGMENTS AGREE, AND THEY MUST BE COMPARABLE FOR THAT TO BE A QUESTION ──
  # Duplicate contributions that must agree are provisioned once. Returns the first fragment, which
  # is the whole content of "they agree".
  #
  # ★★ THE GUARD IS A PRECONDITION OF THE COMPARISON AND NOT A REPAIR OF ITS DIAGNOSTIC. Nix's `==`
  # is not an equivalence relation over values containing functions — it is not even reflexive
  # there. A lambda reached through two evaluations compares FALSE against itself, while the same
  # value slot compared with itself is TRUE by pointer identity. So over function-bearing fragments
  # this fold does not answer "do these agree"; it answers "did these arrive as one value slot",
  # which is a fact about how the caller built the list. An answer that rests on that accident is
  # not a property anything can state, so the fragments are refused by name before they are
  # compared.
  #
  # ★ AND IT IS WHAT MAKES THE MISMATCH DIAGNOSTIC SAFE, which is the half that fires first in
  # practice. `toJSON` ABORTS on a value containing a function at any depth, and an abort is not a
  # throw: no `tryEval` around the call holds it, so the conflict message — written to explain a
  # mismatch to whoever caused it — terminates the evaluation instead, with the evaluator's sentence
  # and no key in it. The guard DOMINATES that branch rather than sitting beside it: no
  # function-bearing fragment reaches the comparison, so nothing that reaches the diagnostic can
  # abort inside it.
  #
  # ★ WHICH WAY THE APPROXIMATION ERRS, stated because it is one. The scan asks a structural
  # question — is there a function anywhere in here — and that is stricter than what `toJSON` can
  # render: an attribute set carrying `__toString` renders through its string coercion and this
  # refuses it anyway. It errs toward refusal, which is the only direction a guard against an
  # uncatchable abort may err, and what it refuses is exactly the set of fragments the comparison
  # could have accepted only by pointer accident.
  same =
    key: vs:
    let
      site = functionSite vs;
    in
    if vs == [ ] then
      throw "gen-scope.folds.same: empty fragment list for key '${key}'"
    else if site != null then
      throw "gen-scope.folds.same: key '${key}' has a fragment carrying a function, at fragment-list position ${site} — `==` is not an equivalence over function-bearing values, so whether these fragments agree is not a question this fold can answer"
    else if all (v: v == head vs) vs then
      head vs
    else
      throw "gen-scope.folds.same: conflicting values for key '${key}': ${toJSON vs}";

  # Exactly one contributor; a second is a loud error. The default combine of a wiring splice, where
  # two authors of one key have no merge rule between them.
  one =
    key: vs:
    if length vs == 1 then
      head vs
    else
      throw "gen-scope.folds.one: key '${key}' has ${toString (length vs)} contributors, expected exactly 1";

  # Collect the fragments in pinned order (`key: [v]: [v]`). The identity of this vocabulary: it
  # imposes nothing, which is what makes it the fold to reach for when the aggregate IS the list.
  list = _key: vs: vs;

  # Shallow merge of attribute-set fragments; disjoint sub-keys required, because two fragments
  # writing one sub-key have no merge rule between them and picking a winner here would decide it
  # silently.
  #
  # The collision diagnostic renders ATTRIBUTE NAMES, which are strings by construction, so it is
  # total for the same reason the fragment-shape refusal above it is not free.
  mergeAttrs =
    key: vs:
    let
      bad = nonAttrsSite vs;
    in
    if bad != null then
      throw "gen-scope.folds.mergeAttrs: key '${key}' has a fragment that is a ${typeOf bad.v} rather than an attribute set, at fragment-list position [${toString bad.i}]"
    else
      foldl' (
        acc: v:
        let
          dup = filter (k: acc ? ${k}) (attrNames v);
        in
        if dup != [ ] then
          throw "gen-scope.folds.mergeAttrs: key '${key}' collision on sub-key(s) ${toJSON dup}"
        else
          acc // v
      ) { } vs;

  # A fold CONSTRUCTOR for attribute-set-shaped fragments: each top-level fragment key `k` is folded
  # by its own named sub-fold `spec.${k}`, under the diagnostic sub-key "<key>.<k>". Fragments not
  # defining `k` are skipped and pinned order is preserved among those that do. A fragment key the
  # spec does not declare is a loud error — an undeclared key has no merge rule, and admitting it
  # would mean picking one.
  #
  # ONE declared level of nesting, which is the stock answer to "a shared resource with a per-
  # claimant sub-entry". Deeper nesting is another `byKey` in the spec, written by the caller who
  # knows the shape.
  byKey =
    spec: key: vs:
    let
      bad = nonAttrsSite vs;
      shaped =
        if bad == null then
          true
        else
          throw "gen-scope.folds.byKey: key '${key}' has a fragment that is a ${typeOf bad.v} rather than an attribute set, at fragment-list position [${toString bad.i}]";
      allKeys = unique (concatMap attrNames vs);
      foldKey =
        k:
        if !(spec ? ${k}) then
          throw "gen-scope.folds.byKey: key '${key}': fragment key '${k}' not declared in the fold spec"
        else
          let
            contributors = filter (v: v ? ${k}) vs;
            values = map (v: v.${k}) contributors;
          in
          spec.${k} "${key}.${k}" values;
    in
    # `shaped` is read in the condition rather than bound and ignored: a precondition nothing forces
    # is a precondition that fires only for the callers who happen to look at the right field.
    if shaped then listToAttrs (map (k: nameValuePair k (foldKey k)) allKeys) else { };
in
{
  folds = {
    inherit
      same
      one
      list
      mergeAttrs
      byKey
      ;
  };
}
