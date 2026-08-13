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
# "Towards a Theory of Declarative Knowledge", in Minker (ed.), pp. 89–148 — a stratified program's
# standard model is built stratum by stratum, `M_i = T_{P_i}↑ω(M_{i-1})` (printed p. 108), each
# stratum reaching its own fixed point before the next begins. That completeness is what aggregation
# classically demands of stratification, and it is NOT a restriction on what a stratum may read:
# strictly-lower indexing is their rule for the NEGATIVE case (§"Stratified Programs", Definition 3,
# printed p. 96) and a sufficient condition for completeness rather than the property itself.
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
    isString
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

  # A value the EVALUATOR treats as its store path rather than as its contents: `==` compares two
  # of these by `outPath` alone, and `toJSON` renders one by its path. The marker is the whole of
  # the test, because it is the whole of the evaluator's test.
  isDerivation = v: isAttrs v && (v.type or null) == "derivation";

  # ── WHERE A FUNCTION SITS INSIDE A VALUE ──
  # The position of the first function anywhere in a value, rendered as a path expression, or null
  # if there is none. Written as a pair of mutually recursive scans whose frame depth is the value's
  # NESTING DEPTH and not its size: siblings are independent applications that do not nest, and the
  # fold over them stops descending as soon as a site is found.
  #
  # ★ IT STOPS AT A DERIVATION, AND AT NOTHING ELSE THAT CARRIES AN `outPath`. The evaluator's
  # shortcut is narrower than its store-path rendering: `==` compares by `outPath` only when BOTH
  # sides are marked derivations, and compares every other attribute set FIELD BY FIELD — functions
  # included. So a bare `outPath` carrier is a value whose comparison the interior decides, and a
  # scan that stopped there would hand exactly such fragments to `==`. Measured on this evaluator:
  # two distinct carriers with one `outPath` and different functions compare FALSE, while the same
  # pair marked `type = "derivation"` compares TRUE.
  siteIn =
    where: v:
    if isFunction v then
      where
    else if isAttrs v then
      if isDerivation v then
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

  # ── THE KEY IS DECIDED BEFORE ANY MESSAGE CAN BE BUILT, AT EVERY FOLD ──
  # Every refusal in this file NAMES the key, and naming it means interpolating it. Interpolating a
  # non-string is not a refusal that mentions the wrong thing — it is a coercion error, which is not
  # a value: `tryEval` does not hold it, and it fires while the message explaining a DIFFERENT
  # refusal is being assembled. So a fold handed a non-string key ended the evaluation both when its
  # fragments were fine and when they were not, and the caller was told neither.
  #
  # ★ THIS IS THE SHAPE A DOOR TAKES WHEN IT CHECKS ONE ARGUMENT AND NOT THE OTHER, and the project
  # has it recorded elsewhere: a published entry point that refuses ill-typed values by name through
  # the arm underneath it, while an ill-typed value in its OWN preamble kills the evaluation before
  # that arm can see it. A door strictly weaker than its own refusals is the same defect wherever it
  # appears, and the answer is the same — decide the argument where the door is, not where the
  # message is.
  #
  # It is checked at EVERY fold, `list` included, even though `list` raises nothing to interpolate.
  # The signature `key: [v]: v` belongs to the VOCABULARY and not to its members: a fold that
  # quietly accepted what the others refuse would make the one contract a caller is given untrue at
  # the member they happened to pick. The check names the fold, so the caller learns which one.
  keyDefect = key: if isString key then null else "`key` is a ${typeOf key} rather than a string";

  # Named for the fold, because a message that names only the vocabulary tells a caller with five
  # folds in a spec nothing about which call to fix.
  refuseKey =
    fold: defect:
    throw "gen-scope.folds.${fold}: ${defect} — every refusal this fold can raise names the key, so a key that cannot be rendered ends the evaluation in place of the refusal that was owed";

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
  # ★ WHERE THE SCAN IS STRICTER THAN THE DIAGNOSTIC, AND WHAT THAT COSTS — measured, because the
  # first version of this paragraph was wrong in both halves. The scan's domain is the COMPARISON's
  # precondition, and it stops exactly where `==` stops: at a marked derivation, whose interior
  # neither the comparison nor the message ever reads. It is stricter than what `toJSON` can RENDER,
  # which is a wider set — a bare `outPath` carrier and a `__toString` carrier both render, and both
  # are refused here when a function sits inside them. That direction is deliberate: their
  # comparison is decided field by field, functions included, so admitting them would buy a rendered
  # message at the price of an answer nobody can account for.
  #
  # ★ AND THE REFUSED SET IS NOT "what the comparison could only have accepted by accident". Some of
  # it would have produced a perfectly catchable conflict — two rendering-capable carriers with
  # different functions inside compare FALSE and the message prints them fine. What the refusal buys
  # THERE is not catchability but meaning: a conflict between two fragments that render IDENTICALLY,
  # reported to a caller who can see no difference between them, is an answer they cannot act on.
  same =
    key: vs:
    let
      kd = keyDefect key;
      site = functionSite vs;
    in
    if kd != null then
      refuseKey "same" kd
    else if vs == [ ] then
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
    let
      kd = keyDefect key;
    in
    if kd != null then
      refuseKey "one" kd
    else if length vs == 1 then
      head vs
    else
      throw "gen-scope.folds.one: key '${key}' has ${toString (length vs)} contributors, expected exactly 1";

  # Collect the fragments in pinned order (`key: [v]: [v]`). The identity of this vocabulary: it
  # imposes nothing, which is what makes it the fold to reach for when the aggregate IS the list.
  # It still decides its key, for the reason given where that check is written: the signature is the
  # vocabulary's, and a member that admits what the others refuse makes it untrue.
  list =
    key: vs:
    let
      kd = keyDefect key;
    in
    if kd != null then refuseKey "list" kd else vs;

  # Shallow merge of attribute-set fragments; disjoint sub-keys required, because two fragments
  # writing one sub-key have no merge rule between them and picking a winner here would decide it
  # silently.
  #
  # The collision diagnostic renders ATTRIBUTE NAMES, which are strings by construction, so it is
  # total for the same reason the fragment-shape refusal above it is not free.
  mergeAttrs =
    key: vs:
    let
      kd = keyDefect key;
      bad = nonAttrsSite vs;
    in
    if kd != null then
      refuseKey "mergeAttrs" kd
    else if bad != null then
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
      kd = keyDefect key;
      bad = nonAttrsSite vs;
      shaped =
        if kd != null then
          refuseKey "byKey" kd
        else if bad == null then
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
