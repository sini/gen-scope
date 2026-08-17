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
# ── AND THE VOCABULARY ITSELF CLAIMS NO PRIMARY ──
# The citation above is the PRECONDITION's, not the algebra's, and the difference is worth saying
# because a citation standing this near the top reads as though it covered the file. Which
# operators exist below, the single `key: [v]: v` shape they share, and the refuse-by-name
# discipline each one carries are original to gen; no published result is being implemented here.
# That is an absence claim, so the search behind it is named rather than implied: the literature a
# construction of this shape would be expected to cite — catamorphisms and the Bird–Meertens
# formalism, Meijer's banana/lens calculus, Hutton's universality-of-fold treatment — is not held
# by this project, so no primary for it was available to verify a citation against and none is
# written. If one is acquired, this paragraph is what it gets checked against.
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
    isPath
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

  # ── THE PROPERTY, WHICH HAS TWO HALVES, AND EACH IS ENFORCED SOMEWHERE DIFFERENT ──
  # Every fragment this fold accepts ends up at two readers: `==` decides whether it agrees, and
  # `toJSON` renders it if it does not. So the fold is sound only if BOTH of these hold:
  #
  #   SKIPPED ⊆ USABLE    — what the scan declines to look inside must still be comparable and
  #                         renderable, since the scan is what would otherwise have caught it
  #   ADMITTED ⊆ USABLE   — and so must everything the scan looked at and passed, because a
  #                         fragment can contain no function at all and still be unrenderable
  #
  # The predicate below is the FIRST half. The scan under it is the second: a value neither reader
  # can take is a refusal SITE wherever it sits, not merely a reason to descend past it. Half one
  # alone was this construction's defect for several revisions — the licence to skip kept being
  # narrowed while the admitted set was assumed usable because nothing in it was a function.
  #
  # ── WHAT MAY BE SKIPPED, DERIVED FROM THE PROPERTY RATHER THAN FROM A LIST OF SHAPES ──
  # A fragment may be skipped only if both readers still work on it. Skipping is a promise about
  # two readers, so the predicate is their INTERSECTION, and any term dropped from it hands the
  # scan's own subject to whichever reader was not considered.
  #
  # That resolves to a three-term conjunction: the derivation MARKER, an `outPath`, and an `outPath`
  # whose value is a STRING. It is deliberately not nixpkgs' `isDerivation`, which tests the marker
  # alone and is a different predicate wearing a name close enough to be mistaken for this one.
  #
  # Measured on this evaluator, VARYING EVERY TERM — a table that fixes any one of them cannot see
  # the rule's ARITY, and each row below was a shape some earlier reading of this predicate skipped.
  # Two distinct fragments, different functions in their interiors:
  #
  #   marker + string `outPath`  ⇒ compared by path, rendered by path      — SAFE, and skipped here
  #   marker, no `outPath`       ⇒ field by field; `toJSON` ABORTS
  #   `outPath`, no marker       ⇒ field by field; the interior decides
  #   `outPath` = a function     ⇒ the paths themselves compare by pointer; `toJSON` ABORTS
  #   `outPath` = an attrs/list holding a function                        ⇒ `toJSON` ABORTS
  #   `outPath` = a path literal ⇒ agrees quietly, and ABORTS on the conflict branch, where
  #                                rendering it attempts a store path that does not exist
  #   `outPath` = an integer     ⇒ both readers cope. It is EXCLUDED anyway, because the licence to
  #                                skip is that the value STANDS FOR a store path, not that it
  #                                happens to render — a predicate built by collecting shapes that
  #                                survive is the enumeration this one exists not to be.
  #
  # ★ AND THE SECOND READER ONLY RUNS ON THE CONFLICT BRANCH, which is why agreement is an axis too:
  # a fixture whose fragments agree never builds a diagnostic, so it reports every rendering hazard
  # in this table as absent.
  comparedByPath = v: isAttrs v && (v.type or null) == "derivation" && isString (v.outPath or null);

  # ── WHAT A FRAGMENT MAY NOT CONTAIN, AND THE GROUND FOR EACH ──
  # Two shapes, and they are refused for DIFFERENT reasons — which is why each carries its own,
  # rather than sharing one sentence that would be true of only one of them.
  #
  # A function breaks the comparison first: `==` is not an equivalence over it, so the fold's answer
  # would be decided by value sharing before rendering ever came up. A PATH compares perfectly well
  # — and cannot be reported. Measured on this evaluator: `toJSON` on a path that is not there
  # ABORTS uncatchably, and on one that IS there it COPIES the caller's path into the store and
  # renders the store path it just created. A message explaining a refusal may do neither, so a path
  # is refused where it sits even though the comparison would have handled it.
  hazardIn =
    v:
    if isFunction v then
      {
        what = "a function";
        because = "`==` is not an equivalence over function-bearing values, so whether these fragments agree is not a question this fold can answer";
      }
    else if isPath v then
      {
        what = "a path";
        because = "reporting a conflict over it would either abort on a path that is not there or copy the caller's path into the store, and a message explaining a refusal may do neither";
      }
    else
      null;

  # ── WHERE AN UNUSABLE VALUE SITS INSIDE A FRAGMENT ──
  # The position of the first one anywhere in a value, rendered as a path expression, or null if
  # there is none. Written as a pair of mutually recursive scans whose frame depth is the value's
  # NESTING DEPTH and not its size: siblings are independent applications that do not nest, and the
  # fold over them stops descending as soon as a site is found.
  #
  # ★ IT STOPS ONLY WHERE THE EVALUATOR ALREADY STOPS, WHICH IS THE WHOLE CONJUNCTION ABOVE AND NO
  # PART OF IT. Every other attribute set is compared FIELD BY FIELD, functions included, and
  # rendered by walking it — so a stop written on a subset of those terms hands the scan's own
  # subject straight to `==`: the fragments whose agreement a function decides, and whose conflict
  # message cannot be built without aborting.
  #
  # ★ AND A PER-FRAGMENT TEST IS SOUND FOR A PAIRWISE RULE, which is worth stating because it is not
  # obvious. Two functions can only be compared with each other where BOTH sides were skipped — and
  # both sides skipped is exactly the case the evaluator decides by path, never reading either
  # interior. Where only one side is skipped, the other is a value this scan ENTERED, so a function
  # able to decide that comparison is found there and refused. Neither case leaves a comparison for
  # a function to settle.
  siteIn =
    where: v:
    let
      hazard = hazardIn v;
    in
    if hazard != null then
      hazard // { w = where; }
    else if isAttrs v then
      if comparedByPath v then
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

  # ★ THE REFUSAL IS ONE THROW OVER TWO GROUNDS, AND WHAT THE MESSAGE CELLS PIN IS ITS RENDERED
  # TEXT, not the template that produces it. The template carries `what` and `because` from the
  # hazard, so the shape of the string here can be re-parameterised without any cell noticing —
  # which is correct, because a caller reads the rendered sentence and never the template. A cell
  # asserting the template would fail on a refactor that changed nothing a caller can observe, and
  # pass on one that changed the sentence while keeping the shape.
  #
  # The first unusable value in a fragment list, as its position and its ground, or null.
  hazardSite =
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
  # ★ WHERE THIS IS STRICTER THAN EITHER READER, AND WHAT EACH PART OF THAT COSTS. Two costs, and
  # they are paid for different reasons:
  #
  # ON THE COMPARISON SIDE, the scan refuses function-bearing fragments that `toJSON` could have
  # rendered — a `__toString` carrier renders through its string coercion, a marker-less `outPath`
  # carrier by its path. Their comparison is still decided field by field, functions included, so
  # admitting them would buy a rendered message at the price of an answer nobody can account for.
  # ★ And that refused set is NOT "what the comparison could only have accepted by accident": some
  # of it would have produced a perfectly catchable conflict, two rendering-capable carriers with
  # different functions comparing FALSE and printing fine. What the refusal buys there is not
  # catchability but meaning — a conflict between two fragments that render IDENTICALLY, reported to
  # a caller who can see no difference between them, is an answer they cannot act on.
  #
  # ON THE REPORTING SIDE, the cost is newer and larger, and it is paid deliberately: a fragment
  # carrying a PATH is refused even though the comparison would have handled it, and even when the
  # fragments AGREE and no message would ever have been built. The fold could have returned those.
  # It does not, because the alternative is a precondition that holds only until two fragments
  # differ — and a fold whose safety depends on its inputs agreeing has no precondition at all. The
  # refusal is at admission for that reason, and a cell pins the agreeing case so the cost stays a
  # decision rather than something discovered later.
  #
  # ★ WHAT IS NOT REFUSED, because the licence is about being reportable and nothing else: an
  # `outPath` that is an integer fails the skip predicate above, and is then ADMITTED and folded
  # like any other value — both readers cope with it. Excluding a shape from the shortcut is not the
  # same act as refusing it, and this file does the first far more often than the second.
  #
  # ── THE ALTERNATIVE THIS DOES NOT TAKE, AND THE PART OF IT THAT IS RIGHT ──
  # The reporting half could be met from the other side: leave everything admitted and make the
  # conflict message TOTAL, so no caller value is ever handed to a partial renderer. The strongest
  # form of that is SELECTIVE rather than blanket — render a derivation by its string `outPath`,
  # and a path or a function by a placeholder naming its type — and it keeps what a blanket total
  # renderer would lose, which is that this engine's real fragments are store paths and a message
  # naming them `<a set>` is worth less than the one it replaced. Nothing above argues against that
  # form, and it is written down here so it is not re-proposed as though it were unconsidered.
  #
  # ★ TWO GROUNDS SURVIVE IT, and they are why the refusals stay where they are:
  #
  #   THE FUNCTION ARM IS NOT A RENDERING PROBLEM. It is a precondition on the COMPARISON, and no
  #   renderer can supply it: `==` is not an equivalence over function-bearing values, so a fold
  #   that rendered such a conflict politely would still be ANSWERING by value sharing. The
  #   message would improve and the answer would remain unaccountable.
  #
  #   A PATH IN A FRAGMENT IS NOT PLAIN DATA. The constructional answer this library's design names
  #   for that class is plain-data conformance of what a resolver may hand back — which makes such
  #   a fragment INEXPRESSIBLE rather than well-rendered. Refusing it early is the same direction
  #   arrived at earlier, so the refusal is a step toward that construction; rendering it politely
  #   would be a step away, and a comfortable one that removes the pressure to build the real thing.
  same =
    key: vs:
    let
      kd = keyDefect key;
      site = hazardSite vs;
    in
    if kd != null then
      refuseKey "same" kd
    else if vs == [ ] then
      throw "gen-scope.folds.same: empty fragment list for key '${key}'"
    else if site != null then
      throw "gen-scope.folds.same: key '${key}' has a fragment carrying ${site.what}, at fragment-list position ${site.w} — ${site.because}"
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
