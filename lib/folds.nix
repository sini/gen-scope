# THE STOCK FOLDS — the vocabulary an aggregation is written in, under ONE signature: `key: [ { site; value; } ]: v`.
#
# The same shape serves both consumers: a kind's resource `foldFragments`, where `key` is the
# resource key and the fragments are what the claimants of one dedup group contributed under it,
# and a wiring splice's combine, where `key` is the top-level wiring key. A fold written for either
# is usable at the other, and neither consumer has a vocabulary of its own.
#
# ── A FRAGMENT IS A CONTRIBUTOR EDGE, NOT A BARE VALUE ──
# A fold's input is the materialised edge set of the query "the contributors of key k", one
# `{ site; value; }` record per contributor edge (ADR-0010 §2: provenance is the graph's; ADR-0012
# §2: a derived view is a named materialized query result). The record carries a RENDERING of the
# edge's source — the identity of the node that contributed the value, rendered by the caller that
# holds the edge — and the value. So every refusal below names the contributor it is about, and
# none names a position in a list the caller projected: a caller cannot re-site a refusal after the
# fact (`tryEval` drops the message, and `addErrorContext` adds a trace frame while the message
# keeps the position), so the site has to be in hand where the refusal is decided.
#
# ★ A RESIDUE AT THE DOOR, ENUMERATED (ADR-0025 item 1). The door admits any list of attribute
# sets carrying `value` and a string `site`. A caller still on the bare-value contract whose values
# happen to be attribute sets of exactly that shape (`list "c" [ { site = "x"; value = 1; } ]`) is
# admitted and read as edges, at rc 0. Telling that list from an edge list needs a mark a caller
# cannot also write, and pure Nix data has none: any tag is copyable, so a tag would move the
# ambiguity rather than close it. A bare-value caller whose values are of any OTHER shape is refused
# by name at the door, so the residue is exactly the values that spell an edge.
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
# operators exist below, the single `key: [ { site; value; } ]: v` shape they share, and the refuse-by-name
# discipline each one carries are original to gen; no published result is being implemented here.
# That is an absence claim, so the search behind it is named rather than implied: the literature a
# construction of this shape would be expected to cite — catamorphisms and the Bird–Meertens
# formalism, Meijer's banana/lens calculus, Hutton's universality-of-fold treatment — is not held
# by this project, so no primary for it was available to verify a citation against and none is
# written. If one is acquired, this paragraph is what it gets checked against.
#
# ── EVERY FOLD REFUSES ITS PRECONDITION BY NAME ──
# A fold's fragments are values a caller chose, and each fold below is defined only over some of
# them: `same` and `set` need their fragments to be comparable, `mergeAttrs`, `mergeAttrsDeep` and
# `byKey` need attribute sets.
# The alternative to refusing by name is not a milder failure, it is a WORSE one — an evaluator type
# error, or a `toJSON` that cannot render what it was asked to. Neither is a value: `tryEval` does
# not hold either, so what surfaces terminates the evaluation and carries no fold, no key and no
# fragment in it. So each precondition is decided where the fragments are in hand, and the refusal
# names the fold, the key and the contributor whose fragment it is.
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
    attrValues
    concatStringsSep
    elemAt
    genList
    isAttrs
    isFunction
    isList
    isPath
    isString
    seq
    toJSON
    typeOf
    unsafeDiscardStringContext
    zipAttrsWith
    ;
  inherit (prelude)
    absorb
    all
    any
    concatMap
    elem
    filter
    foldl'
    groupBy
    head
    imap0
    indexOf
    length
    listToAttrs
    map
    nameValuePair
    sort
    tail
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
        # The ground at a fold that never reports a conflict (`set`): the second of the two below.
        plain = "a path in a fragment is not plain data, and the construction this library names for that class makes such a fragment inexpressible, so it is refused where it sits rather than deduplicated";
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

  hasPath = p: v: p == [ ] || (isAttrs v && v ? ${head p} && hasPath (tail p) v.${head p});
  callable = prelude.isApplicable;

  # ★ THE REFUSAL IS ONE THROW OVER TWO GROUNDS, AND WHAT THE MESSAGE CELLS PIN IS ITS RENDERED
  # TEXT, not the template that produces it. The template carries `what` and `because` from the
  # hazard, so the shape of the string here can be re-parameterised without any cell noticing —
  # which is correct, because a caller reads the rendered sentence and never the template. A cell
  # asserting the template would fail on a refactor that changed nothing a caller can observe, and
  # pass on one that changed the sentence while keeping the shape.
  #
  # The first unusable value among the fragments, as its contributor's site, its position inside
  # that fragment and its ground, or null.
  hazardSite =
    es:
    foldl' (
      found: e:
      if found != null then
        found
      else
        let
          h = siteIn "" e.value;
        in
        if h == null then null else h // { from = e.site; }
    ) null es;

  # Where a hazard sits, as a caller reads it: the contributor first, then the place inside it.
  fromSite = h: "the fragment from ${h.from}${if h.w == "" then "" else ", at ${h.w}"}";

  # The first fragment that is not an attribute set, or null. Kept as its site rather than as the
  # value, because the value is the thing that cannot be rendered.
  nonAttrsSite =
    es:
    let
      bad = filter (e: !isAttrs e.value) es;
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
  # The signature belongs to the VOCABULARY and not to its members: a fold that quietly accepted what
  # the others refuse would make the one contract a caller is given untrue at the member they
  # happened to pick. The check names the fold, so the caller learns which one.
  keyDefect = key: if isString key then null else "`key` is a ${typeOf key} rather than a string";

  # ── A FRAGMENT IS A CONTRIBUTOR EDGE, AND ITS SITE IS DECIDED AT THE SAME DOOR AS THE KEY ──
  # Every refusal names the contributor a fragment came from, so `site` is interpolated exactly as
  # `key` is, and decided where the key is, for the key's reason. The site is the identity of the
  # node that contributed the value, rendered by the caller that holds the edge; this file renders
  # it and never mints one.
  edgeDefect =
    es:
    if !isList es then
      "the fragments are a ${typeOf es} rather than a list of { site; value; } records"
    # The admitted case is one predicate pass; the position is searched for only on refusal.
    else if all (e: isAttrs e && e ? value && isString (e.site or null)) es then
      null
    else
      foldl' (
        found: e:
        if found != null then
          found
        else if !(isAttrs e.e) || !(e.e ? value) || !(e.e ? site) then
          "the fragment at fragment-list position [${toString e.i}] is not a { site; value; } record"
        else if !(isString e.e.site) then
          "the fragment at fragment-list position [${toString e.i}] has a `site` that is a ${typeOf e.e.site} rather than a string"
        else
          null
      ) null (imap0 (i: e: { inherit i e; }) es);

  # Named for the fold, because a message that names only the vocabulary tells a caller with five
  # folds in a spec nothing about which call to fix.
  refuseKey =
    fold: defect:
    throw "gen-scope.folds.${fold}: ${defect} — every refusal this fold can raise names the key, so a key that cannot be rendered ends the evaluation in place of the refusal that was owed";

  # The door every fold opens with: the key, then the fragments' records, then the body.
  admit =
    fold: key: es: body:
    let
      kd = keyDefect key;
      ed = edgeDefect es;
    in
    if kd != null then
      refuseKey fold kd
    else if ed != null then
      throw "gen-scope.folds.${fold}: key '${key}': ${ed}"
    else
      body;

  values = map (e: e.value);
  sitesOf = es: concatStringsSep ", " (map (e: e.site) es);
  # Rendered for a conflict: the contributor beside its value, and nothing else a caller attached.
  rendered = es: toJSON (map (e: { inherit (e) site value; }) es);

  # ── `same`: ALL FRAGMENTS AGREE, AND THEY MUST BE COMPARABLE FOR THAT TO BE A QUESTION ──
  # Duplicate contributions that must agree are provisioned once. Returns the first fragment's value,
  # which is the whole content of "they agree".
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
    key: es:
    admit "same" key es (
      if es == [ ] then
        throw "gen-scope.folds.same: empty fragment list for key '${key}'"
      else
        agree "same" (h: "key '${key}' has ${fromSite h} carrying ${h.what}") key es
    );

  # `agree fold position key es` — `same`'s precondition and comparison, under the name of the fold
  # that invoked it and with that fold's wording of WHERE the value sits (`position hazard`). One
  # construction, so the deep merge's leaves are compared exactly as `same` compares, and refused
  # in the deep merge's own name. `es` is non-empty.
  agree =
    fold: position: key: es:
    let
      h = hazardSite es;
      first = (head es).value;
    in
    if h != null then
      throw "gen-scope.folds.${fold}: ${position h} — ${h.because}"
    else if all (e: e.value == first) es then
      first
    else
      throw "gen-scope.folds.${fold}: conflicting values for key '${key}': ${rendered es}";

  # Exactly one contributor; a second is a loud error, naming every contributor. The default
  # combine of a wiring splice, where two authors of one key have no merge rule between them.
  one =
    key: es:
    admit "one" key es (
      if length es == 1 then
        (head es).value
      else
        throw "gen-scope.folds.one: key '${key}' has ${toString (length es)} contributors, expected exactly 1${
          if es == [ ] then "" else ": from ${sitesOf es}"
        }"
    );

  # Collect the fragments' values in pinned order (`key: [edge]: [v]`). The identity of this
  # vocabulary: it imposes nothing, which is what makes it the fold to reach for when the aggregate
  # IS the list. It still decides its key and its edges, for the reason given where that check is
  # written: the signature is the vocabulary's, and a member that admits what the others refuse
  # makes it untrue.
  list = key: es: admit "list" key es (values es);

  # ── `set`: FIRST-OCCURRENCE DEDUP UNDER `==`, AND THE DEDUP IS A QUOTIENT (`key: [edge]: [v]`) ──
  # The declared dedup the ORDER AND ARITY rule above leaves to a fold that says so: the result is
  # the sub-list of the fragments' values holding each `==` class once, at its first occurrence, in pinned order. It
  # is idempotent over values (re-siting `set k es`'s result and appending `es` folds to the same list), and a singleton is returned as it is,
  # once the key and the scan have admitted it.
  #
  # Dedup is an `==` decision, so `same`'s precondition is this fold's too, with the same function
  # ground. A path takes the plain-data ground instead: this fold never reports a conflict, so the
  # reporting hazard `same` cites is not its reason.
  #
  # ★ A COLLAPSE IS A QUOTIENT (den-hoag-kunjm): `==` is blind to string context, so the kept
  # element carries its twins' store-context edges through gen-prelude's `absorb`, and a non-string
  # collapse that would lose one is refused by name. The scan above has walked every element, which
  # is the precondition `absorb`'s edge walk owes its totality to.
  #
  # COST. String twins are found through the text-keyed table (`groupBy` over the context-free
  # text, `combines.setUnion`'s construction), linear in the fragments but for the first-occurrence sort.
  # Non-strings have no total key, so each is compared against the representatives found so far
  # (one pass, appending only at a new class), and each twin then finds its representative's index
  # by a scan, grouped in ONE `groupBy` by that index: O(n·u) `==` and calls for n elements in u
  # classes, the cost of `unique`'s own fold, and list cells O(u² + n). No list is copied per twin,
  # so one class of n is linear. The process plane pins the pairs case (u = n/2) on calls and list
  # cells, and the one-class case (u = 1) on list cells.
  set =
    key: es:
    admit "set" key es (
      let
        h = hazardSite es;
        vs = values es;
      in
      if h != null then
        throw "gen-scope.folds.set: key '${key}' has ${fromSite h} carrying ${h.what} — ${h.plain or h.because}"
      else if length vs < 2 then
        vs
      else
        let
          tagged = imap0 (i: v: { inherit i v; }) vs;
          byText = groupBy (t: unsafeDiscardStringContext t.v) (filter (t: isString t.v) tagged);
          # Each field forced at every step, so no field accumulates a thunk chain as long as `vs`.
          strictly = r: seq r.reps (seq r.firsts r);
          others =
            foldl'
              (
                acc: t:
                if isString t.v then
                  acc
                else if !(elem t.v acc.reps) then
                  strictly {
                    reps = acc.reps ++ [ t.v ];
                    firsts = acc.firsts ++ [ t ];
                  }
                else
                  acc
              )
              (strictly {
                reps = [ ];
                firsts = [ ];
              })
              tagged;
          # The twins, grouped in ONE pass by their representative's index: a twin is a non-string
          # that is not a first occurrence.
          firstAt = listToAttrs (map (t: nameValuePair (toString t.i) null) others.firsts);
          twinsAt = groupBy (t: toString (indexOf others.reps t.v)) (
            filter (t: !isString t.v && !(firstAt ? ${toString t.i})) tagged
          );
          kept = sort (a: b: a.i < b.i) (
            map (g: head g // { twins = map (t: t.v) (tail g); }) (attrValues byText)
            ++ imap0 (r: t: t // { twins = map (x: x.v) (twinsAt.${toString r} or [ ]); }) others.firsts
          );
        in
        map (
          t:
          absorb {
            fn = "gen-scope.folds.set";
            subject = "the fold at key '${key}'";
            at = " from ${(elemAt es t.i).site}";
          } t.v t.twins
        ) kept
    );

  # Shallow merge of attribute-set fragments; disjoint sub-keys required, because two fragments
  # writing one sub-key have no merge rule between them and picking a winner here would decide it
  # silently.
  #
  # The collision diagnostic renders ATTRIBUTE NAMES, which are strings by construction, and the
  # sites of the fragments that wrote them, found on the refusal branch only; so it is total for the
  # same reason the fragment-shape refusal above it is not free.
  mergeAttrs =
    key: es:
    admit "mergeAttrs" key es (
      let
        bad = nonAttrsSite es;
      in
      if bad != null then
        throw "gen-scope.folds.mergeAttrs: key '${key}' has a fragment from ${bad.site} that is a ${typeOf bad.value} rather than an attribute set"
      else
        foldl' (
          acc: v:
          let
            dup = filter (k: acc ? ${k}) (attrNames v);
          in
          if dup != [ ] then
            throw "gen-scope.folds.mergeAttrs: key '${key}' collision on sub-key(s) ${toJSON dup}, written by the fragments from ${
              sitesOf (filter (e: any (k: e.value ? ${k}) dup) es)
            }"
          else
            acc // v
        ) { } (values es)
    );

  # A fold CONSTRUCTOR for attribute-set-shaped fragments: each top-level fragment key `k` is folded
  # by its own named sub-fold `spec.${k}`, under the diagnostic sub-key "<key>.<k>", over the
  # contributor edges that define `k`, each keeping its site, so a sub-fold's refusal names the same
  # contributors. Fragments not defining `k` are skipped and pinned order is preserved among those
  # that do. A fragment key the spec does not declare is a loud error — an undeclared key has no
  # merge rule, and admitting it would mean picking one.
  #
  # ONE declared level of nesting, which is the stock answer to "a shared resource with a per-
  # claimant sub-entry". Deeper nesting is another `byKey` in the spec, written by the caller who
  # knows the shape; where the key set is data rather than a declaration, it is `mergeAttrsDeep`.
  byKey =
    spec: key: es:
    admit "byKey" key es (
      let
        bad = nonAttrsSite es;
        allKeys = unique (concatMap (e: attrNames e.value) es);
        foldKey =
          k:
          let
            contributors = filter (e: e.value ? ${k}) es;
          in
          if !(spec ? ${k}) then
            throw "gen-scope.folds.byKey: key '${key}': fragment key '${k}' not declared in the fold spec, written by the fragments from ${sitesOf contributors}"
          else
            spec.${k} "${key}.${k}" (
              map (e: {
                inherit (e) site;
                value = e.value.${k};
              }) contributors
            );
      in
      if bad != null then
        throw "gen-scope.folds.byKey: key '${key}' has a fragment from ${bad.site} that is a ${typeOf bad.value} rather than an attribute set"
      else
        listToAttrs (map (k: nameValuePair k (foldKey k)) allKeys)
    );

  # ── `mergeAttrsDeep`: THE JOIN OF COMPATIBLE PARTIAL MAPS (`key: [ { site; value = attrs; } ]: attrs`) ──
  # Every fragment is a partial map from attribute paths to leaves, and the result is their union,
  # defined exactly where no two fragments disagree at a leaf. A NODE is an attribute set that is
  # neither compared by path (the derivation predicate above) nor `_type`-tagged: `_type` is the
  # module system's tag for an opaque value, dispatched on before any attribute merge and never
  # merged field by field, so a tagged set is a LEAF (den-hoag-izo7a OQ-2).
  #
  # Per key, in one pass per level (`zipAttrsWith`, which hands each key its contributors in pinned
  # order, linear in total keys):
  #   one contributor   ⇒ returned as it is, UNFORCED: nothing is compared, so neither reader
  #                       `same`'s precondition protects runs, and a whole system under
  #                       `nixosConfigurations.<h>` is never walked;
  #   all nodes         ⇒ the join one level down, at the diagnostic key `<key>.<k>`;
  #   all leaves        ⇒ `same`'s comparison in this fold's name, and the kept leaf absorbs its
  #                       twins' store-context edges (the quotient rule, as at `set`);
  #   a node and a leaf ⇒ refused by name: a namespace and a value have no merge rule between them.
  #
  # LAWS: associative under any bracketing, and commutative UP TO `==`. Which twin is kept depends
  # on order, and two twins can differ where `==` does not look (two derivations with one `outPath`
  # and different `meta`): reversing the fragments then keeps the other one. The absorbed context
  # does not depend on order. A conflict is symmetric, so a refusal does not either.
  #
  # SITES. The one `zipAttrsWith` pass runs over the values; the contributors at attribute path `p`
  # are the edges whose value reaches `p` (`sitesAt`), in the order of the values zipped there, and
  # they are recovered on a refusal branch only, so the success path never reads a site.
  #
  # Not `byKey` with a self-referential spec (it refuses undeclared keys, and fleet keys are data)
  # and not a `foldl'` over `//`, which copies the accumulator once per fragment and is quadratic in
  # the fleet. Not last-wins either: picking a winner silently is what `mergeAttrs` refuses.
  isNode = v: isAttrs v && !comparedByPath v && !(v ? _type);

  # `joinAt key p xs es` — `xs` are the values at attribute path `p`, in the order of the fragments
  # of `es` that reach `p`; the sites are recovered from `es` on a refusal branch only.
  sitesAt = p: es: filter (e: hasPath p e.value) es;

  joinAt =
    key: p: es: vs:
    zipAttrsWith (
      k: xs:
      let
        at = "${key}.${k}";
        q = p ++ [ k ];
        positionOf = pr: head (filter (i: pr (elemAt xs i)) (genList (i: i) (length xs)));
        siteAt = i: (elemAt (sitesAt q es) i).site;
      in
      if length xs == 1 then
        head xs
      else if all isNode xs then
        joinAt at q es xs
      else if any isNode xs then
        throw "gen-scope.folds.mergeAttrsDeep: the contributors at key '${at}' hold an attribute set from ${siteAt (positionOf isNode)} beside a leaf from ${
          siteAt (positionOf (x: !isNode x))
        }; a namespace and a value have no merge rule between them"
      else
        let
          kept =
            agree "mergeAttrsDeep"
              (
                h:
                "the value from ${h.from}${
                  if h.w == "" then "" else ", at ${h.w}"
                }, among the contributors at key '${at}', carries ${h.what}"
              )
              at
              (
                imap0 (i: x: {
                  site = siteAt i;
                  value = x;
                }) xs
              );
        in
        seq kept (
          absorb {
            fn = "gen-scope.folds.mergeAttrsDeep";
            subject = "the leaf at key '${at}'";
            at = " contributed from ${sitesOf (sitesAt q es)}";
          } kept (tail xs)
        )
    ) vs;

  mergeAttrsDeep =
    key: es:
    admit "mergeAttrsDeep" key es (
      let
        bad = nonAttrsSite es;
      in
      if bad != null then
        throw "gen-scope.folds.mergeAttrsDeep: key '${key}' has a fragment from ${bad.site} that is a ${typeOf bad.value} rather than an attribute set"
      else
        joinAt key [ ] es (values es)
    );

  # ── `typed`: A CHECKER OVER EVERY FRAGMENT, BEFORE THE FOLD, NAMING THE CONTRIBUTOR ──
  # `typed checker fold` is a fold of this vocabulary. `checker` is anything carrying
  # `verify : value -> null | string` (gen-types' checker contract, read by shape: gen-scope takes no
  # gen-types input). Each fragment's value is verified in pinned order; the first that fails is
  # refused as `key '<key>': fragment from <site>: <reason>`, and `fold` is handed the same edges
  # only when every fragment passed, so its own refusals name sites too.
  checkerDefect =
    c:
    if !(isAttrs c) then
      "the checker is a ${typeOf c} rather than an attribute set carrying `verify`"
    else if !(c ? verify) || !(callable c.verify) then
      "the checker carries no applicable `verify`"
    else
      null;

  typed =
    checker: fold:
    let
      cd = checkerDefect checker;
    in
    if cd != null then
      throw "gen-scope.folds.typed: ${cd}"
    else if !(callable fold) then
      throw "gen-scope.folds.typed: the fold is ${prelude.applicableKindOf fold} rather than an applicable fold"
    else
      key: es:
      admit "typed" key es (
        let
          bad = foldl' (
            found: e:
            if found != null then
              found
            else
              let
                r = checker.verify e.value;
              in
              if r == null then
                null
              else if isString r then
                {
                  inherit (e) site;
                  reason = r;
                }
              else
                throw "gen-scope.folds.typed: key '${key}': the checker's `verify` returned a ${typeOf r} rather than null or a string, for the fragment from ${e.site}"
          ) null es;
        in
        if bad != null then
          throw "gen-scope.folds.typed: key '${key}': fragment from ${bad.site}: ${bad.reason}"
        else
          fold key es
      );
in
{
  folds = {
    inherit
      same
      one
      list
      set
      mergeAttrs
      mergeAttrsDeep
      byKey
      typed
      ;
  };
}
