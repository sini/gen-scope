# THE MINTING ENTRY — one staged run over the passes the emitters declared, resolving relatum
# IDENTIFIERS against a frozen set of identities that only strictly earlier passes could have put
# there.
#
# It takes a fixed emitter list and the schema stratum's already-evaluated output, and it returns the
# scope graph those emitters describe: a node map keyed by identifier, one labelled edge per relatum,
# the number of strata the run walked, and the driver's leftover partition carried through. It takes
# neither the identity authority nor a frozen set from its caller — the first is injected by
# `lib/default.nix` and the second is built here.
#
# THEORY — WHY A PASS IS A STRATUM AND WHY THE SET IS FROZEN. Apt, Blair & Walker (1988), "Towards a
# Theory of Declarative Knowledge", in Minker (ed.), pp. 89-148, build the standard model of a
# stratified program one stratum at a time, each reaching its own fixed point before the next begins
# (printed p. 108). A minting pass is that stratum: when pass N runs, every earlier pass has finished
# and the identities it settled are closed. ADR-0016 ruling 7 is the consequence a reader feels — a
# cycle among minted nodes is INEXPRESSIBLE, because writing one would require a pass to see its own
# output, and a pass resolves only against what strictly earlier passes settled.
#
# ── THE THREE VOCABULARIES, KEPT APART ──
# ADR-0016 ruling 5 separates them and this file never merges them:
#
#   IDENTIFIER  a string, the scope graph's own vertex name. It keys the node map, it is what an edge
#               endpoint names, and it is what an emitter writes when it names a relatum. The root
#               has one and has no identity, which is why naming the root as a relatum does not
#               resolve.
#   IDENTITY    the authority's output, `"<kind>:" + digest`. Minted once per identifier, by
#               `hashIdentity` and by nothing here — ruling 5's ONE minting authority is a fact of
#               the dataflow rather than a convention, because this module has no second derivation
#               and no library of its own to reach for.
#   LABEL       a relatum's role in the relation. ADR-0016 ruling 4 makes the label set key the
#               identity; ADR-0024 as amended makes the same string the token an incident edge
#               carries. One vocabulary, so choosing a label is choosing a traversal token.
#
# ★★ THE IDENTITY KEY SET IS THE RELATUM LABELS PLUS THE NODE'S OWN IDENTIFIER, AND THE SECOND HALF
# IS FORCED RATHER THAN CHOSEN. Ruling 4 gives the binding case whole — "a kind whose identity keys
# are its relatum labels and whose values are the relata's identities" — and the authority refuses a
# preimage with NO keys by name ("identity: zero identity keys"), on the ground that a binding
# relates at least one relatum. **But not every vertex of a scope graph is a binding.** An entity
# emitter with no relata is admissible, is what most of a real emitter set consists of, and under the
# relatum-labels-only reading it has no identity to mint at all — while a relatum-free node that
# other emitters name as a relatum must have one to resolve to. So some key is owed. The readings
# this file weighed are refused with their reasons, so neither is re-proposed:
#
#   · KEY THE CONTENT. Refused because it is the one thing the staged construction forbids: a later
#     pass CONTRIBUTES content to an already-minted identity, so an identity that moved when content
#     arrived would re-mint on every contribution. Identity is content-independent, which is exactly
#     what lets two emitters of one relation reach ONE node.
#   · KEY THE KIND ALONE. Total, and refused on ADR-0016's own ground for the zero-relatum binding:
#     it "would collapse every zero-relatum binding of a kind onto sha256(<kind>) — one node,
#     silently". Two distinct declared hosts would share an identity and a relation minted over
#     either would mint the same one, which makes the identifier→identity map many-to-one and takes
#     the information out of resolution — the map's whole job.
#
# ⇒ the node's own identifier joins the key set under the reserved label below. The one property
# ruling 4 states about VALUES is untouched: every relatum's value here is the relatum's resolved
# IDENTITY and never its identifier, because hashing a relatum's declared name would make one node's
# identity a function of another's spelling. The reserved label is a declared-data key beside relatum
# keys, which is the shape the ecosystem's entity minters already ship. A relatum whose label IS the
# reserved one collides, and the authority refuses that by name as a duplicate identity key.
#
# ── ONE REFUSAL FOR RESOLUTION, ONE FOR MERGE, AND THEY ARE DIFFERENT IN KIND ──
# An identifier that does not resolve is refused at MINT time and names the relatum, the label, the
# kind being minted and the emitting pass. Three failures reach it — a same-pass relatum (the node is
# not in the set, because the set holds strictly earlier passes only), the root (an identifier with
# no identity), and a name with no entry — and they differ only in why the lookup missed.
# Contributions that disagree are refused at MERGE time, after minting has already succeeded, exactly
# as a module system refuses two conflicting definitions of one option; that message names the
# identity, the key and both emitters' sites. Both are `throw`, so both are catchable: a refusal a
# caller cannot catch is a refusal no test can assert on.
#
# ★ THE MINT IS A CONTRIBUTION LIKE ANY OTHER, AND THAT IS WHAT MAKES THE MERGE ONE RULE. Within a
# pass there is no order (ADR-0022), so the only outcomes an unordered fold may have are agreement
# and refusal — anything else would make the result depend on the order emitters were presented in.
# Each emitter naming an identifier contributes an identity and a set of content keys, and both are
# merged by the same rule: identical collapses, conflicting refuses. Because the identity is a total
# function of the kind, the identifier and the resolved relata, agreement on the identity IS
# agreement on the kind and the relata, so no separate check for either exists to drift.
#
# ★★ THE CROSS-PASS ARM OF THAT RULE IS PROPOSED RATHER THAN SETTLED, AND A READER MUST NOT TAKE IT
# FOR RULED LAW. A later pass naming an already-frozen identifier contributes content and never
# yields a second node — that half is settled, and where the contribution AGREES or adds a key the
# behaviour is indistinguishable from same-pass agreement and is uncontested. What is NOT settled is
# the case where a later pass DISAGREES on a key an earlier pass had already settled. ADR-0016's
# Consequences say so in its own words: two emitters of one identity yield "one node with
# contributions from both", and "how those contributions compose is not settled here — that is the
# substrate's general content rule". The same passage leaves the mechanism available rather than
# closed: what it forecloses is refusal at MINTING, and "it does not foreclose refusal at content
# merge, which remains available exactly as nixpkgs refuses two conflicting definitions of one
# option."
#
# ⇒ THIS FILE REFUSES THERE, AS A PROPOSAL PENDING THE SUBSTRATE'S GENERAL CONTENT RULE. The argument
# for it, offered rather than asserted: the freeze is over membership and the map's values may be
# revisited, but a stratum's output is closed when the next begins and the standard model only ever
# grows, so a later pass ADDING a key is revision while a later pass REPLACING one is retraction —
# and retraction is the thing stratification exists to keep out of a fold. The argument against it is
# equally available and is why this is not stated as law: pass order IS the contribution order, so a
# later contribution is an ordered one, and the module-system analogy the ADR reaches for admits a
# later definition winning. Nothing here decides between them. Whoever rules the general content rule
# rules this line, and if the ruling goes the other way the change is the merge's disagreement branch
# and nothing else — no other construction in this file reads it.
#
# ── WHO OWNS THE WALK AND WHO OWNS THE SET ──
# The driver walks the schedule; the frozen set is accumulated here. That split is not a preference:
# the per-stratum record the driver hands an instance is `{ stratum, items }` and gains no third
# field, because a user-visible "is X minted yet?" during a pass would make the answer depend on
# evaluation order inside the pass — the very thing the unordered within-pass merge is built to
# avoid. The driver's own text says it hands out no frozen set. So the accumulation is a fold here,
# over the same schedule, under the same per-round forcing the driver uses, and `advance` hands the
# driver the stratum it asks for.
#
# ── ITERATIVE ENCODING, AND TOTAL FORCING AT TWO DEPTHS ──
# Both loops are folds. A walk written as a self-applying lambda costs one evaluator frame per
# iteration — Nix does not reuse the frame of a call in tail position — so its descent depth is its
# iteration count and past the call-depth guard it ends the evaluation, which `tryEval` does not
# contain. The per-round forcing is `forceFields`, taken from where it is defined rather than written
# again, and it is derived from the accumulator's own fields so a field added later is forced without
# anyone re-applying the discipline.
#
# ★ THAT DISCIPLINE REACHES FIELDS AND STOPS, WHICH IS NOT DEEP ENOUGH FOR A REFUSAL. Forcing a list
# field to weak head normal form forces the spine and not the elements, so a refusal written as an
# ELEMENT of a stratum's output would survive the whole run and fire only if some consumer happened
# to force that element — which may be never. Refusals here are properties of the CALL and not of a
# consumer's reading pattern, so a stratum's output is forced through in the round that produced it,
# and the whole result is forced before it is returned. A caller reading one field therefore gets the
# same answer as a caller reading all of them.
#
# ── NO BOUND ON SIZE APPEARS ANYWHERE ──
# The run walks one stratum per declared pass. The schedule is what the emitters declared, `strata`
# is reported and compared against nothing, and no number here refuses a program for being large.
# The frozen set is an attribute set rather than a list of records because resolution is a membership
# test plus a lookup once per relatum per mint, and over a list that is a scan inside the pass loop —
# which turns a per-mint constant into a cost quadratic in the node count. That is a cost argument
# and deliberately not a refusal: no size of frozen set is inadmissible.
#
# ★ AND ONE COST TERM SURVIVES THAT CHOICE RATHER THAN BEING REMOVED BY IT, SO IT IS NAMED HERE
# INSTEAD OF LEFT FOR A READER TO FIND. The accumulation extends the frozen set once per stratum, and
# an attribute-set update copies both operands, so the run carries a residual term on the order of
# the schedule length times the size of the accumulated set. The dimension that could make that
# quadratic is the SCHEDULE LENGTH, and it is bounded by the program rather than by the input: the
# schedule is the DISTINCT DECLARED PASS INDICES, an author-written set that a large emitter list
# does not enlarge so long as emitters share pass indices — which is what a pass is for, a staging
# device rather than a per-node attribute. An emitter set declaring one distinct pass per emitter
# makes the two dimensions equal (measured at the W3 gate: 500 emitters at 500 declared passes ⇒ 500
# strata), and nothing here refuses it. The per-emitter work is separately linear, because the
# placement is indexed once rather than re-scanned per stratum (below). No number bounds either
# dimension and nothing is refused for being large — this is the shape stated, not a threshold.
#
# ★ `graph` REACHES THIS FILE AND STOPS, AND THE ABSENCE IS THE POINT RATHER THAN AN OMISSION. No
# line below applies it. What this entry publishes is the graph's CONTENT — vertices under their own
# names and the labelled incidence between them — as plain data, and the library bound as `graph`
# answers reachability and partition questions about a graph that has already been built. Consuming
# it here would mean this entry deciding those questions during minting, which is a different phase's
# work; the formal is in the signature because the signature is the specified surface, and its
# emptiness is what says the minting run asks the graph nothing.
{
  prelude,
  graph,
  hashIdentity,
  stratify,
}:
let
  inherit (prelude)
    attrNames
    concatMap
    filter
    foldl'
    groupBy
    head
    iterateBounded
    listToAttrs
    map
    mapAttrs
    nameValuePair
    sort
    tail
    unique
    ;

  # The round-loop forcing, taken from the module that defines it rather than written a second time:
  # two copies of a discipline agree only for as long as someone keeps them in step, and the entry's
  # own formals are the specified surface — there is no parameter through which this could arrive.
  inherit (import ./least-model.nix { inherit prelude; }) forceFields;

  ascending = a: b: a < b;

  # The reserved identity key carrying the node's own identifier, named once so the collision a
  # relatum sharing the name would produce has a single site to read.
  identifierKey = "identifier";

  # The reserved merge key naming the mint itself. It is not a content key: contents are merged in
  # their own map, so an emitter whose content carries this name is merging a content key and not
  # colliding with anything.
  mintKey = "identity";

  # ── THE TWO REFUSAL TEXTS ──
  # Each names the coordinates that let a reader find the construction rather than the symptom: the
  # first the relatum, its label, the kind being minted and the emitting pass; the second the
  # identity, the disagreeing key and both emitters' declared sites.
  unresolvedRelatum =
    identifier: label: kind: pass:
    "gen-scope.mintStrata: unresolved relatum '${identifier}' (label '${label}', minting kind '${kind}', pass ${toString pass})";

  # The two sites are ordered by their own text rather than by the order the emitters arrived in.
  # Within a pass there is no order, so a message that named them in arrival order would move under a
  # permutation of the emitter list and the refusal would stop being a property of the program.
  conflictingContribution =
    identity: key: siteA: siteB:
    let
      first = if siteA < siteB then siteA else siteB;
      second = if siteA < siteB then siteB else siteA;
    in
    "gen-scope.mintStrata: conflicting contributions to identity '${identity}' at key '${key}' (${first}, ${second})";
in
{
  mintStrata =
    { emitters, kinds }:
    let
      # ── THE SCHEDULE: THE DISTINCT DECLARED PASSES, ASCENDING ──
      # Not a range over the declared maximum and not a topological sort. Ascending, because pass N's
      # predecessors are passes 0 … N-1. Deduplicated, because the driver walks each member once and
      # a member appearing twice would re-select and re-settle the same items. Derived from the
      # declaration rather than enumerated, so a program declaring passes 0 and 1000000 runs two
      # strata instead of a million empty ones — which removes the cost without introducing a number
      # anywhere.
      schedule = sort ascending (unique (map (e: e.pass) emitters));

      # An emitter declares its own pass; the placement never reads its position in the list.
      stratumOf = e: e.pass;

      # A total order inside one stratum, on the emitter's OWN declared strings. Within a pass the
      # merge is unordered by construction, so this decides nothing about meaning — it decides only
      # that the settled sequence is a function of the program rather than of the order a caller
      # happened to write it in.
      within =
        a: b: if a.identifier != b.identifier then a.identifier < b.identifier else a.site < b.site;

      # The driver requires a way to name an item and requires it to be total. The site description
      # is that name, and it is the same string a conflicting-contribution refusal reports.
      describe = e: e.site;

      # The placement is computed ONCE over the emitter list rather than re-scanning it at each
      # stratum: a scan per stratum turns a per-emitter constant into a cost that is the emitter
      # count times the schedule length, and the engine's bar is thousands of nodes. This is a cost
      # argument and not a refusal — no schedule is inadmissible for being long.
      byPass = groupBy (e: toString e.pass) emitters;
      itemsAt = stratum: sort within (byPass.${toString stratum} or [ ]);

      # ── ONE EMITTER'S MINT ──
      # `frozen` holds what strictly earlier strata settled. Every relatum is looked up in it and an
      # identifier with no entry is refused by name; a same-pass relatum misses for the same reason a
      # nonexistent one does, which is what makes a cycle unwritable rather than detected.
      mintOne =
        frozen: e:
        let
          valueOf =
            label:
            if label == identifierKey then
              e.identifier
            else
              let
                relatum = e.relata.${label};
              in
              frozen.${relatum} or (throw (unresolvedRelatum relatum label e.kind e.pass));
        in
        {
          inherit (e)
            identifier
            kind
            relata
            content
            site
            ;
          identity = hashIdentity e.kind ([ identifierKey ] ++ attrNames e.relata) valueOf;
        };

      # ── THE ACCUMULATION ──
      # One round per scheduled stratum. Each round mints its stratum against everything strictly
      # earlier has settled and adds what it settled to the set the next round will see, which is
      # the stratum-by-stratum construction the theory names.
      accumulate =
        acc:
        let
          stratum = head acc.pending;
          settled = map (mintOne acc.frozen) (itemsAt stratum);
        in
        {
          pending = tail acc.pending;
          frozen = acc.frozen // listToAttrs (map (r: nameValuePair r.identifier r.identity) settled);
          byStratum = acc.byStratum // {
            ${toString stratum} = settled;
          };
        };

      accumulated = iterateBounded forceFields accumulate {
        pending = schedule;
        frozen = { };
        byStratum = { };
      } schedule;

      # ── THE DRIVER'S PER-STRATUM STEP ──
      # `emitted` is empty at every stratum and that is structural rather than incidental: a stratum
      # does not produce emitters. What varies per stratum is what each emitter mints, which is a
      # function of the frozen set; WHICH emitters exist is fixed before the first stratum runs. If a
      # stratum could emit an emitter carrying a fresh declared pass, the schedule computed at the
      # start would be incomplete and the run's boundedness would be delivering silence.
      #
      # ★ `items` IS DECLARED AND NOT READ, AND THE REASON IS SHARING RATHER THAN OVERSIGHT. Nothing
      # is emitted, so the pool the driver selects from is the seed at every round and its selection
      # is this instance's own `itemsAt` applied to the same fixed list — the two agree by
      # construction. The mint for a stratum has to exist BEFORE the driver asks for it, because the
      # next stratum's frozen set is built from it; re-deriving it from `items` here would compute
      # every mint a second time. The formal stays because the record's shape is the driver's.
      #
      # ★ AND THE STRATUM'S OUTPUT IS FORCED THROUGH HERE. The driver's per-round discipline reaches
      # the accumulator's fields, which for a list is the spine, so a refusal living inside an
      # element would survive the run. Forcing it in the round that produced it is what puts the
      # refusal at the pass that caused it.
      advance =
        { stratum, items }:
        {
          emitted = [ ];
          settled =
            let
              produced = accumulated.byStratum.${toString stratum};
            in
            builtins.deepSeq produced produced;
        };

      run = stratify {
        inherit
          schedule
          stratumOf
          within
          advance
          describe
          ;
        seed = emitters;
      };

      # ── THE MERGE ──
      # Every contribution to one identifier, in schedule order with the within-stratum order inside
      # it. The identity is checked first because it is the mint: contributions that disagree about
      # WHICH node they are describing have not reached the question of what its content is.
      mergeGroup =
        records:
        let
          first = head records;
          disagreeing = filter (r: r.identity != first.identity) records;

          contributed =
            foldl'
              (
                acc: r:
                foldl' (
                  a: key:
                  let
                    next =
                      if a.content ? ${key} then
                        (
                          if a.content.${key} == r.content.${key} then
                            a
                          else
                            throw (conflictingContribution first.identity key a.sites.${key} r.site)
                        )
                      else
                        {
                          content = a.content // {
                            ${key} = r.content.${key};
                          };
                          sites = a.sites // {
                            ${key} = r.site;
                          };
                        };
                  in
                  builtins.seq (forceFields next) next
                ) acc (attrNames r.content)
              )
              {
                content = { };
                sites = { };
              }
              records;
        in
        if disagreeing != [ ] then
          throw (conflictingContribution first.identity mintKey first.site (head disagreeing).site)
        else
          {
            inherit (first)
              identity
              kind
              relata
              ;
            inherit (contributed) content;
          };

      merged = mapAttrs (_: mergeGroup) (groupBy (r: r.identifier) run.settled);

      # One node plus one edge per relatum, each edge carrying the label that keyed the identity.
      # Emitted in the node map's own key order with each node's labels in theirs, so the sequence is
      # a function of the program rather than of the order the strata happened to settle in.
      result = {
        nodes = mapAttrs (_: node: {
          inherit (node)
            identity
            kind
            content
            ;
        }) merged;

        edges = concatMap (
          identifier:
          map (label: {
            from = identifier;
            to = merged.${identifier}.relata.${label};
            inherit label;
          }) (attrNames merged.${identifier}.relata)
        ) (attrNames merged);

        # The driver's own two, carried rather than re-derived. `unrun` is the list the driver
        # returned — not filtered, not re-typed, not replaced by a constant. On every run it is empty
        # by theorem, because the schedule is derived FROM the declared passes and no emitter's pass
        # can fall outside it; it is carried because the driver's result carries it, and it is a fact
        # a caller may read rather than a channel anything here depends on.
        inherit (run) strata unrun;
      };
    in
    # The schema stratum is forced and never read, and the forcing establishes LESS than a reader
    # might take from it, so its reach is stated. `seq` forces to weak head normal form, which
    # establishes that `kinds` is a VALUE this call received rather than a fixpoint it participates
    # in — the property the argument boundary exists for. It does NOT establish that every option
    # inside it evaluated: measured on this construction, a throw AS the kinds value fires while a
    # throw as one option inside it passes. That gap is not closed here, because what is owed is
    # dataflow and not a check: the entry is outside the fixpoint that produces kind options and
    # holds no handle with which to re-open one, so contributing an option after minting has begun is
    # not a refused contribution but an expression with nowhere to attach. Deepening the forcing
    # would buy a different property — that the caller's options are total — which is the caller's
    # own and is not what the argument boundary is for.
    builtins.seq kinds (builtins.deepSeq result result);
}
