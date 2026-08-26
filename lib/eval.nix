# HOAG evaluator: demand-driven with co-located _eval memoization.
#
# Nix's native lazy evaluation provides scheduling, memoization, and cycle
# detection (Mokhov et al., 2018). Every attribute evaluates exactly once per
# node — including on dynamically synthesized nodes (Vogt et al., 1989).
#
# The key insight: Nix attrset VALUES are lazy but KEYS are eager. The only way
# to get O(1) attribute access is an attrset entry. We co-locate the memoization
# cache (_eval) ON each node when it is materialized by its parent's `children`
# or `derived-children` attribute.
{
  prelude,
  requireScope,
  graph,
}:
let
  structural = import ./structural.nix { inherit prelude; };
  interface = import ./interface.nix { inherit prelude; };

  # The applicability approximation, taken from the one binding (`lib/callable.nix`): the circular
  # carrier decides it of a `leq` exactly as the kind registry decides it of a `resolve`.
  callable = import ./callable.nix;

  # The round loop's forcing discipline, taken from where it is defined rather than written a
  # seventh time (the same import `lib/mint.nix` takes): the shared round is `forceFields`'
  # sixth consumer, not the second implementation.
  inherit (import ./least-model.nix { inherit prelude; }) forceFields;

  # ── THE CIRCULAR DECLARATION, READ AT THE DEMAND PATH ──
  #
  # A circular attribute arrives as the kind-tagged record `circular` returns — { kind; carrier;
  # step } — and the classification over `attributes` values is TOTAL: a function is an ordinary
  # attribute, a record carrying kind = "circular" is a circular declaration, and anything else is
  # a malformed declaration refused by name. The evaluator therefore needs no registry of which
  # names are circular; the declaration announces its kind, and reading the attribute set answers
  # "which attributes are circular" without forcing any value.
  isCircularDecl = v: builtins.isAttrs v && (v.kind or null) == "circular";

  # The reason a carrier is not one, or null. Total on any value: each arm establishes what the
  # next one reads. The reason NEVER RENDERS the carrier — an order is a function, and rendering a
  # function is itself an abort no caller can catch, which would answer an uncatchable termination
  # with another one while claiming to diagnose it. The refusal fires at the declaration's FIRST
  # DEMAND, `tryEval`-catchably; at universe formation a defective declaration is simply not
  # admitted, because forcing carrier fields there would abort anonymously before this name could
  # be raised.
  #
  # The fourth term, `quotient`, is REQUIRED and TOTAL: it decides whether the instance may be a
  # simultaneous member of a shared round, and an absent declaration would decide that soundness
  # question silently. The field set is CAPPED at the four declared terms — a fifth is refused as
  # a return to the design sitting, never admitted as a refinement.
  carrierDefect =
    c:
    if c == null then
      "declares no `carrier` — a circular attribute is well defined only over one, and its three terms are a bottom, an order and a bounded height (Söderberg & Hedin 2013 §4.1)"
    else if !builtins.isAttrs c then
      "declares a `carrier` that is a ${builtins.typeOf c} rather than a { bottom, leq, height } record"
    else if !(c ? bottom) then
      "declares a `carrier` with no `bottom` (the starting point of the fixed-point iteration)"
    else if !(c ? leq) then
      "declares a `carrier` with no `leq` (the order the step is required to ascend)"
    else if !(callable c.leq) then
      "declares a `carrier` whose `leq` cannot be applied (it is a ${builtins.typeOf c.leq})"
    else if !(c ? height) then
      "declares a `carrier` with no `height` (the lattice's bounded height, from which the iteration bound is derived)"
    else if !builtins.isInt c.height then
      "declares a `carrier` whose `height` is a ${builtins.typeOf c.height} rather than an integer"
    else if c.height < 0 then
      "declares a `carrier` whose `height` is ${toString c.height}, and a lattice has no negative height"
    else if !(c ? quotient) then
      "declares a `carrier` with no `quotient` (whether `leq` orders a quotient of the value space rather than the raw values — required and total, because a shared round admits only antisymmetric carriers and an absent declaration would decide that soundness question silently)"
    else if !builtins.isBool c.quotient then
      "declares a `carrier` whose `quotient` is a ${builtins.typeOf c.quotient} rather than a boolean"
    else if
      builtins.attrNames c != [
        "bottom"
        "height"
        "leq"
        "quotient"
      ]
    then
      "declares a `carrier` carrying ${
        builtins.toJSON (
          builtins.filter (
            n:
            !(builtins.elem n [
              "bottom"
              "height"
              "leq"
              "quotient"
            ])
          ) (builtins.attrNames c)
        )
      } beyond its four declared terms { bottom, leq, height, quotient } — the carrier's field set is capped by ruling, and a fifth term is a return to the design sitting rather than a refinement"
    else
      null;

  # Universe eligibility (the membership-eligibility clause): a WELL-FORMED four-term carrier AND
  # quotient = false. Read without throwing — an instance that cannot be a member is simply not
  # admitted, and its own refusal fires at its own first demand.
  memberEligible =
    d:
    isCircularDecl d
    &&
      builtins.attrNames d == [
        "carrier"
        "kind"
        "step"
      ]
    && builtins.isAttrs (d.carrier or null)
    &&
      builtins.attrNames d.carrier == [
        "bottom"
        "height"
        "leq"
        "quotient"
      ]
    && callable d.carrier.leq
    && builtins.isInt d.carrier.height
    && d.carrier.height >= 0
    && d.carrier.quotient == false;

  # ── THE SPAWN HANDLE — a PROJECTION, never a filtered view of the evaluator ──
  #
  # A spawn builder is not handed the evaluator. It is handed this restricted accessor, through
  # which a round's in-flight value CANNOT BE NAMED by the handle's own vocabulary: the handle
  # serves ONE name, `node`, and the record it answers is RECONSTRUCTED from the node's own four
  # fields — never the evaluator's record with fields removed, which would re-acquire every field
  # a later wrapping adds (`_eval` included). A spawn declares what nodes exist; it does not
  # compute what they are worth — values are attributes, and the substrate has a place for them
  # that is not the spawn channel (ADR-0016 ruling 7's "a same-pass relatum cannot be named";
  # ADR-0033's "cycles across it are inexpressible, never detected"). What the handle does NOT
  # close is a value the consumer bound into `decls`, which it serves and delivers intact — that
  # residue is authoring law's (a computed value in a `decls` field is a modelling error), and its
  # dangerous subset re-enters the demand path and is refused there like any other read.
  spawnHandle = ev: {
    node =
      id:
      let
        n = ev.node id;
      in
      {
        id = n.id or id;
        parent = n.parent or null;
        decls = n.decls or { };
        type = n.type or null;
      };
  };

  # THE ONE CHILD-RESOLUTION BINDING. Every site that asks a node for its child records — the
  # DEMAND sites that resolve a single id, and the ENUMERATION walks that descend into all of
  # them — composes `children` with `derived-children` HERE and nowhere else. It was five inline
  # copies of the same three lines across the two evaluators, and two copies of a discipline
  # agree only for as long as someone keeps them in step. A soundness obligation over spawned
  # children is then a property of THIS binding rather than a rule five call sites must each
  # remember, which is what makes such an obligation unmissable by construction.
  #
  # `ev` is the accessor the caller resolves through — the production evaluator's `self`, or the
  # debug evaluator's fresh per-`get` self, whose trace recording is exactly why it cannot be
  # the same value.
  #
  # `requireChildrenAttribute` IS THE ONE AXIS THE FIVE COPIES DISAGREED ON, and it survives as a
  # formal rather than being normalized away because the disagreement is OBSERVABLE. Against an
  # attribute set carrying no `children` at all, a demanding site read `get`'s unknown-attribute
  # refusal while a walking site read `{ }` and completed over the roots. Collapsing to either arm
  # would move live behaviour under cover of a consolidation, so the divergence was carried as an
  # argument — visible at one site and decidable in one place — rather than settled at the
  # consolidation that surfaced it.
  #
  # ★ IT IS NOW SETTLED, AND BOTH ARMS ARE KEPT AS PRINCIPLED. They answer different questions and
  # the right answers differ. An ENUMERATION must be TOTAL over a heterogeneous node set: a walk
  # that refused at the first node lacking the attribute could not report the rest, and "no
  # children" is a perfectly ordinary thing for a node to be. A DEMAND is a question about ONE id
  # and its answer is either the record or a refusal — reading `{ }` there turns "this attribute
  # set declares no `children`" into "that node has none", which is a wrong answer wearing a right
  # shape. The split is intentional, and the formal is what says so.
  #
  # ★ STRICTNESS, DECIDED AND STATED, because the consolidation left it open. This binding returns
  # the whole child-record attrset with KEYS EAGER and VALUES LAZY, and the open question was
  # whether a soundness obligation homed here would have to read each child's `kind` — which would
  # force EVERY sibling's record at demand sites that today force one. It does not, and that is a
  # consequence of where the obligation ended up rather than a concession: descent is settled at
  # registration, and the produced kind is STAMPED (written) rather than read, so nothing on this
  # path inspects a child to decide whether it is admissible. The only record read is the HOST's,
  # for its own kind, and a host is already resolved by the time anything asks it for children.
  childRecordsOf =
    {
      attributes,
      requireChildrenAttribute,
    }:
    ev: id:
    let
      children =
        if requireChildrenAttribute || attributes ? "children" then ev.get id "children" else { };
      derived = if attributes ? ${spawnChannel} then ev.get id spawnChannel else { };
    in
    children // derived;

  # ── THE SPAWN CHANNEL ──
  # This attribute is the one that grows the NODE SET, and it is where the domain half of
  # well-definedness is bought or lost. It used to be a caller-written function returning whatever
  # records it liked, each carrying whatever `type` string its author wrote — so a spawn minted a
  # fresh kind per level as freely as it minted a fresh id, and an expansion that descended nothing
  # was indistinguishable from one that did.
  #
  # THEORY. Söderberg §7 (printed 320) states the conservative termination technique as "ordering
  # the nonterminals (the node types), so that each new NTA has a lower order than its host", and in
  # Vogt's formalism an expansion produces a symbol the GRAMMAR declares: the produced symbol is
  # never a runtime choice. Both put the expansion on the node TYPE, which is why the declaration
  # lives on the kind record and not here, and why what arrives here is already known to descend —
  # `mkKind` refuses a `spawns` key outside its own `below` set, and a registered `below` edge
  # strictly decreases the rank `graph.coneRank` publishes.
  #
  # WHAT REMAINS FOR THIS BINDING is to make the produced kind the DECLARATION'S rather than the
  # body's: the builder is written under the key naming what it produces, and the kind is stamped
  # from that key. A builder that writes its own `type` is refused by name, because that field is
  # the firing-time choice the mandate removes — the only way one could still be attempted.
  #
  # ⇒ A NON-DESCENDING OR UNDECLARED SPAWN IS INEXPRESSIBLE rather than detected. Nothing here
  # compares two ranks; the comparison happened at registration and cannot be reached from a
  # grammar. What this does is a lookup and a stamp.
  spawnChannel = "derived-children";

  # ── THE SELECTION CHANNEL ──
  # `children` names WHICH of the scope's nodes stand below this one. It does not make them. A
  # record arriving here under a key the scope does not carry is a node minted while the attribute
  # is read, and it is refused by name.
  #
  # WHY THE OTHER HALF OF THIS ATTRIBUTE CLOSED. The channel used to do two things under one name:
  # select among nodes already registered, and synthesize fresh ones. The second is GROWTH, and
  # growth is what the kind order governs — a minted child's kind was whatever its body wrote, so
  # nothing could say it descended its host's. Requiring descent HERE was the arm that could not be
  # taken: this binding receives records, not provenance, so a check placed on it would bind static
  # containment too, and a directory containing a directory is same-kind by nature and would become
  # inexpressible. So the two things are separated instead of ordered. Growth leaves through the
  # spawn channel, where the produced kind is the DECLARATION's and descent is settled at
  # registration; what stays here selects, and selection moves nothing through the kind order
  # because it introduces no node to rank. ⇒ The descent guarantee covers ALL growth by
  # construction, with no second check and no cost to same-kind containment.
  #
  # THE MEMBERSHIP AUTHORITY IS THE SCOPE'S OWN NODE SET, and it is the only one that is
  # well-founded. `buildRoots` closes that set before evaluation begins — every vertex of every
  # contribution becomes a node — so the selection shape `filterAttrs (_: n: n.parent == id) roots`
  # yields a SUBSET of it by construction and passes without an author doing anything. The spawned
  # set is deliberately NOT an authority: it is what the walk through this binding produces, so
  # asking whether an id is in it is asking the question that is being answered, and a spawned node
  # is reachable through the spawn that produces it, which is what keeps growth single-pathed.
  #
  # ⇒ IT IS A KEY TEST, AND THAT IS SUFFICIENT RATHER THAN CHEAP. Keys are eager and values lazy, so
  # this forces no child record and the strictness decided at `childRecordsOf` is untouched. What
  # makes it sufficient is that for a REGISTERED id the child record is already inert: `resolveNode`
  # and `get` both answer from `roots` before this value is consulted, so a body returning a
  # different record under a registered key changes no read. The only thing a body can contribute
  # that the scope does not already hold is a new KEY — which is exactly growth, and exactly what
  # this refuses.
  selectionChannel = "children";

  selectAmong =
    nodes: declared: ev: id:
    let
      records = declared ev id;
      unregistered = builtins.filter (childId: !(nodes ? ${childId})) (builtins.attrNames records);
    in
    if unregistered == [ ] then
      records
    else
      throw "gen-scope: node '${id}' declares child(ren) ${builtins.toJSON unregistered} that the scope does not carry. `children` SELECTS among the nodes the scope already registered — it is not a growth channel, and a record under an unregistered key is a node minted while the attribute is read, whose kind nothing can have checked descends its host's. Growth is the spawn channel's: declare it on the host's kind as `mkKind { spawns = { <produced-kind> = builder; }; }` with the produced kind named in that kind's `below`. To keep a node here, register it in the scope and select it.";

  spawnFrom =
    kinds: ev: id:
    let
      hostKind = (ev.node id).type or null;
      # A node of NO kind spawns nothing, and that is the honest reading rather than a hole: an
      # expansion descends a rank, and a node outside the kind vocabulary has no rank to descend
      # from. A node carrying a kind the registry does not know is refused by name — `buildRoots`
      # already refuses that at the door, so what this arm covers is a scope record assembled by
      # hand, which is the one route that skips the door.
      spawns =
        if hostKind == null then
          { }
        else if kinds.kinds ? ${hostKind} then
          kinds.kinds.${hostKind}.spawns
        else
          throw "gen-scope: node '${id}' carries kind '${toString hostKind}', which the supplied registry does not carry. A node's kind is a name in a registered vocabulary — register it with `mkKinds`, or build the scope through `buildRoots`, which refuses an unregistered kind at the door.";
      stamped =
        produced:
        let
          builder = spawns.${produced};
        in
        builtins.mapAttrs
          (
            childId: record:
            if record ? type then
              throw "gen-scope: kind '${hostKind}' spawns '${produced}' and its builder returned a child '${childId}' carrying its own `type`. A spawn does not choose its child's kind: the kind is the key the builder was declared under, and the substrate stamps it from there — a kind chosen while the spawn fires is one nothing can have checked descends. Drop the field."
            else if (record.parent or id) != id then
              throw "gen-scope: kind '${hostKind}' spawns '${produced}' and its builder returned a child '${childId}' whose `parent` is '${toString record.parent}' rather than its host '${id}'. A spawn descends one level of the registered kind order, so the host IS the parent: the substrate stamps the edge from the host id in the same act that stamps `type` from the declaration key, and a builder asserting a different containment is asserting an edge the registry never checked. Drop the field."
            else
              record
              // {
                type = produced;
                parent = id;
              }
          )
          (
            if isCircularDecl builder then
              throw "gen-scope: kind '${hostKind}' declares spawn '${produced}' whose builder is a circular declaration. A spawn builder computes the NODE SET, and wrapping it in `circular` makes that set a fixed point of its own iterate — the per-step growth the spawn-read restriction refuses. A spawned node's ATTRIBUTES may be circular; its EXISTENCE may not. Declare the builder as a plain function."
            else
              builder (spawnHandle ev) id
          );
    in
    prelude.foldl' (acc: produced: acc // stamped produced) { } (builtins.attrNames spawns);

  # The attribute set the evaluators actually run: the caller's, with the selection channel guarded
  # and the spawn channel the registry declares added. Writing the spawn channel by hand is refused —
  # it is the one surface on which an expansion could still be declared outside the kind order, and
  # leaving it open would make the order a convention rather than a property.
  #
  # BOTH CHANNELS ARE FIXED UP HERE, at the ONE place the two evaluators build the set they run, so
  # neither guard is a rule a call site remembers. The selection guard is unconditional on the
  # registry: a scope with no kinds still may not grow through `children`, because an unregistered
  # key is a node the scope does not carry whether or not any kind was declared.
  effectiveAttributes =
    entry: checked: attributes:
    let
      kinds = checked.kinds or null;
      selected =
        if attributes ? ${selectionChannel} then
          attributes
          // {
            ${selectionChannel} = selectAmong checked.nodes attributes.${selectionChannel};
          }
        else
          attributes;
    in
    if attributes ? ${selectionChannel} && isCircularDecl attributes.${selectionChannel} then
      throw "gen-scope.${entry}: `${selectionChannel}` is declared circular, and a child-bearing attribute cannot be. The ground is bootstrap, not growth: a shared round's universe is derived from the materialized node set, the materialization walk reads the child-bearing attributes, and a circular one there would need a round whose bound needs the walk — measured as an uncatchable infinite recursion with this refusal removed. Every other structural attribute may be circular; this one selects the node set the universe is derived from."
    else if attributes ? ${spawnChannel} then
      throw "gen-scope.${entry}: `attributes` declares `${spawnChannel}` directly. A node expansion is declared on the KIND it expands FROM — `mkKind { spawns = { <produced-kind> = builder; }; }` — so that the produced kind is a registered name below its host's own and the descent is settled before anything fires. Written as a bare attribute the produced kind is whatever the body returns, which is a choice made at firing time and one nothing can check. Move the builder onto its host kind's `spawns`."
    else if kinds == null then
      selected
    else
      selected
      // {
        ${spawnChannel} = spawnFrom kinds;
      };

  eval =
    {
      scope,
      attributes,
      parseParent ? null,
      prior ? null,
      decision ? interface.coldDecision,
      provenance ? [ ],
    }:
    let
      checked = requireScope "eval" scope;
      roots = checked.nodes;

      # WHAT THE CALLER DECLARED versus WHAT RUNS, and the two are different sets because the spawn
      # channel is the registry's rather than the caller's. Everything below reads `runAttributes`:
      # the partition, the per-node evaluator, the memo map and `get`'s own membership test all have
      # to agree about which names exist, and reading the declared set at any one of them would make
      # a spawned node reachable by one route and unknown by another.
      #
      # The registry travels ON the scope, so the vocabulary a node's kind was validated against and
      # the vocabulary its expansions are declared in are ONE value. Two formals would be two
      # declarations that agree only while someone keeps them in step, and a disagreement between
      # them is a node whose kind is registered here and absent there.
      runAttributes = effectiveAttributes "eval" checked attributes;

      # The two arms of the binding above, taken once each so the divergence the five collapsed
      # copies carried has exactly two names instead of five inline spellings.
      childRecordsStrict = childRecordsOf {
        attributes = runAttributes;
        requireChildrenAttribute = true;
      };
      childRecordsLenient = childRecordsOf {
        attributes = runAttributes;
        requireChildrenAttribute = false;
      };
    in
    let
      # ── THE ROUND-INDEXED ACCESSOR FAMILY ──
      #
      # The evaluator is a FUNCTION OF THE ROUND STATE, and `self` is one member of the family:
      # `self0` is bound once with the round closed and is what `eval` returns; one further
      # accessor exists per level of an open round (and per nested ascent), dropped when the round
      # closes. The round state is a parameter of the WHOLE evaluator rather than an argument
      # threaded at call sites — Söderberg & Hedin's IN_CIRCLE / attr_visited are a global every
      # attribute evaluation reads (Figure 5 lines 1-2), and the pure transcription of a global is
      # a parameter of the fix. Route closure is then a property of WHERE the parameter is read:
      # every value route bottoms out at one application site inside one fix, so a body handed
      # `self` cannot reach an unguarded evaluator.
      #
      # The state's fields, each with its reader:
      #   open        — the demand rule's case split, the cache lifetimes, the reuse gate
      #   members     — the shared snapshot of the previous level a member read serves (CASE 2);
      #                 at the outer seat's re-check it is the earlier level CLAMPED ENTRYWISE to
      #                 the later one
      #   qsnap       — the snapshot QUOTIENTS derive against. Normally identical to `members`;
      #                 at the outer seat's re-check it stays the later level RAW, and the two
      #                 must stay separable or the seat's neutrality argument is lost
      #   level       — which level of the open round this accessor serves
      #   provisional — the ARMING RULE: below the level the round returns, no refusal raised
      #                 inside a nested ascent fires (the ascent returns its last iterate);
      #                 refusals arm at the returning level, where the inputs are the ones the
      #                 program itself produces
      #   path        — the WALKED PATH: the circular instances whose evaluation is in progress,
      #                 outermost first, each with the declaration it was entered under. A demand
      #                 re-entering an instance on it IS the cycle, and the entries between the
      #                 two occurrences are that cycle exactly — the cycle-closure check reads the
      #                 declarations on that segment and nothing else
      #   qcur        — the in-progress iterate of each nested ascent on the path, served to a
      #                 re-entry whose segment carries no quotient declaration
      closedRound = {
        open = false;
        members = { };
        qsnap = { };
        level = 0;
        provisional = false;
        path = [ ];
        qcur = { };
      };
      mkAccessor =
        round:
        prelude.fix (
          self:
          let
            # The reuse vocabulary: this attribute set minus the structural partition. A structural
            # name is absent from it, so it contributes nothing to what may be served — there is
            # nothing for it to intersect with. The attribute set is one set for every node, so the
            # projection is node-independent here; the per-node signature is the interface's,
            # because a substrate whose attribute set varies by node must still answer per node.
            resolutionalNamesAll = structural.resolutionalNames (builtins.attrNames runAttributes);
            resolutionalAt = _nodeId: resolutionalNamesAll;
            structuralNamesAll = builtins.filter structural.structural (builtins.attrNames runAttributes);

            # served nodeId = reusable nodeId ∩ resolutional nodeId. A total function, not a check
            # that can fail.
            servedAt =
              nodeId: builtins.filter (a: builtins.elem a resolutionalNamesAll) (decision.reusable nodeId);

            servePrior =
              nodeId: attrName:
              if prior == null then
                throw "gen-scope: the decision reuses '${attrName}' on '${nodeId}' but no prior evaluation was supplied"
              else
                prior.get nodeId attrName;

            # One per-attribute evaluator, shared by rootEval + wrapChild._eval.
            #
            # THE STRUCTURAL BRANCH FIRES FIRST AND NEVER CONSULTS THE DECISION — by branch order,
            # not by a check. Structure is always recomputed, so dirty descendants stay reachable
            # and a labelled reachability relation is never read stale. That the branch tests the
            # PARTITION rather than two literal names is what extends the law from the child
            # attributes to the whole `edges-*` family, to the relations the resolver traverses, and
            # to `includes`.
            #
            # THE COST OF THAT, ON THE RECORD: edge sets are never reused, so a warm evaluation
            # pays edge-set recomputation. That is a cost fact, not a correctness fact, and it is
            # taken deliberately — an edge set IS the labelled reachability relation, and the
            # reason structure is always recomputed applies to it exactly. If the recomputation
            # proves dominant the answer is to make the structural recompute cheaper, never to
            # serve structure from a prior evaluation.
            #
            # The second branch consults the SERVED INTERSECTION, not the decision's raw list. The
            # structural branch has already fired, so the two agree at this call site — and that is
            # exactly why the intersection is written here rather than assumed: an agreement that
            # holds because of a neighbouring branch is a fact about today's branch order, and the
            # clause this implements is about what may be served, not about which branch ran. Both
            # halves are real; neither is decoration for the other.
            # The partition test decides what may be REUSED; the declaration kind decides HOW A VALUE
            # IS COMPUTED. They are different questions about different things, so the branch that
            # answers the second sits inside the act of computing — `applyAttr`, downstream of the
            # partition on BOTH arms — and the structural always-recompute law is untouched: a
            # circular structural attribute takes the structural arm, is always recomputed, and
            # recomputing it is running or joining the round. The reuse branch is additionally gated
            # on the round being closed: a prior's settled value served inside a round would replace
            # an in-flight approximation with a value from a different world.
            evalAttr =
              nodeId: attrName: fn:
              if structural.structural attrName then
                let
                  raw = applyAttr nodeId attrName fn;
                in
                if structural.childBearing attrName then builtins.mapAttrs (_: wrapChild) raw else raw
              else if !round.open && decision.isClean nodeId && builtins.elem attrName (servedAt nodeId) then
                servePrior nodeId attrName
              else
                applyAttr nodeId attrName fn;

            # The ONE site at which a member of `runAttributes` is applied, and the total
            # classification over declaration shapes: a function is an ordinary attribute, a
            # kind-tagged record is a circular declaration, and anything else is refused by name —
            # without the third arm a malformed declaration reaches Nix as "attempt to call something
            # which is not a function", an abort carrying no name of ours.
            applyAttr =
              nodeId: attrName: fn:
              if isCircularDecl fn then
                circularDemand nodeId attrName fn
              else if builtins.isAttrs fn then
                throw "gen-scope: attribute '${attrName}' on '${nodeId}' is declared as a record that is not a circular declaration — an attribute is a function `self: id: value`, or the record `circular { carrier = { bottom; leq; height; quotient; }; } step` returns; anything else is refused by name rather than reaching Nix as an anonymous call error"
              else
                fn self nodeId;

            # ── THE DEMAND RULE (three cases), THE ADMISSION, AND THE SHARED ROUND ──
            #
            # A demand on a circular instance from OUTSIDE any round opens one (CASE 1) — the shared
            # round when the universe holds more than one eligible instance, the degenerate own-value
            # ascent when it holds exactly one, the per-instance nested ascent when the declaration
            # says quotient = true (a coarsened order's convergence test is an own-value comparison,
            # so a quotient cannot be a simultaneous member). A demand from INSIDE an open round on a
            # fresh member reads the shared snapshot of the previous level (CASE 2). A demand
            # re-entering an instance already on the walked path IS the cycle (CASE 3): the entries
            # between the two occurrences are that cycle exactly, and admission is asked of it —
            # a quotient declaration on the segment refuses BY NAME; otherwise the re-entry is served
            # the in-progress iterate.
            instanceKey = nodeId: attrName: "${nodeId}.${attrName}";

            circularDemand =
              nodeId: attrName: decl:
              let
                key = instanceKey nodeId attrName;
                declExtras = builtins.filter (
                  n:
                  !(builtins.elem n [
                    "carrier"
                    "kind"
                    "step"
                  ])
                ) (builtins.attrNames decl);
                defect = carrierDefect (decl.carrier or null);
                onPath = builtins.any (e: e.key == key) round.path;
              in
              if declExtras != [ ] then
                throw "gen-scope: circular attribute on '${nodeId}' declares ${builtins.toJSON declExtras} beyond the declaration's three fields — `circular { carrier = ...; } step` returns exactly { kind, carrier, step }, and the field set is capped: a term beyond it is a return to the design sitting rather than a refinement"
              else if defect != null then
                throw "gen-scope: circular attribute on '${nodeId}' ${defect}"
              else if onPath then
                closeCycle decl key
              else if round.open && !decl.carrier.quotient then
                # CASE 2, member: one step against the previous level, served from the round's shared
                # snapshot. A member is never pushed on the path — its reads are level-map lookups,
                # and the cycle it closes is the round itself.
                round.members.${key}
                  or (throw "gen-scope: circular instance '${key}' is demanded inside an open round whose universe does not carry it — its node is outside the evaluated node set the round was derived from")
              else if decl.carrier.quotient then
                nestedAscent nodeId decl key
              else
                openRound nodeId decl key;

            # CASE 3 — the cycle-closure check, over the walked path's segment. Complete for the
            # property despite quantifying only over the path, because of the strategy split: every
            # quotient = true instance evaluated inside an open round is PUSHED (a quotient
            # declaration selects the nested ascent), so at any closure every quotient participating
            # in the cycle is on the segment. A demand that closes no cycle is checked against
            # nothing.
            closeCycle =
              decl: key:
              let
                tailFrom =
                  entries:
                  if entries == [ ] then
                    [ ]
                  else if (builtins.head entries).key == key then
                    entries
                  else
                    tailFrom (builtins.tail entries);
                seg = tailFrom round.path;
                segKeys = map (e: e.key) seg;
                declaring = map (e: e.key) (builtins.filter (e: e.quotient) seg);
              in
              if declaring != [ ] then
                throw "gen-scope: circular demand re-entered '${key}': the walked path closes the cycle ${builtins.toJSON segKeys}, and quotient declaration(s) ${builtins.toJSON declaring} are on it. A quotient carrier cannot be driven in a shared round — its convergence is an own-value comparison over classes, which a simultaneous ascent cannot answer — so the cycle is refused rather than iterated. Declare an antisymmetric order for the instances that read each other, or keep this instance out of the other's cycle."
              else
                round.qcur.${key} or decl.carrier.bottom;

            # The per-instance ascent — the landed `circular` loop, selected by a quotient
            # declaration (from outside a round: today's semantics at every arity) and by every
            # nested derivation inside an open round, where the LIFETIME RULE re-derives it from ⊥ at
            # every level: its inputs there are the enclosing round's intermediates, and are meant to
            # be — the primary's rule for an intermediate is DO NOT CACHE, not REFUSE. Below the
            # level an open round returns the ascent is PROVISIONAL (the arming rule): a refusal
            # raised inside it does not fire, and the ascent returns its LAST iterate — the value
            # before the offending step, the only one the chain invariant still covers.
            nestedAscent =
              nodeId: decl: key:
              let
                inherit (decl.carrier) leq height;
                entry = {
                  inherit key;
                  quotient = true;
                };
                continue =
                  n: prev: next:
                  let
                    ascends = leq prev next;
                  in
                  if ascends && leq next prev then
                    next
                  else if !ascends then
                    if round.provisional then
                      prev
                    else
                      throw "gen-scope: circular attribute on '${nodeId}' took a step its declared order does not ascend, at iteration ${toString n} — the step is not monotone on the declared carrier, so the iteration is not a Kleene ascent and no least fixed point is being computed"
                  else if n >= height then
                    if round.provisional then
                      next
                    else
                      throw "gen-scope: circular attribute on '${nodeId}' is still ascending after ${toString (n + 1)} steps, so the declared height of ${toString height} is exceeded — the bound is derived from the declaration, and what this refutes is the declaration rather than an iteration budget"
                  else
                    go (n + 1) next;
                go =
                  n: prev:
                  let
                    acc = mkAccessor (
                      round
                      // {
                        members = round.qsnap;
                        path = round.path ++ [ entry ];
                        qcur = round.qcur // {
                          ${key} = prev;
                        };
                      }
                    );
                  in
                  if round.provisional then
                    let
                      attempt = builtins.tryEval (decl.step acc nodeId prev);
                    in
                    if attempt.success then continue n prev attempt.value else prev
                  else
                    continue n prev (decl.step acc nodeId prev);
              in
              go 0 decl.carrier.bottom;

            # CASE 1 — a demand from outside any round on a quotient = false instance opens one.
            # The universe is the evaluated node set × the circular attribute names that could be
            # shared-round members (well-formed four-term carrier AND quotient = false), computed
            # once per round; the budget is the sum of the declared heights over it, and the derived
            # bound is Σ hᵢ + 1 — the height of the product order, a REFUSAL THRESHOLD and never a
            # stopping rule. universe ⊇ M at every level, so the budget is sound without knowing the
            # membership: a larger budget delays a refusal and can never cause one.
            openRound =
              nodeId: decl: key:
              let
                eligibleNames = builtins.filter (an: memberEligible runAttributes.${an}) (
                  builtins.attrNames runAttributes
                );
                universe = prelude.concatMap (
                  nid:
                  map (an: {
                    key = instanceKey nid an;
                    inherit nid an;
                    inherit (runAttributes.${an}) carrier step;
                  }) eligibleNames
                ) self.allNodeIds;
              in
              if !(builtins.any (i: i.key == key) universe) then
                throw "gen-scope: circular instance '${key}' is not in the round's universe — its node is outside the evaluated node set the universe is derived from"
              else if builtins.length universe == 1 then
                degenerateAscent nodeId decl key
              else
                runSharedRound {
                  inherit universe;
                  targetKey = key;
                };

            # The degenerate shortcut: a universe of ONE eligible instance is the k = 1 degeneration
            # of the composed rule, and the landed single-attribute behaviour must not move — the
            # own-value exit, the `!ascends` refusal at the first offending step and the derived
            # `h + 1` bound, each with its landed text byte-identical.
            degenerateAscent =
              nodeId: decl: key:
              let
                inherit (decl.carrier) leq height;
                go =
                  n: prev:
                  let
                    acc = mkAccessor (
                      round
                      // {
                        open = true;
                        members = {
                          ${key} = prev;
                        };
                        qsnap = {
                          ${key} = prev;
                        };
                        level = n + 1;
                        provisional = false;
                      }
                    );
                    next = decl.step acc nodeId prev;
                    ascends = leq prev next;
                  in
                  if ascends && leq next prev then
                    next
                  else if !ascends then
                    throw "gen-scope: circular attribute on '${nodeId}' took a step its declared order does not ascend, at iteration ${toString n} — the step is not monotone on the declared carrier, so the iteration is not a Kleene ascent and no least fixed point is being computed"
                  else if n >= height then
                    throw "gen-scope: circular attribute on '${nodeId}' is still ascending after ${toString (n + 1)} steps, so the declared height of ${toString height} is exceeded — the bound is derived from the declaration, and what this refutes is the declaration rather than an iteration budget"
                  else
                    go (n + 1) next;
              in
              go 0 decl.carrier.bottom;

            # ── THE SHARED ROUND ──
            #
            # A level is a lazy map over the universe whose entry k is k's step under the previous
            # level's accessor; level 0 pins every member at ITS OWN declared bottom. Nix forces only
            # what is demanded, so a level costs exactly the instances the demand transitively forces
            # and NOTHING UNDEMANDED IS EVALUATED — which matters more than economy: forcing an
            # undemanded instance would evaluate a circular attribute at a node its author never
            # meant it for, an error rather than a wasted step. "How a member joins" is Nix's own
            # laziness; there is no member list, no join, no widen, no eq and no maxIter.
            #
            # THE FORCE GATE. Two seats ride EVERY member, on the column the demand actually
            # produced, and they refute DIFFERENT things. Two constraints hold at once and each is
            # a defect without the other: NO UNDEMANDED FORCING — the laziness law above turned on
            # the seats themselves, since a protection that forces an undemanded entry reintroduces
            # at the guard the exact error class the guard exists to remove — and NO SILENT DESCENT
            # ON A MEMBER, since a member that descends unrefused leaves the round returning the
            # Kleene iterate of a step that is not monotone, a fixed point that need not be the
            # least one, at EXIT 0, with nothing downstream looking for it.
            #
            # Pure Nix cannot OBSERVE which entries a demand forced — so nothing here observes it.
            # The demanded set is made TRUE BY CONSTRUCTION instead. Let `D` be the least set of
            # (member, level) entries closed under four rules: (D0) every member at level 0 — the
            # carrier bottoms, a DECLARED value with NO STEP behind it; (D1) the target at every
            # level, which is the demand pass; (D2) read-closure — `(m, j)` in `D` and `m`'s step
            # at level j reading `k` at level j−1 gives `(k, j−1)`, which is Nix's own laziness;
            # and (D3) UPWARD COLUMN CLOSURE — `(m, j)` in `D` and `j < bound` gives `(m, j+1)`.
            # The domain is finite and the rules monotone, so the least such set exists and is
            # reached in at most `|universe| × (bound + 1)` steps. Each member a read reaches has a
            # FIRST DEMANDED LEVEL `f(m)` and a column `{0} ∪ [f(m) … bound]`, decidable from
            # `f(m)` alone WITHOUT FORCING ANYTHING TO DECIDE IT. A SEAT FOR `m` IS LIVE AT
            # TRANSITION `(j−1 → j)` IFF BOTH ENDPOINTS ARE IN `D`, so asking it forces no entry
            # outside `D`; and `D` APPLIES THE STEP OF NO MEMBER THAT NO READ REACHES, because
            # (D1) admits the target, (D2) only what a step reads, (D3) only further levels of
            # members a read already reached, and (D0) admits level 0 without applying a step. The
            # bound's cone rule below and this gate are the same principle at two seats, and they
            # agree on that class by construction.
            #
            # The price, stated rather than dismissed: (D3) forces entries no reader asked for, so
            # a partial step above a member's last read level turns an answer into an abort, and a
            # non-monotone or over-running one there is refused on a transition the natural demand
            # never produced. Both refusals are TRUE OF THE PROGRAM THE GATE RAN — the pair is one
            # the round holds an order over — which is the same sentence that forbids reaching
            # BELOW `f(m)`: there the round holds nothing and could come to hold it only by running
            # steps the program's own demand never ran. One rule, two ends. Transitions strictly
            # below `f(m)` therefore carry no seat, and a lie living wholly inside that prefix is
            # answered: a stated scope, not an incompleteness to be repaired later.
            #
            #   THE HEIGHT SEAT refutes a DECLARATION. The witness is the instance's LONGEST STRICTLY
            #   ASCENDING RUN — extended by a strict ascent, left alone by a quiet level, RESET BY A
            #   DESCENT — because k consecutive strict ascents are a chain of k edges in the
            #   instance's own carrier whatever produced the inputs, where a mere tally of ascents
            #   composes no chain. It needs no membership. Its counter is CARRIED BY THE WALK and
            #   is never a fold down the column: a per-level recurrence has no base case above
            #   level 0, so it reaches every earlier entry INCLUDING entries below `f(m)`, which is
            #   the undemanded forcing above exactly. The walk seeds the counter at 0 at the lowest
            #   transition its seat is live at, so THE COUNTER'S REACH IS THE GATE'S REACH.
            #
            #   THE OUTER SEAT refutes the MEMBER'S STEP, and only where it can construct a pair it
            #   has ordered: at a transition where that member itself descended, its own step is
            #   re-applied to the earlier level's member map CLAMPED ENTRYWISE to the later one —
            #   entrywise, inside each entry's own thunk, so an entry the step never demands is never
            #   compared — with quotients derived against the LATER snapshot raw (the same derivation
            #   at both accessors, so a quotient coordinate contributes nothing to the verdict). The
            #   clamp is FLOORED AT `f(m)`: it never reads below the member's own domain, so at a
            #   walk's first transition — where the earlier snapshot would sit below the walk's
            #   seed — the seat is provisional and no clamp is built. If elsewhere the re-applied
            #   step still does not ascend to the value under test, the step is refuted
            #   outright; where it cannot be established — it raises, or a refusal trips inside the
            #   hybrid — the seat is PROVISIONAL and nothing is refused, because a claim about the
            #   program may be raised only at an input the program produces.
            #
            # At the bound the round asks whether ITS DEMAND CONE has stopped moving RAW: the
            # settlement walk re-derives an in-cone member's final value with every member read
            # routed back through the walk, so the compared set is READ-CLOSED BY CONSTRUCTION and
            # nothing undemanded is ever forced. A cone stationary across two consecutive levels IS a
            # fixed point of the round's deterministic step on everything the answer is computed
            # from — no counting precondition — and any member still moving refuses BY NAME.
            runSharedRound =
              { universe, targetKey }:
              let
                index = builtins.listToAttrs (
                  map (i: {
                    name = i.key;
                    value = i;
                  }) universe
                );
                budget = builtins.foldl' (a: i: a + i.carrier.height) 0 universe;
                bound = budget + 1;
                bottoms = builtins.listToAttrs (
                  map (i: {
                    name = i.key;
                    value = i.carrier.bottom;
                  }) universe
                );

                levelsRaw = prelude.genList (
                  j:
                  if j == 0 then
                    bottoms
                  else
                    let
                      prev = builtins.elemAt levelsChecked (j - 1);
                      acc = mkAccessor (
                        round
                        // {
                          open = true;
                          members = prev;
                          qsnap = prev;
                          level = j;
                          provisional = j < bound;
                        }
                      );
                    in
                    builtins.listToAttrs (
                      map (i: {
                        name = i.key;
                        value = i.step acc i.nid (prev.${i.key});
                      }) universe
                    )
                ) (bound + 1);

                # THE COLUMN THE SEATS WALK IS NEITHER `levelsChecked` NOR `levelsRaw`. It is a
                # ladder carrying no seat anywhere in its transitive dependency: the same steps
                # over the same universe, chained on ITSELF. `levelsRaw[j + 1]` is built from
                # `levelsChecked[j]`, so a seat riding `levelsChecked[j]` that read level `j + 1`
                # through either ladder would be inside its own thunk and the round would abort
                # `infinite recursion encountered` on the ordinary case — an abort `tryEval` does
                # not contain. This ladder is extensionally identical to `levelsRaw` by induction
                # on j (level 0 is `bottoms` in both, and `levelsChecked` differs from `levelsRaw`
                # by a `seq` alone), so the walk asks the same question about the same column. The
                # second materialization is the price of (D3): an upward walk must read a column
                # seat-free at every level at or above its own seat, and one ladder cannot both be
                # read by the steps (which is what makes laziness the gate) and be seat-free.
                #
                # LEVEL 1 IS SHARED WITH `levelsRaw`, NOT RE-MATERIALIZED. `levelsRaw[1]` is built
                # from `levelsChecked[0]`, and level 0 of the checked ladder IS `bottoms` — no seat
                # rides it — so `levelsRaw[1]` carries no seat in its transitive dependency and is
                # a legal seed. The seed LEVEL is load-bearing, not a convenience: `levelsRaw[j]`
                # for j ≥ 2 is built from `levelsChecked[j − 1]`, which carries every member's
                # seat, and a ladder seeded there re-enters its own seat's walk — `infinite
                # recursion encountered`, uncatchable. The per-process suite pins that boundary
                # (`ci/tests-process-cells.nix`, arm `hctl2`): if a later revision ever seats
                # level 0, this seed becomes that shape, and the control is what says so loudly.
                # The second materialization therefore starts at level 2.
                shadow = prelude.genList (
                  j:
                  if j == 0 then
                    bottoms
                  else if j == 1 then
                    builtins.elemAt levelsRaw 1
                  else
                    let
                      prev = builtins.elemAt shadow (j - 1);
                      acc = mkAccessor (
                        round
                        // {
                          open = true;
                          members = prev;
                          qsnap = prev;
                          level = j;
                          provisional = j < bound;
                        }
                      );
                    in
                    builtins.listToAttrs (
                      map (i: {
                        name = i.key;
                        value = i.step acc i.nid (prev.${i.key});
                      }) universe
                    )
                ) (bound + 1);

                # EVERY member's entry carries its own seat, and the seat rides the ENTRY — so
                # laziness IS the gate: a member's seat runs when, and only when, that member's
                # entry at that level is read. Nothing enumerates the demanded set; the demand
                # enumerates itself.
                levelsChecked = prelude.genList (
                  j:
                  if j == 0 then
                    bottoms
                  else
                    builtins.mapAttrs (k: v: builtins.seq (checkAt j k) v) (builtins.elemAt levelsRaw j)
                ) (bound + 1);

                # (D3), realized by the seat itself as an UPWARD WALK from the entry's own level to
                # the bound, under the shared bounded-iteration discipline — so the walk's
                # ITERATION is bounded and is never a self-applying recursion. At each transition
                # it carries the previous value and the run counter and asks the two seats.
                #
                # `j0` is the lowest transition the seat is live at. For an entry at level 1 that
                # is `(0 → 1)`, which (D0) supplies at NO STEP COST — level 0 is `bottoms`. Above
                # that the walk never looks below its own entry level: seeding at `j − 1` in
                # general would reach `(m, f(m) − 1)`, a step-computed entry outside `D`, which is
                # the undemanded forcing one level deep. A later re-entry seeds at its own higher
                # level and can only UNDER-count, so it adds no false refusal.
                #
                # `j0` also FLOORS THE OUTER SEAT'S CLAMP: `outerCheck` receives the seed and
                # short-circuits any transition whose earlier snapshot (`j − 2`) would sit below
                # it, so the clamp never reads below the member's own domain either. A re-entry
                # walk thereby loses only its own first transition's refinement — vacuous inside
                # the domain — the same under-counting posture as the run counter above.
                checkAt =
                  j: k:
                  let
                    i = index.${k};
                    inherit (i.carrier) leq;
                    j0 = if j == 1 then 0 else j;
                    advance =
                      st:
                      let
                        jj = st.j + 1;
                        b = (builtins.elemAt shadow jj).${k};
                        r =
                          if leq st.prev b && !leq b st.prev then
                            st.runs + 1
                          else if !leq st.prev b then
                            0
                          else
                            st.runs;
                      in
                      builtins.seq (heightCheck jj i r) (
                        builtins.seq (outerCheck j0 jj i st.prev b) {
                          j = jj;
                          prev = b;
                          runs = r;
                        }
                      );
                  in
                  prelude.iterateBounded forceFields advance {
                    j = j0;
                    prev = (builtins.elemAt shadow j0).${k};
                    runs = 0;
                  } (prelude.genList (x: x) (bound - j0));

                heightCheck =
                  j: i: r:
                  if r > i.carrier.height then
                    let
                      blame = blameAt j i;
                      base = "gen-scope: circular attribute on '${i.nid}' is still ascending after ${toString r} steps, so the declared height of ${toString i.carrier.height} is exceeded — the bound is derived from the declaration, and what this refutes is the declaration rather than an iteration budget";
                    in
                    throw (
                      if blame == [ ] then
                        base
                      else
                        base + " (the still-moving members its step reads: ${builtins.toJSON blame})"
                    )
                  else
                    true;

                # THE FAILURE-PATH PASS — run only when refusing, so its cost lands on the error path
                # alone. It poisons one universe instance at a time and reads the answer off whether
                # the failing step survives: a LOWER bound on the read set, which is honest for a
                # blame set (under-approximation is a shorter list, and the text never reads as a
                # completeness claim). Where the pass cannot observe — anything in it dies — the
                # refusal declares itself partial by naming no blame set at all.
                blameAt =
                  j: i:
                  let
                    prevRaw = builtins.elemAt shadow (j - 1);
                    curRaw = builtins.elemAt shadow j;
                    others = builtins.filter (k2: k2 != i.key) (builtins.attrNames index);
                    reads =
                      k2:
                      let
                        poisoned = prevRaw // {
                          ${k2} = throw "gen-scope: failure-path poison";
                        };
                        accP = mkAccessor (
                          round
                          // {
                            open = true;
                            members = poisoned;
                            qsnap = poisoned;
                            level = j;
                            provisional = false;
                          }
                        );
                      in
                      !(builtins.tryEval (builtins.seq (i.step accP i.nid (poisoned.${i.key})) true)).success;
                    moving = k2: prevRaw.${k2} != curRaw.${k2};
                    blame = builtins.filter (k2: reads k2 && moving k2) others;
                    attempt = builtins.tryEval (builtins.deepSeq blame blame);
                  in
                  if attempt.success then attempt.value else [ ];

                # THE CLAMP IS FLOORED AT THE WALK'S OWN SEED. The guard generalizes the old
                # `j < 2` — which guarded exactly the first transition of a walk seeded at 0, and
                # to which this reduces literally at `j0 = 0` — to THIS walk's first transition:
                # at `j = j0 + 1` the earlier snapshot would be `shadow[j0 − 1]`, below the
                # member's own domain, and the seat never reads below the domain. Inside the
                # domain the first transition has nothing to refine against anyway: the only
                # in-domain candidate for the lower snapshot is `shadow[j0]` itself, a clamp of a
                # level to itself is that level, and the re-applied step reproduces the value
                # under test — so the seat is PROVISIONAL there by construction, no refusal is
                # withdrawn that the domain could have established, and a real first-transition
                # descent is caught by the later transitions' clamps, the settlement walk, or the
                # height seat.
                outerCheck =
                  j0: j: i: vprev: vk:
                  if j - 2 < j0 then
                    true
                  else
                    let
                      inherit (i.carrier) leq;
                      p1 = builtins.elemAt shadow (j - 1);
                      p2 = builtins.elemAt shadow (j - 2);
                      est = builtins.tryEval (leq vprev vk);
                    in
                    if !est.success || est.value then
                      true
                    else
                      # The probe's two halves come from DIFFERENT levels by design, so the
                      # accessor can serve a coordinate combination the program's own
                      # trajectory never produces — and there the re-applied step may demand
                      # an instance nothing on the trajectory reads (SM§2.4a's EXISTENCE
                      # axis). A fault forced only at that combination can die on a channel
                      # `tryEval` does not catch — division by zero, deep recursion — so the
                      # abort is uncatchable BY SUBSTRATE, and this context is what keeps it
                      # from being ANONYMOUS: the death carries the seat, the instance, and
                      # the coordinate, joining the refusal vocabulary even where no refusal
                      # value can be returned.
                      builtins.addErrorContext
                        "gen-scope: the outer seat is re-applying the walked member's step on '${i.nid}' at a constructed clamped pair, probing the descent it detected at iteration ${toString (j - 1)} — a coordinate combination the program's own trajectory does not produce, where the step may demand an entry nothing on the trajectory reads"
                        (
                          let
                            star = builtins.mapAttrs (
                              k2: _:
                              let
                                lo = p2.${k2};
                                hi = p1.${k2};
                              in
                              if index.${k2}.carrier.leq lo hi then lo else hi
                            ) bottoms;
                            accStar = mkAccessor (
                              round
                              // {
                                open = true;
                                members = star;
                                qsnap = p1;
                                level = j;
                                provisional = false;
                              }
                            );
                            attempt = builtins.tryEval (i.step accStar i.nid (star.${i.key}));
                          in
                          if !attempt.success then
                            true
                          else if !(leq attempt.value vk) then
                            throw "gen-scope: circular attribute on '${i.nid}' took a step its declared order does not ascend, at iteration ${toString (j - 1)} — the step is not monotone on the declared carrier, so the iteration is not a Kleene ascent and no least fixed point is being computed"
                          else
                            true
                        );

                # The demand pass: the round's own demand is the target's entry at every level, in
                # order, as a bounded iteration under the shared forcing discipline — never a
                # self-applying recursion, whose frame cost would lose the catchable blame at exactly
                # the depth the blame exists for.
                demandPass = prelude.iterateBounded forceFields (
                  st: builtins.seq (builtins.elemAt levelsChecked st.j).${targetKey} { j = st.j + 1; }
                ) { j = 1; } (prelude.genList (x: x) bound);

                # The settlement walk at the bound.
                priorRaw = builtins.elemAt levelsRaw (bound - 1);
                settleWalk =
                  visited: key:
                  let
                    i = index.${key};
                    accS = mkAccessor (
                      round
                      // {
                        open = true;
                        members = builtins.mapAttrs (
                          k2: v: if builtins.elem k2 visited then v else builtins.seq (settleWalk (visited ++ [ k2 ]) k2) v
                        ) priorRaw;
                        qsnap = priorRaw;
                        level = bound;
                        provisional = false;
                      }
                    );
                    b = i.step accS i.nid (priorRaw.${key});
                  in
                  if b != priorRaw.${key} then
                    throw "gen-scope: a shared circular round is still moving at its derived bound: instance '${key}' takes a step across levels ${toString (bound - 1)} and ${toString bound} that its declared order cannot separate from movement, against the composed bound ${toString bound} (the sum of the declared heights over the round's universe, plus one). The bound is a theorem over the declared carriers, so what this refutes is a declaration — a carrier said `quotient = false` of an order too coarse to settle the states it serves. Declare a finer carrier."
                  else
                    true;
              in
              builtins.seq (demandPass) (
                builtins.seq (settleWalk [ targetKey ] targetKey) (builtins.elemAt levelsRaw bound).${targetKey}
              );

            wrapChild =
              childNode:
              childNode
              // {
                # THE LIFETIME RULE: a round's memo is reachable only through the round's own
                # accessor. While a round is open the co-located cache refuses by name rather than
                # serving — the alternative measured is a silent wrong answer from a snapshot the
                # round has left behind; `self.get` on the same instance is unaffected and serves the
                # round's current level.
                _eval =
                  if round.open then
                    builtins.mapAttrs (
                      attrName: _:
                      throw "gen-scope: the `_eval` cache for '${attrName}' on '${childNode.id or "<child>"}' is not readable inside an open circular round — a round's memo lives on the round's own accessor, and a value cached here would be an approximation wearing a final value's clothes. Read through `self.get`, which serves the round's current level."
                    ) runAttributes
                  else
                    builtins.mapAttrs (attrName: fn: evalAttr childNode.id attrName fn) runAttributes;
              };
            rootEval = prelude.mapAttrs (
              id: _: builtins.mapAttrs (attrName: fn: evalAttr id attrName fn) runAttributes
            ) roots;

            # Resolve a node by ID.
            # Roots: direct lookup. Non-roots: via parseParent or generic walk.
            resolveNode =
              id:
              if roots ? ${id} then
                roots.${id}
              else if parseParent != null then
                let
                  parentId = parseParent id;
                in
                if parentId == null then
                  genericResolve id
                else
                  let
                    all = childRecordsStrict self parentId;
                  in
                  if all ? ${id} then
                    all.${id}
                  else
                    throw "gen-scope: node '${id}' not reachable (parent: ${parentId})"
              else
                genericResolve id;

            # Fallback resolution: walk from all roots through children.
            # O(n) worst case — use parseParent for production scale.
            genericResolve =
              id:
              let
                walkChildren =
                  parentId:
                  let
                    all = childRecordsStrict self parentId;
                  in
                  if all ? ${id} then
                    all.${id}
                  else
                    prelude.foldl' (acc: childId: if acc != null then acc else walkChildren childId) null (
                      builtins.attrNames all
                    );
                found = prelude.foldl' (acc: rootId: if acc != null then acc else walkChildren rootId) null (
                  builtins.attrNames roots
                );
              in
              if found != null then found else throw "gen-scope: node '${id}' not reachable from roots";

            # The materialization walk itself, before it is collapsed into an attrset. Both
            # `allNodes` and `allNodeIds` are projections of this ONE list, so a consumer that
            # wants the node set AND its order pays for a single walk.
            walkEntries = prelude.concatMap self._walkFrom checked.nodeOrder;
          in
          {
            node = resolveNode;

            get =
              id: attrName:
              builtins.addErrorContext "evaluating '${attrName}' on '${id}'" (
                if !(runAttributes ? ${attrName}) then
                  throw "gen-scope: unknown attribute '${attrName}' on node '${id}'"
                else if rootEval ? ${id} then
                  rootEval.${id}.${attrName}
                else
                  let
                    n = self.node id;
                  in
                  # While a round is open the co-located cache is not consulted — its fields refuse
                  # by construction (the lifetime rule at `wrapChild`) — and the demand routes
                  # through the guarded per-attribute evaluator instead.
                  if !round.open && n ? _eval then
                    n._eval.${attrName}
                  else
                    evalAttr id attrName runAttributes.${attrName}
              );

            # --- Tier 2: Materialization (forces evaluation, memoized) ---

            # Internal: walk children/derived-children from a node.
            _walkFrom =
              id:
              let
                all = childRecordsLenient self id;
              in
              [
                {
                  name = id;
                  value = self.node id;
                }
              ]
              ++ prelude.concatMap self._walkFrom (builtins.attrNames all);

            # Internal: the composed child-record read — `children` with the spawn channel's half —
            # published under one name so the sibling query and resolver modules can reach it. They
            # receive only this accessor, and the guard that makes the composition safe on a
            # kindless scope (`attributes ? "derived-children"`) is a test on the running attribute
            # set, which is not in scope there — so the composition is expressible here and nowhere
            # they could spell it. The demanding (strict) arm: every caller asks ONE id for its
            # records, so the `children` half is exactly the guarded `get` and the refusal axis
            # does not move.
            _childRecords = childRecordsStrict self;

            # Full tree materialization. Forces all children attributes recursively.
            # O(n) — each node computed once. Use for gen-graph global ops, diagrams.
            # An attrset is a SET: `attrNames` on it answers in bytewise codepoint order, and the
            # order the walk found the nodes in is not recoverable from this value. Consumers
            # that need that order read `allNodeIds`.
            allNodes = prelude.listToAttrs walkEntries;

            # The SAME node set as `allNodes`, as an ORDERED list of ids in MATERIALIZATION
            # order: root order, then pre-order depth-first through `children` /
            # `derived-children`, so a subtree is contiguous and a parent precedes its
            # descendants. This is the survey order a gather or a reverse reference attribute is
            # defined over — contributions combine in a traversal order of the tree, not in a
            # codepoint order of node names. The rule is this library's own and is argued at
            # `lib/resolve.nix:queryReverse` from the duality with `queryAll`; the citation it
            # once carried ("Hedin & Magnusson 2003 inter-type declarations; Sloane 2010 §7
            # collection attributes") named nothing in either paper — see that comment for the
            # measurements.
            #
            # Two tie-breaks, declared because a declared order is the whole point:
            #
            # 1. Root and sibling ties break on `attrNames`, which is BYTEWISE CODEPOINT order,
            #    not dictionary order — `attrNames { z; A; a; _b; "1"; }` is
            #    `[ "1" "A" "_b" "a" "z" ]`, uppercase before underscore before lowercase. This
            #    is NOT because an attrset "carries no order". The algebraic graph layer carries
            #    a declaration-ordered vertex LIST (`lib/graph.nix`, where `overlay` and
            #    `connect` concatenate), and `lib/build-nodes.nix` collapses that list through
            #    `listToAttrs` and back out through `attrNames` — the same construction this
            #    walk exists to stop doing — so `eval` receives `roots` already set-shaped and
            #    the declared order is gone before anything here runs. The codepoint tie-break
            #    is that collapse's residue. Recovering the declared order is a change to the
            #    constructor, not to this walk.
            #
            # 2. A `derived-children` node INTERLEAVES with its `children` siblings rather than
            #    following them: `_walkFrom` descends what `childRecordsOf` returns, and that is the
            #    two halves merged into ONE attrset, so a derived id sorts into the sibling run under
            #    the same codepoint rule and nothing in this list marks it as derived.
            #
            # Repeats are dropped FIRST-OCCURRENCE-WINS, the same rule `listToAttrs` applies to
            # `allNodes`, so `allNodeIds` is exactly `attrNames allNodes` as a set. A node
            # reached both as a root and as another root's child is common (`buildNodes` makes
            # every vertex a root), so the walk really does repeat. The dedup is index-based —
            # one `listToAttrs` recording first positions, one pass reading them back — because
            # a fold carrying a `seen` attrset copies that attrset per node (quadratic) and
            # recurses once per node (Nix's call-depth ceiling), and this is an O(n) surface.
            allNodeIds =
              let
                names = map (e: e.name) walkEntries;
                n = builtins.length names;
                firstAt = prelude.listToAttrs (
                  prelude.genList (i: {
                    name = builtins.elemAt names i;
                    value = i;
                  }) n
                );
              in
              prelude.concatMap (
                i:
                let
                  nodeId = builtins.elemAt names i;
                in
                prelude.optional (firstAt.${nodeId} == i) nodeId
              ) (prelude.genList (i: i) n);

            # Selective materialization: forces only nodes matching a predicate.
            # Predicate receives structural node data. Descends into ALL children
            # but only INCLUDES matching nodes in the result.
            # O(n) walk but result size ≤ matching nodes.
            allNodesWhere =
              pred:
              let
                walkFrom =
                  id:
                  let
                    node = self.node id;
                    all = childRecordsLenient self id;
                    childResults = prelude.concatMap walkFrom (builtins.attrNames all);
                  in
                  (
                    if pred node then
                      [
                        {
                          name = id;
                          value = node;
                        }
                      ]
                    else
                      [ ]
                  )
                  ++ childResults;
              in
              prelude.listToAttrs (prelude.concatMap walkFrom (builtins.attrNames roots));

            # Subtree materialization: forces only the subtree rooted at a given node.
            # O(subtree size). Does not touch nodes outside the subtree.
            subtreeOf = rootId: prelude.listToAttrs (self._walkFrom rootId);

            # Type-targeted materialization: all nodes of a given type.
            # Walks full tree but only includes matching types.
            # O(n) walk, result size = nodes of that type.
            nodesOfType = type: self.allNodesWhere (node: node.type == type);

            # --- The plane interface ---

            # What an incremental plane reads this evaluation through. It is handed the FACADE,
            # never `self`: the materialization surfaces, the node accessor and the combinators are
            # absent from the RECORD, so a read outside those three names cannot be written against
            # this value at all.
            #
            # ★ That closes the KEY SET, not reachability. `get id "children"` answers node records
            # carrying `decls` / `parent` and the co-located `_eval` cache, so a caller holding one
            # can evaluate through `_eval` without passing through `get`; and `get` takes any
            # string, so a dynamically constructed name is issuable whether or not the combinators
            # travel. Measured, and pinned by the facade cells. What survives that residual is the
            # property reuse rests on — the always-recompute branch below fires before the decision
            # is consulted, so no structural value is ever served from a prior evaluation.
            facade = interface.mkFacade {
              get = self.get;
              nodeIds = self.allNodeIds;
              resolutional = resolutionalAt;
            };

            # The reuse vocabulary, per node, and the subset of a decision's request that is
            # actually served. Both are the same projection the facade carries, exposed so the
            # intersection is inspectable rather than only inferable from behaviour.
            resolutional = resolutionalAt;
            served = servedAt;

            # THE STRUCTURAL PARTITION OF THE ATTRIBUTE SET, PER NODE — the children /
            # derived-children / edges-* / includes attributes, materialized by the always-recompute
            # branch, readable WITHOUT forcing any resolutional attribute. Reads derive from it
            # statically. It is derived rather than declared: the substrate constructed these
            # attributes, so no impossibility argument is owed for them.
            #
            # It is an attribute-name-indexed RECORD and not a relation — `id -> {name -> value}`,
            # which is not even the arity of an edge set. Naming it for the attributes it partitions
            # is what keeps it distinct from the node-level dependency relation the seal publishes.
            structuralAttributes = id: prelude.genAttrs structuralNamesAll (name: self.get id name);

            # THE SAME PARTITION AS A RELATION — `id -> [id]`, which is the arity the record above is
            # not. The projection itself is gen-graph's: it is edge vocabulary, it belongs beside the
            # library's other endpoint extractors, and keeping it there is what stops this evaluator
            # from growing a second copy of a contract the graph library already states.
            #
            # WHAT THIS SIDE SUPPLIES IS THE TWO FACTS ONLY THE SUBSTRATE HOLDS, and it supplies them
            # as VALUES rather than as an import in the other direction. `childBearing` is taken from
            # the same binding `evalAttr` branches on, so the predicate that decides which shape to
            # MATERIALIZE and the predicate that decides which shape to READ are one fact seen from
            # two sides rather than two literals that happen to agree.
            #
            # THE MEMBERSHIP AUTHORITY IS THE EVALUATED NODE SET, NOT THE REGISTRATION SET, and the
            # difference is the point: a structural relation must be allowed to name a node the walk
            # produced, so the larger set is the correct authority. `eval.nix`'s selection guard reads
            # the registration set for the opposite reason — it runs INSIDE a descent channel, where
            # consulting the set being produced is asking the question that is being answered. This
            # seat is not that one: it runs over a completed record, where `allNodeIds` and
            # `structuralAttributes` are sibling thunks.
            #
            # Reading this forces `allNodeIds`, hence the walk. That is the claim's meaning rather
            # than a leak — membership is a statement about the whole graph — and it is why the
            # surface exists on `eval` alone: `evalDebug` binds `allNodeIds` to a refusal, so there is
            # no authority for it to check against there.
            structuralEdges = graph.mkEndpointProjection {
              inherit (structural) childBearing;
              isNode = t: builtins.elem t self.allNodeIds;
            } self.structuralAttributes;

            # The debug-mode validator for that relation, as a value, in the same seat and under the
            # same discipline as `decisionFindings` below: nothing in the production path forces it,
            # so it alters no production result. Forcing it reports every structural attribute of this
            # node whose value violates the codomain contract, and `[ ]` when none does — which is
            # what lets an assertion land on the returned message rather than on a caught throw.
            projectionFindings = graph.mkProjectionFindings {
              inherit (structural) childBearing;
              isNode = t: builtins.elem t self.allNodeIds;
            } self.structuralAttributes;

            # The debug-mode validator, as a value. Nothing in the production path forces it, so it
            # alters no production result and is not a rule the plane must obey; forcing it reports
            # every attribute a decision named that this node's vocabulary does not contain.
            decisionFindings = interface.decisionFindings {
              inherit decision;
              resolutional = resolutionalAt;
              nodeIds = self.allNodeIds;
            };

            # PROVENANCE RIDES THE RESULT. Plain data the caller receives with its answer, never a
            # side channel and never debug-only: a print goes to stderr, which the evaluation cache
            # swallows after the first run, and a debug-only field is invisible in ordinary use.
            # A field that IS the result survives caching because it is what was cached.
            #
            # This library carries the field and never invents a record for it. The facts that get
            # stamped — an input past a benchmark-verified bound, and the bound itself — are the
            # engine's, derived from a cost curve measured there; the substrate holds no threshold
            # and makes no comparison. Carried, so no layer between the engine and the caller can
            # silently drop it.
            inherit provenance;
          }
        );
    in
    mkAccessor closedRound;

  # Diagnostic variant with shadow-stack cycle tracing.
  #
  # Uses attrset-based visited (O(1) cycle check) + parallel list for ordered
  # trace output. Cycles produce: "gen-scope: cycle: a.x -> b.x -> a.x"
  #
  # Trade-off: defeats Nix's native memoization — every get call creates a
  # new self with updated visited/traceList. Use eval for production.
  evalDebug =
    {
      scope,
      attributes,
      parseParent ? null,
    }:
    let
      checked = requireScope "evalDebug" scope;
      roots = checked.nodes;

      # The debug evaluator runs the same effective set for the same reason: a spawn the production
      # evaluator materializes and this one cannot see would make the trace a statement about a
      # different graph.
      runAttributes = effectiveAttributes "evalDebug" checked attributes;

      # The debug evaluator resolves on DEMAND only — it refuses materialization outright — so it
      # takes the demanding arm, which is the arm its inline copy carried.
      childRecordsStrict = childRecordsOf {
        attributes = runAttributes;
        requireChildrenAttribute = true;
      };
      mkSelf =
        visited: traceList:
        let
          # THE TRACE IS A RESULT, NOT A THROW FRAGMENT. `getTraced` answers with the read path
          # AND the value, and the path is readable WITHOUT forcing the value — so the trace is
          # available in exactly the case where it used to be reachable only by parsing a throw
          # message. It is the dynamic read recording, run against the same names the static
          # structural derivation is defined over, and it stays in the debug evaluator because
          # the fresh-self-per-get that records it is what defeats memoization.
          #
          # WHAT IT IS AND IS NOT: the path from the root read to this one. The union of reads
          # across sibling branches is not recoverable here — the thread runs downward into the
          # consumer's attribute functions, and their results are values, so nothing carries a
          # read set back up.
          getTraced =
            id: attrName:
            let
              traceEntry = "${id}.${attrName}";
              path = traceList ++ [ traceEntry ];
            in
            {
              trace = path;
              value =
                if !(runAttributes ? ${attrName}) then
                  throw "gen-scope: unknown attribute '${attrName}' on node '${id}'"
                else if visited ? ${traceEntry} then
                  throw "gen-scope: cycle detected: ${builtins.concatStringsSep " -> " path}"
                else
                  let
                    fn = runAttributes.${attrName};
                    s = mkSelf (visited // { ${traceEntry} = true; }) path;
                  in
                  # The debug evaluator's production reading of a circular declaration is the
                  # per-instance ascent: its fresh-self-per-get shadow stack already detects the
                  # cross-instance re-entry a shared round exists to drive, and driving one here
                  # would defeat the tracing the evaluator exists for.
                  if isCircularDecl fn then
                    debugCircular id fn s
                  else if builtins.isAttrs fn then
                    throw "gen-scope: attribute '${attrName}' on '${id}' is declared as a record that is not a circular declaration — an attribute is a function `self: id: value`, or the record `circular { carrier = { bottom; leq; height; quotient; }; } step` returns; anything else is refused by name rather than reaching Nix as an anonymous call error"
                  else
                    fn s id;
            };
          debugCircular =
            id: decl: s:
            let
              declExtras = builtins.filter (
                n:
                !(builtins.elem n [
                  "carrier"
                  "kind"
                  "step"
                ])
              ) (builtins.attrNames decl);
              defect = carrierDefect (decl.carrier or null);
              go =
                n: prev:
                let
                  next = decl.step s id prev;
                  ascends = decl.carrier.leq prev next;
                in
                if ascends && decl.carrier.leq next prev then
                  next
                else if !ascends then
                  throw "gen-scope: circular attribute on '${id}' took a step its declared order does not ascend, at iteration ${toString n} — the step is not monotone on the declared carrier, so the iteration is not a Kleene ascent and no least fixed point is being computed"
                else if n >= decl.carrier.height then
                  throw "gen-scope: circular attribute on '${id}' is still ascending after ${toString (n + 1)} steps, so the declared height of ${toString decl.carrier.height} is exceeded — the bound is derived from the declaration, and what this refutes is the declaration rather than an iteration budget"
                else
                  go (n + 1) next;
            in
            if declExtras != [ ] then
              throw "gen-scope: circular attribute on '${id}' declares ${builtins.toJSON declExtras} beyond the declaration's three fields — `circular { carrier = ...; } step` returns exactly { kind, carrier, step }, and the field set is capped: a term beyond it is a return to the design sitting rather than a refinement"
            else if defect != null then
              throw "gen-scope: circular attribute on '${id}' ${defect}"
            else
              go 0 decl.carrier.bottom;
        in
        {
          inherit getTraced;

          # The read path this accessor was reached along, as a value.
          trace = traceList;

          node =
            id:
            if roots ? ${id} then
              roots.${id}
            else if parseParent != null then
              let
                parentId = parseParent id;
                s = mkSelf visited traceList;
              in
              # The null parent is a control-flow guard, not a vocabulary one: it stops a null id
              # reaching `get`, where it would surface as a coercion failure rather than as the
              # unreachability this reports. The inline copy spelled it as an `else { }` on both
              # halves, which reached the same throw one attrset construction later.
              if parentId == null then
                throw "gen-scope: node '${id}' not reachable"
              else
                (childRecordsStrict s parentId).${id} or (throw "gen-scope: node '${id}' not reachable")
            else
              throw "gen-scope: evalDebug requires parseParent for non-root nodes";

          get = id: attrName: (getTraced id attrName).value;

          # Internal: the composed child-record read, mirroring the production accessor's
          # `_childRecords` so the query surface answers against either evaluator. Its argument is
          # built the way `node` above builds one — from `mkSelf visited traceList`, never from a
          # captured outer accessor — so the reads it makes land in the trace rather than
          # bypassing the recording this evaluator exists for.
          _childRecords = id: childRecordsStrict (mkSelf visited traceList) id;

          allNodes = throw "gen-scope: evalDebug does not support allNodes (use eval for materialization)";

          allNodeIds = throw "gen-scope: evalDebug does not support allNodeIds (use eval for materialization)";
        };
    in
    mkSelf { } [ ];

  # Reuse-driven evaluator. Same interface as `eval` with the plane's two arguments made
  # MANDATORY: an evaluation that means to reuse says which prior it reuses from and which
  # decision authorises it, rather than inheriting a default that decides for it. A thin
  # wrapper over `eval` — one code path, whose cold case is the same path under a decision
  # saying nothing is clean.
  #
  # THE PRIOR IS AN ACCESSOR, NOT A RESULT MAP. The plane is handed the prior evaluation to
  # read, never a snapshot to hold: a projection is something the EVALUATOR performs on demand
  # from the accessor, not an artefact the plane constructs and carries. The accessor is live
  # inside the same evaluation — this reuse is INTRA-EVALUATION, over the override cone and
  # across targets composed within one evaluation. Nothing here persists from one invocation of
  # the evaluator to the next, and nothing here may claim to.
  # (Informed by Acar, Blelloch & Harper 2002, *Adaptive functional programming*: reusing clean
  # prior results is that paper's change propagation. The 2002 edition is the one this project
  # holds, and it does not use the later "self-adjusting computation" name.)
  evalWarm =
    {
      scope,
      attributes,
      parseParent ? null,
      prior,
      decision,
      provenance ? [ ],
    }:
    eval {
      inherit
        scope
        attributes
        parseParent
        prior
        decision
        provenance
        ;
    };

  # THERE IS NO DECLARED-READS PROJECTION HERE, and its absence is the design rather than a gap.
  # A read-set declared beside a rule does not simplify away — it never exists: the BODY IS THE
  # READ SET (Van Gelder 1991, Definition 3.3 and §8; Sagiv 1990, printed 664; Vogt, Swierstra &
  # Kuiper 1989, Definition 3.5 p. 139). A consumer wanting the read edges of a node reads them off
  # the graph's edge set, which is where they already are.
  #
  # WHAT THE PROJECTION USED TO SAY THAT IS STILL TRUE, kept because it is a property of the
  # evaluator and not of the retired surface: the dynamic read-set — the attributes a node actually
  # `self.get`s — is recoverable only via `evalDebug`'s fresh-self-per-get, which defeats the memo.
  # There is no pure, memo-preserving way to capture it, so the graph's edges are the inspectable
  # contract, and a validator over the dynamic recording is what shows whether they cover the reads
  # (Acar, Blelloch & Harper 2002: the read edges its change propagation walks. "Dynamic dependence
  # graph" is the later editions' name for that structure and does not appear in the edition this
  # project holds, so it is not used here.)
in
{
  inherit
    eval
    evalDebug
    evalWarm
    ;
}
