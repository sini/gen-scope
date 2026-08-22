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
{ prelude, requireScope }:
let
  structural = import ./structural.nix { inherit prelude; };
  interface = import ./interface.nix { inherit prelude; };

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
  # would move live behaviour under cover of a consolidation, so the divergence is carried as an
  # argument — visible at one site and decidable in one place — instead of being settled here.
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
        builtins.mapAttrs (
          childId: record:
          if record ? type then
            throw "gen-scope: kind '${hostKind}' spawns '${produced}' and its builder returned a child '${childId}' carrying its own `type`. A spawn does not choose its child's kind: the kind is the key the builder was declared under, and the substrate stamps it from there — a kind chosen while the spawn fires is one nothing can have checked descends. Drop the field."
          else
            record // { type = produced; }
        ) (spawns.${produced} ev id);
    in
    prelude.foldl' (acc: produced: acc // stamped produced) { } (builtins.attrNames spawns);

  # The attribute set the evaluators actually run, which is the caller's plus the spawn channel the
  # registry declares. Writing that channel by hand is refused: it is the one surface on which an
  # expansion could still be declared outside the kind order, and leaving it open would make the
  # order a convention rather than a property.
  effectiveAttributes =
    entry: kinds: attributes:
    if attributes ? ${spawnChannel} then
      throw "gen-scope.${entry}: `attributes` declares `${spawnChannel}` directly. A node expansion is declared on the KIND it expands FROM — `mkKind { spawns = { <produced-kind> = builder; }; }` — so that the produced kind is a registered name below its host's own and the descent is settled before anything fires. Written as a bare attribute the produced kind is whatever the body returns, which is a choice made at firing time and one nothing can check. Move the builder onto its host kind's `spawns`."
    else if kinds == null then
      attributes
    else
      attributes
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
      runAttributes = effectiveAttributes "eval" (checked.kinds or null) attributes;

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
        evalAttr =
          nodeId: attrName: fn:
          if structural.structural attrName then
            let
              raw = fn self nodeId;
            in
            if structural.childBearing attrName then builtins.mapAttrs (_: wrapChild) raw else raw
          else if decision.isClean nodeId && builtins.elem attrName (servedAt nodeId) then
            servePrior nodeId attrName
          else
            fn self nodeId;
        wrapChild =
          childNode:
          childNode
          // {
            _eval = builtins.mapAttrs (attrName: fn: evalAttr childNode.id attrName fn) runAttributes;
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
              if n ? _eval then n._eval.${attrName} else runAttributes.${attrName} self id # fallback (shouldn't happen)
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
      runAttributes = effectiveAttributes "evalDebug" (checked.kinds or null) attributes;

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
                  runAttributes.${attrName} (mkSelf (visited // { ${traceEntry} = true; }) path) id;
            };
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
