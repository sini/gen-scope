# THE COLD FOLD — a validated schedule's equations bound to the demand fixpoint, sealed as one
# context.
#
# This entry is the evaluator's CALLER and holds no fixpoint of its own: the equations' compute
# functions become the attribute set `eval` folds, and what the entry adds around it is the sealing —
# the topology accessor the graph and plane consumers read, the trace derived over it, and the
# schedule that validated the grammar.
#
# THEORY. Knuth (1968), "Semantics of Context-Free Languages", gives the semantic equations and the
# dependency schedule over them; Vogt, Swierstra & Kuiper (1989), "Higher Order Attribute Grammars",
# give the node-spawning attributes that make the node set itself demand-driven, which is why the
# accessor's node list is read off the evaluator after materialization rather than off the roots.
#
# THE SCHEDULE ARRIVES VALIDATED AND IS NOT BUILT HERE. The circularity test and the stratum assert
# belong to the scheduler that constructs the schedule, and this entry's whole obligation to that
# gate is to force it where a caller can see the throw.
#
# AND THE EQUATIONS COME OFF THE SCHEDULE RATHER THAN ARRIVING BESIDE IT. A second `equations`
# formal would admit a caller pairing a schedule with equations it was NOT built from: the seal would
# carry a schedule nobody folded, and the gate would have validated a grammar the fold never ran.
# Reading them off the schedule makes that pair inexpressible rather than forbidden — there is no
# second argument for the first to disagree with.
{
  prelude,
  eval,
  requireScope,
}:
{
  foldEquations =
    {
      scope,
      parseParent,
      schedule,
      # REQUIRED AND TOTAL, with no default. A defaulted relation would make the ABSENCE of a
      # declaration mean something, and what it meant would be the strongest claim available —
      # this node depends on nothing — awarded to the caller who said nothing at all. The
      # neighbouring decision fields are required for the same reason; absence is a decision, so
      # the caller makes it and says so.
      declaredDependencies,
      settings ? { },
    }:
    let
      equations = schedule.equations;
      attributes = prelude.mapAttrs (_: eq: eq.compute) equations;
      # The guard is forced here rather than left to `eval`, so the entry this caller named is the
      # entry the message names.
      checked = requireScope "foldEquations" scope;
      # The plane re-exports the node map under its established name. That is OUTPUT data, not an
      # entry formal, so the input-type ruling does not reach it — and a consumer that hands this
      # half back to an evaluator is refused by name rather than served silently.
      #
      # ★ AND THE WHOLE RECORD IS SEALED BESIDE IT, as `scope` — which is what makes that refusal a
      # REDIRECTION rather than a dead end. A consumer that must CALL an evaluator, as the warm
      # plane does, needs the declared vertex order and the kind registry; neither is recoverable
      # from the node map, and neither is carried by any other sealed field. Publishing only the
      # half left that consumer refused by name with nowhere to be sent, so the seal published a
      # surface the interface's own consumer could not be written against.
      roots = checked.nodes;
      # The declared relation travels DOWN into the evaluator as well as into the seal. The contract
      # is a FIRING check and the firings happen inside the demand fixpoint, so a relation held here
      # and not there would be a declaration nothing consults — the dead declared surface ADR-0008
      # retires. This entry's formal is required and total, so every fold reached through it arms
      # the `self.node` seam guard; an evaluator reached directly is not under this contract and
      # says so by receiving no relation at all.
      ev = eval {
        scope = checked;
        inherit attributes parseParent declaredDependencies;
      }; # demand fixpoint (delegate)

      nodeIds = prelude.attrNames ev.allNodes; # includes NTA-spawned children
      accessor = {
        nodes = nodeIds;
        # ── THE UNION THE STALENESS CONE IS TAKEN OVER, AND THE ONE PLACE IT IS NORMALIZED ──
        # This field and `declaredDependencies` used to be the same value under two names. They are
        # two relations and ADR-0008 rules them two fields, so the alias was the ruling unmade: the
        # gate reads the CONTRACTED declared relation, and a consumer computing reuse reads the
        # relation the substrate actually induces. Only the second admits the structural half.
        #
        # THE DECLARED HALF ALONE IS UNSOUND BY CONSTRUCTION, which is why this is a union and not a
        # choice. A parent reaches its children's decls and evaluated attributes through a SELF-READ
        # — the parent's value is a function of the child's — so a parent whose child changed is
        # stale whether or not its author wrote the edge down. That self-read is the ordinary shape
        # of an inherited attribute (Knuth 1968), and nothing at the authoring surface is obliged to
        # mirror it.
        #
        # THE TWO HALVES ARE DIRECTION-COMPATIBLE, and getting this backwards would invert the cone
        # silently. The declared half is consumer->producer (it must over-declare, soundness (c));
        # the structural projection is parent->child. By the self-read above the parent IS the
        # consumer and the child IS the producer, so the two agree and `++` unions like-directed
        # relations rather than mixing a relation with its converse.
        #
        # THE NORMALIZATION IS PART OF THE RELATION'S IDENTITY, NOT AN IMPLEMENTATION DETAIL. A
        # reuse layer compares the deps it recorded against the deps it is handed, as LISTS — same
        # members, same multiplicity, same order — and a consumer's accessor already dedups what it
        # receives. Under the alias the asymmetry was invisible because a declared relation carries
        # no duplicates; the union introduces them the moment a node is both declared and a child,
        # and the two sides then disagree for exactly those nodes, permanently and silently.
        # `prelude.unique` settles both halves in one call: dedup is what is REQUIRED, and its
        # first-occurrence order is deterministic, so a canonical order arrives free rather than
        # needing a sort. A consumer's own dedup becomes idempotent rather than corrective.
        #
        # ONE CONSTRUCTION SITE IS WHAT MAKES THE ORDER HALF FREE. The trace below derives from this
        # field, so what the seal records and what a consumer is handed are the same list because
        # they are the same expression — not because both ends sort. Order could diverge only if
        # each end re-derived the union independently, and there is nowhere here for a second
        # derivation to live.
        #
        # STRICTNESS, STATED BECAUSE THIS STOPPED BEING A RE-BINDING: reading this forces the
        # structural partition and, through the projection's membership authority, the evaluated
        # node set. Both are already forced by `nodeIds` above for any caller that reads the trace.
        # The projection forces no resolutional attribute.
        dependencies = id: prelude.unique (ev.structuralEdges id ++ declaredDependencies id);
        parent = id: parseParent id;
        nodeData = id: (ev.node id).decls or { };
        # ── THE GUARDED TRACE LOOKUP ──
        # `trace.<id>` selection on a MISSING id is the interpreter's own `attribute missing`
        # abort — uncatchable by `tryEval`, naming neither the id nor the relation — and attribute
        # selection is not interceptable, so the refusal cannot live on the sealed attrset itself.
        # It lives here instead, beside `dependencies`, whose missing-id read already refuses the
        # same way: every operation returns a value or a NAMED refusal (ADR-0025 item 1). Present
        # ids answer the sealed `trace` entry unchanged — one derivation site — and
        # `trace.<id> or default` remains the caller-side opt-out (ordinary selection).
        trace =
          id: trace.${id} or (throw "gen-scope: no trace for node '${id}' — node not reachable from roots");
      };
      # The trace's deps are DERIVED — read off the accessor's dependency relation, which is the
      # normalized union above and NOT the declared relation the gate runs over. Those were one
      # graph while `dependencies` aliased `declaredDependencies`, and separating them is the whole
      # of ADR-0008's two-field ruling made physical: the gate keeps its contracted relation at the
      # field of that name, and the trace follows the relation a reuse decision must actually be
      # sound over. Nothing declares a read set beside the rule, because a declared read set does
      # not exist to declare: the body IS the read set (Van Gelder 1991 Def 3.3 and §8; Sagiv 1990
      # printed 664; Vogt 1989 Def 3.5 p. 139). The projection that used to stand between these two
      # lines duplicated a truth the relation already held.
      trace = prelude.listToAttrs (
        prelude.map (id: {
          name = id;
          value = {
            deps = accessor.dependencies id; # derived from the normalized union, by construction
            hash = null; # a reuse layer across evaluations is what would populate this
          };
        }) nodeIds
      );
    in
    # Force the schedule HERE: the gate and the stratum assert live inside the scheduler's
    # `if bad then throw else {…}`, so a caller handing an invalid grammar is refused at this entry
    # rather than lazily on a first attribute read. Binding the equations off the schedule does NOT
    # subsume this — that binding is consumed lazily, through `attributes`, which nothing forces
    # until an attribute is demanded.
    builtins.seq schedule {
      inherit
        accessor
        declaredDependencies
        equations
        parseParent
        roots
        schedule
        settings
        trace
        # The evaluator's attribute set, sealed alongside the equations it projects: what a
        # re-evaluation needs is the attribute functions, and deriving them inside the plane would
        # hand it a vocabulary belonging to the authoring surface.
        attributes
        ;
      eval = ev;
      # The validated record, NOT the formal. `inherit scope` would seal the raw argument and hand
      # a consumer back the very thing `requireScope` exists to reject — the guard would have run
      # and published its input anyway. `checked` is the value that passed it.
      scope = checked;
    };
}
