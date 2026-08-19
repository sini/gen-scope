# THE COLD FOLD — a validated schedule's equations bound to the demand fixpoint, sealed as one
# context.
#
# This entry is the evaluator's CALLER and holds no fixpoint of its own: the equations' compute
# functions become the attribute set `eval` folds, and what the entry adds around it is the sealing —
# the topology accessor the graph and plane consumers read, the declared-read trace, and the schedule
# that validated the grammar.
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
  recordedDeps,
  requireScope,
}:
{
  foldEquations =
    {
      scope,
      parseParent,
      schedule,
      declaredEdges ? (_: [ ]),
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
      roots = checked.nodes;
      ev = eval {
        scope = checked;
        inherit attributes parseParent;
      }; # demand fixpoint (delegate)

      nodeIds = prelude.attrNames ev.allNodes; # includes NTA-spawned children
      accessor = {
        nodes = nodeIds;
        edges = declaredEdges; # consumer->producer (must over-declare, soundness (c))
        parent = id: parseParent id;
        nodeData = id: (ev.node id).decls or { };
      };
      trace = prelude.listToAttrs (
        prelude.map (id: {
          name = id;
          value = {
            deps = recordedDeps { inherit declaredEdges; } id; # eager, declared read-edges
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
        declaredEdges
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
    };
}
