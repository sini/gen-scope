# The evaluator↔plane interface: the DECISION an incremental plane returns, and the
# RESTRICTED READ FACADE it is given.
#
# DIRECTION. The plane takes the current program, a prior evaluation and the graph, and
# returns a DECISION — a predicate over nodes and a projection over the prior evaluation's
# results. The evaluator consumes the decision and does all recomputation. The plane returns
# no values it computed and holds no results it produced.
#
# WHY THE RETURN TYPE CARRIES NO VALUES. A second place where results live and drift would
# have to be a `Decision` field carrying values. There is none: a `Decision` is two total
# functions, both of which the EVALUATOR applies against the prior accessor to obtain a value.
# A plane that accumulates its own evaluation state therefore has nowhere to put a result even
# if it wanted one. The property is discharged by the RECORD, and widening that record is a
# visible change to a documented type rather than the silent drift it guards against —
# `mkDecision`'s pattern refuses an unknown field BY NAME at construction.
#
# WHY TWO FIELDS AND NOT ONE. Reuse asks two independent questions — is this node clean, and
# is this attribute one we may reuse. Answering the second with a FUNCTION rather than with
# membership in a snapshot is what removes the data structure that would otherwise hold values.
#
# THE FAILURE DIRECTION IS SAFE ON THE NAMING AXIS. Anything outside the served set falls
# through to a recompute, so over the `reusable` axis the worst a rogue or buggy plane achieves
# is a MISSED REUSE, never a stale serve — and that holds for every value of `reusable`,
# including a malicious one. It does not hold over the `isClean` axis: a decision calling a
# dirty node clean serves prior values for resolutional attributes that should have been
# recomputed. Deciding cleanliness IS the plane's function, so no construction here closes
# that class; the byte-parity oracle is its instrument.
{ prelude }:
let
  structural = import ./structural.nix { inherit prelude; };
in
rec {
  # The cold decision: nothing is clean, nothing is reusable. The cold case is the warm case
  # with the decision saying so, rather than a separate code path.
  coldDecision = {
    isClean = _: false;
    reusable = _: [ ];
  };

  # Both fields are REQUIRED and both are TOTAL. A defaulted `isClean` would make the absence
  # of a decision mean something, and what it meant would be invisible at the call site.
  mkDecision =
    { isClean, reusable }:
    {
      inherit isClean reusable;
    };

  # The facade the plane reads through. WHAT IS CLOSED IS THE RECORD'S KEY SET: `get`,
  # `nodeIds`, `resolutional` and nothing else. No `node` entry, no `allNodes`, no combinator
  # entries. A read outside those three names is not refused at run time — it is absent from
  # the record, so it cannot be written against this value at all, and the enumeration is
  # checkable because it is defined here.
  #
  # ★ WHAT IS *NOT* CLOSED, STATED BECAUSE THE WIDE FORM OF THIS CLAIM WAS FALSE OF THE
  # MECHANISM. Closing the key set does NOT bound what is reachable through the values `get`
  # returns, and two measured channels show why:
  #
  # 1. **A child-bearing attribute hands back NODE RECORDS.** `get id "children"` answers an
  #    attrset of nodes, and each carries `id` / `type` / `parent` / `decls` AND the co-located
  #    `_eval` cache — so `(get id "children").<kid>._eval.<attr>` is a complete parallel
  #    evaluation channel that never passes through `get`, and `.decls` / `.parent` are read
  #    straight off the record. Raw node records are therefore REACHABLE, not unreachable.
  # 2. **`get` accepts any string.** Withholding the combinators withholds the combinators; it
  #    does not stop a caller building `"edges-" + label` and passing it in. A dynamically
  #    constructed attribute name IS issuable through the facade.
  #
  # This is the same shape as the finding that there is no single read choke point anywhere in
  # this library: an accessor returning a raw record is not confined by the accessor's own key
  # set. The residual is real and is pinned as measured fact by the facade cells rather than
  # argued away — a claim of containment that a two-line probe refutes is worse than no claim,
  # because the next reader trusts it.
  #
  # WHAT THIS BOUNDS AND WHAT IT DOES NOT. The closed key set bounds the NAMES the plane can
  # ask this record for. It does NOT make this library single-choke-point: the evaluator's own
  # attribute functions keep every read channel they have, and they must, because those
  # channels are how the substrate works. The facade is a boundary on ONE consumer's entry
  # points, and stating it that narrowly is the point.
  #
  # What DOES hold regardless of the residual is the property the reuse design actually rests
  # on: no structural value is ever served from a prior evaluation, because the evaluator's
  # always-recompute branch fires before the decision is consulted. That is a property of the
  # evaluator, not of this record, so no amount of reaching through a returned value weakens it.
  #
  # `get` answers within the resolutional vocabulary; asked for a structural attribute it
  # RECOMPUTES rather than serving, which is the evaluator's own always-recompute branch and
  # not a check performed here.
  mkFacade =
    {
      get,
      nodeIds,
      resolutional,
    }:
    {
      inherit get nodeIds resolutional;
    };

  # The names a facade carries, as data, so a widening fails a cell rather than passing
  # silently.
  facadeNames = builtins.attrNames (mkFacade {
    get = null;
    nodeIds = null;
    resolutional = null;
  });

  # THE DEBUG-MODE VALIDATOR. A decision naming an attribute outside the resolutional
  # vocabulary is a PLANE DEFECT: the name is inconsequential — the structural branch fires
  # first and the name is absent from the served intersection — but the condition is known and
  # there has to be somewhere to say it.
  #
  # This is a VALUE, not a guard. Nothing in the production path forces it, so it cannot alter
  # a production result and it is not a rule the plane must obey to get a correct answer. It is
  # the disagreement between what the plane names and what the vocabulary contains, reported as
  # a finding rather than left as silence.
  decisionFindings =
    {
      decision,
      resolutional,
      nodeIds,
    }:
    prelude.concatMap (
      nodeId:
      let
        vocabulary = resolutional nodeId;
      in
      map (attrName: {
        inherit nodeId attrName;
        reason =
          if structural.structural attrName then
            "structural attribute named in a reuse decision (always recomputed; never served)"
          else
            "attribute not in this node's resolutional vocabulary";
      }) (builtins.filter (attrName: !(builtins.elem attrName vocabulary)) (decision.reusable nodeId))
    ) nodeIds;
}
