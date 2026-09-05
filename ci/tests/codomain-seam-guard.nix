# THE `self.node` SEAM GUARD — O15.
#
# A body may not ACQUIRE a node record across an edge its node did not declare. The coverage
# condition already governs the READ seam (`self.get`); this cell governs the one beside it, and the
# distinction is the whole of the cell: `node` is a separate entry point, and the traversal helpers
# — `siblings`, `ancestors`, the Neron collection walks, the reverse query — reach their targets
# through it rather than through `get`. A suite carrying only the read-seam cell leaves this seam
# unarmed, and the dispositions that rest on it rest on an undetectable mechanism.
#
# THE SEEDED DEFECT IS THE SUBSTRATE'S OWN BEHAVIOUR, not an implementer's possible slip: an
# undeclared cross-node acquisition SUCCEEDS on an evaluator reached directly, which is the last
# control below and is the dominant extract idiom in this library and its consumers.
#
# THE ASSERTION ON THE MESSAGE GOES THROUGH THE VALIDATOR, never through a caught throw:
# `builtins.tryEval` catches a throw and discards its text, so a guard that only threw would be a
# guard whose message no cell could assert. The validator returns the reason and the seam raises it;
# the wired cells below assert the FACT of the refusal, and the validator cell asserts its CONTENT.
{ genScope, genGraph, ... }:
let
  inherit (genScope)
    buildRoots
    circular
    eval
    foldEquations
    seamAcquisitionDefect
    ;

  # Two peers under one root: `a` and `b` are siblings, so an acquisition between them crosses an
  # edge that no structural containment supplies and that only a declaration can license.
  scope = buildRoots {
    parentGraph = genScope.overlays [
      (genScope.edge "a" "root")
      (genScope.edge "b" "root")
    ];
    decls = {
      root.v = 0;
      a.v = 1;
      b.v = 2;
    };
    types = { };
  };

  peerOf = id: if id == "a" then "b" else "a";

  # The relation the entries accept, built through `gen-graph.mkDeclaredEdges`. `peerRelation` is
  # `id: [ (peerOf id) ]` written as the index that constructor normalizes to, and it carries `root`
  # for a reason a set of two would miss: a shared round ranges over EVERY eligible instance, so
  # `root`'s own step acquires `a`'s record and a declaration omitting it refuses the round for a
  # node the cells never name.
  contracted = import ./_fixtures/declared.nix { inherit genGraph scope; };
  peerRelation = contracted {
    root = [ "a" ];
    a = [ "b" ];
    b = [ "a" ];
  };
  emptyRelation = contracted { };

  attributes = {
    children =
      _self: id:
      builtins.listToAttrs (
        map (cid: {
          name = cid;
          value = scope.nodes.${cid};
        }) (builtins.filter (cid: scope.nodes.${cid}.parent == id) (builtins.attrNames scope.nodes))
      );
    imports = _self: _id: [ ];

    # THE SEED: a cross-node acquisition, written the way every measured extract site writes it.
    peer-v = self: id: (self.node (peerOf id)).decls.v;

    # THE CLEAN PATH: an acquisition of the node's OWN record, which crosses no edge and which the
    # inherited-attribute idiom rests on.
    self-v = self: id: (self.node id).decls.v;
  };

  equations = builtins.mapAttrs (name: compute: {
    inherit name compute;
    kind = if name == "children" then "nta" else "synthesized";
    readsAttrs = [ ];
    stratum = if name == "children" then "structural" else "resolution";
  }) attributes;

  foldWith =
    declaredDependencies:
    foldEquations {
      inherit scope declaredDependencies;
      schedule = { inherit equations; };
      parseParent = id: scope.nodes.${id}.parent or null;
    };

  # The empty relation is a DECLARATION — this node depends on nothing — so it arms the guard and
  # every cross-node acquisition under it is refused.
  emptyCtx = foldWith emptyRelation;
  declaredCtx = foldWith peerRelation;

  # No relation at all: the evaluator was not reached through the contracted entry, so the guard is
  # unarmed. This is the seeded defect measured passing, and it is also the guardless-entry case —
  # a query entry point acquires a record with no body behind it, so there is no reader whose
  # declaration a guard could consult.
  unarmedEv = eval { inherit scope attributes; };

  # ── THE CIRCULAR DEMAND PATHS, AND THERE ARE TWO OF THEM ──
  # A circular attribute's step is a body too, and it does not reach the substrate through the
  # ordinary application site: an ascent applies it against the accessor it built for the level.
  # The two paths take the step from different places — the SHARED ROUND takes it off the universe
  # index it derives from the running attribute set, and the NESTED ASCENT a quotient declaration
  # selects takes it off the declaration the demand arrived with. A binding on one leaves the other
  # open, and from outside the two read identically, so each gets its own cell.
  carrierWith = quotient: {
    bottom = 0;
    leq = x: y: x <= y;
    height = 2;
    inherit quotient;
  };

  # THE STEP CONVERGES WHEN THE ACQUISITION IS PERMITTED, and that is what makes these cells
  # discriminate rather than merely refuse. A step of `prev + peer.v` ascends forever and exceeds
  # its declared height, so it throws whether or not the guard fired — `tryEval` reports the same
  # `success = false` for both, and the cell would pass with the guard removed. Reading the peer's
  # value outright reaches its fixed point in one step, so the ONLY throw available is the guard's.
  peerStep =
    self: id: _prev:
    (self.node (peerOf id)).decls.v;

  circularFold =
    { quotient, declaredDependencies }:
    let
      circularAttributes = attributes // {
        peer-reach = circular { carrier = carrierWith quotient; } peerStep;
      };
    in
    foldEquations {
      inherit scope declaredDependencies;
      parseParent = id: scope.nodes.${id}.parent or null;
      schedule.equations = builtins.mapAttrs (name: compute: {
        inherit name compute;
        kind =
          if name == "children" then
            "nta"
          else if name == "peer-reach" then
            "circular"
          else
            "synthesized";
        readsAttrs = [ ];
        stratum = if name == "children" then "structural" else "resolution";
      }) circularAttributes;
    };

  # quotient = false: three eligible instances, so the demand opens a SHARED ROUND.
  sharedRoundCtx = circularFold {
    quotient = false;
    declaredDependencies = emptyRelation;
  };
  sharedRoundDeclaredCtx = circularFold {
    quotient = false;
    declaredDependencies = peerRelation;
  };
  # quotient = true: a quotient carrier cannot be a simultaneous member, so the demand takes the
  # per-instance NESTED ASCENT instead, which reads its step off the declaration the demand arrived
  # with rather than off the round's universe index.
  nestedAscentCtx = circularFold {
    quotient = true;
    declaredDependencies = emptyRelation;
  };
  nestedAscentDeclaredCtx = circularFold {
    quotient = true;
    declaredDependencies = peerRelation;
  };
in
{
  flake.tests."codomain-seam-guard" = {
    # ── O15 ──
    # The seeded defect: a cross-node acquisition under an empty declared relation. The subject is
    # the FACT of the refusal; its CONTENT is the next cell's.
    test-O15-undeclared-cross-node-acquisition-is-refused = {
      expr = (builtins.tryEval (emptyCtx.eval.get "a" "peer-v")).success;
      expected = false;
    };

    # The refusal's CONTENT, read off the validator rather than off a caught throw: it names the
    # READER, the TARGET and the DECLARED RELATION as it stands, and it names the repair.
    test-O15-the-refusal-names-reader-target-and-relation = {
      expr = seamAcquisitionDefect {
        reader = "a";
        target = "b";
        declared = [ ];
      };
      expected = "gen-scope: node 'a' acquired the record of node 'b' through `self.node`, and 'b' is not in the dependency relation 'a' declared: []. A body may not read across an edge its node did not declare — the relation a grammar gate runs over is contracted at every firing, so an undeclared acquisition would make the declaration false while the evaluation still answered. Declare 'b' among 'a's dependencies; a traversal that ranges over the graph declares the range it ranges over.";
    };

    # The guard reaches the OTHER demand paths. A circular attribute's step acquires its peer's
    # record under an empty relation and is refused the same way — without these the seam would be
    # guarded on the ordinary path and open on the circular ones, which read identically from
    # outside. Two cells because the two ascents take the step from two different places.
    test-O15-the-guard-reaches-a-shared-rounds-step = {
      expr = (builtins.tryEval (sharedRoundCtx.eval.get "a" "peer-reach")).success;
      expected = false;
    };

    test-O15-the-guard-reaches-a-nested-ascents-step = {
      expr = (builtins.tryEval (nestedAscentCtx.eval.get "a" "peer-reach")).success;
      expected = false;
    };

    # The declared arm of each, which is what separates "the guard fired" from "the ascent threw".
    # Without them a step that never converged would satisfy the two cells above with the guard
    # entirely removed — measured: it did, and these are what closed it.
    test-control-a-declared-acquisition-converges-in-a-shared-round = {
      expr = sharedRoundDeclaredCtx.eval.get "a" "peer-reach";
      expected = 2;
    };

    test-control-a-declared-acquisition-converges-in-a-nested-ascent = {
      expr = nestedAscentDeclaredCtx.eval.get "a" "peer-reach";
      expected = 2;
    };

    # ── THE CONTROLS ──
    # The SAME acquisition, declared: permitted, and the body returns its value. Without this the
    # cell above could be passing on a guard that refuses everything.
    test-control-the-same-acquisition-declared-is-permitted = {
      expr = declaredCtx.eval.get "a" "peer-v";
      expected = 2;
    };

    # The guard's clean path, wired: a self-acquisition under an EMPTY relation still answers,
    # because `reader == target` crosses no edge for the contract to govern.
    test-control-a-self-acquisition-is-not-refused = {
      expr = emptyCtx.eval.get "a" "self-v";
      expected = 1;
    };

    # The same clean path at the validator, where the reason is a value: null, not a message.
    test-control-the-validator-permits-a-self-acquisition = {
      expr = seamAcquisitionDefect {
        reader = "a";
        target = "a";
        declared = [ ];
      };
      expected = null;
    };

    # THE SEEDED DEFECT MEASURED PASSING: with no relation supplied at all the evaluator is not
    # under this contract, the guard is unarmed, and the undeclared acquisition answers — which is
    # the behaviour every measured extract site relies on today, and the guardless-entry case the
    # landing had to keep working.
    test-control-an-unarmed-evaluator-still-answers-the-acquisition = {
      expr = unarmedEv.get "a" "peer-v";
      expected = 2;
    };
  };
}
