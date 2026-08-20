# The engine's front door: the semantics, the partition it consumes, and the provenance its own
# result carries.
#
# THREE THINGS MEET HERE AND EACH BELONGS TO A DIFFERENT OWNER.
#
# 1. THE SEMANTICS is the well-founded partial model, computed one file over. It needs no graph
#    and takes none.
#
# 2. THE PARTITION IS NOT THIS LIBRARY'S. Strongly connected components and the condensation are
#    the graph library's concern, and this engine CONSUMES that library's one published front
#    door rather than carrying a second partitioner. The door holds the default; the arms are
#    published under their own names for a caller whose correctness depends on which algorithm
#    answers. Nothing here re-implements a traversal, and nothing here asks the door for a
#    labelled edge set — the accessor it is handed is the unsigned dependency relation, which is
#    the relation mutual reachability is a property of.
#
# 3. THE THRESHOLD IS THE ENGINE'S, and so is the comparison. The door reports the condensation
#    DEPTH as plain partition data — it computes that depth in the course of condensing, holds no
#    number and makes no comparison. The engine owns the figure, derived from its OWN measured
#    cost curve, the comparison against it, and the stamp on its own result. A door holding the
#    number would be holding a figure derived from a curve measured in another repository.
#
# ── THE WARNING RIDES THE RESULT ──
# The engine returns the answer AND the fact that the input exceeded the verified range. It is a
# value the caller receives, never a side channel: a printed warning goes to stderr, which the
# evaluation cache swallows after the first run, and a debug-only field is invisible in ordinary
# use. A field that IS the result survives caching because it is what was cached, and no layer
# between here and the caller can silently drop it. It is plain data, so it crosses an evaluation
# boundary as itself.
#
# ★ THIS IS NOT THE SEMANTICS' THIRD VALUE. UNDEFINED is a verdict on an atom INSIDE the model;
# this is an emission accompanying a SUCCESSFUL operation. Different kinds of third thing, and
# the two names must keep meaning what they say.
#
# ── THE DEPTH IS DEMAND-DRIVEN, LIKE EVERYTHING ELSE HERE ──
# `provenance` is on the result and a consumer cannot drop it; the partition behind it is
# computed when it is read. A caller that never reads the field never pays for the condensation,
# and a caller that reads it gets a figure computed from the same door the contract publishes.
{ prelude, graph }:
let
  wellFoundedLib = import ./well-founded.nix { inherit prelude; };
  acceptanceLib = import ./acceptance.nix { inherit prelude; };

  inherit (acceptanceLib) verifiedDepth;

  # The stamp, as a function of the depth alone, so the condition is readable and testable apart
  # from the cost of computing a condensation. Empty where the input is inside the bound — which
  # is what makes a stamped result mean something, since a field that is always populated says
  # nothing about the input that produced it.
  provenanceFor =
    depth:
    prelude.optional (depth > verifiedDepth.depth) {
      fact = "the input exceeds the engine's benchmark-verified condensation depth";
      condensationDepth = depth;
      verifiedDepth = verifiedDepth.depth;
      inherit (verifiedDepth) derivation fixtures environment;
    };

  # ── THE INTERPRETATION IS REQUIRED, AND THE ABSENCE OF A DEFAULT IS THE POINT ──
  # A defaulted empty interpretation is the precise shape of this project's one defect: a caller
  # who forgets the carry gets, SILENTLY, the collapse the parameter exists to prevent. Absence is
  # a decision, so the caller makes it — the first pass supplies `interpretation = [ ]` and says so.
  # The strict pattern also refuses an unknown field by name at application, by the evaluator
  # itself, which is the discipline `mkRule` and `stratify` already ship.
  #
  # ★ THE PARTITION AND THE STAMP DO NOT MOVE, AND THE REASON IS STRUCTURAL. `program.dependency`
  # is the accessor the condensation door reads, and CARRIED ATOMS CONTRIBUTE NO EDGES — they are
  # isolated nodes, so they cannot exceed an existing longest path. The interpretation is therefore
  # NOT added to the dependency accessor, the verified-depth comparison stays a reading of the same
  # quantity it was before, and the demand-driven property survives.
  #
  # ★ ADR-0013's BURDEN — *a dependence fact is DERIVED unless derivation is proven impossible* —
  # never arises, and that is argued rather than assumed, because a parameter carrying
  # caller-supplied atoms into an engine is exactly the shape that burden exists for. The
  # dependence relation stays DERIVED from the rules; an interpretation is not a dependence
  # declaration, because what it declares is a set of VERDICTS and not a set of reads. Nothing here
  # declares a fact the substrate could have derived.
  solve =
    { program, interpretation }:
    let
      partition = graph.condensation program.dependency;
    in
    wellFoundedLib.wellFoundedModel { inherit program interpretation; }
    // {
      # Read from the door, reported as the door reports it.
      condensationDepth = partition.depth;
      provenance = provenanceFor partition.depth;
    };

  # ── THE ORDERED FOLD ──
  # Positional authority is the substrate's: contributions combine in the order they were
  # DECLARED, and the fold reads no strength annotation. A priority is content — a value carrying
  # meaning — and interpreting one here would make the substrate read a payload it has no
  # business reading, and would make a value's authority depend on a lattice that cannot cross an
  # evaluation boundary. Where module-system content reaches this fold the module system has
  # already resolved its own priorities, and what arrives is an ordered list.
  #
  # NOTHING IS SORTED, DEDUPED OR FILTERED BY RANK. The list's order IS the authority, so a fold
  # that reordered it would be answering a different question.
  #
  # ★ AND A CONTESTED GATE IS NAMED, NEVER SILENT. A contribution whose gating atom is UNDEFINED
  # is not admitted — an undefined gate does not derive its contribution — and it is not dropped
  # either: it comes back in `contested`, which is the third value carried out to the caller
  # rather than collapsed into "absent". A caller that treats `contested` as empty has decided
  # that; a caller that never sees it had the decision made for them.
  foldContributions =
    {
      model,
      contributions,
      op,
      init,
    }:
    let
      byVerdict = builtins.groupBy (c: model.verdict c.atom) contributions;
      admitted = byVerdict."true" or [ ];
    in
    {
      value = prelude.foldl' op init admitted;
      contested = byVerdict."undefined" or [ ];
      inherit admitted;
    };
in
{
  inherit
    solve
    provenanceFor
    foldContributions
    ;
}
