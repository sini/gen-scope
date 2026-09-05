# THE DECLARED RELATION'S INPUT TYPE — what each entry taking one admits, and what it refuses.
#
# `gen-graph` ships the declared relation's CONSTRUCTOR, its shared TYPE and the discriminator over
# that type, and ships no refusal helper beside them on purpose: a refusal minted there would name
# `gen-graph` for a defect at this library's door. So the discriminator is shared and the message is
# not — each entry states its own, naming itself — and until a consumer calls it, a discriminator is
# a guard nobody calls.
#
# TWO ENTRIES, AND THEY ARE NOT THE SAME ENTRY. `foldEquations`' formal is REQUIRED and total, so
# absence cannot be expressed there at all and every value it receives is a candidate relation.
# `eval`'s carries a THIRD STATE — `null` says no declaration was supplied and this evaluation was
# not constructed under the contract — which is a sequencing fact rather than a relation, so it is
# not put to the guard and its survival is a cell here.
#
# ── WHY EVERY CELL BELOW READS A SELF-ACQUISITION ──
# `self-v` acquires the node's OWN record, which the `self.node` seam guard permits unconditionally
# because `reader == target` crosses no edge. That is not incidental: under a cross-node read the
# seam guard throws too, so a refusal cell written over one would pass with THIS guard entirely
# removed — the seed would be caught by the neighbouring mechanism and the cell would separate
# nothing. On a self-acquisition the only throw available is the input type's.
#
# ── THE MESSAGES ARE NEXT DOOR ──
# `builtins.tryEval` catches a throw and discards its text, so what these cells assert is the FACT
# of a refusal; the CONTENT — which entry named itself, and which detail arm fired — is in
# `../tests-error.nix`, where a cell can assert it.
{
  genScope,
  genGraph,
  ...
}:
let
  # One node and no edges. The contract is about what the entry ACCEPTS, so the smallest substrate
  # that can answer an attribute is the right fixture: a richer graph would add ways for a cell to
  # go red that have nothing to do with the type.
  scope = genScope.buildRoots {
    parentGraph = genScope.vertex "solo";
    decls.solo.v = 1;
    types = { };
  };

  attributes = {
    children = _self: _id: { };
    self-v = self: id: (self.node id).decls.v;
  };

  equations = builtins.mapAttrs (name: compute: {
    inherit name compute;
    kind = if name == "children" then "nta" else "synthesized";
    readsAttrs = [ ];
    stratum = if name == "children" then "structural" else "resolution";
  }) attributes;

  contracted = import ./_fixtures/declared.nix { inherit genGraph scope; };

  foldWith =
    declaredDependencies:
    genScope.foldEquations {
      inherit scope declaredDependencies;
      schedule = { inherit equations; };
      parseParent = _: null;
    };

  evalWith = declaredDependencies: genScope.eval { inherit scope attributes declaredDependencies; };

  # THE SEEDS, both of them shapes a caller really produces.
  # (1) The bare relation — what every call site wrote before the contract existed.
  bare = _: [ ];
  # (2) The FORGERY: the constructor's own field names, correctly behaving, and no tag. A STRUCTURAL
  # predicate admits it; the nominal one does not, and that difference is the whole reason the
  # discriminator is nominal.
  forged = {
    index = { };
    dependencies = _: [ ];
  };
in
{
  flake.tests.declared-relation-contract = {

    # ══ THE FOLD ══
    # A bare relation is refused AT THE ENTRY — forced there rather than left to a first attribute
    # read, so the entry the caller named is the entry that answers. With the guard removed this
    # expression is a sealed record and the cell reads `true`.
    test-foldEquations-refuses-an-uncontracted-relation = {
      expr = (builtins.tryEval (foldWith bare)).success;
      expected = false;
    };
    # THE CONTROL the cell above rests on: the same call over a contracted relation is not refused.
    # Without it a guard that refused everything would satisfy the cell above.
    test-control-foldEquations-accepts-the-contracted-relation = {
      expr = (builtins.tryEval (foldWith (contracted { }))).success;
      expected = true;
    };
    # And the fold RUNS over it, which the control above cannot see: that one forces the seal to
    # WHNF, this one applies a body through the reader binding the relation is projected into. A
    # projection taken off the wrong field would pass the control and fail here.
    test-control-the-contracted-fold-answers = {
      expr = (foldWith (contracted { })).eval.get "solo" "self-v";
      expected = 1;
    };
    # ★ THE SEAL ROUND-TRIPS. The relation is sealed as the CONTRACTED VALUE rather than as the
    # projected function, so a consumer can hand the field it read straight back to the entry it
    # must call. Sealed as a bare function it would be refused by name with nowhere to be sent —
    # this cell is what holds the seal and the entry to the same type.
    test-the-sealed-relation-round-trips-into-the-entry = {
      expr = (foldWith (foldWith (contracted { })).declaredDependencies).eval.get "solo" "self-v";
      expected = 1;
    };

    # ══ THE EVALUATOR ══
    # The delegate refuses on its own account. It is reached directly by callers who never touch the
    # fold, so a contract living only at the fold would leave this door open — which is the measured
    # class this whole clause exists for. With the guard removed the bare relation arms the reader
    # binding, the self-acquisition is permitted, and the cell reads `true`.
    test-eval-refuses-an-uncontracted-relation = {
      expr = (builtins.tryEval ((evalWith bare).get "solo" "self-v")).success;
      expected = false;
    };
    test-control-eval-accepts-the-contracted-relation = {
      expr = (evalWith (contracted { })).get "solo" "self-v";
      expected = 1;
    };
    # ★ THE THIRD STATE SURVIVES. `null` is not a candidate relation and is not put to the guard: an
    # evaluation outside the contract pays nothing and refuses nothing. A guard asked to adjudicate
    # absence would have to admit `null`, and would then admit it at `foldEquations` too, where the
    # formal is required and absence is exactly what may not be expressed. This throws if that
    # happens.
    test-control-eval-with-no-relation-at-all-still-answers = {
      expr = (evalWith null).get "solo" "self-v";
      expected = 1;
    };

    # ══ THE PREDICATE IS NOMINAL, NOT STRUCTURAL ══
    # The forgery carries the constructor's field names and behaves correctly, and is refused
    # anyway, because what it lacks is the tag only those constructors write. A structural predicate
    # admits it and the cell reads `true`.
    test-a-forged-relation-of-the-right-shape-is-refused = {
      expr = (builtins.tryEval ((evalWith forged).get "solo" "self-v")).success;
      expected = false;
    };
    # THE SEED, MEASURED LIVE: the forgery really is a working relation, so the cell above is about
    # PROVENANCE and not about a value that would have failed anyway.
    test-seed-the-forged-relation-answers-on-its-own-terms = {
      expr = forged.dependencies "solo";
      expected = [ ];
    };
  };
}
