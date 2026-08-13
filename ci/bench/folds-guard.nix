# THE FOLD PRECONDITIONS AS EXIT-CODE CELLS — one construction per arm, read by `folds-guard.sh`.
#
# WHY THESE CANNOT BE SUITE CELLS. A fold handed a fragment it is not defined over used to fail
# through the EVALUATOR — `toJSON` on a value containing a function, `attrNames` on a function —
# and neither is a throw. `tryEval` holds `throw` and `assert` and nothing else, so an evaluation
# that ends that way ends the RUNNER: `didThrow` never returns a boolean for a suite to compare,
# and there is no arm of `nix-unit` that can host the cell. What can be read is the evaluator's own
# exit code, which is what this pair reads.
#
# ★ THE UNGUARDED CONSTRUCTIONS BELOW ARE BUILT HERE TO BE MEASURED AND ARE NEVER USED. Each is the
# fold as it stands WITHOUT its precondition, so every guarded arm has a live control in the same
# run: a guarded arm returning cleanly proves nothing unless the same input, through the
# unguarded construction, is measured ending the evaluation.
#
# ★ AND ONE ARM IS THE OPPOSITE CONTROL — `plain-conflict-wrapped`. If the `tryEval` idiom itself
# were broken, every wrapped arm would report an escape and the table would read as a discovery.
# That arm is an ordinary named refusal wrapped the same way, and it must be CAUGHT.
#
# It imports `lib/folds.nix` DIRECTLY, with the prelude and nothing else. That is not a shortcut
# around the library's own entry point: the module takes `{ prelude }` alone, and a bench file that
# had to reach for the graph to build a fold would be reporting that it does not.
{
  arm ? "guarded-wrapped",
}:
let
  lock = builtins.fromJSON (builtins.readFile ../../flake.lock);
  fetch =
    name:
    let
      node = lock.nodes.${name}.locked;
    in
    builtins.fetchTree {
      inherit (node)
        type
        owner
        repo
        rev
        narHash
        ;
    };
  prelude = import "${fetch "gen-prelude"}/lib";
  inherit (import ../../lib/folds.nix { inherit prelude; }) folds;

  inherit (builtins)
    all
    attrNames
    filter
    foldl'
    head
    toJSON
    ;

  didThrow = e: !(builtins.tryEval (builtins.deepSeq e null)).success;

  # ── THE UNGUARDED CONSTRUCTIONS, VERBATIM IN SHAPE FROM WHAT THE PRECONDITIONS REPLACED ──
  unguardedSame =
    key: vs:
    if vs == [ ] then
      throw "unguarded.same: empty fragment list for key '${key}'"
    else if all (v: v == head vs) vs then
      head vs
    else
      throw "unguarded.same: conflicting values for key '${key}': ${toJSON vs}";

  unguardedMergeAttrs =
    key: vs:
    foldl' (
      acc: v:
      let
        dup = filter (k: acc ? ${k}) (attrNames v);
      in
      if dup != [ ] then
        throw "unguarded.mergeAttrs: key '${key}' collision on sub-key(s) ${toJSON dup}"
      else
        acc // v
    ) { } vs;

  unguardedByKey =
    spec: key: vs:
    let
      checkAttr =
        v:
        if builtins.isAttrs v then
          true
        else
          throw "unguarded.byKey: key '${key}' has a non-attrset fragment: ${toJSON v}";
      ok = all checkAttr vs;
      allKeys = prelude.unique (prelude.concatMap attrNames vs);
      foldKey =
        k:
        let
          contributors = filter (v: v ? ${k}) vs;
          values = map (v: v.${k}) contributors;
        in
        spec.${k} "${key}.${k}" values;
    in
    if ok then builtins.listToAttrs (map (k: prelude.nameValuePair k (foldKey k)) allKeys) else { };

  # ── THE FRAGMENTS ──
  # Two fragments carrying functions, built as DISTINCT values: the comparison a fold makes over
  # them is decided by the evaluator's pointer identity, and two literals share no slot.
  fnA = {
    gen = _: "a";
  };
  fnB = {
    gen = _: "b";
  };
  # ONE fragment, listed twice. The same value slot on both sides of the comparison, which is the
  # only way `==` reports agreement between function-bearing values.
  shared =
    let
      v = {
        gen = _: "a";
      };
    in
    [
      v
      v
    ];
  plain = [
    { a = 1; }
    { a = 1; }
  ];
  spec = {
    gen = folds.same;
  };
  unguardedSpec = {
    gen = unguardedSame;
  };

  arms = {
    # The guarded fold: a named refusal, which `tryEval` holds — so the wrapped arm RETURNS.
    guarded-wrapped = didThrow (
      folds.same "k" [
        fnA
        fnB
      ]
    );
    guarded-bare = folds.same "k" [
      fnA
      fnB
    ];
    # The same input through the construction without the precondition.
    unguarded-wrapped = didThrow (
      unguardedSame "k" [
        fnA
        fnB
      ]
    );
    unguarded-bare = unguardedSame "k" [
      fnA
      fnB
    ];

    # The pointer accident, both ways: the guard refuses what the comparison would have "agreed"
    # on only because the caller happened to pass one value slot twice.
    guarded-shared = didThrow (folds.same "k" shared);
    unguarded-shared = builtins.typeOf (unguardedSame "k" shared);

    # OPPOSITE CONTROL: an ordinary refusal, wrapped identically, must be caught.
    plain-conflict-wrapped = didThrow (
      folds.same "k" [
        1
        2
      ]
    );
    # The guard refuses fragments it cannot compare, and nothing else.
    plain-agree = folds.same "k" plain;

    bykey-wrapped = didThrow (folds.byKey spec "k" [ (_: "not a fragment") ]);
    unguarded-bykey-wrapped = didThrow (unguardedByKey unguardedSpec "k" [ (_: "not a fragment") ]);

    mergeattrs-wrapped = didThrow (
      folds.mergeAttrs "k" [
        { a = 1; }
        (_: "not a fragment")
      ]
    );
    unguarded-mergeattrs-wrapped = didThrow (
      unguardedMergeAttrs "k" [
        { a = 1; }
        (_: "not a fragment")
      ]
    );
  };
in
if arms ? ${arm} then
  arms.${arm}
else
  throw "folds-guard.nix: no arm '${arm}' — arms are ${toJSON (attrNames arms)}"
