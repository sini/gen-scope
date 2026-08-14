# The engine's CEILING cells, and the two accumulator constructions that have one.
#
# WHY THIS IS NOT A TEST. A stack overflow is an ABORT, not a throw: `tryEval` does not catch it,
# so no in-language assertion can observe one and neither test runner can host these cells. The
# only instrument that reads an abort is the EXIT CODE of a separate evaluation. The `tryUnforced`
# arm below is the demonstration of exactly that, run as a cell rather than asserted in prose.
#
# ── THE CLAIM UNDER TEST, AND WHY THE COMPARISON IS THE INSTRUMENT ──
# `foldl'` forces its accumulator to weak head normal form — for a record, the record and not its
# fields — so a field written every round and read in none accumulates one update thunk per
# round, and forcing that chain at the end spends stack per link. The engine's answer is
# `forceFields`, which derives the forcing from the accumulator's OWN fields rather than from a
# maintained list of them. Every arm below runs THE SAME LOOP over THE SAME ACCUMULATOR at THE
# SAME round count, and differs only in whether that function is applied — so a green forced arm
# beside an aborting unforced one is a controlled comparison on the construction itself, not an
# inference from two different programs.
#
# ── THE ACCUMULATOR IS THE ENGINE'S OWN SHAPE, INCLUDING ITS TRAP ──
# It carries an attrset field the control flow reads STRICTLY and a scalar counter the control
# flow never reads. A strict read is itself a force, but only of the field read — so the strict
# arm is force-free on `set` and the counter chains anyway. That is "a partial fix is measured
# indistinguishable from no fix" arising BY CONSTRUCTION rather than by omission, and it is the
# shape the engine's own alternating fixpoint carries (`innerConverged` is read by no control
# flow).
#
# ── TWO SIGNATURES, NOT ONE, AND AN ENGINE ARMED FOR ONE MISSES THE OTHER ──
#   unforcedCall     — the counter chains through a FUNCTION APPLICATION. Each link is a call, so
#                      the descent exhausts the evaluator's call-depth guard first:
#                      `stack overflow; max-call-depth exceeded`.
#   unforcedOperator — the counter chains through `+`, which is an OPERATOR and increments no
#                      call-depth counter. There is no guard in front of this one: it goes
#                      straight to the C stack, `stack overflow (possible infinite recursion)`.
# The two abort at different round counts through different mechanisms, so a sweep testing for
# one label reads the other as a green run.
#
# ── THE ENGINE'S OWN LOOPS ARE HERE TOO, AND THEIR BOUND IS STATED ──
# `rounds` drives the least-model round loop and `outer` the alternating fixpoint. Their cost is
# rounds × rules, so the round counts the unforced arms abort at are hours away on either of
# them: the engine arms are run at the sizes that are reachable, and what they establish is that
# the engine's loops are green where they were run — not that they were driven into the cliff
# region. The forced/unforced comparison above is what carries the construction claim.
#
# RUN (per cell — the sweep is the shell script):
#   nix-instantiate --eval --strict --json \
#     --arg n 46000 --argstr arm unforcedOperator ./ci/bench/engine-ceiling.nix
{
  n ? 20000,
  arm ? "forced",
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
  graph = import "${fetch "gen-graph"}/lib" { inherit prelude; };
  # The identity authority the library injects into its minting module. Built on the prelude this
  # file derives rather than on the one inside gen-schema's own lock, which is the same simplification
  # the root shim states and is inert here: the authority's closure is `builtins`-only.
  schema = import "${fetch "gen-schema"}/lib" {
    inherit prelude;
    merge = import "${fetch "gen-merge"}/lib" { inherit prelude; };
    algebra = import "${fetch "gen-algebra"}/lib";
  };
  s = import ../../lib { inherit prelude graph schema; };

  bound = builtins.genList (i: i) n;
  pad =
    p: i:
    let
      t = toString i;
    in
    p + builtins.substring 0 (6 - builtins.stringLength t) "000000" + t;

  # A FUNCTION APPLICATION, so each link of a chain built with it opens a call frame.
  succ = x: x + 1;

  # The step, parameterized by HOW the unread counter's link is built — a named application or a
  # bare operator. The two spellings compute the same number and chain through different
  # machinery, which is the whole distinction between the signatures. `set` is written every
  # round and read strictly by the guard; `tick` is written every round and read by nothing.
  mkStep = link: acc: {
    set = acc.set // {
      ${toString acc.depth} = true;
    };
    depth = acc.depth + 1;
    done = acc.set == { };
    tick = if link == "call" then succ acc.tick else acc.tick + 1;
  };
  init = {
    set = { };
    depth = 0;
    done = false;
    tick = 0;
  };

  # The loop, run several ways over ONE accumulator. The unforced arms pass `_: null`, which is
  # `iterateBounded`'s own "nothing to force" spelling — so what differs between the arms is the
  # forcing and the link, and never the loop.
  run =
    strict: link: builtins.deepSeq (prelude.iterateBounded strict (mkStep link) init bound).tick n;

  # A chain of `n` atoms whose bodies are BINARY, so the program routes to the round loop and
  # the loop runs one round per atom.
  roundsProgram = s.mkProgram {
    rules = map (
      i:
      if i == 0 then
        { head = pad "a" i; }
      else
        {
          head = pad "a" i;
          pos = [
            (pad "a" (i - 1))
            (pad "a" 0)
          ];
        }
    ) (builtins.genList (i: i) n);
  };

  # A negation chain: the alternating fixpoint's outer loop runs d/2 + 2 rounds on it.
  outerProgram = s.mkProgram {
    rules = map (
      i:
      if i == 0 then
        { head = pad "a" i; }
      else
        {
          head = pad "a" i;
          neg = [ (pad "a" (i - 1)) ];
        }
    ) (builtins.genList (i: i) n);
  };
in
if arm == "forced" then
  run s.forceFields "operator"
else if arm == "unforcedCall" then
  run (_: null) "call"
else if arm == "unforcedOperator" then
  run (_: null) "operator"
else if arm == "tryUnforced" then
  # THE UNCATCHABILITY CELL. If `tryEval` contained this class the arm would return
  # `{ success = false; }`; it does not, and the process dies with the same signature the bare
  # arm produces. Read beside `catchControl`, which shows the catcher works in this evaluation.
  builtins.tryEval (run (_: null) "operator")
else if arm == "rounds" then
  let
    m = s.leastModelRounds (s.reduct roundsProgram { });
  in
  builtins.deepSeq m.derived {
    inherit (m) converged;
    inherit (m.work) arm rounds;
  }
else if arm == "outer" then
  let
    m = s.wellFoundedModel outerProgram;
  in
  builtins.deepSeq m.trueAtoms {
    inherit (m) converged outerRounds arm;
    true' = prelude.length m.trueAtoms;
  }
else if arm == "refuseUnknownField" then
  # ★ AN ARGUMENT-ARITY ERROR IS NOT CONTAINED BY `tryEval`. `mkRule`'s pattern refuses an
  # unknown field by name — the interpreter names the argument and even suggests the intended
  # one — but the refusal kills the evaluation rather than answering `{ success = false; }`, so
  # it is read here, off an exit code, for the same reason the aborts above are. The message is
  # on stderr and the sweep matches it.
  builtins.deepSeq (s.mkRule {
    head = "f";
    negs = [ "x" ];
  }) 1
else if arm == "refuseConjunctiveOnUnaryArm" then
  # The unary arm's refusal IS catchable, so the suite pins that it fires. What the suite cannot
  # read is the MESSAGE — `tryEval` discards it — and a refusal that does not name the surface
  # and the offending rule is not a named refusal. That text is read here.
  builtins.deepSeq (s.leastModelUnary (
    s.mkProgram {
      rules = [
        { head = "a"; }
        { head = "b"; }
        {
          head = "c";
          pos = [
            "a"
            "b"
          ];
        }
      ];
    }
  )) 1
else if arm == "okControl" then
  1
else if arm == "catchControl" then
  builtins.tryEval (throw "catchControl")
else
  throw "unknown arm ${arm}"
