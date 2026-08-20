# The engine's COST-CLASS cells: one measurement per (fixture family, arm, size), reporting the
# curve the benchmark-acceptance bound is derived from.
#
# ★ THIS PATH IS A FIXED CITATION TARGET. `lib/acceptance.nix` names it as the suite its
# derivation function reads, and `README.md` cites it as the re-run command behind the recorded
# figure. Add arms and shapes; do not rename.
#
# WHAT IT REPORTS AND WHAT IT DOES NOT. It reports the curve. It states no budget and offers no
# figure as one: the engine constrains nothing on cost, and the judge of whether a curve is
# adequate for the fleet the engine is for is a PERSON reading it, once, not a threshold in this
# file. A threshold here would be the shape that was rejected — a cost bound wearing a
# correctness face.
#
# THE ARMS SEPARATE THREE COSTS THAT WOULD OTHERWISE BE READ AS ONE:
#
#   model  — the well-founded model alone. No partition, no door. This is the semantics' own cost
#            and it is the one the round axis belongs to.
#   depth  — the model PLUS the partition door, reporting the condensation depth beside it.
#            ★ It is NOT the door alone, and the difference matters when a figure is quoted:
#            `report` binds the model and `deepSeq`s the whole row on every arm, so the OTHER
#            library's price is the `depth` − `model` DIFFERENCE and never the `depth` reading.
#            Separating the two costs is what these arms are for; the separation is a subtraction,
#            not a column.
#   solve  — the front door: the same, plus the provenance stamp. Measured rather than added up
#            from the two above.
#
# `converged` is on every cell and an unconverged cell is INVALID rather than slow. It is what
# makes the acceptance derivation readable at all: the bound is the greatest depth at which every
# arm completed with `converged=true`, so a cell that returns without converging is not a point
# on the curve.
#
# THE FIXTURE FAMILIES, and why six rather than one axis:
#
#   chain d          — d+1 singleton components in a line. UNARY. Depth d: the deepest
#                      condensation the suite reaches per atom, and the cheapest per depth.
#   cycle d          — ONE positive component of d atoms with no support. Depth 0. The
#                      component-SIZE axis, where the per-node partition arm pays per member.
#   blocks d k       — d/k k-cycles CHAINED. Many small components AND a deep condensation DAG,
#                      which is the shape neither partition arm is linear on.
#   blocksWide d k   — d/k INDEPENDENT k-cycles. Depth 0, many components: the fleet shape.
#   deepContested d  — a negation chain of depth d with a contested pair hung off every level.
#                      Deep AND contested: outer rounds scale with d, and every level whose gate
#                      is true carries two atoms the model must name UNDEFINED. ★ Its rules have
#                      TWO literals each and a POSITIVE arity of one, so it routes to the unary
#                      arm — which is the routing discriminator's whole point read on a live
#                      fixture: reduction deletes the negative literal, and what is left is unary.
#   layers d w k     — d+1 layers of w atoms, every atom above layer 0 carrying a k-ary body from
#                      the layer below. The only genuinely CONJUNCTIVE family at k>1, and the only
#                      fixture that separates body arity from depth.
#
# RUN (per cell — the sweep is the shell script):
#   nix-instantiate --eval --strict --json \
#     --arg d 128 --arg w 1 --arg k 2 --argstr shape chain --argstr arm solve \
#     ./ci/bench/cost-classes.nix
# `nix eval --file` does NOT auto-call a function-headed file.
{
  shape ? "chain",
  d ? 128,
  w ? 1,
  k ? 2,
  arm ? "solve",
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

  ix = m: builtins.genList (i: i) m;
  # Fixed-width names so an id's sort position does not drift with the size of the sweep.
  pad =
    p: i:
    let
      t = toString i;
    in
    p + builtins.substring 0 (6 - builtins.stringLength t) "000000" + t;

  # d+1 atoms in a line: a0 is a fact, every other atom has the previous one as its only body.
  chain = map (
    i:
    if i == 0 then
      { head = pad "a" i; }
    else
      {
        head = pad "a" i;
        pos = [ (pad "a" (i - 1)) ];
      }
  ) (ix (d + 1));

  # One positive cycle with nothing supporting it: every atom is FALSE, and finding that out is
  # the unfounded-set half of the semantics rather than the derivation half.
  ring =
    p: n: base:
    map (i: {
      head = pad p (base + i);
      pos = [ (pad p (base + (if i + 1 < n then i + 1 else 0))) ];
    }) (ix n);

  # r rings of k atoms. `link` joins ring j to ring j-1, which is what turns independent
  # components into a chained condensation DAG.
  rings =
    { link }:
    let
      r = if k <= 0 then 0 else d / k;
    in
    prelude.concatMap (
      j:
      let
        base = j * k;
        body = ring "c" k base;
      in
      if link && j > 0 then
        [
          (
            builtins.head body
            // {
              pos = (builtins.head body).pos ++ [ (pad "c" ((j - 1) * k)) ];
            }
          )
        ]
        ++ builtins.tail body
      else
        body
    ) (ix r);

  # a0 a fact, a_i :- not a_{i-1}: a chain whose every edge is negative, so the model is TOTAL
  # and alternates. The contested pair at each level is the shape with no meaning under the
  # stratified semantics, and it is what the third verdict is for.
  deepContested = prelude.concatMap (
    i:
    (
      if i == 0 then
        [ { head = pad "a" i; } ]
      else
        [
          {
            head = pad "a" i;
            neg = [ (pad "a" (i - 1)) ];
          }
        ]
    )
    ++ [
      {
        head = pad "x" i;
        pos = [ (pad "a" i) ];
        neg = [ (pad "y" i) ];
      }
      {
        head = pad "y" i;
        pos = [ (pad "a" i) ];
        neg = [ (pad "x" i) ];
      }
    ]
  ) (ix (d + 1));

  # d+1 layers of w atoms; every atom above the base carries a k-ary body drawn from the layer
  # below, so arity moves without depth or atom count moving with it.
  layers = prelude.concatMap (
    j:
    map (
      c:
      if j == 0 then
        { head = pad "l" (j * w + c); }
      else
        {
          head = pad "l" (j * w + c);
          pos = map (b: pad "l" ((j - 1) * w + (if b < w then b else w - 1))) (ix k);
        }
    ) (ix w)
  ) (ix (d + 1));

  # An unknown shape refuses as loudly as an unknown arm: a fallback fixture would tag a reading
  # with a family nobody measured.
  rules =
    {
      inherit chain deepContested layers;
      cycle = ring "c" d 0;
      blocks = rings { link = true; };
      blocksWide = rings { link = false; };
    }
    .${shape} or (throw "unknown shape ${shape}");

  program = s.mkProgram { inherit rules; };

  # `deepSeq` over the whole record, so no cell can pass by leaving the expensive field a thunk,
  # and every arm reports the same shape so a row is comparable across arms.
  report =
    extra:
    let
      model = s.wellFoundedModel {
        inherit program;
        interpretation = [ ];
      };
      row = {
        inherit
          arm
          shape
          d
          w
          k
          ;
        atoms = prelude.length program.atoms;
        rules = prelude.length program.rules;
        arity = program.bodyArity;
        inherit (model) outerRounds converged;
        engineArm = model.arm;
        true' = prelude.length model.trueAtoms;
        undefined' = prelude.length model.undefinedAtoms;
        false' = prelude.length model.falseAtoms;
      }
      // extra;
    in
    builtins.deepSeq row row;
in
if arm == "model" then
  report { }
else if arm == "depth" then
  # The door alone. Reported apart so an engine figure never quotes a partitioner's price.
  report { inherit ((graph.condensation program.dependency)) depth; }
else if arm == "solve" then
  let
    solved = s.solve {
      inherit program;
      interpretation = [ ];
    };
  in
  report {
    inherit (solved) condensationDepth;
    warned = prelude.length solved.provenance;
  }
else
  throw "unknown arm ${arm}"
