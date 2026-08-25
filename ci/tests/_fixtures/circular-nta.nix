# THE CIRCULAR-NTA GRAMMAR — one spawned subtree, one declared-circular attribute taken over it,
# and the two seeded variants whose refusal TEXTS are asserted next door.
#
# NOT A SUITE. It sits under `_fixtures/` because the tree importer ignores any path containing
# `/_`, so this file is reached only by the suites that import it and never as a flake module.
#
# WHY IT IS SHARED. The convergence cells and the refusal cells are the same grammar seen twice:
# `flake.tests` can assert THAT a seeded violation refuses, and only `flake.testsError` can assert
# WHICH refusal fired. A second copy of the grammar would let the two halves drift, and the claim
# this fixture exists to carry is that ONE grammar buys both carriers at once.
#
# ── WHAT THE COMBINATION IS ──
# Circular attributes and node spawning are two separate extensions past Knuth (1968), whose own
# condition is purely structural — "the semantic rules are well defined if and only if no directed
# graph D(T) contains an oriented cycle" (printed 135) — and each extension carries its own
# soundness condition:
#
#   the DOMAIN carrier, for spawning — a ranked kind vocabulary every expansion STRICTLY
#   descends. The strictness is gen's own (`mkKind`'s registered rank, refused at registration):
#   the primary's ordering — Krishnan & Van Wyk 2012, Lemma 4, reported via Söderberg & Hedin
#   2013 §7 printed 320 — is NON-INCREASING, equal-order steps permitted and named (constant
#   tree creation sequences), so gen is the stricter of the two and owes its strictness to the
#   registry, never to them;
#
#   the VALUES carrier, for circularity — §4.1, printed 311: "a lattice of bounded height, that the
#   semantic function is monotonic, and that a bottom value is provided as the starting point of
#   the fixed-point iteration".
#
# TAKEN TOGETHER THEY MEET AT ONE SET. The node set the DOMAIN carrier bounds IS the index set the
# VALUES carrier's lattice is taken over — the members below are spawned, and the lattice is the
# pointwise powerset over exactly them. Neither carrier alone says anything about that meeting:
# without the kind order the index set is not known to be finite, and without the declared lattice a
# finite index set still admits a step that never ascends.
#
# ── WHY THE LATTICE IS A PRODUCT OVER THE MEMBERS RATHER THAN ONE ATTRIBUTE PER MEMBER ──
# This library's `circular` computes a fixed point per attribute INSTANCE: `prev` is that instance's
# own previous approximation and there is nowhere for a neighbour's to be read from, so two
# instances that read each other re-enter rather than share a round. Iterating a whole SCC of
# instances together is the scheduled convergence fold's work, and the capability sheet's ownership
# table puts that with the scheduler that builds the schedule. What IS expressible here is the SCC
# carried inside one instance over a product carrier — which is what the bounded-height-lattice
# condition quantifies over in the first place, the condition being about the value domain and not
# about how many attributes the domain is spread across.
{ genScope }:
let
  inherit (genScope)
    circular
    mkKind
    mkKinds
    buildRoots
    eval
    foldEquations
    ;

  # ── THE DOMAIN CARRIER: A RANKED VOCABULARY, WITH EVERY EXPANSION DECLARED ON THE KIND IT
  # EXPANDS FROM ──
  # `below` is Krishnan & Van Wyk's order and `spawns` is the expansion written under the key naming
  # what it produces, so `cluster` ⊐ `member` ⊐ `endpoint` ranks 2 ⊐ 1 ⊐ 0 and each expansion
  # strictly descends it. TWO levels rather than one is what makes the descent a CHAIN: a single
  # spawn exercises one comparison, and a chain is what the rank being a natural-number measure
  # actually buys.
  kinds = mkKinds [
    (mkKind { name = "endpoint"; })
    (mkKind {
      name = "member";
      below = [ "endpoint" ];
      spawns.endpoint = self: id: {
        "${id}-ep" = {
          id = "${id}-ep";
          parent = id;
          decls = {
            inherit ((self.node id).decls) tag;
          };
        };
      };
    })
    (mkKind {
      name = "cluster";
      below = [ "member" ];
      spawns.member =
        self: id:
        builtins.mapAttrs (memberId: spec: {
          id = memberId;
          parent = id;
          decls = spec;
        }) (self.node id).decls.members;
    })
  ];

  # The whole grammar is ONE declared root. Everything else below it arrives through the spawn
  # channel, which is what makes the index set of the lattice a grown set rather than a listed one.
  # The `needs` relation the members carry is a 3-CYCLE, so no evaluation order settles them and the
  # least fixed point is the only value they have.
  scope = buildRoots {
    inherit kinds;
    parentGraph = genScope.vertex "c";
    importGraph = genScope.empty;
    decls.c = {
      members = {
        "c-a" = {
          tag = "a";
          needs = [ "c-b" ];
        };
        "c-b" = {
          tag = "b";
          needs = [ "c-c" ];
        };
        "c-c" = {
          tag = "c";
          needs = [ "c-a" ];
        };
      };
    };
    types.c = "cluster";
  };

  # ── THE VALUES CARRIER: THE POINTWISE POWERSET OVER THE SPAWNED MEMBERS ──
  # Tag sets are attribute sets used as sets, so inclusion is a key test; the order lifts to the map
  # pointwise, with an absent key read as the empty set — which is what makes the empty map a bottom
  # rather than a special case, since every member's component starts at ⊥ and the first step
  # introduces the keys.
  subset = x: y: builtins.all (k: y ? ${k}) (builtins.attrNames x);

  # THE DECLARED HEIGHT IS THE EXACT LENGTH OF THE ASCENDING CHAIN, NOT ROUNDED UP, and the trade
  # that buys is stated rather than left for a reader to hit. This carrier's own height is nine —
  # three members times three tags — and a nine would converge too, and would leave nothing for a
  # cell to falsify. Three is the length of the `needs` cycle, and it is the length of the chain
  # because a tag travels exactly one `needs` edge per step. What the library does not check is "that
  # `height` is large enough for the carrier it names": a height declared at the chain rather than at
  # the lattice is sound for THIS step and would be a false red for a step whose chain is longer.
  carrier = {
    bottom = { };
    leq = a: b: builtins.all (k: (b ? ${k}) && subset a.${k} b.${k}) (builtins.attrNames a);
    height = 3;
    # Pointwise tag-set inclusion is antisymmetric on the values this step produces (equal key
    # sets with `true` values are equal attrsets), so the order is not a quotient and the
    # instance is a shared-round member.
    quotient = false;
  };

  # ── THE STEP, AND WHERE THE SPAWNED SUBTREE ENTERS IT ──
  # BOTH spawned levels participate, and they participate differently. The members are the lattice's
  # INDEX SET: their `needs` relation is the cycle, so the fixed point is what their values are. The
  # endpoints are the SEEDS: each supplies the one tag its member starts from, reached through the
  # same spawn channel the member's own existence came out of.
  #
  # NOTHING HERE READS A KIND OR COMPARES A RANK. The descent was settled at registration, so what
  # this walks is the node set that settlement already bounds.
  stepWith =
    join: self: id: prev:
    let
      members = builtins.attrNames (self.get id "derived-children");
      seed =
        m:
        builtins.foldl' (acc: ep: acc // { ${(self.node ep).decls.tag} = true; }) { } (
          builtins.attrNames (self.get m "derived-children")
        );
      fromNeeds = m: builtins.foldl' (acc: n: acc // (prev.${n} or { })) { } (self.node m).decls.needs;
    in
    builtins.listToAttrs (
      map (m: {
        name = m;
        value = join (seed m) (fromNeeds m);
      }) members
    );

  # The join is a UNION: a member keeps its own seed and gains its neighbours', which is monotone in
  # `prev` because `fromNeeds` is.
  step = stepWith (own: needed: own // needed);

  # THE SEEDED VIOLATION, and it is an authoring mistake rather than a contrivance: the neighbours'
  # contribution REPLACES the member's own seed instead of joining it. Every member is seeded before
  # any neighbour has anything to give, so the first round that finds a non-empty neighbour DROPS a
  # tag the member already held, and the run descends where it declared it would ascend.
  nonMonotoneStep = stepWith (own: needed: if needed == { } then own else needed);

  attributesWith = attrCarrier: f: {
    children = _self: _id: { };
    imports = _self: _id: [ ];
    closure = circular { carrier = attrCarrier; } f;
  };

  evalWith =
    attrCarrier: f:
    eval {
      inherit scope;
      attributes = attributesWith attrCarrier f;
    };

  ev = evalWith carrier step;

  # ── THE SAME GRAMMAR REACHED THROUGH THE COLD FOLD ──
  # `foldEquations` RECEIVES a validated schedule as a value; the circularity test and the stratum
  # assert belong to the scheduler that builds one, and the capability sheet's ownership table puts
  # that elsewhere. So what this leg demonstrates is the combination arriving at the entry a
  # scheduler's output actually reaches — the equations bound to the demand fixpoint, and the sealed
  # accessor's node list read off the evaluator AFTER materialization, which is why it carries the
  # spawned subtree at all.
  #
  # THE EXPANSION IS NOT AN EQUATION AND CANNOT BE ONE. A hand-written spawn channel is refused at
  # the entry, so growth reaches this fold the same way it reaches `eval`: off the registry that
  # travels on the scope.
  equations = builtins.mapAttrs (name: compute: {
    inherit name compute;
    kind = if name == "closure" then "circular" else "synthesized";
    readsAttrs = if name == "closure" then [ "derived-children" ] else [ ];
    stratum = if name == "closure" then "resolution" else "structural";
  }) (attributesWith carrier step);

  ctx = foldEquations {
    inherit scope;
    schedule = { inherit equations; };
    parseParent = id: scope.nodes.${id}.parent or null;
    declaredDependencies = _: [ ];
  };
in
{
  inherit
    kinds
    scope
    carrier
    step
    ev
    ctx
    ;

  converged = ev.get "c" "closure";

  # The carrier with a height ONE SHORT of the chain. The step is unchanged and perfectly monotone,
  # so what this separates is the height term from the monotonicity term.
  shortHeight = (evalWith (carrier // { height = 2; }) step).get "c" "closure";

  nonMonotone = (evalWith carrier nonMonotoneStep).get "c" "closure";
}
