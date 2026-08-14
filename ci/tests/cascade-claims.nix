# The demand cascade's run: what a resolver is handed, what the constructor refuses and WHEN, what
# the result says about things that produced nothing, and which claims the schedule reaches.
#
# ★ THE REFUSAL CELLS HERE PIN REACHABILITY, NOT MESSAGES. `tryEval` reports that a refusal fired
# and discards what it said, so no cell in this file can tell one refusal from another; five cells
# reporting `true` are equally satisfied by a construction with one refusal in it. What each
# refusal SAYS is asserted in `../tests-error.nix`, on the `testsError` output, where nix-unit's
# `expectedError` can read the text. The division is stated here so the reachability half is not
# read as more than it is.
#
# ★★ THE EAGERNESS CELL IS ABOUT WHERE A REFUSAL FIRES, so it is measured against a construction
# that refuses the same input LATER. `lazilyCanonicalizing` below is the constructor with its kind
# check moved into a field of the returned record — the shape that passes a malformed claim on to
# whoever eventually forces it. It is built here to be measured, never to be used, and the cells
# beside it show it is the same defect and not a different one.
{
  genScope,
  genGraph,
  genPreludeLib,
  lib,
  ...
}:
let
  inherit (genScope)
    mkKind
    mkKinds
    mkClaim
    resolveClaims
    ;

  didThrow = e: !(builtins.tryEval (builtins.deepSeq e null)).success;
  succeeds = e: (builtins.tryEval (builtins.deepSeq e null)).success;
  # Weak head normal form only: an attribute set is already in it, so a refusal bound to a FIELD
  # of the returned record leaves this reporting success.
  survivesWhnf = e: (builtins.tryEval e).success;

  subjA = {
    id_hash = "id-a";
    name = "a-subject";
  };
  subjB = {
    id_hash = "id-b";
    name = "b-subject";
  };

  # ── (a) THE DISCIPLINE FIXTURE ──
  ctxIn = {
    alpha = 1;
    beta = {
      nested = true;
    };
  };

  probe = c: ctx: {
    ctxNames = builtins.attrNames ctx;
    ctxAlpha = ctx.alpha;
    ctxHasResources = ctx ? resources;
    ctxHasWiring = ctx ? wiring;
    ctxHasTrace = ctx ? trace;
    claimNames = builtins.attrNames c;
    # ARMED: the same reading with one field added. The exact-set cell above must reject it, or
    # the equality is satisfied by any superset and the row it discharges is untested.
    claimNamesPlusOne = builtins.attrNames (c // { _extra = true; });
    claimCarriesBookkeeping = c ? _reserved;
  };

  disciplineKinds = mkKinds [
    (mkKind {
      name = "leaf";
      resolve = c: ctx: { resources.leafSeen = probe c ctx; };
    })
    (mkKind {
      name = "comp";
      below = [ "leaf" ];
      resolve = c: ctx: {
        resources.compSeen = probe c ctx;
        claims = [
          (mkClaim {
            kind = "leaf";
            subject = c.subject;
          })
        ];
      };
    })
  ];

  disciplineRun = resolveClaims {
    kinds = disciplineKinds;
    ctx = ctxIn;
    claims = [
      (mkClaim {
        kind = "comp";
        subject = subjA;
        extra = "payload";
      })
    ];
  };

  comp = disciplineRun.resources.comp.compSeen;
  leaf = disciplineRun.resources.leaf.leafSeen;

  # ── THE CASCADE FIXTURE ──
  # A diamond over four strata-bearing kinds plus one that nothing ever claims, and two roots on
  # two subjects: the second subject is claimed and never wired, which is the case a result that
  # drops empty entries cannot express.
  pathKey = c: "at_" + lib.concatMapStringsSep "_" builtins.toString c._path;

  cascadeKindList = [
    (mkKind {
      name = "leaf";
      resolve = c: _: { resources.${pathKey c} = c.subject.id_hash; };
    })
    (mkKind {
      name = "a";
      below = [ "leaf" ];
      resolve = c: _: {
        resources.${pathKey c} = "a";
        wiring.fromA = c._path;
        claims = [
          (mkClaim {
            kind = "leaf";
            inherit (c) subject;
          })
        ];
      };
    })
    (mkKind {
      name = "b";
      below = [ "leaf" ];
      resolve = c: _: {
        resources.${pathKey c} = "b";
        claims = [
          (mkClaim {
            kind = "leaf";
            inherit (c) subject;
          })
        ];
      };
    })
    (mkKind {
      name = "top";
      below = [
        "a"
        "b"
      ];
      resolve = c: _: {
        resources.${pathKey c} = "top";
        claims = [
          (mkClaim {
            kind = "a";
            inherit (c) subject;
          })
          (mkClaim {
            kind = "b";
            inherit (c) subject;
          })
        ];
      };
    })
    (mkKind {
      name = "unused";
      resolve = _: _: { };
    })
  ];

  cascadeKinds = mkKinds cascadeKindList;

  cascadeRun = resolveClaims {
    kinds = cascadeKinds;
    claims = [
      (mkClaim {
        kind = "top";
        subject = subjA;
      })
      (mkClaim {
        kind = "leaf";
        subject = subjB;
      })
    ];
  };

  chainKinds = mkKinds [
    (mkKind {
      name = "c0";
      resolve = c: _: { resources.${pathKey c} = 0; };
    })
    (mkKind {
      name = "c1";
      below = [ "c0" ];
      resolve = c: _: {
        resources.${pathKey c} = 1;
        claims = [
          (mkClaim {
            kind = "c0";
            inherit (c) subject;
          })
        ];
      };
    })
    (mkKind {
      name = "c2";
      below = [ "c1" ];
      resolve = c: _: {
        resources.${pathKey c} = 2;
        claims = [
          (mkClaim {
            kind = "c1";
            inherit (c) subject;
          })
        ];
      };
    })
  ];

  chainRun = resolveClaims {
    kinds = chainKinds;
    claims = [
      (mkClaim {
        kind = "c2";
        subject = subjA;
      })
    ];
  };

  soloRun = resolveClaims {
    kinds = cascadeKinds;
    claims = [
      (mkClaim {
        kind = "leaf";
        subject = subjB;
      })
    ];
  };

  # ── (e) THE ARMED SCHEDULE VARIANT ──
  # A registry record whose declared maximum does not cover its own measure. The registry passes
  # through the run's intake verbatim — that is what the marker is for — so this is the real loop
  # running a schedule with one stratum missing off the top, and not a second implementation of
  # it written here.
  truncatedKinds = cascadeKinds // {
    maxDepth = 1;
  };

  truncatedRun = resolveClaims {
    kinds = truncatedKinds;
    claims = [
      (mkClaim {
        kind = "top";
        subject = subjA;
      })
      (mkClaim {
        kind = "a";
        subject = subjB;
      })
    ];
  };

  # ── (b) THE ARMED CONSTRUCTOR VARIANT ──
  # The constructor with its kind check in a FIELD rather than in the chain's condition. Refuses
  # the same inputs; refuses them somewhere else.
  lazilyCanonicalizing =
    args:
    let
      canon =
        k:
        if builtins.isAttrs k && (k._type or null) == "gen-scope/kind" then
          k.name
        else if builtins.isString k then
          k
        else
          throw "armed variant: `kind` is neither a kind value nor a kind-name string";
    in
    if !(args ? kind) then
      throw "armed variant: missing required field `kind`"
    else if !(args ? subject) then
      throw "armed variant: missing required field `subject`"
    else
      builtins.removeAttrs args [
        "kind"
        "subject"
      ]
      // {
        _type = "gen-scope/claim";
        kind = canon args.kind;
        inherit (args) subject;
        _reserved = [ ];
      };

  leafKindValue = mkKind {
    name = "leaf";
    resolve = _: _: { };
  };

  # ── (d) THE REFUSAL SHAPES ──
  runWith =
    claims:
    resolveClaims {
      kinds = cascadeKinds;
      inherit claims;
    };

  emitsOutsideBelow = mkKinds [
    (mkKind {
      name = "l";
      resolve = _: _: { };
    })
    (mkKind {
      name = "sibling";
      resolve = _: _: { };
    })
    (mkKind {
      name = "t";
      below = [ "l" ];
      resolve = c: _: {
        claims = [
          (mkClaim {
            kind = "sibling";
            inherit (c) subject;
          })
        ];
      };
    })
  ];

  outsideBelowRun = resolveClaims {
    kinds = emitsOutsideBelow;
    claims = [
      (mkClaim {
        kind = "t";
        subject = subjA;
      })
    ];
  };

  legalEmissionRun = resolveClaims {
    kinds = emitsOutsideBelow;
    claims = [
      (mkClaim {
        kind = "l";
        subject = subjA;
      })
    ];
  };

  # A kind at the BOTTOM of the measure that emits anyway. Its emission is created in the last
  # round the schedule has, so nothing downstream selects it and no result field is built from
  # it: it is the one claim in a run that a construction forcing only what it reports would let
  # through. A leaf emitting anything is an error whether or not anyone was going to look.
  #
  # ★ THREE STRATA, NOT ONE. A single-kind registry has `maxDepth = 0`, so its only round is also
  # its last and "the last round" is not distinguished from "the only round" — a construction that
  # forced just the first round would pass. Here the emitter sits at the bottom of a three-deep
  # chain, so the round that strands its emission is the third of three.
  bottomEmitter = mkKinds [
    (mkKind {
      name = "t0";
      resolve = c: _: {
        resources.t0 = "ran";
        claims = [
          (mkClaim {
            kind = "t0";
            inherit (c) subject;
          })
        ];
      };
    })
    (mkKind {
      name = "t1";
      below = [ "t0" ];
      resolve = c: _: {
        resources.t1 = "ran";
        claims = [
          (mkClaim {
            kind = "t0";
            inherit (c) subject;
          })
        ];
      };
    })
    (mkKind {
      name = "t2";
      below = [ "t1" ];
      resolve = c: _: {
        resources.t2 = "ran";
        claims = [
          (mkClaim {
            kind = "t1";
            inherit (c) subject;
          })
        ];
      };
    })
  ];

  bottomEmissionRun = resolveClaims {
    kinds = bottomEmitter;
    claims = [
      (mkClaim {
        kind = "t2";
        subject = subjA;
      })
    ];
  };

  # The same three-stratum shape with the bottom kind emitting nothing: the control that says the
  # cells above are about the stranded emission and not about the fixture being broken.
  quietBottom = mkKinds [
    (mkKind {
      name = "t0";
      resolve = _: _: { resources.t0 = "ran"; };
    })
    (mkKind {
      name = "t1";
      below = [ "t0" ];
      resolve = c: _: {
        resources.t1 = "ran";
        claims = [
          (mkClaim {
            kind = "t0";
            inherit (c) subject;
          })
        ];
      };
    })
    (mkKind {
      name = "t2";
      below = [ "t1" ];
      resolve = c: _: {
        resources.t2 = "ran";
        claims = [
          (mkClaim {
            kind = "t1";
            inherit (c) subject;
          })
        ];
      };
    })
  ];

  quietBottomRun = resolveClaims {
    kinds = quietBottom;
    claims = [
      (mkClaim {
        kind = "t2";
        subject = subjA;
      })
    ];
  };

  # ── A REGISTRY WHOSE MEASURE IS NOT ITS RELATION'S RANK ──
  # The marker vouches for provenance and not for agreement between `kinds`, `depth` and
  # `maxDepth`. Flattened to one stratum, `top` runs and its emissions are created after that
  # round selected its items — so they are never resolved, while every stratum they carry IS in
  # the schedule. A run that derived "not run" from stratum membership would call them scheduled
  # and report their kinds as empty, which is byte-identical to a kind nobody claimed.
  flattenedKinds = cascadeKinds // {
    depth = {
      leaf = 0;
      a = 0;
      b = 0;
      top = 0;
      unused = 0;
    };
    maxDepth = 0;
  };

  flattenedRun = resolveClaims {
    kinds = flattenedKinds;
    claims = [
      (mkClaim {
        kind = "top";
        subject = subjA;
      })
    ];
  };

  # A registry that registers a kind the measure has no entry for. Read where no refusal can
  # follow it — `depth.<kind>` while a child is being built — so it must be decided as data.
  undepthedKinds = cascadeKinds // {
    depth = {
      top = 2;
      a = 1;
      b = 1;
    };
  };

  nonIntegerMaxDepth = cascadeKinds // {
    maxDepth = "two";
  };

  # ── TWO GROUPS, ONE RESOURCE KEY ──
  # A kind with no `dedupKey` puts every claim in its own group, so two claims of that kind
  # writing one key have two authors and no merge rule between them.
  collidingKinds = mkKinds [
    (mkKind {
      name = "dup";
      resolve = _: _: { resources.same = "mine"; };
    })
  ];

  collisionRun = resolveClaims {
    kinds = collidingKinds;
    claims = [
      (mkClaim {
        kind = "dup";
        subject = subjA;
      })
      (mkClaim {
        kind = "dup";
        subject = subjB;
      })
    ];
  };

  singleContributorRun = resolveClaims {
    kinds = collidingKinds;
    claims = [
      (mkClaim {
        kind = "dup";
        subject = subjA;
      })
    ];
  };

  # The same two claims under a kind that DOES declare a grouping and a merge: one group, one
  # author, no collision. Without this the refusal above reads as "two claims of one kind is an
  # error", which it is not.
  foldedKinds = mkKinds [
    (mkKind {
      name = "dup";
      dedupKey = _: "one-group";
      fold = _: vs: builtins.concatStringsSep "+" vs;
      resolve = c: _: { resources.same = c.subject.id_hash; };
    })
  ];

  foldedRun = resolveClaims {
    kinds = foldedKinds;
    claims = [
      (mkClaim {
        kind = "dup";
        subject = subjA;
      })
      (mkClaim {
        kind = "dup";
        subject = subjB;
      })
    ];
  };

  # ── FORGED KIND RECORDS: THE FIELDS THE RUN PROJECTS ──
  # `resolve`, `dedupKey` and `fold` are read at five places in a run, each of them a projection
  # where no refusal can follow — a missing attribute is a type error, and `tryEval` does not hold
  # a type error. So `didThrow` reporting TRUE below is itself the evidence: it can only be true if
  # the failure is a named `throw`, which means the registry decided it while it was still data.
  #
  # ★ THE UNCLAIMED ROWS ARE THE SHARP ONES. Resource combination ranges over every REGISTERED
  # kind, because a kind nobody claimed must still report an empty entry — so one bare record
  # reaches a projection in a run that holds no claim of it at all.
  forgedKind =
    fields:
    {
      _type = "gen-scope/kind";
      name = "ghost";
      below = [ ];
    }
    // fields;

  # Every forged resolver PRODUCES a resource. Without that the fold path is never entered and the
  # `fold` projection is never reached, so a probe over these would report a refusal it never
  # actually asked for.
  ghostResolve = _: _: { resources.ghostRes = "ran"; };

  withForged =
    fields: claimed:
    let
      registry = mkKinds [
        (mkKind {
          name = "host";
          resolve = _: _: { resources.hostRes = "ran"; };
        })
        (forgedKind fields)
      ];
    in
    resolveClaims {
      kinds = registry;
      claims = [
        (mkClaim {
          kind = "host";
          subject = subjA;
        })
      ]
      ++ (
        if claimed then
          [
            (mkClaim {
              kind = "ghost";
              subject = subjA;
            })
          ]
        else
          [ ]
      );
    };

  noResolve = {
    dedupKey = null;
    fold = null;
  };
  noDedupKey = {
    resolve = ghostResolve;
    fold = null;
  };
  noFold = {
    resolve = ghostResolve;
    dedupKey = _: "g";
  };
  wellFormedForged = {
    resolve = ghostResolve;
    dedupKey = null;
    fold = null;
  };

  # ── THE SECOND DOOR: A HAND-BUILT KIND-SET RECORD ──
  # A record carrying the kind-set token is handed to the run WHOLE — `mkKinds` is never called on
  # it, so no entry inside it has met the registration checks. The same four fields a run projects
  # are therefore just as absent here, and reached by the same code.
  #
  # ★ WHICH FIELDS A RUN ACTUALLY PROJECTS WAS ENUMERATED BY SUBSTITUTION, NOT BY READING THE
  # SOURCE: each field replaced in turn by a throw carrying its own name, so a form a scan has no
  # case for — `inherit (…)`, `getAttr`, a map over `attrValues` — fires exactly the same. Four
  # fire: `below`, `resolve`, `dedupKey`, `fold`. `_type` and `name` do not.
  forgedEntry =
    fields:
    {
      _type = "gen-scope/kind";
      name = "unused";
    }
    // fields;

  kindSetWithForged =
    fields:
    cascadeKinds
    // {
      kinds = cascadeKinds.kinds // {
        unused = forgedEntry fields;
      };
    };

  # `unused` is registered and nothing claims it, so the unclaimed arm reaches it only through
  # resource combination — which ranges over every registered kind so an unclaimed one can report
  # an empty entry.
  withForgedKindSet =
    fields: claimed:
    resolveClaims {
      kinds = kindSetWithForged fields;
      claims =
        if claimed then
          [
            (mkClaim {
              kind = "unused";
              subject = subjA;
            })
          ]
        else
          [
            (mkClaim {
              kind = "leaf";
              subject = subjB;
            })
          ];
    };

  entryNoResolve = {
    below = [ ];
    dedupKey = null;
    fold = null;
  };
  entryNoDedupKey = {
    below = [ ];
    resolve = ghostResolve;
    fold = null;
  };
  entryNoFold = {
    below = [ ];
    resolve = ghostResolve;
    dedupKey = _: "g";
  };
  # `below` is read only where an emission is validated, so this entry must emit or the cell
  # reports a refusal it never asked for.
  entryNoBelow = {
    resolve = c: _: {
      claims = [
        (mkClaim {
          kind = "leaf";
          inherit (c) subject;
        })
      ];
    };
    dedupKey = null;
    fold = null;
  };
  entryWellFormed = {
    below = [ ];
    resolve = ghostResolve;
    dedupKey = null;
    fold = null;
  };

  # ── PRESENT BUT NOT APPLICABLE ──
  # A field that exists but cannot be applied is projected, then APPLIED, and applying a
  # non-function is a type error that `tryEval` does not hold. Same predicate as the missing-field
  # class, one scoping on.
  entryResolveNotCallable = entryWellFormed // {
    resolve = 42;
  };
  entryResolveIsAString = entryWellFormed // {
    resolve = "str";
  };
  entryDedupKeyNotCallable = entryWellFormed // {
    dedupKey = 42;
    fold = _: vs: builtins.head vs;
  };
  entryFoldNotCallable = entryWellFormed // {
    dedupKey = _: "g";
    fold = 42;
  };
  # `isFunction` alone would refuse this, and it APPLIES — measured. A check that refused it would
  # be wrong about its own domain, which is the same defect as admitting what does not work.
  entryResolveIsAFunctor = entryWellFormed // {
    resolve = {
      __functor = _: _: _: { resources.ghostRes = "ran"; };
    };
  };
  # THE BOUND, ARMED. Applicable, applied, and still an uncatchable abort — because arity is not
  # decidable in this language. The cell asserts the bound rather than pretending it is closed.
  entryResolveWrongArity = entryWellFormed // {
    resolve = x: x;
  };

  # ── CARRYING `__functor` IS NOT BEING APPLICABLE ──
  # `v arg` on such a set evaluates `v.__functor v arg`, so what is applied is the ATTRIBUTE'S
  # VALUE. A `__functor` holding an integer aborts at the call site exactly as a bare integer does.
  entryFunctorHoldsAnInt = entryWellFormed // {
    resolve = {
      __functor = 42;
    };
  };
  entryFunctorHoldsAString = entryWellFormed // {
    resolve = {
      __functor = "s";
    };
  };
  entryFunctorNestedBad = entryWellFormed // {
    resolve = {
      __functor = {
        __functor = 42;
      };
    };
  };
  # A value whose application diverges: applying it applies it again, forever. Refusing it turns a
  # stack overflow into a named refusal.
  entryFunctorSelfReferential =
    let
      selfRef = {
        __functor = selfRef;
      };
    in
    entryWellFormed // { resolve = selfRef; };
  # THE SECOND BOUND, MEASURED IN THE DIRECTION IT ACTUALLY FALLS. A nested functor DOES apply —
  # measured, it returns — and the one-level check refuses it. The approximation errs toward
  # refusing working input rather than admitting input that aborts, and this cell is that cost
  # stated rather than discovered.
  entryFunctorNestedWorking = entryWellFormed // {
    resolve = {
      __functor = {
        __functor = _: _: ghostResolve;
      };
    };
  };

  kindWith =
    fields:
    mkKinds [
      (mkKind {
        name = "host";
        resolve = _: _: { resources.hostRes = "ran"; };
      })
      (forgedEntry fields)
    ];

  runKindWith =
    fields:
    resolveClaims {
      kinds = kindWith fields;
      claims = [
        (mkClaim {
          kind = "unused";
          subject = subjA;
        })
      ];
    };

  runKindSetWith = fields: withForgedKindSet fields true;

  # ── WHAT A RESOLVER HANDS BACK ──
  # ★ NO FORGERY ANYWHERE BELOW. Every fixture here is an ordinary `mkKind` through the ordinary
  # door — which is what separates this class from the earlier ones, where reaching the defect
  # meant hand-writing a marker record.
  runReturning =
    resolver:
    resolveClaims {
      kinds = mkKinds [
        (mkKind {
          name = "g";
          resolve = resolver;
        })
      ];
      claims = [
        (mkClaim {
          kind = "g";
          subject = subjA;
        })
      ];
    };

  # ── SUBJECT IDENTITY THAT IS PRESENT BUT NOT USABLE ──
  # `id_hash` becomes an attribute name in the result, so a non-string one is a type error where
  # the result is assembled — with no mention of the claim that supplied it.
  runWithSubject =
    subject:
    resolveClaims {
      kinds = mkKinds [
        (mkKind {
          name = "g";
          resolve = _: _: { resources.ok = 1; };
        })
      ];
      claims = [
        (mkClaim {
          kind = "g";
          inherit subject;
        })
      ];
    };

  runWithSubjectId =
    h:
    resolveClaims {
      kinds = mkKinds [
        (mkKind {
          name = "g";
          resolve = _: _: { resources.ok = 1; };
        })
      ];
      claims = [
        (mkClaim {
          kind = "g";
          subject = {
            id_hash = h;
            name = "s";
          };
        })
      ];
    };

  # ── A HAND-BUILT CLAIM DECLARING A VIOLATION THE CONSTRUCTOR WOULD HAVE REFUSED ──
  # `mkClaim` now refuses a shadowing payload where the author is, so the run's own reserved-key
  # arm is reachable only through a record that did not come from it — which is exactly the class
  # the marker cannot vouch for, and exactly why that arm stays.
  handBuiltShadowingClaim = {
    _type = "gen-scope/claim";
    kind = "leaf";
    subject = subjA;
    _reserved = [ "_path" ];
  };

  # ── (f) THE COMPOSITION PREDICATE ──
  # Domain: every registered kind, and for each, every one of its `below` names that is itself
  # registered — which is exactly the set an emission can name. Parameterised on the schedule so
  # the same predicate can be aimed at orders known to violate it.
  positionIn = schedule: stratum: genPreludeLib.indexOf schedule stratum;

  runsStrictlyLater =
    { schedule, kindSet }:
    builtins.all (
      k:
      builtins.all (b: positionIn schedule kindSet.depth.${b} > positionIn schedule kindSet.depth.${k}) (
        builtins.filter (b: kindSet.kinds ? ${b}) kindSet.kinds.${k}.below
      )
    ) (builtins.attrNames kindSet.kinds);

  # Read off the run rather than rebuilt here: a schedule the cell computed for itself would
  # answer about arithmetic, not about the order the loop actually visited.
  observedSchedule = run: lib.unique (map (c: c.stratum) run.trace.claims);

  # ── (g) THE COLLISION SET ──
  cascadeNames = builtins.attrNames (
    import ../../lib/cascade.nix {
      prelude = genPreludeLib;
      graph = genGraph;
    }
  );
  incumbentNames = builtins.filter (n: !(builtins.elem n cascadeNames)) (builtins.attrNames genScope);
  collidesWith = names: builtins.filter (n: builtins.elem n incumbentNames) names;
in
{
  flake.tests.cascade-claims = {
    # ── (a) EMISSION ⊥ CONSUMPTION, BY SIGNATURE ──
    # A resolver sees the claim's own fields plus `_path`, and the caller's context verbatim —
    # never resources, wiring, trace, or any partial view of the run.
    test-comp-ctx-names-verbatim = {
      expr = comp.ctxNames;
      expected = [
        "alpha"
        "beta"
      ];
    };
    test-comp-ctx-value-verbatim = {
      expr = comp.ctxAlpha;
      expected = 1;
    };
    test-comp-ctx-no-resources = {
      expr = comp.ctxHasResources;
      expected = false;
    };
    test-comp-ctx-no-wiring = {
      expr = comp.ctxHasWiring;
      expected = false;
    };
    test-comp-ctx-no-trace = {
      expr = comp.ctxHasTrace;
      expected = false;
    };
    test-comp-claim-names = {
      expr = comp.claimNames;
      expected = [
        "_path"
        "_type"
        "extra"
        "kind"
        "subject"
      ];
    };
    test-leaf-ctx-names-verbatim = {
      expr = leaf.ctxNames;
      expected = [
        "alpha"
        "beta"
      ];
    };
    test-leaf-ctx-no-resolution-view = {
      expr = [
        leaf.ctxHasResources
        leaf.ctxHasWiring
        leaf.ctxHasTrace
      ];
      expected = [
        false
        false
        false
      ];
    };
    test-leaf-claim-names = {
      expr = leaf.claimNames;
      expected = [
        "_path"
        "_type"
        "kind"
        "subject"
      ];
    };

    # ── (c) THE RESOLVER'S VIEW IS THE DOCUMENTED SET, EXACTLY ──
    # The two cells above assert the set; these two arm that assertion and pin what the view does
    # NOT carry. An equality against a list is only a statement about a superset until something
    # shows a superset failing it.
    test-armed-one-extra-field-fails-the-exact-set = {
      expr = comp.claimNamesPlusOne == comp.claimNames;
      expected = false;
    };
    test-resolver-view-strips-the-bookkeeping-channel = {
      expr = [
        comp.claimCarriesBookkeeping
        leaf.claimCarriesBookkeeping
      ];
      expected = [
        false
        false
      ];
    };

    # ── (b) THE KIND IS CANONICALIZED WHERE THE CLAIM IS WRITTEN ──
    # A record is in weak head normal form before any field is looked at, so a check bound to a
    # field is a check that fires wherever something eventually forces it. These cells discriminate
    # the two by forcing to weak head normal form and no further.
    test-non-kind-refused-at-weak-head-normal-form = {
      expr = survivesWhnf (mkClaim {
        kind = 42;
        subject = subjA;
      });
      expected = false;
    };
    test-armed-lazy-canonicalization-survives-weak-head-normal-form = {
      expr = survivesWhnf (lazilyCanonicalizing {
        kind = 42;
        subject = subjA;
      });
      expected = true;
    };
    # The armed variant refuses the same input, only later — so the cell above is about WHERE the
    # refusal fires and not about one construction refusing something the other accepts.
    test-armed-lazy-canonicalization-refuses-under-deep-forcing = {
      expr = didThrow (lazilyCanonicalizing {
        kind = 42;
        subject = subjA;
      });
      expected = true;
    };
    test-control-a-well-formed-claim-survives-weak-head-normal-form = {
      expr = survivesWhnf (mkClaim {
        kind = "leaf";
        subject = subjA;
      });
      expected = true;
    };
    test-missing-kind-refused-at-weak-head-normal-form = {
      expr = survivesWhnf (mkClaim {
        subject = subjA;
      });
      expected = false;
    };
    test-missing-subject-refused-at-weak-head-normal-form = {
      expr = survivesWhnf (mkClaim {
        kind = "leaf";
      });
      expected = false;
    };
    test-kind-value-canonicalizes-to-its-name = {
      expr =
        (mkClaim {
          kind = leafKindValue;
          subject = subjA;
        }).kind;
      expected = "leaf";
    };
    test-kind-name-string-passes-through = {
      expr =
        (mkClaim {
          kind = "leaf";
          subject = subjA;
        }).kind;
      expected = "leaf";
    };
    # A kind record whose own name is not a string denotes no attribute, and the name is what
    # every later read indexes by.
    test-kind-value-with-a-non-string-name-refused = {
      expr = survivesWhnf (mkClaim {
        kind = {
          _type = "gen-scope/kind";
          name = 42;
        };
        subject = subjA;
      });
      expected = false;
    };

    # ── (d) THE FIVE REFUSALS ARE EACH REACHABLE ──
    # Reachability only: `tryEval` discards the message, so these five cells cannot tell one
    # refusal from another. The message discrimination is an exit-code sweep beside this suite.
    test-value-that-is-not-a-claim-refused = {
      expr = didThrow (runWith [
        {
          kind = "leaf";
          subject = subjA;
        }
      ]);
      expected = true;
    };
    test-unknown-kind-refused = {
      expr = didThrow (runWith [
        (mkClaim {
          kind = "nosuchkind";
          subject = subjA;
        })
      ]);
      expected = true;
    };
    # The run's arm, reached through a record the constructor did not build — the constructor
    # refuses this payload itself now, so a fixture built with `mkClaim` would exercise the
    # constructor and report the run's arm as covered when it was never entered.
    test-reserved-payload-key-refused = {
      expr = didThrow (runWith [ handBuiltShadowingClaim ]);
      expected = true;
    };
    test-subject-without-id-hash-refused = {
      expr = didThrow (runWith [
        (mkClaim {
          kind = "leaf";
          subject = {
            name = "no-identity";
          };
        })
      ]);
      expected = true;
    };
    test-emission-outside-the-below-set-refused = {
      expr = didThrow outsideBelowRun;
      expected = true;
    };
    # The registry that produces the refusal above is otherwise a working registry, so that cell
    # is about the emission and not about the fixture being broken.
    test-control-a-claim-of-a-registered-kind-resolves = {
      expr = succeeds legalEmissionRun;
      expected = true;
    };
    test-control-the-cascade-fixture-resolves = {
      expr = succeeds cascadeRun;
      expected = true;
    };
    # ★ THE REFUSAL NO REPORTED FIELD SELECTS. An emission made in the schedule's LAST round is
    # created after that round chose its items, so nothing downstream reads it and no result
    # field is built from it. Each field is forced ON ITS OWN below, because the property is
    # "every way into the result carries the run's refusals" and a cell that forced the whole
    # record would pass on a construction where only one field did.
    test-bottom-stratum-emission-refused-through-resources-alone = {
      expr = didThrow bottomEmissionRun.resources;
      expected = true;
    };
    test-bottom-stratum-emission-refused-through-wiring-alone = {
      expr = didThrow bottomEmissionRun.wiring;
      expected = true;
    };
    test-bottom-stratum-emission-refused-through-unrun-alone = {
      expr = didThrow bottomEmissionRun.unrun;
      expected = true;
    };
    test-bottom-stratum-emission-refused-through-the-trace-alone = {
      expr = didThrow bottomEmissionRun.trace;
      expected = true;
    };
    # The same three-stratum shape whose bottom kind emits nothing: each field returns. Without
    # it the four cells above are satisfied by a run that refuses everything.
    test-control-a-quiet-bottom-stratum-resolves-through-every-field = {
      expr = [
        (succeeds quietBottomRun.resources)
        (succeeds quietBottomRun.wiring)
        (succeeds quietBottomRun.unrun)
        (succeeds quietBottomRun.trace)
      ];
      expected = [
        true
        true
        true
        true
      ];
    };
    # And it is three strata deep, so "the last round" is not the same event as "the only round".
    test-control-the-bottom-emitter-fixture-is-three-strata-deep = {
      expr = quietBottom.maxDepth;
      expected = 2;
    };

    # ── THE ARGUMENTS' OWN SHAPE, DECIDED WHILE THEY ARE STILL DATA ──
    # `claims` is walked by index and a kind's `depth` entry is projected while a child is built.
    # Both are type errors on the wrong shape, and `tryEval` does not contain a type error — so
    # `didThrow` reporting true here is itself the evidence these are named refusals now.
    test-claims-that-are-not-a-list-refused = {
      expr = didThrow (resolveClaims {
        kinds = cascadeKinds;
        claims = "not-a-list";
      });
      expected = true;
    };
    test-registry-registering-a-kind-with-no-depth-entry-refused = {
      expr = didThrow (resolveClaims {
        kinds = undepthedKinds;
        claims = [
          (mkClaim {
            kind = "top";
            subject = subjA;
          })
        ];
      });
      expected = true;
    };
    test-registry-with-a-non-integer-maxdepth-refused = {
      expr = didThrow (resolveClaims {
        kinds = nonIntegerMaxDepth;
        claims = [
          (mkClaim {
            kind = "top";
            subject = subjA;
          })
        ];
      });
      expected = true;
    };
    test-registry-that-is-not-a-kind-set-at-all-refused = {
      expr = didThrow (resolveClaims {
        kinds = "nope";
        claims = [ ];
      });
      expected = true;
    };
    test-control-a-well-formed-registry-and-an-empty-claim-list-resolve = {
      expr = succeeds (resolveClaims {
        kinds = cascadeKinds;
        claims = [ ];
      });
      expected = true;
    };

    # ── ONE RESOURCE KEY, TWO AUTHORS ──
    # Under the refusal's absence the loser is `listToAttrs` first-wins: one contributor's
    # resource disappears with no diagnostic, which is the vanishing class behind a guard.
    test-resource-key-contributed-by-two-groups-refused = {
      expr = didThrow collisionRun;
      expected = true;
    };
    test-control-one-contributor-for-that-key-resolves = {
      expr = singleContributorRun.resources.dup.same;
      expected = "mine";
    };
    # A kind that declares a grouping and a merge puts both claims in ONE group, so there is one
    # author and no collision: the refusal is about ungrouped co-authorship, not about arity.
    test-control-two-claims-in-one-dedup-group-merge-instead-of-colliding = {
      expr = foldedRun.resources.dup.same;
      expected = "id-a+id-b";
    };
    test-control-the-merged-key-records-both-contributors = {
      expr = foldedRun.trace.resources.dup.same.claims;
      expected = [
        [ 0 ]
        [ 1 ]
      ];
    };

    # ── A SHADOWING PAYLOAD IS REFUSED WHERE IT IS WRITTEN ──
    # On the same terms as the three arms beside it, none of which holds a path either.
    test-payload-shadowing-an-engine-field-refused-at-weak-head-normal-form = {
      expr = survivesWhnf (mkClaim {
        kind = "leaf";
        subject = subjA;
        _path = [ 9 ];
      });
      expected = false;
    };
    test-payload-shadowing-the-bookkeeping-channel-refused = {
      expr = survivesWhnf (mkClaim {
        kind = "leaf";
        subject = subjA;
        _reserved = [ "x" ];
      });
      expected = false;
    };
    test-control-an-ordinary-payload-key-is-carried = {
      expr =
        (mkClaim {
          kind = "leaf";
          subject = subjA;
          extra = "payload";
        }).extra;
      expected = "payload";
    };
    test-a-built-claim-declares-no-violation = {
      expr =
        (mkClaim {
          kind = "leaf";
          subject = subjA;
        })._reserved;
      expected = [ ];
    };

    # ── THE FIELDS A RUN PROJECTS ARE DECIDED AT REGISTRATION, NOT AT THE PROJECTION ──
    # Six cells, one per field × claimed/unclaimed. `didThrow` can only report true here if the
    # refusal is a named `throw`: a missing attribute is a type error and `tryEval` does not hold
    # one, so under a construction that projects instead of deciding, these cells do not fail —
    # they take the runner down with them.
    test-kind-record-with-no-resolver-refused-when-claimed = {
      expr = didThrow (withForged noResolve true);
      expected = true;
    };
    test-kind-record-with-no-resolver-refused-when-nothing-claims-it = {
      expr = didThrow (withForged noResolve false);
      expected = true;
    };
    test-kind-record-with-no-dedupkey-refused-when-claimed = {
      expr = didThrow (withForged noDedupKey true);
      expected = true;
    };
    # ★ The widest one: resource combination ranges over every registered kind, so this record is
    # reached in a run that holds no claim of it.
    test-kind-record-with-no-dedupkey-refused-when-nothing-claims-it = {
      expr = didThrow (withForged noDedupKey false);
      expected = true;
    };
    test-kind-record-with-no-fold-refused-when-claimed = {
      expr = didThrow (withForged noFold true);
      expected = true;
    };
    test-kind-record-with-no-fold-refused-when-nothing-claims-it = {
      expr = didThrow (withForged noFold false);
      expected = true;
    };
    # CONTROL — the same forged shape carrying all three fields registers and runs, so the six
    # cells above are about the missing field and not about a marker the registry now rejects.
    test-control-a-forged-record-carrying-all-three-fields-runs = {
      expr = (withForged wellFormedForged true).resources.ghost;
      expected = {
        ghostRes = "ran";
      };
    };
    # ── THE SAME QUESTION ON THE DOOR THAT SKIPS REGISTRATION ──
    # A kind-set record is handed over whole, so nothing inside it met the registration checks.
    # Eight cells: four projected fields × claimed/unclaimed. `didThrow` reporting true is again
    # the evidence — a missing attribute is a type error and `tryEval` does not hold one.
    test-kind-set-entry-with-no-resolver-refused-when-claimed = {
      expr = didThrow (withForgedKindSet entryNoResolve true);
      expected = true;
    };
    test-kind-set-entry-with-no-resolver-refused-when-nothing-claims-it = {
      expr = didThrow (withForgedKindSet entryNoResolve false);
      expected = true;
    };
    test-kind-set-entry-with-no-dedupkey-refused-when-claimed = {
      expr = didThrow (withForgedKindSet entryNoDedupKey true);
      expected = true;
    };
    test-kind-set-entry-with-no-dedupkey-refused-when-nothing-claims-it = {
      expr = didThrow (withForgedKindSet entryNoDedupKey false);
      expected = true;
    };
    test-kind-set-entry-with-no-fold-refused-when-claimed = {
      expr = didThrow (withForgedKindSet entryNoFold true);
      expected = true;
    };
    test-kind-set-entry-with-no-fold-refused-when-nothing-claims-it = {
      expr = didThrow (withForgedKindSet entryNoFold false);
      expected = true;
    };
    test-kind-set-entry-with-no-below-refused-when-claimed = {
      expr = didThrow (withForgedKindSet entryNoBelow true);
      expected = true;
    };
    test-kind-set-entry-with-no-below-refused-when-nothing-claims-it = {
      expr = didThrow (withForgedKindSet entryNoBelow false);
      expected = true;
    };
    # ── APPLICABILITY IS DECIDED WHERE PRESENCE IS ──
    # Eight cells, four shapes × both doors. A field that exists but cannot be applied reproduces
    # the missing-field predicate exactly: read where no refusal follows, type error, no name.
    test-resolve-that-is-not-callable-refused-at-the-registration-door = {
      expr = didThrow (runKindWith entryResolveNotCallable);
      expected = true;
    };
    test-resolve-that-is-not-callable-refused-at-the-pass-through-door = {
      expr = didThrow (runKindSetWith entryResolveNotCallable);
      expected = true;
    };
    test-resolve-that-is-a-string-refused-at-the-registration-door = {
      expr = didThrow (runKindWith entryResolveIsAString);
      expected = true;
    };
    test-resolve-that-is-a-string-refused-at-the-pass-through-door = {
      expr = didThrow (runKindSetWith entryResolveIsAString);
      expected = true;
    };
    test-dedupkey-that-is-not-callable-refused-at-the-registration-door = {
      expr = didThrow (runKindWith entryDedupKeyNotCallable);
      expected = true;
    };
    test-dedupkey-that-is-not-callable-refused-at-the-pass-through-door = {
      expr = didThrow (runKindSetWith entryDedupKeyNotCallable);
      expected = true;
    };
    test-fold-that-is-not-callable-refused-at-the-registration-door = {
      expr = didThrow (runKindWith entryFoldNotCallable);
      expected = true;
    };
    test-fold-that-is-not-callable-refused-at-the-pass-through-door = {
      expr = didThrow (runKindSetWith entryFoldNotCallable);
      expected = true;
    };
    # CONTROL — a callable attribute set is NOT refused, at both doors. `isFunction` reports false
    # for it and this evaluator applies it, so a check written on `isFunction` alone would refuse
    # an input that works. These two cells are what stop that check from being written.
    test-control-a-functor-resolver-is-not-refused-at-either-door = {
      expr = [
        (succeeds (runKindWith entryResolveIsAFunctor))
        (succeeds (runKindSetWith entryResolveIsAFunctor))
      ];
      expected = [
        true
        true
      ];
    };

    # ── CARRYING `__functor` IS NOT BEING APPLICABLE ──
    # The attribute's VALUE is what gets applied, so a set carrying a non-function `__functor`
    # aborts at the same site a bare integer does. Refusing on the attribute's presence alone was
    # the same defect as `isFunction`, pointed the other way.
    test-functor-holding-an-int-refused-at-the-registration-door = {
      expr = didThrow (runKindWith entryFunctorHoldsAnInt);
      expected = true;
    };
    test-functor-holding-an-int-refused-at-the-pass-through-door = {
      expr = didThrow (runKindSetWith entryFunctorHoldsAnInt);
      expected = true;
    };
    test-functor-holding-a-string-refused-at-the-registration-door = {
      expr = didThrow (runKindWith entryFunctorHoldsAString);
      expected = true;
    };
    test-functor-holding-a-string-refused-at-the-pass-through-door = {
      expr = didThrow (runKindSetWith entryFunctorHoldsAString);
      expected = true;
    };
    test-functor-nesting-a-non-function-refused = {
      expr = didThrow (runKindWith entryFunctorNestedBad);
      expected = true;
    };
    # A value whose application diverges is refused at REGISTRATION instead of exhausting the call
    # depth. ★ ASSERTED AT WEAK HEAD NORMAL FORM, AND ON THE REGISTRY RATHER THAN ON A RUN, because
    # both of the obvious spellings are unfalsifiable: deep-forcing the registry walks the
    # self-reference forever, and running the cascade under a construction that ADMITTED this value
    # overflows the evaluator — which `tryEval` does not contain, so the cell would not fail, it
    # would vanish from the report along with everything after it. Forcing the registration chain
    # alone reaches the refusal and nothing else, so a construction that admits this value makes
    # this cell FAIL rather than disappear.
    test-self-referential-functor-refused-at-registration = {
      expr = survivesWhnf (kindWith entryFunctorSelfReferential);
      expected = false;
    };
    # ★ THE BOUND, IN THE DIRECTION IT FALLS. A nested functor APPLIES — measured, it returns — and
    # the one-level check refuses it. Exact applicability is not decidable by any terminating
    # predicate: the `__functor` chain is unbounded and can refer to itself, so a walk would
    # diverge and a depth ceiling would be a number nobody can justify. This cell is the cost of
    # that choice, asserted rather than described; if the approximation ever changes it goes red.
    test-a-nested-functor-that-would-apply-is-refused-and-that-is-the-bound = {
      expr = didThrow (runKindWith entryFunctorNestedWorking);
      expected = true;
    };
    # CONTROL — a hand-built kind-set record whose entries are well formed still passes through.
    # The pass-through is the door's whole purpose; the check is about what comes through it.
    test-control-a-hand-built-kind-set-with-sound-entries-runs = {
      expr = (withForgedKindSet entryWellFormed true).resources.unused;
      expected = {
        ghostRes = "ran";
      };
    };
    # CONTROL — the two hand-modified registries this suite already relies on still pass, so the
    # new check does not close the door the schedule and measure cells are measured through.
    test-control-the-hand-modified-registries-still-pass-the-door = {
      expr = [
        (succeeds truncatedRun.unrun)
        (succeeds flattenedRun.unrun)
      ];
      expected = [
        true
        true
      ];
    };

    # CONTROL — the ordinary door requires all three, so a cooperative caller pays nothing: a kind
    # declaring neither grouping nor merge still registers and still runs.
    test-control-a-constructed-kind-declaring-no-dedup-still-runs = {
      expr = cascadeRun.resources.leaf;
      expected = {
        at_0_0_0 = "id-a";
        at_0_1_0 = "id-a";
        at_1 = "id-b";
      };
    };

    # ── WHAT A RESOLVER HANDS BACK IS DECIDED WHERE IT IS RETURNED ──
    # THE LOUD HALF: a present container of the wrong type is read by `attrNames` or `imap0`, which
    # is a type error carrying no library, no kind and no path. `didThrow` reporting true is the
    # evidence it is a named refusal now.
    test-resources-that-is-a-list-refused = {
      expr = didThrow (
        runReturning (
          _: _: {
            resources = [
              1
              2
            ];
          }
        )
      );
      expected = true;
    };
    test-resources-that-is-a-string-refused = {
      expr = didThrow (runReturning (_: _: { resources = "s"; }));
      expected = true;
    };
    test-wiring-that-is-a-string-refused = {
      expr = didThrow (runReturning (_: _: { wiring = "s"; }));
      expected = true;
    };
    test-claims-that-is-an-int-refused = {
      expr = didThrow (runReturning (_: _: { claims = 42; }));
      expected = true;
    };
    # ★ THE SILENT HALF, AND IT IS THE WORSE ONE. A resolver returning a list, a number or null is
    # a type error nowhere: every field is read through an `or` default, so all three fire and the
    # claim contributes nothing — with no throw and no report, byte-identical to a resolver that
    # returned an empty set deliberately. The control two cells down is that identical output.
    test-a-result-that-is-a-list-refused = {
      expr = didThrow (runReturning (_: _: [ 1 ]));
      expected = true;
    };
    test-a-result-that-is-an-int-refused = {
      expr = didThrow (runReturning (_: _: 42));
      expected = true;
    };
    test-a-result-that-is-null-refused = {
      expr = didThrow (runReturning (_: _: null));
      expected = true;
    };
    # CONTROL — a resolver that legitimately produces nothing still runs, and its output is what
    # the silent half was indistinguishable from.
    test-control-a-resolver-returning-an-empty-set-still-runs = {
      expr = (runReturning (_: _: { })).resources.g;
      expected = { };
    };
    test-control-a-resolver-producing-resources-still-runs = {
      expr = (runReturning (_: _: { resources.ok = 1; })).resources.g;
      expected = {
        ok = 1;
      };
    };
    # ★ THE LIMIT ON THE OTHER SIDE OF THE SAME BOUNDARY, ASSERTED RATHER THAN ONLY WRITTEN DOWN.
    # The answer's SHAPE is decided here; the VALUES inside it are not. A function-valued fragment
    # is CARRIED, not refused — which is what "conformance of a fragment is not established here"
    # means, stated as a cell so that building plain-data conformance later has to change something
    # visible rather than quietly narrowing a documented limit.
    test-a-function-valued-fragment-is-carried-and-that-is-the-limit = {
      expr = builtins.isFunction (runReturning (_: _: { resources.frag = (x: x); })).resources.g.frag;
      expected = true;
    };
    # The two halves of the boundary in one place: the same run that carries that fragment refuses
    # a `resources` whose container is wrong.
    test-control-the-shape-half-still-refuses-beside-it = {
      expr = didThrow (runReturning (_: _: { resources = [ 1 ]; }));
      expected = true;
    };

    # CONTROL — the three containers in their legitimate forms, including `wiring` as a LIST, which
    # the accumulator accepts and a naive attrset-only check would have refused.
    test-control-wiring-as-a-list-is-accepted = {
      expr =
        builtins.attrNames
          (runReturning (
            c: _: {
              wiring = [
                {
                  inherit (c) subject;
                  wiring.port = 1;
                }
              ];
            }
          )).wiring;
      expected = [ "id-a" ];
    };

    # ── AN IDENTITY THAT IS PRESENT BUT NOT USABLE AS ONE ──
    # `id_hash` becomes an attribute name when the result is keyed by subject, so a non-string one
    # aborts where the result is assembled rather than where the claim was written.
    test-subject-id-hash-that-is-a-list-refused = {
      expr = didThrow (runWithSubjectId [ 1 ]);
      expected = true;
    };
    test-subject-id-hash-that-is-an-int-refused = {
      expr = didThrow (runWithSubjectId 42);
      expected = true;
    };
    test-control-a-string-id-hash-runs = {
      expr = builtins.attrNames (runWithSubjectId "id-a").wiring;
      expected = [ "id-a" ];
    };

    # ── A REFUSAL MUST BE ABLE TO RENDER ITS OWN SUBJECT ──
    # ★★ EVERY SUBJECT IN THE FIVE CELLS BELOW CARRIES NO `name` AND NO `rendered` — unlike the
    # identity cells further up, which supply a name and are the known-member controls. That is the shape the identity arm
    # exists to catch, and it is the shape that makes the arm's own message unbuildable: the
    # renderer fell through to the raw `id_hash`, so constructing the diagnostic coerced the very
    # non-string the diagnostic was about. A refusal that cannot render its subject is the same
    # abort wearing a different stack, and a fixture that supplies a `name` never sees it.
    test-bare-subject-with-a-list-id-hash-refuses-rather-than-aborting = {
      expr = didThrow (runWithSubject {
        id_hash = [ 1 ];
      });
      expected = true;
    };
    test-bare-subject-with-an-int-id-hash-refuses-rather-than-aborting = {
      expr = didThrow (runWithSubject {
        id_hash = 42;
      });
      expected = true;
    };
    test-bare-subject-with-an-attrset-id-hash-refuses-rather-than-aborting = {
      expr = didThrow (runWithSubject {
        id_hash = {
          a = 1;
        };
      });
      expected = true;
    };
    test-bare-subject-with-a-null-id-hash-refuses-rather-than-aborting = {
      expr = didThrow (runWithSubject {
        id_hash = null;
      });
      expected = true;
    };
    # A non-string `name` is a SECOND route into the same interpolation: the renderer prefers `name`
    # over `id_hash`, so a subject carrying both unrenderable reaches it through the earlier arm.
    test-a-non-string-name-does-not-break-the-refusal = {
      expr = didThrow (runWithSubject {
        id_hash = [ 1 ];
        name = [ 9 ];
      });
      expected = true;
    };
    # KNOWN-MEMBER CONTROLS — a renderable `name` or `rendered` makes the message buildable, which
    # is why the with-`name` fixture never exposed the defect.
    test-control-a-subject-with-a-name-still-refuses = {
      expr = didThrow (runWithSubject {
        id_hash = [ 1 ];
        name = "has-a-name";
      });
      expected = true;
    };
    test-control-a-subject-with-rendered-still-refuses = {
      expr = didThrow (runWithSubject {
        id_hash = 42;
        rendered = "has-rendered";
      });
      expected = true;
    };

    # ── A DIAGNOSTIC MUST NOT RENDER A VALUE IT DID NOT CHOOSE ──
    # `toJSON` aborts on anything containing a function at any depth, so a message that renders
    # caller data can kill the evaluation it was written to explain.
    test-a-kind-that-is-not-a-string-refuses-before-the-lookup = {
      expr = didThrow (runWith [
        {
          _type = "gen-scope/claim";
          kind = [ 1 ];
          subject = subjA;
          _reserved = [ ];
        }
      ]);
      expected = true;
    };
    test-a-reserved-channel-holding-a-function-still-refuses = {
      expr = didThrow (runWith [
        {
          _type = "gen-scope/claim";
          kind = "leaf";
          subject = subjA;
          _reserved = [ (x: x) ];
        }
      ]);
      expected = true;
    };
    test-a-dedupkey-returning-a-function-still-refuses = {
      expr = didThrow (resolveClaims {
        kinds = mkKinds [
          (mkKind {
            name = "g";
            dedupKey = _: (x: x);
            fold = _: vs: builtins.head vs;
            resolve = _: _: { resources.ok = 1; };
          })
        ];
        claims = [
          (mkClaim {
            kind = "g";
            subject = subjA;
          })
        ];
      });
      expected = true;
    };
    # CONTROL — a dedupKey returning a plain non-string still refuses, and one returning a string
    # still runs, so the cell above is about the RENDERING and not about the check.
    test-control-a-dedupkey-returning-an-int-refuses = {
      expr = didThrow (resolveClaims {
        kinds = mkKinds [
          (mkKind {
            name = "g";
            dedupKey = _: 42;
            fold = _: vs: builtins.head vs;
            resolve = _: _: { resources.ok = 1; };
          })
        ];
        claims = [
          (mkClaim {
            kind = "g";
            subject = subjA;
          })
        ];
      });
      expected = true;
    };
    test-control-a-dedupkey-returning-a-string-runs = {
      expr =
        (resolveClaims {
          kinds = mkKinds [
            (mkKind {
              name = "g";
              dedupKey = _: "k";
              fold = _: vs: builtins.head vs;
              resolve = _: _: { resources.ok = 1; };
            })
          ];
          claims = [
            (mkClaim {
              kind = "g";
              subject = subjA;
            })
          ];
        }).resources.g;
      expected = {
        ok = 1;
      };
    };

    # ── A MEASURE THAT IS NOT THE RELATION'S RANK STRANDS CLAIMS, AND THEY ARE NAMED ──
    # The marker vouches for provenance, not for agreement between `kinds`, `depth` and
    # `maxDepth`. What the run reports is what it SETTLED, so a claim it created and left is
    # named — the reading a stratum-membership proxy loses, because every stratum here is in the
    # schedule and the proxy would call the stranded claims scheduled.
    test-a-flattened-measure-strands-claims-and-names-them = {
      expr = map (i: i.kind) flattenedRun.unrun;
      expected = [
        "a"
        "b"
      ];
    };
    # The pair of readings a caller needs to tell the two cases apart: the kind's entry is empty
    # AND a claim of it is named. Under the proxy the first held and the second did not, which is
    # byte-identical to a kind nobody claimed.
    test-a-stranded-kind-is-empty-and-named-at-the-same-time = {
      expr = [
        (flattenedRun.resources.a == { })
        (builtins.elem "a" (map (i: i.kind) flattenedRun.unrun))
      ];
      expected = [
        true
        true
      ];
    };
    # A kind nobody claimed is empty and NOT named, which is what makes the pair discriminating.
    test-an-unclaimed-kind-is-empty-and-not-named = {
      expr = [
        (flattenedRun.resources.unused == { })
        (builtins.elem "unused" (map (i: i.kind) flattenedRun.unrun))
      ];
      expected = [
        true
        false
      ];
    };
    test-control-the-same-registry-built-properly-strands-nothing = {
      expr = [
        cascadeRun.unrun
        (builtins.attrNames cascadeRun.resources.a)
      ];
      expected = [
        [ ]
        [ "at_0_0" ]
      ];
    };

    # ── (e) THE SCHEDULE REACHES EVERY CLAIM ──
    test-unrun-is-empty-on-the-cascade-fixture = {
      expr = cascadeRun.unrun;
      expected = [ ];
    };
    test-unrun-is-empty-on-the-chain-fixture = {
      expr = chainRun.unrun;
      expected = [ ];
    };
    test-unrun-is-empty-on-a-single-leaf = {
      expr = soloRun.unrun;
      expected = [ ];
    };
    # ARMED: one stratum off the top of the schedule. The claim it would have run is REPORTED,
    # and the run returns — a refusal here would destroy the only record of what was missed.
    test-armed-truncated-schedule-reports-the-unreached-claim = {
      expr = map (i: {
        inherit (i) kind stratum;
      }) truncatedRun.unrun;
      expected = [
        {
          kind = "top";
          stratum = 2;
        }
      ];
    };
    test-armed-truncated-schedule-does-not-throw = {
      expr = succeeds truncatedRun;
      expected = true;
    };
    # And it is not merely dead: the strata the schedule does cover still run, so the cell above
    # reports a claim the loop skipped rather than a loop that did nothing.
    test-armed-truncated-schedule-still-runs-its-scheduled-strata = {
      expr = map (c: c.kind) truncatedRun.trace.claims;
      expected = [
        "a"
        "leaf"
      ];
    };

    # ── (f) A BACKWARD EMISSION IS UNCONSTRUCTIBLE ──
    # Every kind an emission can name is a registered member of the emitter's `below` set, and
    # every such kind sits strictly later in the run order. The schedule is read off the run.
    test-every-emission-nameable-kind-runs-strictly-later = {
      expr = runsStrictlyLater {
        schedule = observedSchedule cascadeRun;
        kindSet = cascadeKinds;
      };
      expected = true;
    };
    test-composition-holds-on-the-chain-fixture = {
      expr = runsStrictlyLater {
        schedule = observedSchedule chainRun;
        kindSet = chainKinds;
      };
      expected = true;
    };
    # ARMED, two ways: the predicate must reject the reverse of the order the run used, and must
    # reject an order that ascends the measure. Without these it is satisfied by any schedule at
    # all on a registry whose `below` sets happen to be empty.
    test-armed-the-reversed-order-fails-the-predicate = {
      expr = runsStrictlyLater {
        schedule = lib.reverseList (observedSchedule cascadeRun);
        kindSet = cascadeKinds;
      };
      expected = false;
    };
    test-armed-an-ascending-order-fails-the-predicate = {
      expr = runsStrictlyLater {
        schedule = [
          0
          1
          2
        ];
        kindSet = cascadeKinds;
      };
      expected = false;
    };
    # The order the run visited, so the three cells above are anchored to a stated sequence
    # rather than to whatever the fixture produced.
    test-the-observed-order-descends-the-measure = {
      expr = observedSchedule cascadeRun;
      expected = [
        2
        1
        0
      ];
    };
    # Global order across kinds, path-lexicographic within a stratum. ★ WHAT THIS DOES NOT COVER:
    # the comparator's prefix arm. Every different-length pair sorted together below differs at
    # index 0, so the length comparison is never the deciding branch — and no fixture can make it
    # one, because two paths are prefix-related only when one is an ancestor of the other and a
    # child is created after the round that resolves its parent has already chosen its items.
    test-claims-are-emitted-in-global-schedule-order = {
      expr = map (c: c.path) cascadeRun.trace.claims;
      expected = [
        [ 0 ]
        [
          0
          0
        ]
        [
          0
          1
        ]
        [
          0
          0
          0
        ]
        [
          0
          1
          0
        ]
        [ 1 ]
      ];
    };

    # ── ABSENCE MEANS NOT REGISTERED ──
    # A registered kind nothing claimed, and a claimed subject nothing wired, both keep an entry.
    # The controls beside them are what stop "everything is empty" from passing.
    test-registered-kind-with-no-claim-keeps-an-empty-entry = {
      expr = cascadeRun.resources.unused;
      expected = { };
    };
    test-control-a-claimed-kind-has-a-non-empty-entry = {
      expr = builtins.attrNames cascadeRun.resources.top;
      expected = [ "at_0" ];
    };
    test-an-unregistered-kind-name-is-absent-from-the-result = {
      expr = cascadeRun.resources ? nosuchkind;
      expected = false;
    };
    test-resources-are-total-on-the-registry = {
      expr = builtins.attrNames cascadeRun.resources;
      expected = builtins.attrNames cascadeKinds.kinds;
    };
    test-subject-with-no-wiring-keeps-its-entry = {
      expr = cascadeRun.wiring."id-b".byKind;
      expected = { };
    };
    test-subject-with-no-wiring-keeps-its-subject = {
      expr = cascadeRun.wiring."id-b".subject;
      expected = subjB;
    };
    test-control-a-wired-subject-has-a-non-empty-bykind = {
      expr = builtins.attrNames cascadeRun.wiring."id-a".byKind;
      expected = [ "a" ];
    };
    test-the-wiring-trace-is-total-on-the-same-domain = {
      expr = builtins.attrNames cascadeRun.trace.wiring;
      expected = builtins.attrNames cascadeRun.wiring;
    };
    test-the-resource-trace-is-total-on-the-same-domain = {
      expr = builtins.attrNames cascadeRun.trace.resources;
      expected = builtins.attrNames cascadeRun.resources;
    };
    test-a-subject-no-claim-named-is-absent-from-the-wiring = {
      expr = cascadeRun.wiring ? "id-never";
      expected = false;
    };

    # ── (g) THE RENAMED SURFACE AGAINST THE LIBRARY IT LANDS IN ──
    # The comparand is the library's exports MINUS this module's own, so the check is about what
    # was already there and not about the names this module just added.
    test-the-renamed-surface-collides-with-nothing = {
      expr = collidesWith [
        "mkClaim"
        "resolveClaims"
        "Claim"
      ];
      expected = [ ];
    };
    # ARMED: the predicate fires on names that ARE in the comparand, so an empty result above is
    # a measurement rather than a predicate that could not match.
    test-armed-the-collision-predicate-fires = {
      expr = collidesWith [
        "resolve"
        "leastModel"
      ];
      expected = [
        "resolve"
        "leastModel"
      ];
    };
    # 84 rather than 80: the fold vocabulary, the stratification driver, the minting entry and the
    # cold fold are each a module of their own, so `folds`, `stratify`, `mintStrata` and
    # `foldEquations` are part of the library's surface WITHOUT being one of this module's names —
    # which is exactly what an incumbent is. The figure is a baseline over the library's export
    # surface and re-derives whenever that surface grows.
    test-the-comparand-is-the-library-without-this-module = {
      expr = builtins.length incumbentNames;
      expected = 84;
    };
    # Four: the registration and run doors, and nothing else. The consumer accessors that used to
    # sit beside them reconstructed a list the run already computed, and the run publishes it now —
    # so reading one subject's wiring is an attribute lookup with no surface of its own. This cell
    # is the module's inventory, and an export it does not list is an export nothing measured.
    test-this-module-exports-exactly-its-four-names = {
      expr = cascadeNames;
      expected = [
        "mkClaim"
        "mkKind"
        "mkKinds"
        "resolveClaims"
      ];
    };
  };
}
