# The demand cascade's run: what a resolver is handed, what the constructor refuses and WHEN, what
# the result says about things that produced nothing, and which claims the schedule reaches.
#
# ★ THE REFUSAL CELLS HERE PIN REACHABILITY, NOT MESSAGES. `tryEval` reports that a refusal fired
# and discards what it said, so no cell in this file can tell one refusal from another; five cells
# reporting `true` are equally satisfied by a construction with one refusal in it. The five
# messages are discriminated by an exit-code sweep instead, and that division is stated here so
# the in-suite half is not read as more than it is.
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
  bottomEmitter = mkKinds [
    (mkKind {
      name = "l";
      resolve = c: _: {
        claims = [
          (mkClaim {
            kind = "l";
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
        kind = "l";
        subject = subjA;
      })
    ];
  };

  quietBottom = mkKinds [
    (mkKind {
      name = "l";
      resolve = _: _: { };
    })
  ];

  quietBottomRun = resolveClaims {
    kinds = quietBottom;
    claims = [
      (mkClaim {
        kind = "l";
        subject = subjA;
      })
    ];
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
    test-reserved-payload-key-refused = {
      expr = didThrow (runWith [
        (mkClaim {
          kind = "leaf";
          subject = subjA;
          _path = [ 9 ];
        })
      ]);
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
    # ★ THE ONE REFUSAL A REPORTED FIELD DOES NOT REACH. Reading `resources` alone — never the
    # trace, never `unrun` — must still refuse an emission made in the schedule's last round, so
    # the cell forces exactly that one field. A run that forced only what it reports would answer
    # `{ }` here and say nothing.
    test-a-bottom-stratum-emission-is-refused-through-the-resources-field-alone = {
      expr = didThrow bottomEmissionRun.resources;
      expected = true;
    };
    test-control-a-bottom-stratum-kind-that-emits-nothing-resolves = {
      expr = succeeds quietBottomRun.resources;
      expected = true;
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
    # Global order across kinds, path-lexicographic within a stratum — including two paths of
    # different lengths, which a comparison that stopped at the shorter one would misorder.
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
    test-the-comparand-is-the-library-without-this-module = {
      expr = builtins.length incumbentNames;
      expected = 80;
    };
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
