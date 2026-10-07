# THE SECOND TEST OUTPUT — cells whose subject is an ERROR MESSAGE, and why they cannot live in
# `flake.tests`.
#
# Two subjects are here, split from their own suites' non-refusal cells by the SHAPE of the
# assertion rather than by what they are about: the cascade's five refusals, argued below, and the
# minting entry's, whose non-refusal cells are `flake.tests.minting` in `tests/mint.nix` and whose
# fixtures both files read from `tests/_fixtures/mint.nix`.
#
# The cascade refuses five different things about a claim, and a caller must act differently on
# each: a value that is not a claim is a construction bug, an unknown kind is a registration bug, a
# shadowed engine field is a payload bug, a subject with no identity is a data bug, and an emission
# outside the emitter's `below` set is a topology bug. THAT each refuses is a boolean and `tryEval`
# can assert it. WHICH one refused is a claim about the message, and `tryEval` returns
# `{ success, value }` and discards the text — so a suite of five booleans is equally satisfied by a
# construction with one refusal in it, and a reworded message regresses nothing that any cell reads.
# nix-unit's `expectedError` is the assertion for that, and this is where it goes.
#
# ★ WHY A SECOND OUTPUT RATHER THAN A SECOND SUITE. The batch asserter behind `checks.default`
# evaluates `t.expr == t.expected` UNCONDITIONALLY and quantifies over `config.flake.tests` and
# nothing else, so a cell with no `expected` and a throwing `expr` CRASHES that gate rather than
# failing it. Hosting these on `flake.testsError` puts them outside that quantifier while keeping
# them live on the nix-unit path. The split is structural, not conventional: this file is not under
# `./tests`, which is the whole of `testModules`, so nothing about which cells land in which output
# depends on a filter predicate or an ignore convention.
#
#   nix-unit --flake ./ci#tests        # the suites
#   nix-unit --flake ./ci#testsError   # these cells
#
# ★★ `expectedError.msg` IS SEARCHED, NOT WHOLE-MATCHED, so a pattern that names a prefix of the
# message passes against a message that says something else after it — which would make these cells
# agree with the very rewording they exist to catch. Every pattern over a message THIS LIBRARY
# COMPOSES is therefore anchored at both ends and built by ESCAPING THE LITERAL TEXT rather than by
# hand: a hand-written pattern is one forgotten backslash away from a metacharacter matching
# something it was meant to spell.
#
# ★ ONE CELL IS DELIBERATELY OUTSIDE THAT RULE, and it is the arity cell at the end. Its message is
# the EVALUATOR'S, not this library's: it renders the offending value, including a thunk placeholder
# and an attribute set whose printed form is the evaluator's business and not a contract anyone
# here owns. Anchoring it would pin this suite to the internals of a renderer no clause in this
# repository governs, so it matches on the invariant part — the error's own sentence — and says so.
# The rule above is about messages we author; this cell asserts one we merely receive.
{
  lib,
  genScope,
  genPreludeLib,
  genGraph,
  ...
}:
let
  inherit (genScope)
    circular
    mkKind
    mkKinds
    mkClaim
    resolveClaims
    folds
    ;

  # The message, pinned to the byte. `escapeRegex` is the prelude's own and its metacharacter set
  # is byte-identical to nixpkgs', so what is anchored below is the text as written above it.
  exactly = msg: "^" + genPreludeLib.escapeRegex msg + "$";
  # gen-prelude's refusal text, composed with this library's own literal door, field and accepted
  # set (den-hoag-7jltk): every assertion kept, none of gen-prelude's wording copied.
  inherit (genPreludeLib) refusals;

  # The assembly's own fold, over module sets the cell builds: the real module set has no duplicate
  # to refuse, so what the library's evaluation shows is that the merge MERGES, and a synthetic set
  # is what shows it refuses — and names both contributors while doing it.
  mergeSurface = import ../lib/merge-surface.nix { prelude = genPreludeLib; };

  # ── THE CONSTRUCTOR'S RESERVED-LABEL COLLISION ──
  # Both privileged relations are supplied EXPLICITLY, so the label the caller offers has something
  # to collide with. `collide` varies only that label; `ci/tests/build-nodes.nix` runs the same
  # fixture for the boolean half and for the ordinary-label controls.
  collide =
    labels:
    genScope.buildRoots {
      parentGraph = genScope.edge {
        from = "a";
        to = "root";
      };
      importGraph = genScope.edge {
        from = "a";
        to = "lib1";
      };
      edgeGraphs = map (label: {
        inherit label;
        graph = genScope.edge {
          from = "a";
          to = "HIJACKED";
        };
      }) labels;
    };

  # The invariant frame of that refusal, with the two parts a cell varies left to the cell — the
  # rendered label list and the per-label explanation, which are what a caller reads to learn WHICH
  # of the two names they hit and WHICH argument owns it.
  reservedLabelRefusal =
    rendered: explained:
    "gen-scope.buildRoots: `edgeGraphs` carries reserved label(s) ${rendered}: ${explained}. A reserved label is this library's own name for a relation it privileges, and `edgeGraphs` does not extend to it — supply those edges as the argument named, or relabel them.";

  containment = "'P' is the containment relation, whose edges arrive as the `parentGraph` argument";
  importing = "'I' is the import relation, whose edges arrive as the `importGraph` argument";

  subjA = {
    id_hash = "id-a";
    name = "a-subject";
  };

  kinds = mkKinds [
    (mkKind {
      resolve = _: _: { };
    } "l")
    (mkKind {
      resolve = _: _: { };
    } "sibling")
    (mkKind {
      below = [ "l" ];
      resolve = c: _: {
        claims = [
          (mkClaim {
            kind = "sibling";
            inherit (c) subject;
          })
        ];
      };
    } "t")
  ];

  run = claims: resolveClaims { } kinds claims;

  # The reserved-key arm is reachable only through a record the constructor did not build: it
  # refuses a shadowing payload itself, at the site the author wrote. A fixture built with
  # `mkClaim` would exercise the constructor and report this arm as covered without entering it.
  handBuiltShadowingClaim = {
    _type = "gen-scope/claim";
    kind = "l";
    subject = subjA;
    _reserved = [ "_path" ];
  };

  # ── THE EMISSION HALVES OF THE SAME TWO ARMS ──
  # `validate` is shared by intake and emission, but it is CALLED TWICE — once at intake and once
  # per emitted sub-claim (`lib/cascade.nix:756` and `:805`). The two intake cells enter it at the
  # first call site; the two below enter it at the second, and the messages are what tell them
  # apart: a sub-claim's path is `[0,0]` and its refusal carries the emitting claim's own chain.
  #
  # ★ THE SECOND CALL SITE WAS UNREACHED BY ANY CELL, AND THAT IS MEASURED RATHER THAN SUPPOSED:
  # deleting it outright left every cell in `#tests` green, because the intake cells only ever
  # exercise the first, and the below-membership cell above refuses at a later line on a sub-claim
  # that has already passed `validate` cleanly.
  emitKinds =
    bad:
    mkKinds [
      (mkKind {
        resolve = _: _: { };
      } "b")
      (mkKind {
        below = [ "b" ];
        resolve = _: _: { claims = [ bad ]; };
      } "a")
    ];
  runEmit =
    bad:
    resolveClaims { } (emitKinds bad) [
      (mkClaim {
        kind = "a";
        subject = subjA;
      })
    ];

  # Hand-built for the same reason `handBuiltShadowingClaim` is: the constructor refuses a
  # shadowing payload where the author writes it, so a fixture built with `mkClaim` would refuse
  # INSIDE the resolver and report the emission arm as covered without entering it.
  handBuiltShadowingEmission = {
    _type = "gen-scope/claim";
    kind = "b";
    subject = subjA;
    _reserved = [ "_path" ];
  };

  # ── FRAGMENTS FOR THE FOLD PRECONDITIONS ──
  # Two fragments carrying functions, built as DISTINCT values: two literals share no value slot,
  # so the comparison between them is decided by structure and reaches the arm under test.
  fnA = {
    gen = _: "a";
  };
  fnB = {
    gen = _: "b";
  };
  # ── THE SCAN'S STOPPING RULE, WHICH ONLY A MESSAGE CAN REPORT ──
  # The evaluator compares by store path under a CONJUNCTION — the derivation marker AND an
  # `outPath` — so the fixtures vary both terms. With both, the fold reaches its COMPARISON and the
  # conflict renders each fragment by its path. With either one missing, the comparison would be
  # decided field by field, functions included, so the fold refuses first.
  #
  # Why the text and not `tryEval`: for the marker-less pair BOTH outcomes throw — a fold that
  # admitted them would report a conflict between two fragments that render IDENTICALLY, which is a
  # throw and a useless one — so only the message says which fired.
  drvA = {
    type = "derivation";
    outPath = "/nix/store/aaaa";
    passthru = _: 1;
  };
  drvB = {
    type = "derivation";
    outPath = "/nix/store/bbbb";
    passthru = _: 2;
  };
  bareA = {
    outPath = "/nix/store/aaaa";
    passthru = _: 1;
  };
  bareA2 = {
    outPath = "/nix/store/aaaa";
    passthru = _: 2;
  };
  markerOnly1 = {
    type = "derivation";
    passthru = _: 1;
  };
  markerOnly2 = {
    type = "derivation";
    passthru = _: 2;
  };
  # Marker and `outPath` both present, and the path's VALUE is a function — which both readers need
  # and neither can use. The refusal names `outPath` itself, which is what distinguishes this term
  # of the rule from the two above it.
  fnPath1 = {
    type = "derivation";
    outPath = _: 1;
    passthru = _: 1;
  };
  fnPath2 = {
    type = "derivation";
    outPath = _: 2;
    passthru = _: 2;
  };

  # The comparison WITHOUT its precondition, built here to be measured and never used. It is what
  # the fold did before, and its failure is an error of a different CLASS: a `TypeError` from the
  # diagnostic's own `toJSON`, which no `tryEval` holds and which names neither fold nor key.
  unguardedSame =
    key: vs:
    if builtins.all (v: v == builtins.head vs) vs then
      builtins.head vs
    else
      throw "unguarded.same: conflicting values for key '${key}': ${builtins.toJSON vs}";

  # ── THE MINTING FIXTURES ──
  # Shared with `tests/mint.nix`, which holds the same run's non-refusal cells. The two refusal
  # TEXTS are defined there and read here, so the specification of those bytes has one copy.
  mintFixtures = import ./tests/_fixtures/mint.nix {
    inherit
      lib
      genScope
      genPreludeLib
      genGraph
      ;
  };
  inherit (mintFixtures)
    mint
    mintUnderStubIdentity
    mkEmitter
    withKinds
    db
    conflictA
    conflictB
    conflictOtherA
    conflictOtherB
    crossPassConflictA
    crossPassConflictB
    smuggledFieldEmitter
    unresolvedRelatum
    conflictingContribution
    ;

  # ── THE CIRCULAR-NTA FIXTURE ──
  # Shared with `tests/circular-nta.nix`, which holds the same grammar's convergence cells. Both
  # seeded variants are defined there, so the grammar a refusal is earned on and the grammar the
  # clean path converges on are one value rather than two that agree while someone keeps them so.
  circularNta = import ./tests/_fixtures/circular-nta.nix { inherit genScope genGraph; };

  # The shared-round corpus: the tracked model of record's forty fixtures, ported. The refusing
  # fixtures are asserted here — WHICH refusal fires is a claim about a message — and the
  # answering fixtures next door in `tests/scc-round.nix`. Provenance and the hand-derived
  # expectations are documented at the fixture file.
  sccCorpus = import ./tests/_fixtures/scc-corpus.nix { inherit genScope; };
  sccForceGate = import ./tests/_fixtures/scc-force-gate.nix { inherit genScope; };
  firstTransition = import ./tests/_fixtures/first-transition.nix { inherit genScope; };

  # The spawned-visibility witness, shared with `tests/spawned-visibility.nix`: the refusal below
  # is earned on the same graph whose clean path answers there.
  spawnedVisibility = import ./tests/_fixtures/spawned-visibility.nix { inherit lib genScope; };
in
{
  config.flake.testsError.cascade-refusals = {
    # ── THE FIVE ARMS OF THE CLAIM CHAIN, EACH BY ITS OWN TEXT ──
    test-value-that-is-not-a-claim-names-the-constructor = {
      expr = run [
        {
          kind = "l";
          subject = subjA;
        }
      ];
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope.resolveClaims: value at path [0] is not a claim (build it with `mkClaim`)";
      };
    };
    # A `kind` that is not a string is refused BEFORE the registry lookup, and the message says
    # which type arrived: the lookup would otherwise index an attribute set by a list and end the
    # evaluation in the evaluator's words rather than the library's. Hand-built, because `mkClaim`
    # canonicalizes the field and refuses there — a fixture built with the constructor would never
    # reach this arm.
    test-a-kind-that-is-not-a-string-is-named-before-the-lookup = {
      expr = run [
        {
          _type = "gen-scope/claim";
          kind = [ 1 ];
          subject = subjA;
          _reserved = [ ];
        }
      ];
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope.resolveClaims: claim at path [0] carries a `kind` that is a list rather than a string";
      };
    };
    test-unknown-kind-names-the-kind-and-the-path = {
      expr = run [
        (mkClaim {
          kind = "nosuchkind";
          subject = subjA;
        })
      ];
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope.resolveClaims: unknown kind 'nosuchkind' at path [0]";
      };
    };
    test-reserved-payload-key-names-the-keys = {
      expr = run [ handBuiltShadowingClaim ];
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope.resolveClaims: claim at path [0] (kind 'l', subject 'a-subject') shadows reserved payload key(s) [\"_path\"]";
      };
    };
    test-subject-without-identity-names-how-it-renders = {
      expr = run [
        (mkClaim {
          kind = "l";
          subject = {
            name = "no-identity";
          };
        })
      ];
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope.resolveClaims: claim at path [0] (kind 'l') has a subject without id_hash (renders as 'no-identity')";
      };
    };
    # The same two arms, entered from the emission site instead. Each message carries the emitting
    # claim's chain, which is what says the refusal came from `:805` and not from `:756`.
    test-emitted-reserved-payload-key-names-the-keys-and-the-emitter = {
      expr = runEmit handBuiltShadowingEmission;
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope.resolveClaims: claim at path [0,0] (kind 'b', subject 'a-subject') shadows reserved payload key(s) [\"_path\"] (emitted by claim at path [0], kind 'a', subject 'a-subject')";
      };
    };
    test-emitted-subject-without-identity-names-how-it-renders-and-the-emitter = {
      expr = runEmit (mkClaim {
        kind = "b";
        subject = {
          name = "no-id";
        };
      });
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope.resolveClaims: claim at path [0,0] (kind 'b') has a subject without id_hash (renders as 'no-id') (emitted by claim at path [0], kind 'a', subject 'a-subject')";
      };
    };

    # ── THE CASCADE'S OWN REFUSAL, WHICH MUST NOT READ LIKE ANY OF THE FIVE ──
    # It names the emitting kind, the path and the `below` set, because a caller told only "bad
    # emission" has to re-derive all three from a topology the engine has already walked.
    test-emission-outside-below-names-the-emitter-the-path-and-the-set = {
      expr = run [
        (mkClaim {
          kind = "t";
          subject = subjA;
        })
      ];
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope.resolveClaims: kind 't' at path [0] emitted a sub-claim of kind 'sibling' not in its `below` set [\"l\"] (emitted by claim at path [0], kind 't', subject 'a-subject')";
      };
    };

    # ── THE CONSTRUCTOR'S OWN SHADOW REFUSAL ──
    # The run's arm above fires for records it did not build; this one fires where the author is.
    # Both exist and they say different things, which is the whole point of separating them.
    test-constructor-shadow-refusal-names-the-keys-and-the-kind = {
      expr = mkClaim {
        kind = "l";
        subject = subjA;
        _path = [ 9 ];
      };
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope.mkClaim: payload shadows engine field(s) [\"_path\"] (kind 'l')";
      };
    };

    # ── A KIND WITH NO RESOLVER REGISTERS, AND IS REFUSED WHERE IT IS ASKED TO ANSWER ──
    # `resolve` was total at this door, which made the registry unusable as the home of the NODE
    # kind order: a structural kind has no demand semantics and requiring it to invent one imposes a
    # vocabulary it has no use for. So the field became an option and the requirement moved to the
    # consumer — the run, where the claim naming the kind is, and where both the kind and the
    # caller's path can be named. These two cells are that move: the construction is admitted (the
    # control for that sits in `#tests`, where a kind with no resolver registers and ranks), and the
    # demand is refused with a message saying which of the two vocabularies the kind belongs to.
    test-a-claim-on-a-kind-with-no-resolver-is-refused-at-the-run = {
      expr = resolveClaims { } (mkKinds [ (mkKind { } "structural") ]) [
        (mkClaim {
          kind = "structural";
          subject = subjA;
        })
      ];
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope.resolveClaims: kind 'structural' at path [0] declares no `resolve`, so it cannot answer a demand — it is a registered kind and not a demand kind";
      };
    };
    # An explicit null and an omitted field are one case, which is the sentinel's whole cost and its
    # whole point: nothing legitimate is collapsed, because null is not a resolver on any reading.
    test-an-explicitly-null-resolver-is-refused-the-same-way = {
      expr =
        resolveClaims { }
          (mkKinds [
            (mkKind {
              resolve = null;
            } "structural")
          ])
          [
            (mkClaim {
              kind = "structural";
              subject = subjA;
            })
          ];
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope.resolveClaims: kind 'structural' at path [0] declares no `resolve`, so it cannot answer a demand — it is a registered kind and not a demand kind";
      };
    };
    # ── THE SPAWN DECLARATION'S OWN REFUSAL, AT THE DOOR ──
    # A produced kind outside the host's `below` set is what a non-descending expansion IS, and it
    # is refused where the record is built rather than when the spawn fires. That is the whole
    # difference between an expansion that is checked and one that cannot be written.
    test-a-spawn-outside-the-hosts-below-set-is-refused-at-construction = {
      expr = mkKind {
        below = [ "low" ];
        spawns.sideways = _self: _id: { };
      } "host";
      expectedError = {
        type = "ThrownError";
        msg = exactly ''gen-scope.mkKind: kind 'host' declares a spawn producing kind(s) ["sideways"] that its `below` set ["low"] does not carry. A spawn's produced kind must be BELOW its host's, which is what makes the expansion descend a rank that strictly decreases — declare the kind in `below`, or spawn a kind that is already there.'';
      };
    };
    # A spawn declared on a kind with NO `below` at all is the same refusal reached from the other
    # side, and it is the ordinary shape of the mistake: an author writes the builder and forgets
    # that the order is what licenses it.
    test-a-spawn-with-no-below-at-all-is-refused = {
      expr = mkKind {
        spawns.child = _self: _id: { };
      } "host";
      expectedError = {
        type = "ThrownError";
        msg = exactly ''gen-scope.mkKind: kind 'host' declares a spawn producing kind(s) ["child"] that its `below` set [] does not carry. A spawn's produced kind must be BELOW its host's, which is what makes the expansion descend a rank that strictly decreases — declare the kind in `below`, or spawn a kind that is already there.'';
      };
    };
    # A PRESENT but unusable `resolve` is a different reason and says so, mirroring the registry's
    # own two reasons at the construction site. Without this arm the constructor would build a
    # record that its own registry then refuses — the door and the intake disagreeing about the
    # same field.
    test-constructor-refuses-a-resolve-that-cannot-be-applied = {
      expr = mkKind {
        resolve = 5;
      } "k";
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope.mkKind: kind 'k' declares a `resolve` that cannot be applied (it is a int)";
      };
    };
    # LIVE CONTROL, same suite, same constructor: an arm that was ALREADY named and catchable still
    # is. Without it the three cells above are equally consistent with a constructor that refuses
    # everything, and the fix would read as green while having broken the door.
    test-constructor-still-refuses-dedupKey-without-fold-control = {
      expr = mkKind {
        resolve = _: { };
        dedupKey = _: "d";
      } "k";
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope.mkKind: kind 'k' declares `dedupKey` without `fold` (a fold is required to merge grouped fragments)";
      };
    };

    # ── THE REGISTRY NAMES THE ENTRY AND THE FIELD ──
    # A run projects `resolve`, `dedupKey` and `fold` at points where no refusal can follow, so
    # their absence is decided at registration. The message has to carry BOTH coordinates a caller
    # needs — which entry, and which field — because a registry is a list and "one of these is not
    # a kind" leaves the caller to bisect it.
    test-registry-names-the-entry-and-the-missing-field = {
      expr = mkKinds [
        {
          _type = "gen-scope/kind-declaration";
          name = "ghost";
          below = [ ];
          dedupKey = null;
          fold = null;
        }
      ];
      expectedError = {
        type = "ThrownError";
        msg = exactly ''gen-scope.mkKinds: not every entry is a kind declaration: ["entry 0 carries no `resolve` field"]'';
      };
    };

    # ── THE PASS-THROUGH DOOR NAMES THE ENTRY'S KEY, WHICH IS HOW THE RUN INDEXES IT ──
    # A registry handed over whole may hold kinds no fold minted, so the run asks the same question
    # of its entries. The key is what the message carries — not the record's own
    # `name` field — because the key is what a claim's `kind` resolves through, and on a forged
    # record the two need not agree.
    test-pass-through-door-names-the-entry-key-and-the-missing-field = {
      expr = resolveClaims { } {
        kinds = {
          l = {
            _type = "gen-scope/kind";
            name = "l";
            below = [ ];
            depth = 0;
            belowKinds = { };
            dedupKey = null;
            fold = null;
          };
        };
      } [ ];
      expectedError = {
        type = "ThrownError";
        msg = exactly ''gen-scope.resolveClaims: the kind set holds entries that are not minted kinds: ["`l` carries no `resolve` field"]'';
      };
    };

    # ── APPLICABILITY IS NAMED AS SUCH, NOT AS A MISSING FIELD ──
    # A caller whose resolver is an integer and one whose resolver is absent have different bugs
    # and must not read the same message.
    test-a-resolve-that-cannot-be-applied-says-so = {
      expr = mkKinds [
        {
          _type = "gen-scope/kind-declaration";
          name = "l";
          below = [ ];
          resolve = 42;
          spawns = { };
          dedupKey = null;
          fold = null;
          kindValue = null;
        }
      ];
      expectedError = {
        type = "ThrownError";
        msg = exactly ''gen-scope.mkKinds: not every entry is a kind declaration: ["entry 0 carries a `resolve` that cannot be applied"]'';
      };
    };
    # ── THE OTHER NINE REASONS THE REGISTRY CAN GIVE, EACH BY ITS OWN TEXT ──
    # `notAKind` is an eleven-arm chain and its answer is the whole of what either registry door
    # renders, so an arm whose text no cell reads can be reworded into any other arm's and
    # nothing here notices. Each arm names a different field, or a different defect in the same
    # field, and the repair differs with it — which is the rule that decides what gets a pin,
    # applied arm by arm rather than to the chain as a whole.
    test-a-non-record-entry-is-named-by-its-type = {
      expr = mkKinds [ 42 ];
      expectedError = {
        type = "ThrownError";
        msg = exactly ''gen-scope.mkKinds: not every entry is a kind declaration: ["entry 0 is a int rather than a kind declaration"]'';
      };
    };
    # A record that could be a kind but never met the constructor, which is a different repair
    # from a value that could not be one at all.
    test-a-record-without-the-constructor-marker-says-so = {
      expr = mkKinds [ { } ];
      expectedError = {
        type = "ThrownError";
        msg = exactly ''gen-scope.mkKinds: not every entry is a kind declaration: ["entry 0 was not built by `mkKind`"]'';
      };
    };
    test-a-name-that-is-not-a-string-is-named-as-such = {
      expr = mkKinds [
        {
          _type = "gen-scope/kind-declaration";
          name = 42;
        }
      ];
      expectedError = {
        type = "ThrownError";
        msg = exactly ''gen-scope.mkKinds: not every entry is a kind declaration: ["entry 0 carries a `name` that is not a string"]'';
      };
    };
    # The container and its elements are two repairs, and the folds' refusals draw the same line
    # for the same reason.
    test-a-below-that-is-not-a-list-names-the-container = {
      expr = mkKinds [
        {
          _type = "gen-scope/kind-declaration";
          name = "l";
          below = 42;
        }
      ];
      expectedError = {
        type = "ThrownError";
        msg = exactly ''gen-scope.mkKinds: not every entry is a kind declaration: ["entry 0 carries a `below` that is not a list"]'';
      };
    };
    test-a-below-holding-a-non-string-names-the-element = {
      expr = mkKinds [
        {
          _type = "gen-scope/kind-declaration";
          name = "l";
          below = [ 42 ];
        }
      ];
      expectedError = {
        type = "ThrownError";
        msg = exactly ''gen-scope.mkKinds: not every entry is a kind declaration: ["entry 0 carries a `below` holding a name that is not a string"]'';
      };
    };
    # The other two missing-field arms. WHICH field is absent is the coordinate the caller acts
    # on, and the three arms are interchangeable without it: a registry is a list, and a message
    # naming the entry but not the field leaves the caller bisecting a record they already wrote.
    test-a-missing-spawns-names-that-field = {
      expr = mkKinds [
        {
          _type = "gen-scope/kind-declaration";
          name = "l";
          below = [ ];
          resolve = _: _: { };
        }
      ];
      expectedError = {
        type = "ThrownError";
        msg = exactly ''gen-scope.mkKinds: not every entry is a kind declaration: ["entry 0 carries no `spawns` field"]'';
      };
    };
    test-a-missing-dedupkey-names-that-field = {
      expr = mkKinds [
        {
          _type = "gen-scope/kind-declaration";
          name = "l";
          below = [ ];
          resolve = _: _: { };
          spawns = { };
        }
      ];
      expectedError = {
        type = "ThrownError";
        msg = exactly ''gen-scope.mkKinds: not every entry is a kind declaration: ["entry 0 carries no `dedupKey` field"]'';
      };
    };
    test-a-missing-fold-names-that-field = {
      expr = mkKinds [
        {
          _type = "gen-scope/kind-declaration";
          name = "l";
          below = [ ];
          resolve = _: _: { };
          spawns = { };
          dedupKey = null;
        }
      ];
      expectedError = {
        type = "ThrownError";
        msg = exactly ''gen-scope.mkKinds: not every entry is a kind declaration: ["entry 0 carries no `fold` field"]'';
      };
    };
    # ── THE APPLICABILITY ARMS, WHOSE RECORDS THE SUPPORTED CONSTRUCTOR ITSELF BUILDS ──
    # `mkKind` decides that `name` is a string, that `below` is a list of them, and that
    # `dedupKey` and `fold` are declared TOGETHER. It says nothing about what any of the three
    # function-valued fields ARE, so a record carrying an integer where a resolver belongs is
    # built by the constructor and refused after it — which is as true of the `resolve` arm
    # pinned above as of these two. The fixtures below use `mkKind` rather than a forged record
    # to keep that reachable-as-documented reading on the page.
    test-a-dedupkey-that-cannot-be-applied-says-so = {
      expr = mkKinds [
        (mkKind {
          resolve = _: _: { };
          dedupKey = 42;
          fold = _: _: { };
        } "l")
      ];
      expectedError = {
        type = "ThrownError";
        msg = exactly ''gen-scope.mkKinds: not every entry is a kind declaration: ["entry 0 carries a `dedupKey` that is neither null nor applicable"]'';
      };
    };
    test-a-fold-that-cannot-be-applied-says-so = {
      expr = mkKinds [
        (mkKind {
          resolve = _: _: { };
          dedupKey = _: "k";
          fold = 42;
        } "l")
      ];
      expectedError = {
        type = "ThrownError";
        msg = exactly ''gen-scope.mkKinds: not every entry is a kind declaration: ["entry 0 carries a `fold` that is neither null nor applicable"]'';
      };
    };

    # ── A RESOLVER'S ANSWER NAMES THE KIND AND THE PATH ──
    # Both halves. What the evaluator would have said instead — "expected a set but found a list" —
    # names no library, no kind and no path, and for the silent half it says nothing at all.
    test-a-result-that-is-not-a-set-names-the-kind-and-the-path = {
      expr =
        resolveClaims { }
          (mkKinds [
            (mkKind {
              resolve = _: _: [ 1 ];
            } "g")
          ])
          [
            (mkClaim {
              kind = "g";
              subject = {
                id_hash = "id-a";
              };
            })
          ];
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope.resolveClaims: kind 'g' at path [0] returned a list rather than an attribute set";
      };
    };
    test-a-container-of-the-wrong-type-names-which-container = {
      expr =
        resolveClaims { }
          (mkKinds [
            (mkKind {
              resolve = _: _: { resources = [ 1 ]; };
            } "g")
          ])
          [
            (mkClaim {
              kind = "g";
              subject = {
                id_hash = "id-a";
              };
            })
          ];
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope.resolveClaims: kind 'g' at path [0] returned a `resources` that is a list rather than an attribute set";
      };
    };
    # ── THE UNRECOGNISED KEY NAMES ITSELF, THE CLOSED SET, THE KIND AND THE PATH ──
    # A caller reading this acts on it by fixing a spelling, and only the key and the set they may
    # spell tell them which one — a boolean says a resolver was refused and leaves them to find out
    # which of its keys this library does not read.
    test-an-unrecognised-result-key-names-the-key-and-the-closed-set = {
      expr =
        resolveClaims { }
          (mkKinds [
            (mkKind {
              resolve = _: _: { resourcez.ok = 1; };
            } "g")
          ])
          [
            (mkClaim {
              kind = "g";
              subject = {
                id_hash = "id-a";
              };
            })
          ];
      expectedError = {
        type = "ThrownError";
        msg = exactly ''gen-scope.resolveClaims: kind 'g' at path [0] returned unrecognised result key(s) ["resourcez"]: this record is closed to ["resources","wiring","claims"], and a key outside that set is read by nothing here — correct the spelling or drop it'';
      };
    };
    # An identity that is present but cannot be an attribute name is named as such, distinctly from
    # one that is absent — two different bugs for the caller.
    test-an-unusable-id-hash-is-named-distinctly-from-a-missing-one = {
      expr =
        resolveClaims { }
          (mkKinds [
            (mkKind {
              resolve = _: _: { };
            } "g")
          ])
          [
            (mkClaim {
              kind = "g";
              subject = {
                id_hash = [ 1 ];
                name = "s";
              };
            })
          ];
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope.resolveClaims: claim at path [0] (kind 'g') has a subject whose id_hash is a list rather than a string (renders as 's')";
      };
    };

    # ── THE BOUND: ARITY, WHICH NO PREDICATE IN THIS LANGUAGE DECIDES ──
    # A one-argument resolver is applicable, is applied, and its RESULT is applied again — so it
    # fails with the same uncatchable type error a non-function does. It is the one member of the
    # uncatchable class left open, and it is asserted here rather than described, because a bound
    # nothing measures is a bound nobody notices closing or widening.
    test-a-wrong-arity-resolver-is-not-refused-and-this-is-the-bound = {
      expr =
        resolveClaims { }
          (mkKinds [
            (mkKind {
              resolve = x: x;
            } "l")
          ])
          [
            (mkClaim {
              kind = "l";
              subject = {
                id_hash = "id-a";
              };
            })
          ];
      # ★ `tryEval` does NOT hold this — that is the whole reason the class matters — but
      # nix-unit's `expectedError` catches at a level `tryEval` does not reach, which is what
      # makes the bound assertable instead of merely described.
      expectedError = {
        type = "TypeError";
        msg = ".*attempt to call something which is not a function.*";
      };
    };

    # ── LIVE CONTROL, SAME INVOCATION ──
    # An `expected` cell inside an `expectedError` output on purpose: a control has to run in the
    # same invocation as the thing it controls, or it controls nothing. Without it the six cells
    # above are consistent with a cascade that refuses every input it is given.
    test-control-a-legal-claim-resolves = {
      expr =
        (run [
          (mkClaim {
            kind = "l";
            subject = subjA;
          })
        ]).unrun;
      expected = [ ];
    };
  };

  # ── THE FOLD PRECONDITIONS, EACH BY ITS OWN TEXT ──
  # A fold's precondition refusal has to name the fold, the key AND the position in the fragment
  # list, because the caller's fragments all arrived through one call and a message that says only
  # "a fragment" sends them looking through the group by hand. Reachability is asserted in
  # `tests/folds.nix`; these cells are what makes "refuses by name" a claim about anything.
  config.flake.testsError.folds-refusals = {
    test-same-names-the-fold-the-key-and-the-function-position = {
      expr = folds.same "k" [
        fnA
        fnB
      ];
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope.folds.same: key 'k' has a fragment carrying a function, at fragment-list position [0].gen — `==` is not an equivalence over function-bearing values, so whether these fragments agree is not a question this fold can answer";
      };
    };

    # The scan did not descend into a MARKED derivation: the fold reached its comparison, and the
    # conflict renders each fragment by its path. Had the scan descended, this would be the guard's
    # message instead — which is exactly what the next cell asserts for the unmarked pair.
    test-same-conflict-renders-derivations-by-their-paths = {
      expr = folds.same "k" [
        drvA
        drvB
      ];
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope.folds.same: conflicting values for key 'k': [\"/nix/store/aaaa\",\"/nix/store/bbbb\"]";
      };
    };
    # ★ THE SAME SHAPE WITHOUT THE MARKER IS THE GUARD'S, AND THIS IS THE CELL THAT SAYS WHICH.
    # These two share a store path, so a fold that stopped at `outPath` would compare them field by
    # field, decide FALSE on their differing functions, and report a conflict whose two rendered
    # values are the same string — an answer naming a difference the caller cannot see. The
    # evaluator's shortcut is the marker, so the scan's is too.
    test-a-store-path-without-the-derivation-marker-is-refused-by-name = {
      expr = folds.same "k" [
        bareA
        bareA2
      ];
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope.folds.same: key 'k' has a fragment carrying a function, at fragment-list position [0].passthru — `==` is not an equivalence over function-bearing values, so whether these fragments agree is not a question this fold can answer";
      };
    };

    test-mergeattrs-names-the-fragment-type-and-position = {
      expr = folds.mergeAttrs "k" [
        { a = 1; }
        (_: "not a fragment")
      ];
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope.folds.mergeAttrs: key 'k' has a fragment that is a lambda rather than an attribute set, at fragment-list position [1]";
      };
    };

    test-bykey-names-the-fragment-type-and-position = {
      expr = folds.byKey { gen = folds.same; } "k" [ (_: "not a fragment") ];
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope.folds.byKey: key 'k' has a fragment that is a lambda rather than an attribute set, at fragment-list position [0]";
      };
    };

    # ★ AND THE MARKER WITHOUT A PATH IS REFUSED TOO, WHICH IS THE OTHER TERM OF THE CONJUNCTION.
    # The evaluator's shortcut needs both, so these are compared field by field and their conflict
    # message would be assembled by a `toJSON` that ABORTS on the functions inside them. This cell
    # asserting the GUARD's text is what says the scan entered them; a fold that skipped them on the
    # marker alone would not fail this cell, it would end the evaluation.
    test-a-derivation-marker-without-a-store-path-is-refused-by-name = {
      expr = folds.same "k" [
        markerOnly1
        markerOnly2
      ];
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope.folds.same: key 'k' has a fragment carrying a function, at fragment-list position [0].passthru — `==` is not an equivalence over function-bearing values, so whether these fragments agree is not a question this fold can answer";
      };
    };

    # ★ AND THE THIRD TERM, WHOSE POSITION IS ITS OWN EVIDENCE. The refusal points at `[0].outPath`
    # rather than at the interior, so this cell says the scan entered the fragment AND found the
    # defect in the path itself — the one term a marker-and-presence rule reports as satisfied.
    test-a-store-path-that-is-not-a-string-is-refused-by-name = {
      expr = folds.same "k" [
        fnPath1
        fnPath2
      ];
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope.folds.same: key 'k' has a fragment carrying a function, at fragment-list position [0].outPath — `==` is not an equivalence over function-bearing values, so whether these fragments agree is not a question this fold can answer";
      };
    };

    # ★ A PATH IS REFUSED ON ITS OWN GROUND, AND THE MESSAGE IS WHERE THAT SHOWS. These fragments
    # carry NO function, so a refusal naming one would mean the fold found something that is not
    # there; what it names instead is the path, and the reason it gives is about REPORTING rather
    # than about comparing — which is the half of the property this term belongs to.
    test-a-path-is-refused-on-its-own-ground = {
      expr = folds.same "k" [
        { a = /x; }
        { a = /y; }
      ];
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope.folds.same: key 'k' has a fragment carrying a path, at fragment-list position [0].a — reporting a conflict over it would either abort on a path that is not there or copy the caller's path into the store, and a message explaining a refusal may do neither";
      };
    };

    # ── THE KEY, WHICH IS REFUSED BEFORE ANY MESSAGE IS BUILT ──
    # The refusal names the fold, because a caller with five folds in one spec learns nothing from a
    # message that names only the vocabulary.
    test-same-names-itself-when-the-key-is-not-a-string = {
      expr = folds.same 42 [
        1
        2
      ];
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope.folds.same: `key` is a int rather than a string — every refusal this fold can raise names the key, so a key that cannot be rendered ends the evaluation in place of the refusal that was owed";
      };
    };
    # ★ `list` RAISES NOTHING ELSE AT ALL, and it still decides its key: the signature belongs to
    # the vocabulary, so the member with no diagnostics of its own is exactly the one where silent
    # acceptance would make the shared contract untrue.
    test-list-names-itself-when-the-key-is-not-a-string = {
      expr = folds.list [ "not a key" ] [ 1 ];
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope.folds.list: `key` is a list rather than a string — every refusal this fold can raise names the key, so a key that cannot be rendered ends the evaluation in place of the refusal that was owed";
      };
    };

    # ── LIVE CONTROL: WHAT THE PRECONDITION REPLACED, IN THE SAME INVOCATION ──
    # ★ The same fragments through the comparison without its precondition. It fails as a
    # `TypeError` from the diagnostic's own `toJSON` — a different CLASS from every refusal above,
    # holding no fold, no key and no position, and `tryEval` does not hold it at all. Without this
    # row the four cells above are consistent with a fold that always refused this input.
    test-control-the-unguarded-comparison-fails-as-a-type-error = {
      expr = unguardedSame "k" [
        fnA
        fnB
      ];
      expectedError = {
        type = "TypeError";
        msg = ".*cannot convert a function to JSON.*";
      };
    };

    # ── LIVE CONTROL: A FOLD THAT RETURNS ──
    # Without it the suite above is satisfied by a vocabulary that refuses everything.
    test-control-a-legal-fold-returns = {
      expr = folds.same "k" [
        1
        1
      ];
      expected = 1;
    };
  };

  # ── THE ARGUMENT-BINDING CONSTRUCTOR'S REFUSALS (den-hoag-0cmbt U5, K1) ──
  # The admitting half is `flake.tests.argument-binding`. The route set is closed, so a misspelt route
  # is refused rather than minting an id nothing else mints; `definer` is required exactly on
  # `moduleArgs`. The missing-field and non-set refusals are the door table's (`door-checks`).
  config.flake.testsError.argument-binding-refusals =
    let
      thrown = expr: msg: {
        expr = builtins.deepSeq expr expr;
        expectedError = {
          type = "ThrownError";
          msg = exactly msg;
        };
      };
      b =
        r:
        genScope.argumentBinding (
          {
            scope = "root";
            name = "pkgs";
          }
          // r
        );
    in
    {
      test-an-unknown-route-is-refused-by-name =
        thrown (b { supplyRoute = "specialArg"; })
          "gen-scope.argumentBinding: 'specialArg' is not a supply route; the routes are closed (accepted: 'context', 'specialArgs', 'moduleArgs', 'wrap')";
      test-moduleArgs-without-a-definer-is-refused =
        thrown (b { supplyRoute = "moduleArgs"; })
          "gen-scope.argumentBinding: supplyRoute 'moduleArgs' requires a definer, the module that defines the argument";
      test-an-empty-definer-on-moduleArgs-is-refused =
        thrown
          (b {
            supplyRoute = "moduleArgs";
            definer = "";
          })
          "gen-scope.argumentBinding: supplyRoute 'moduleArgs' requires a non-empty definer; an empty one would make every module so keyed one binding";
      test-a-definer-on-another-route-is-refused =
        thrown
          (b {
            supplyRoute = "wrap";
            definer = "/m.nix";
          })
          "gen-scope.argumentBinding: a definer is given on supplyRoute 'wrap', and only 'moduleArgs' takes one";
      test-a-scope-that-is-not-a-string-is-refused = thrown (b {
        scope = {
          name = "root";
        };
        supplyRoute = "context";
      }) "gen-scope.argumentBinding: scope: got set, expected a scope identifier (a string)";
    };

  # ── THE MINTING ENTRY'S REFUSALS ──
  # The same staged run whose non-refusal cells are `flake.tests.minting` in `tests/mint.nix`. They
  # are split by the shape of the assertion and not by subject: these name a MESSAGE, and a cell
  # with a throwing `expr` crashes the batch asserter behind `checks.default` rather than failing.
  config.flake.testsError.minting-refusals = {
    # ── ONE REFUSAL, THREE REACHABLE CAUSES, EACH BY ITS OWN TEXT ──
    # The three differ only in why the lookup misses, which is why they land on one mechanism; each
    # message names the relatum, the label, the kind being minted and the emitting pass, so the three
    # texts are distinct and no cell can pass on another's construction.
    #
    # A same-pass relatum: the node is not in the frozen set, because the set is accumulated from
    # STRICTLY EARLIER strata only. Merging two adjacent strata turns an earlier-pass relatum into a
    # same-pass one and turns success into refusal with no conflicting contribution anywhere — which
    # is meaning being stratification-dependent by construction (ADR-0016 ruling 7).
    test-a-same-pass-relatum-refuses-by-name = {
      expr = mint (withKinds [
        (mkEmitter {
          pass = 0;
          identifier = "db";
          kind = "store";
        })
        (mkEmitter {
          pass = 0;
          identifier = "app";
          kind = "service";
          relata.backing = "db";
        })
      ]);
      expectedError = {
        type = "ThrownError";
        msg = exactly (unresolvedRelatum "db" "backing" "service" 0);
      };
    };
    # The root as a relatum: the root has an identifier by declaration and NO identity (ADR-0016
    # ruling 5). Resolution is identifier-to-identity, so there is nothing for it to resolve to.
    test-the-root-as-a-relatum-refuses-by-name = {
      expr = mint (withKinds [
        db
        (mkEmitter {
          pass = 1;
          identifier = "app";
          kind = "service";
          relata.scope = "root";
        })
      ]);
      expectedError = {
        type = "ThrownError";
        msg = exactly (unresolvedRelatum "root" "scope" "service" 1);
      };
    };
    # A nonexistent identifier: no entry.
    test-a-nonexistent-identifier-refuses-by-name = {
      expr = mint (withKinds [
        db
        (mkEmitter {
          pass = 1;
          identifier = "app";
          kind = "service";
          relata.backing = "nosuchnode";
        })
      ]);
      expectedError = {
        type = "ThrownError";
        msg = exactly (unresolvedRelatum "nosuchnode" "backing" "service" 1);
      };
    };

    # ── WITHIN ONE PASS, CONFLICTING CONTRIBUTIONS REFUSE BY NAME ──
    # Refusal at content merge, exactly as nixpkgs refuses two conflicting definitions of one option.
    # It names the identity, the conflicting key and both emitters' sites, and it reads through a
    # substituted authority so the identity in the message is a text a cell can anchor.
    test-conflicting-same-pass-contributions-refuse-by-name = {
      expr = mintUnderStubIdentity (withKinds [
        conflictOtherA
        conflictOtherB
      ]);
      expectedError = {
        type = "ThrownError";
        msg = exactly (conflictingContribution "host" "site-x" "site-y");
      };
    };

    # ── CROSS-PASS, A SETTLED KEY DISAGREEING REFUSES BY NAME (den-hoag-bp6u) ──
    # Same merge-time mechanism as the cell above; only the two emitters' passes differ (0 and 2
    # rather than both 1), which is what makes the replacement cross-pass rather than same-pass.
    # `tests/mint.nix`'s cross-pass comment marks this RULED and reads the merge arm this refuses.
    test-a-cross-pass-settled-key-disagreement-refuses-by-name = {
      expr = mintUnderStubIdentity (withKinds [
        crossPassConflictA
        crossPassConflictB
      ]);
      expectedError = {
        type = "ThrownError";
        msg = exactly (conflictingContribution "port" "site-cpc-a" "site-cpc-b");
      };
    };

    # ── PERMUTATION, ARM 1b: THE REFUSAL SET MOVES WITH ORDER OR IT DOES NOT ──
    # A permutation cell that compares only successful output passes on a construction whose REFUSAL
    # set moves with order. These two anchor the same literal on the two orders, so a refusal that
    # named its sites in emitter order would fail one of them.
    test-arm-1b-refusal-is-identical-under-within-pass-order-a = {
      expr = mintUnderStubIdentity (withKinds [
        conflictA
        conflictB
      ]);
      expectedError = {
        type = "ThrownError";
        msg = exactly (conflictingContribution "port" "site-a" "site-b");
      };
    };
    test-arm-1b-refusal-is-identical-under-within-pass-order-b = {
      expr = mintUnderStubIdentity (withKinds [
        conflictB
        conflictA
      ]);
      expectedError = {
        type = "ThrownError";
        msg = exactly (conflictingContribution "port" "site-a" "site-b");
      };
    };

    # ── AN UNKNOWN EMITTER FIELD REFUSES BY NAME (den-hoag-mintone-silent-drop-1wjov) ──
    # `smuggledFieldEmitter` is `wellFormedEmitter` (asserted admitted, `tests/mint.nix`'s green
    # twin) plus one field neither `mintOne` nor anything upstream of it reads — standing for a
    # kind-option contribution smuggled onto an emitter record, which is what the measured defect
    # let through silently. The emitter is checked at intake by the shared checks, closed on purpose
    # beyond R5's open record (den-hoag-7gp66 P1), so the refusal is a `throw` naming the door, the
    # field and the accepted set — catchable, where `mintOne`'s closed pattern aborted past `tryEval`.
    test-an-unknown-emitter-field-refuses-by-name = {
      expr = mint (withKinds [ smuggledFieldEmitter ]);
      expectedError = {
        type = "ThrownError";
        msg = exactly (
          refusals.unknownOption "gen-scope.mintStrata: an emitter" [
            "pass"
            "identifier"
            "kind"
            "relata"
            "content"
            "site"
          ] "kindOption"
        );
      };
    };
  };

  # ── THE ASSEMBLY'S REFUSAL ──
  # A duplicated export is refused by the fold that builds the library's surface. `tryEval` can say
  # THAT it refused, and `ci/tests/merge-surface.nix` does; WHICH name and WHICH two modules is a
  # claim about the text, and a shadowing whose message named only the key would leave a reader
  # hunting sixteen modules for the second contributor.
  config.flake.testsError.assembly-refusal = {
    test-a-duplicated-export-names-the-key-and-both-modules = {
      expr = builtins.attrNames (mergeSurface {
        alpha = {
          one = 1;
        };
        beta = {
          one = 2;
        };
      });
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: 'one' is exported by both 'alpha' and 'beta', and the library refuses a duplicate export rather than resolving it by position";
      };
    };
  };

  # ── THE CONSTRUCTOR'S RESERVED LABELS ──
  # `buildNodes` refuses a caller's `edgeGraphs` label that is one of its own two. `tryEval` can say
  # THAT it refused, and `tests/build-nodes.nix` does; WHICH label was offered and WHICH argument
  # already owns it is a claim about the text, and a caller told only that "a label is reserved" is
  # sent to read the constructor for the pair — which is the reading the reservation exists to spare
  # them. Two labels means two repairs (`parentGraph` or `importGraph`), so each is pinned on its own
  # rather than through one cell standing for both.
  # ── THE VERTEX-ORDER REFUSALS ──
  # `expr` here is a message, not a boolean, which is the whole reason these live in this output.
  # The scope refusal is keyed on the FAILED CONJUNCT, so each limb gets its own cell: a roster of
  # example shapes would leave gaps, and the count is whatever the predicate has.
  config.flake.testsError.vertex-order-refusals =
    let
      pg = genScope.edge {
        from = "a";
        to = "root";
      };
      built = genScope.buildRoots { parentGraph = pg; };
      attrs = {
        children = _self: _id: { };
        imports = _self: _id: [ ];
      };
      scopeRefusal =
        entry: detail:
        exactly (
          "gen-scope.${entry}: `scope` must be the record returned by `buildRoots` ({ nodes, nodeOrder }); "
          + detail
          + ". A node map alone no longer carries the declared order — pass the whole record."
        );
    in
    {
      # O12 — the retired NAME is a tombstone, so an un-migrated call cannot be written at all.
      test-O12-the-retired-constructor-name-is-a-tombstone = {
        expr = genScope.buildNodes { parentGraph = pg; };
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope: `buildNodes` is retired. Use `buildRoots`, which returns `{ nodes, nodeOrder }` — the node set together with its declared vertex order. Renaming the call is NOT sufficient: the evaluators take that whole record as `scope`, not a bare node map as `roots`, so `eval { roots = buildRoots {…}; }` is refused too.";
        };
      };

      # O6 — a label names a DIMENSION. The list form makes a second claim on one label expressible
      # where the attrset could not, so the list form owes the refusal.
      test-O6-a-duplicate-label-is-refused-by-name = {
        expr =
          (genScope.buildRoots {
            parentGraph = pg;
            edgeGraphs = [
              {
                label = "M";
                graph = genScope.edge {
                  from = "n";
                  to = "m";
                };
              }
              {
                label = "M";
                graph = genScope.edge {
                  from = "d";
                  to = "c";
                };
              }
            ];
          }).nodeOrder;
        expectedError = {
          type = "ThrownError";
          msg = exactly ''gen-scope.buildRoots: `edgeGraphs` claims label(s) ["M"] more than once. A label names a dimension, not a node, so two contributions under one label is a collision with no order semantics to resolve it — merge them with `overlay` before contributing, or give each its own label.'';
        };
      };

      # O14, limb 1 — a bare NODE MAP where the record belongs. This is the shape that used to be
      # served silently on every enumerating read.
      test-O14-a-node-map-is-refused-with-the-conjunct-named = {
        expr = (genScope.eval { } attrs built.nodes).allNodeIds;
        expectedError = {
          type = "ThrownError";
          msg = scopeRefusal "eval" "received an attrset with no `nodes`";
        };
      };

      # O14, limb 2 — the ADVERSARIAL graph, whose node ids are literally `nodes` and `nodeOrder`.
      # Its key set is IDENTICAL to the record's, so only the TYPE discriminates.
      test-O14-the-adversarial-node-map-is-refused-on-type = {
        expr =
          (genScope.eval { } attrs (
            (genScope.buildRoots {
              parentGraph = genScope.overlays [
                (genScope.vertex "nodes")
                (genScope.vertex "nodeOrder")
              ];
            }).nodes
          )).allNodeIds;
        expectedError = {
          type = "ThrownError";
          msg = scopeRefusal "eval" "received an attrset whose `nodeOrder` is a set, not a list";
        };
      };

      # O14, limb 3 — not an attrset at all.
      test-O14-a-non-attrset-is-refused-with-its-type-named = {
        expr = (genScope.eval { } attrs [ ]).allNodeIds;
        expectedError = {
          type = "ThrownError";
          msg = scopeRefusal "eval" "received a list";
        };
      };

      # O14 — the refusal is the ENTRY's, so the message names the entry the caller wrote.
      test-O14-the-message-names-the-entry-that-was-called = {
        expr = (genScope.evalDebug { } attrs built.nodes).node "a";
        expectedError = {
          type = "ThrownError";
          msg = scopeRefusal "evalDebug" "received an attrset with no `nodes`";
        };
      };
    };

  # ── THE SELECTION CHANNEL'S REFUSAL, AND THE DESCENT NAMING BESIDE IT ──
  # `ci/tests/child-selection.nix` asserts THAT a minting body is refused, and a boolean cannot say
  # WHICH of the two things a caller must now do — register the node, or declare a spawn. That is a
  # claim about the text, so it lives here.
  #
  # The two cells are one subject entered from its two ends. A caller who wrote a growth body on
  # the wrong channel meets the first; a caller who moved it to the right channel and then declared
  # it as an expansion into its OWN kind meets the second. The second used to answer with a CYCLE
  # message — true, since a self-loop is a 1-cycle in `below`, and about a relation the author was
  # not thinking of as a graph. Both messages now name the concept that was violated.
  config.flake.testsError.child-selection-refusals =
    let
      selectionScope = {
        nodes = {
          host = {
            id = "host";
            type = "t";
            parent = null;
            decls = { };
          };
          kid = {
            id = "kid";
            type = "t";
            parent = "host";
            decls = { };
          };
        };
        nodeOrder = [
          "host"
          "kid"
        ];
      };
    in
    {
      # TWO offending keys and one registered one in the same body: the message enumerates every
      # key it refuses rather than stopping at the first, and the registered sibling is absent from
      # that list, so the cell reads the PREDICATE and not merely the throw.
      test-a-minted-child-names-the-host-the-keys-and-the-ground = {
        expr = genScope.childrenIds (genScope.eval { } {
          children =
            _self: id:
            if id == "host" then
              {
                alpha = {
                  id = "alpha";
                  type = "t";
                  parent = "host";
                  decls = { };
                };
                zeta = {
                  id = "zeta";
                  type = "t";
                  parent = "host";
                  decls = { };
                };
                inherit (selectionScope.nodes) kid;
              }
            else
              { };
        } selectionScope) "host";
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope: node 'host' declares child(ren) [\"alpha\",\"zeta\"] that the scope does not carry. `children` SELECTS among the nodes the scope already registered — it is not a growth channel, and a record under an unregistered key is a node minted while the attribute is read, whose kind nothing can have checked descends its host's. Growth is the spawn channel's: declare it on the host's kind as `mkKind { spawns = { <produced-kind> = builder; }; }` with the produced kind named in that kind's `below`. To keep a node here, register it in the scope and select it.";
        };
      };

      # A kind that spawns its own kind. `mkKind` accepts `spawns.a` when `below` carries `a` —
      # `elem "a" [ "a" ]` holds — and what it builds is a declaration. The fold cannot mint it: `a`
      # is not minted before itself, so the refusal is the unresolved-name one (G1).
      test-G1-a-self-spawning-declaration-cannot-be-minted = {
        expr = builtins.seq (mkKinds [
          (mkKind {
            below = [ "a" ];
            spawns.a = _self: _id: { };
          } "a")
        ]) null;
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope.mkKinds: kind 'a' names 'a' in `below`, which no kind registered before it carries. A kind resolves its `below` names against the kinds declared EARLIER in the list, so declare every kind after the kinds its `below` names; a kind naming itself, or a cycle of kinds, has no such order and cannot be declared.";
        };
      };
      # G2: a two-cycle misses at its first member, in the caller's list order.
      test-G2-a-two-cycle-misses-at-its-first-member = {
        expr = builtins.seq (mkKinds [
          (mkKind {
            below = [ "b" ];
          } "a")
          (mkKind {
            below = [ "a" ];
          } "b")
        ]) null;
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope.mkKinds: kind 'a' names 'b' in `below`, which no kind registered before it carries. A kind resolves its `below` names against the kinds declared EARLIER in the list, so declare every kind after the kinds its `below` names; a kind naming itself, or a cycle of kinds, has no such order and cannot be declared.";
        };
      };
      # The attribute-set form is retired by name, pointing at the list form.
      test-the-attribute-set-form-is-refused-by-name = {
        expr = builtins.seq (mkKinds { a = mkKind { } "a"; }) null;
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope.mkKinds: expected a LIST of kind declarations, not an attribute set. Kinds are minted in list order, each against the kinds declared before it, and an attribute set has no order to mint in: list the declarations with every kind after the kinds its `below` names.";
        };
      };
    };

  config.flake.testsError.build-nodes-reserved-labels = {
    test-a-reserved-P-names-the-label-and-the-argument-that-owns-it = {
      expr = (collide [ "P" ]).nodes.a.parent;
      expectedError = {
        type = "ThrownError";
        msg = exactly (reservedLabelRefusal ''["P"]'' containment);
      };
    };
    test-a-reserved-I-names-the-label-and-the-argument-that-owns-it = {
      expr = (collide [ "I" ]).nodes.a.decls.__edges.I;
      expectedError = {
        type = "ThrownError";
        msg = exactly (reservedLabelRefusal ''["I"]'' importing);
      };
    };
    # A caller who offered both is told about both. A refusal naming only the first would send them
    # back for a second round over a defect they made once.
    test-both-reserved-labels-are-named-in-one-refusal = {
      expr =
        (collide [
          "P"
          "I"
        ]).a.parent;
      expectedError = {
        type = "ThrownError";
        msg = exactly (reservedLabelRefusal ''["P","I"]'' "${containment}; ${importing}");
      };
    };
    # The calculus's non-letters: a label no alphabet may list is refused at the lift, not carried
    # to be walked by nothing.
    test-a-reserved-underscore-names-the-label-and-why-no-letter-walks-it = {
      expr = (collide [ "_" ]).nodes.a.decls.__edges;
      expectedError = {
        type = "ThrownError";
        msg = exactly (
          reservedLabelRefusal ''["_"]'' "'_' is the path-expression grammar's any-label wildcard, which no alphabet may list as a letter"
        );
      };
    };
    test-a-reserved-dollar-names-the-label-and-why-no-letter-walks-it = {
      expr = (collide [ "$" ]).nodes.a.decls.__edges;
      expectedError = {
        type = "ThrownError";
        msg = exactly (
          reservedLabelRefusal ''["$"]'' "'$' is the extended label marking the end of a path, which no alphabet may list as a letter"
        );
      };
    };
  };

  # ── MULTI-PARENT ATTACHMENT, THE DOORS ──
  # `ci/tests/build-nodes.nix` asserts THAT `mintAttachmentId`/`parseParent` refuse each of their
  # three decidable failure modes (O5/O6/O7 in the carrying spec); WHICH one fired is a claim about
  # the message, asserted here.
  config.flake.testsError.multi-parent-attachment-refusals = {
    # O5 — bareId already contains '@'.
    test-mintAttachmentId-refuses-a-bareId-containing-at = {
      expr = genScope.mintAttachmentId "heddle@shaft1" [ "shaft1" "shaft2" ] "shaft1";
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: mintAttachmentId: bareId 'heddle@shaft1' contains '@', reserved to separate a multiply-attached id from its parent (Neron §2.2, buildRoots' own throw). Choose a bareId with no '@'.";
      };
    };

    # O6 — parent is not a member of parents.
    test-mintAttachmentId-refuses-a-parent-not-in-parents = {
      expr = genScope.mintAttachmentId "heddle" [ "shaft1" "shaft2" ] "shaft3";
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: mintAttachmentId: parent 'shaft3' is not a member of the parents passed for 'heddle'.";
      };
    };

    # O7 — non-string/non-list arguments, each named with its actual (wrong) type.
    test-mintAttachmentId-refuses-a-non-string-bareId = {
      expr = genScope.mintAttachmentId 1 [ "shaft1" "shaft2" ] "shaft1";
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: mintAttachmentId: bareId must be a string, got int";
      };
    };
    test-mintAttachmentId-refuses-a-non-list-parents = {
      expr = genScope.mintAttachmentId "heddle" "shaft1" "shaft1";
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: mintAttachmentId: parents must be a list, got string";
      };
    };
    test-mintAttachmentId-refuses-a-non-string-parent = {
      expr = genScope.mintAttachmentId "heddle" [ "shaft1" "shaft2" ] 3;
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: mintAttachmentId: parent must be a string, got int";
      };
    };
    test-parseParent-refuses-a-non-string-id = {
      expr = genScope.parseParent [ ];
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: parseParent: id must be a string, got list";
      };
    };
  };

  # ── THE INTERPRETATION'S REFUSALS, WHERE THEIR CONTENT LIVES ──
  # `ci/tests/interpretation.nix` asserts THAT each of these fires, which is a boolean `tryEval`
  # can read. WHICH one fired is a claim about the message, and four booleans are equally satisfied
  # by a constructor with one refusal in it — so the text is asserted here.
  #
  # ★ THE INCONSISTENCY REFUSAL IS THE ONE THAT MATTERS MOST, because it is the primary's own
  # requirement rather than a validation convention: VGRS Definition 2.4 makes a partial
  # interpretation a CONSISTENT set of literals, so admitting a violation would mean the engine
  # computed over something that paper's theorems do not quantify over. A refusal naming neither
  # the atom nor the two verdicts sends a caller back to find them.
  config.flake.testsError.interpretation-refusals =
    let
      solveWith =
        interpretation: (genScope.wellFoundedModel interpretation (genScope.mkProgram [ ])).trueAtoms;
    in
    {
      test-an-inconsistent-interpretation-names-the-atom-and-both-verdicts = {
        expr = solveWith [
          {
            atom = "x";
            verdict = "true";
          }
          {
            atom = "x";
            verdict = "false";
          }
        ];
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope: the interpretation is INCONSISTENT — 'x' is carried with verdicts 'true' and 'false', and Van Gelder, Ross & Schlipf 1991 Definition 2.4 makes a partial interpretation a CONSISTENT set of literals";
        };
      };

      test-a-missing-verdict-names-the-atom-and-refuses-the-default = {
        expr = solveWith [ { atom = "x"; } ];
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope: the carried atom 'x' has no verdict, and a carried atom with no verdict is REFUSED rather than defaulted — 'absent means false' is the exact substitution this parameter exists to prevent";
        };
      };

      test-an-unknown-entry-field-is-named = {
        expr = solveWith [
          {
            atom = "x";
            verdict = "true";
            why = "no";
          }
        ];
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope: the interpretation entry for 'x' carries the unknown field(s) 'why' — an entry is { atom, verdict } and nothing else";
        };
      };

      test-a-verdict-outside-the-vocabulary-names-it-and-the-vocabulary = {
        expr = solveWith [
          {
            atom = "x";
            verdict = "maybe";
          }
        ];
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope: the carried atom 'x' has verdict 'maybe', which is not one of 'true', 'undefined', 'false'";
        };
      };

      test-an-entry-with-no-atom-names-its-position = {
        expr = solveWith [ { verdict = "true"; } ];
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope: interpretation entry 0 has no 'atom' field — an interpretation is a list of { atom, verdict }";
        };
      };
    };

  # ── THE DOMAIN CARRIER'S REFUSALS, EACH BY ITS OWN TEXT ──
  # Four different facts, and a caller acts differently on each: a kind vocabulary that was never
  # registered, a spelling the registry does not carry, an expansion declared outside the registry
  # altogether, and a builder choosing its child's kind while it fires. `tryEval` reports one
  # boolean for all four, and the booleans live beside their controls in `tests/build-nodes.nix`
  # and `tests/hoag.nix`.
  config.flake.testsError.domain-carrier-refusals =
    let
      lowHigh =
        spawn:
        genScope.mkKinds [
          (genScope.mkKind { } "low")
          (genScope.mkKind {
            below = [ "low" ];
            spawns.low = spawn;
          } "high")
        ];
      runWith =
        kinds: attributes:
        builtins.deepSeq
          (genScope.eval { }
            (
              {
                children = _self: _id: { };
                imports = _self: _id: [ ];
              }
              // attributes
            )
            (
              genScope.buildRoots {
                inherit kinds;
                parentGraph = genScope.vertex "h";
                types.h = "high";
              }
            )
          ).allNodes
          null;
    in
    {
      test-declaring-types-with-no-registry-names-the-vocabulary = {
        expr =
          builtins.deepSeq
            (genScope.buildRoots {
              parentGraph = genScope.vertex "n";
              types.n = "host";
            }).nodes
            null;
        expectedError = {
          type = "ThrownError";
          msg = exactly ''gen-scope.buildRoots: `types` declares kind(s) ["host"] but no `kinds` registry was supplied. A kind is a name in a registered vocabulary, not a free string: without the registry there is no order for the kinds to be ranked in, so nothing can say that an expansion descends and every spelling is its own kind. Register them with `mkKinds` and pass the result as `kinds`, or declare no types.'';
        };
      };

      test-a-spelling-the-registry-does-not-carry-is-named = {
        expr =
          builtins.deepSeq
            (genScope.buildRoots {
              parentGraph = genScope.vertex "n";
              kinds = genScope.mkKinds [ (genScope.mkKind { } "host") ];
              types.n = "gost";
            }).nodes
            null;
        expectedError = {
          type = "ThrownError";
          msg = exactly ''gen-scope.buildRoots: `types` declares kind(s) ["gost"] that the supplied `kinds` registry does not carry. An unregistered kind has no rank, so nothing can decide whether an expansion into or out of it descends — register the kind, or use one that is registered.'';
        };
      };

      # A hand-written spawn attribute is refused at the ENTRY, before any node resolves, because it
      # is a statement about the whole program rather than about one node.
      test-a-hand-written-spawn-attribute-names-where-the-declaration-belongs = {
        expr = runWith (lowHigh (_self: _id: { })) {
          derived-children = _self: _id: { };
        };
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope.eval: `attributes` declares `derived-children` directly. A node expansion is declared on the KIND it expands FROM — `mkKind { spawns = { <produced-kind> = builder; }; }` — so that the produced kind is a registered name below its host's own and the descent is settled before anything fires. Written as a bare attribute the produced kind is whatever the body returns, which is a choice made at firing time and one nothing can check. Move the builder onto its host kind's `spawns`.";
        };
      };

      # A builder writing `type` is the only way a firing-time kind choice could still be attempted,
      # and the message says which host, which produced kind and which child — the three coordinates
      # an author needs to find the line.
      test-a-builder-choosing-its-childs-kind-is-refused-by-name = {
        expr = runWith (lowHigh (
          _self: id: {
            "${id}-c" = {
              id = "${id}-c";
              parent = id;
              type = "low";
              decls = { };
            };
          }
        )) { };
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope: kind 'high' spawns 'low' and its builder returned a child 'h-c' carrying its own `type`. A spawn does not choose its child's kind: the kind is the key the builder was declared under, and the substrate stamps it from there — a kind chosen while the spawn fires is one nothing can have checked descends. Drop the field.";
        };
      };

      # The route that skips the constructor's door: a scope record assembled by hand carries nodes
      # nothing validated, so the spawn channel refuses the unregistered kind where it reads it.
      test-a-hand-built-scope-with-an-unregistered-kind-is-refused = {
        expr =
          builtins.deepSeq
            (genScope.eval { }
              {
                children = _self: _id: { };
                imports = _self: _id: [ ];
              }
              {
                nodes.n = {
                  id = "n";
                  parent = null;
                  type = "ghost";
                  decls = { };
                };
                nodeOrder = [ "n" ];
                kinds = genScope.mkKinds [ (genScope.mkKind { } "high") ];
              }
            ).allNodes
            null;
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope: node 'n' carries kind 'ghost', which the supplied registry does not carry. A node's kind is a name in a registered vocabulary — register it with `mkKinds`, or build the scope through `buildRoots`, which refuses an unregistered kind at the door.";
        };
      };
    };

  # ── THE SPAWNED KEY'S CONTRACT, TWO COLLISION FLAVORS ──
  # A spawn builder's return is keyed by the child it names, and that key was checked against
  # neither the scope's own registered nodes nor a sibling spawn's own output — either one silently
  # discards whichever record materializes second. Both cells build their own fixture by hand
  # (rather than through `domain-carrier-refusals`' `runWith`) because that helper's scope carries
  # exactly one registered vertex, and a registered-id collision needs a second one to collide with.
  config.flake.testsError.spawn-key-collision-refusals = {
    # flavor (B): the spawned key equals an ALREADY-REGISTERED node's id.
    test-a-spawned-key-colliding-with-a-registered-node-is-refused-by-name = {
      expr =
        builtins.deepSeq
          (genScope.eval { }
            {
              children = _self: _id: { };
            }
            (
              genScope.buildRoots {
                parentGraph = genScope.overlay (genScope.vertex "a") (genScope.vertex "b");
                types.a = "host";
                types.b = "leaf";
                decls.a = { };
                decls.b = { };
                kinds = genScope.mkKinds [
                  (genScope.mkKind { } "leaf")
                  (genScope.mkKind {
                    below = [ "leaf" ];
                    spawns.leaf = _self: id: {
                      b = {
                        id = "b";
                        parent = id;
                        decls = { };
                      };
                    };
                  } "host")
                ];
              }
            )
          ).allNodes
          null;
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: kind 'host' spawns 'leaf' and its builder returned a child 'b', which is already a registered node's id. A spawned key mints an identity nothing declared; colliding with a key the scope already carries discards whichever record materializes second, silently. Choose a key no registered node already carries.";
      };
    };

    # flavor (C): two of a host's OWN spawns produce the same key.
    test-a-spawned-key-colliding-with-a-sibling-spawn-is-refused-by-name = {
      expr =
        builtins.deepSeq
          (genScope.eval { }
            {
              children = _self: _id: { };
            }
            (
              genScope.buildRoots {
                parentGraph = genScope.vertex "a";
                types.a = "host";
                decls.a = { };
                kinds = genScope.mkKinds [
                  (genScope.mkKind { } "leafOne")
                  (genScope.mkKind { } "leafTwo")
                  (genScope.mkKind {
                    below = [
                      "leafOne"
                      "leafTwo"
                    ];
                    spawns.leafOne = _self: id: {
                      shared = {
                        id = "shared";
                        parent = id;
                        decls = { };
                      };
                    };
                    spawns.leafTwo = _self: id: {
                      shared = {
                        id = "shared";
                        parent = id;
                        decls = { };
                      };
                    };
                  } "host")
                ];
              }
            )
          ).allNodes
          null;
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: kind 'host' spawns 'leafTwo' and its builder returned a child 'shared', which an earlier spawn on this same host already produced. Two spawns sharing a key on one host silently overwrite one another. Choose a key none of this host's own spawns already produced.";
      };
    };

    # A child whose `id` disagrees with its key: the key is the identity, so the second copy is
    # refused naming the kind, the key and the offending id (it used to recurse without bound).
    test-a-spawned-child-whose-id-disagrees-with-its-key-is-refused-by-name = {
      expr =
        builtins.deepSeq
          (genScope.eval { }
            {
              children = _self: _id: { };
            }
            (
              genScope.buildRoots {
                parentGraph = genScope.vertex "a";
                types.a = "host";
                decls.a = { };
                kinds = genScope.mkKinds [
                  (genScope.mkKind { } "leaf")
                  (genScope.mkKind {
                    below = [ "leaf" ];
                    spawns.leaf = _self: id: {
                      warp = {
                        id = "weft";
                        parent = id;
                        decls = { };
                      };
                    };
                  } "host")
                ];
              }
            )
          ).allNodes
          null;
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: kind 'host' spawns 'leaf' and its builder returned a child 'warp' whose `id` is 'weft' rather than its key 'warp'. A spawned child's identity is the key its builder returned it under: the substrate settles collisions on that key and stamps `id` from it, so a builder asserting a different id is naming a node the key set never registered. Drop the field.";
      };
    };
  };

  # ── THE CIRCULAR CARRIER'S REFUSALS, EACH BY ITS OWN TEXT ──
  # A caller must act differently on each of these and `tryEval` cannot tell them apart: an absent
  # carrier is a declaration missing, a malformed one is a declaration wrong, an antitone step is
  # the STEP disagreeing with the declared order, and an exhausted height is the DECLARATION
  # disagreeing with the step. The last two are the pair the combinator this replaces reported with
  # one message — "did not converge after N iterations" — which named the iteration count for both
  # and the cause for neither. Splitting them is the reason the cells are worth their text.
  #
  # The combinator is applied DIRECTLY rather than through an evaluator: `eval`'s `get` wraps every
  # attribute in `addErrorContext`, and these cells are about what the carrier says, not about
  # where a reader was standing when it said it. `null` is a legitimate `self` here because no arm
  # reached below applies it.
  config.flake.testsError.circular-refusals =
    let
      # The declaration is reached THROUGH THE EVALUATOR: under the kind-tagged declaration shape
      # an applied `circular` is a record, and the carrier refusal fires at the instance's FIRST
      # DEMAND on the demand path — the texts below survive that relocation byte-identically.
      run =
        carrierArg: f:
        (genScope.eval { }
          {
            children = _self: _id: { };
            imports = _self: _id: [ ];
            probe = circular carrierArg f;
          }
          (
            genScope.buildRoots {
              parentGraph = genScope.vertex "n";
              importGraph = genScope.empty;
              decls.n = { };
              types = { };
            }
          )
        ).get
          "n"
          "probe";
      ascending = {
        bottom = 0;
        leq = a: b: a <= b;
        height = 3;
        quotient = false;
      };
    in
    {
      test-an-absent-carrier-names-the-three-terms = {
        expr = run { } (
          _self: _id: prev:
          prev
        );
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope: circular attribute on 'n' declares no `carrier` — a circular attribute is well defined only over one, and its three terms are a bottom, an order and a bounded height (Söderberg & Hedin 2013 §4.1)";
        };
      };

      test-a-carrier-that-is-not-a-record-names-what-arrived = {
        expr = run { carrier = 5; } (
          _self: _id: prev:
          prev
        );
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope: circular attribute on 'n' declares a `carrier` that is a int rather than a { bottom, leq, height } record";
        };
      };

      # `bottom` is checked for PRESENCE and not against null, because null is a value some lattices
      # really do carry as their least element — the sentinel discipline that lets an absent
      # `carrier` be named cannot be spent twice on the same record.
      test-a-carrier-with-no-bottom-is-refused = {
        expr =
          run
            {
              carrier = {
                leq = a: b: a <= b;
                height = 1;
              };
            }
            (
              _self: _id: prev:
              prev
            );
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope: circular attribute on 'n' declares a `carrier` with no `bottom` (the starting point of the fixed-point iteration)";
        };
      };

      test-a-carrier-with-no-leq-is-refused = {
        expr =
          run
            {
              carrier = {
                bottom = 0;
                height = 1;
              };
            }
            (
              _self: _id: prev:
              prev
            );
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope: circular attribute on 'n' declares a `carrier` with no `leq` (the order the step is required to ascend)";
        };
      };

      # The arm that keeps an unapplicable order from ending the evaluation in the evaluator's
      # words. Without it `leq prev next` is "attempt to call something which is not a function" —
      # uncatchable, and carrying no name of ours.
      test-a-leq-that-cannot-be-applied-is-refused = {
        expr =
          run
            {
              carrier = {
                bottom = 0;
                leq = "not an order";
                height = 1;
              };
            }
            (
              _self: _id: prev:
              prev
            );
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope: circular attribute on 'n' declares a `carrier` whose `leq` cannot be applied (it is a string)";
        };
      };

      test-a-carrier-with-no-height-is-refused = {
        expr =
          run
            {
              carrier = {
                bottom = 0;
                leq = a: b: a <= b;
              };
            }
            (
              _self: _id: prev:
              prev
            );
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope: circular attribute on 'n' declares a `carrier` with no `height` (the lattice's bounded height, from which the iteration bound is derived)";
        };
      };

      test-a-height-that-is-not-an-integer-is-refused = {
        expr =
          run
            {
              carrier = {
                bottom = 0;
                leq = a: b: a <= b;
                height = "tall";
              };
            }
            (
              _self: _id: prev:
              prev
            );
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope: circular attribute on 'n' declares a `carrier` whose `height` is a string rather than an integer";
        };
      };

      test-a-negative-height-is-refused = {
        expr =
          run
            {
              carrier = {
                bottom = 0;
                leq = a: b: a <= b;
                height = -1;
              };
            }
            (
              _self: _id: prev:
              prev
            );
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope: circular attribute on 'n' declares a `carrier` whose `height` is -1, and a lattice has no negative height";
        };
      };

      # ── THE TWO THE OLD MESSAGE CONFLATED ──
      # An ANTITONE step, refused at the first iteration that does not ascend rather than after the
      # cap's worth of recomputations. Under an equality convergence test this failure was invisible
      # by construction: consecutive states of an oscillation are never equal, so the run could only
      # ever end by exhausting its budget.
      test-an-antitone-step-names-monotonicity-and-the-iteration = {
        expr = run { carrier = ascending; } (
          _self: _id: prev:
          if prev == 0 then 1 else 0
        );
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope: circular attribute on 'n' took a step its declared order does not ascend, at iteration 1 — the step is not monotone on the declared carrier, so the iteration is not a Kleene ascent and no least fixed point is being computed";
        };
      };

      # A perfectly MONOTONE step on a carrier whose declared height is too small for it. Same
      # boolean as the cell above, different fact: the step is sound and the declaration is wrong,
      # and the message refutes the declaration by name.
      test-an-exhausted-height-refutes-the-declaration = {
        expr = run { carrier = ascending; } (
          _self: _id: prev:
          prev + 1
        );
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope: circular attribute on 'n' is still ascending after 4 steps, so the declared height of 3 is exceeded — the bound is derived from the declaration, and what this refutes is the declaration rather than an iteration budget";
        };
      };
    };

  # ── THE QUOTIENT ACCESSOR OBLIGATION (ADR-0020 never-silence, ADR-0008 §3) ──
  # The two demand forms refuse by name on the declarations the other one serves: `get` on a
  # quotient carrier, `getRepresentative` on anything else. Pinned on every channel that carries
  # them — top level, a step's own accessor, the reuse path, the debug evaluator — because a
  # `tryEval` boolean cannot tell this refusal from any other throw on the same path: the warm
  # fixture's recompute arm throws too, and only the text says which one fired. The answers and the
  # controls are `tests/quotient-accessor.nix`.
  config.flake.testsError.quotient-accessor-refusals =
    let
      inherit (import ./tests/_fixtures/quotient-accessor.nix { inherit genScope; }) r debug warm;
      rawOnQuotient = id: attrName: {
        type = "ThrownError";
        msg = exactly "gen-scope: self.get '${attrName}' on '${id}' demands a raw value of a quotient-converged instance — its carrier declares `quotient = true`, so what converged is a class representative under the declared order and not a fixed point of the step. Read it with `getRepresentative`, which returns it tagged.";
      };
    in
    {
      test-a-raw-get-on-a-quotient-instance-is-refused-by-name = {
        expr = r.get "node" "enriched";
        expectedError = rawOnQuotient "node" "enriched";
      };

      test-getRepresentative-on-a-non-quotient-instance-is-refused-by-name = {
        expr = r.getRepresentative "node" "counter";
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope: getRepresentative 'counter' on 'node' names an attribute whose declaration is not a quotient carrier — its value is not a class representative. Read it with `get`.";
        };
      };

      test-a-steps-raw-get-on-a-quotient-instance-is-refused-by-name = {
        expr = r.get "node" "reader";
        expectedError = rawOnQuotient "node" "enriched";
      };

      test-the-warm-paths-raw-get-is-refused-by-name-not-recomputed = {
        expr = warm.get "node" "enriched";
        expectedError = rawOnQuotient "node" "enriched";
      };

      test-evalDebug-raw-get-on-a-quotient-instance-is-refused-by-name = {
        expr = debug.get "node" "enriched";
        expectedError = rawOnQuotient "node" "enriched";
      };

      # The identifier door names the entry the caller used, on both evaluators.
      test-getRepresentative-names-itself-at-the-identifier-door = {
        expr = r.getRepresentative { name = "node"; } "enriched";
        expectedError = {
          type = "ThrownError";
          msg = exactly ((genGraph.key "gen-scope").notAnIdentifier "self.getRepresentative" { });
        };
      };

      test-evalDebug-getRepresentative-names-itself-at-the-identifier-door = {
        expr = debug.getRepresentative { name = "node"; } "enriched";
        expectedError = {
          type = "ThrownError";
          msg = exactly ((genGraph.key "gen-scope").notAnIdentifier "self.getRepresentative" { });
        };
      };
    };

  # ── THE SAME TWO REFUSALS, EARNED OVER A SPAWNED SUBTREE ──
  # The cells above run the combinator on a bare integer and settle what each message SAYS. These
  # run the same two failures inside the composed grammar — a lattice indexed by nodes that did not
  # exist when the attribute was declared — and settle that composing the carriers does not blunt
  # either refusal. `tests/circular-nta.nix` holds the same grammar's clean path, without which a
  # pair of refusals is equally consistent with a grammar that refuses whatever it is given.
  #
  # ★ WHAT THE MESSAGE NAMES, STATED BECAUSE IT IS THE DIAGNOSTIC COST OF THE PRODUCT CARRIER. Both
  # texts name 'c' — the node the circular attribute is homed at — and neither names the member
  # whose contribution broke the ascent or exhausted the chain. That follows from where the SCC is
  # carried: one attribute instance over a product lattice is ONE circular attribute as far as the
  # combinator is concerned, so the coordinate it can report is the instance's. An author reads
  # which member moved by diffing the two states, not out of the refusal.
  config.flake.testsError.circular-nta-refusals = {
    # The neighbours' contribution replacing a member's own seed rather than joining it. The
    # iteration index is the first round in which any member had a non-empty neighbour, which is
    # the first round in which a replacement could drop anything.
    test-a-non-monotone-contribution-over-the-spawned-subtree-names-monotonicity = {
      expr = circularNta.nonMonotone;
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: circular attribute on 'c' took a step its declared order does not ascend, at iteration 1 — the step is not monotone on the declared carrier, so the iteration is not a Kleene ascent and no least fixed point is being computed";
      };
    };

    # A height one short of the cycle's length. The step count the message reports is the one this
    # run actually took, so a cell asserting the text asserts that the bound came off the
    # declaration rather than being recited from it.
    test-a-height-one-short-of-the-cycle-refutes-the-declaration = {
      expr = circularNta.shortHeight;
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: circular attribute on 'c' is still ascending after 3 steps, so the declared height of 2 is exceeded — the bound is derived from the declaration, and what this refutes is the declaration rather than an iteration budget";
      };
    };
  };

  # ── THE SHARED ROUND'S REFUSALS — the corpus's refusing fixtures, each by its own text
  # (plus the first-transition family at the end, which states its own provenance) ──
  # The fixtures and their provenance live in `tests/_fixtures/scc-corpus.nix`; the expected
  # VERDICT KIND of every cell here is the tracked model's hand-derived default column, and the
  # texts are the landed refusal idiom those verdicts arrive in. The ascent and height texts are
  # the landed `circular` texts byte-identically — the k = 1 degeneration and the composed round
  # share one wording, which is what the shipped errors suite already pins.
  config.flake.testsError.scc-round-refusals = {
    # The hybrid-only quotient at value 9: the constructed pair is ordered on both coordinates, so the seat's refutation stands — the value-0 twin answers next door.
    test-unevalxc-the-hybrid-quotient-at-nine-is-refused = {
      expr = sccCorpus.results."UNEVALXC-ZR9";
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: circular attribute on 'n' took a step its declared order does not ascend, at iteration 3 — the step is not monotone on the declared carrier, so the iteration is not a Kleene ascent and no least fixed point is being computed";
      };
    };

    # An unread hybrid-only quotient whose value DESCENDS: the entrywise clamp keeps the refusal a whole-map gate would lose.
    test-udesc-an-unread-descending-quotient-does-not-disarm-the-seat = {
      expr = sccCorpus.results."UDESC";
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: circular attribute on 'n' took a step its declared order does not ascend, at iteration 3 — the step is not monotone on the declared carrier, so the iteration is not a Kleene ascent and no least fixed point is being computed";
      };
    };

    # The discriminating twin: the same declaration ASCENDING leaves the verdict refused, so the family keys on the member's own step and not on the extra declaration's presence.
    test-control-uasc-the-ascending-twin-still-refuses = {
      expr = sccCorpus.results."UASC";
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: circular attribute on 'n' took a step its declared order does not ascend, at iteration 3 — the step is not monotone on the declared carrier, so the iteration is not a Kleene ascent and no least fixed point is being computed";
      };
    };

    test-control-uflat-the-flat-twin-still-refuses = {
      expr = sccCorpus.results."UFLAT";
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: circular attribute on 'n' took a step its declared order does not ascend, at iteration 3 — the step is not monotone on the declared carrier, so the iteration is not a Kleene ascent and no least fixed point is being computed";
      };
    };

    # A member non-monotone in a MEMBER it reads: the shared round applies it at the intermediates and refuses — the row's own stated cost, with the remedy the row's own.
    test-h10b-a-step-nonmonotone-in-a-member-it-reads-is-refused = {
      expr = sccCorpus.results."H10B";
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: circular attribute on 'n' took a step its declared order does not ascend, at iteration 3 — the step is not monotone on the declared carrier, so the iteration is not a Kleene ascent and no least fixed point is being computed";
      };
    };

    # UNSHOW's ordered twin: where the clamp CAN order the pair, the descent is real and the refusal returns — separating the neutral fallback from a seat that never fires.
    test-unshoword-the-ordered-twin-is-refused = {
      expr = sccCorpus.results."UNSHOWORD";
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: circular attribute on 'n' took a step its declared order does not ascend, at iteration 3 — the step is not monotone on the declared carrier, so the iteration is not a Kleene ascent and no least fixed point is being computed";
      };
    };

    test-nonrefl-a-non-reflexive-order-reads-quiet-as-descent = {
      expr = sccCorpus.results."NONREFL";
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: circular attribute on 'n' took a step its declared order does not ascend, at iteration 1 — the step is not monotone on the declared carrier, so the iteration is not a Kleene ascent and no least fixed point is being computed";
      };
    };

    test-flip-a-descending-quotient-driving-a-branch-flip-is-refused = {
      expr = sccCorpus.results."FLIP";
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: circular attribute on 'n' took a step its declared order does not ascend, at iteration 3 — the step is not monotone on the declared carrier, so the iteration is not a Kleene ascent and no least fixed point is being computed";
      };
    };

    # The TWIN family: an antitone member refuses on every arm; the presence and the order of an unread quotient beside it move nothing.
    test-twin-an-antitone-member-is-refused = {
      expr = sccCorpus.results."TWIN";
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: circular attribute on 'n' took a step its declared order does not ascend, at iteration 1 — the step is not monotone on the declared carrier, so the iteration is not a Kleene ascent and no least fixed point is being computed";
      };
    };

    test-control-twin-with-a-present-unread-quotient-still-refuses = {
      expr = sccCorpus.results."TWINP";
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: circular attribute on 'n' took a step its declared order does not ascend, at iteration 1 — the step is not monotone on the declared carrier, so the iteration is not a Kleene ascent and no least fixed point is being computed";
      };
    };

    test-control-twin-with-an-unread-descending-quotient-still-refuses = {
      expr = sccCorpus.results."TWIN2";
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: circular attribute on 'n' took a step its declared order does not ascend, at iteration 1 — the step is not monotone on the declared carrier, so the iteration is not a Kleene ascent and no least fixed point is being computed";
      };
    };

    # The corpus's own refusal control: a member step that descends on its trajectory with no quotient anywhere.
    test-control-a-plainly-antitone-member-is-refused = {
      expr = sccCorpus.results."CTLREFUSAL";
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: circular attribute on 'n' took a step its declared order does not ascend, at iteration 3 — the step is not monotone on the declared carrier, so the iteration is not a Kleene ascent and no least fixed point is being computed";
      };
    };

    # The clamp is ENTRYWISE, inside each entry's own thunk: a declaration pair nothing reads descends across the compared levels, and the verdict is byte-identical to UNEVALXC's because the undemanded entry is never compared — a whole-map clamp would have to compare it.
    test-clamplazy-an-undemanded-descending-pair-is-never-compared = {
      expr = sccCorpus.results."CLAMPLAZY";
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: circular attribute on 'n' took a step its declared order does not ascend, at iteration 3 — the step is not monotone on the declared carrier, so the iteration is not a Kleene ascent and no least fixed point is being computed";
      };
    };

    # One member read DIRECTLY (the clamped map) and THROUGH A QUOTIENT (the later snapshot raw) inside one step: the constructed pair stays ordered on both coordinates and the refutation stands. An implementation memoising the member once for both routes breaks this cell.
    test-qsplit-one-accessor-serves-two-values-for-one-member-by-route = {
      expr = sccCorpus.results."QSPLIT";
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: circular attribute on 'n' took a step its declared order does not ascend, at iteration 4 — the step is not monotone on the declared carrier, so the iteration is not a Kleene ascent and no least fixed point is being computed";
      };
    };

    # A wide flat carrier whose step walks off the order, no quotient anywhere — the degenerate universe's own ascent seat.
    test-wideflat-a-self-driven-walk-off-the-order-is-refused = {
      expr = sccCorpus.results."WIDEFLAT";
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: circular attribute on 'n' took a step its declared order does not ascend, at iteration 1 — the step is not monotone on the declared carrier, so the iteration is not a Kleene ascent and no least fixed point is being computed";
      };
    };

    # The height seat refutes the DECLARATION on a witness intrinsic to one carrier: a genuine chain 0 < 2 < 4 against a declared height of one, whatever else the program contains — the quotient beside it moves nothing.
    test-h8b-a-genuine-chain-past-a-truthful-height-is-refused = {
      expr = sccCorpus.results."H8B";
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: circular attribute on 'n' is still ascending after 2 steps, so the declared height of 1 is exceeded — the bound is derived from the declaration, and what this refutes is the declaration rather than an iteration budget";
      };
    };

    test-control-h8c-the-same-chain-with-no-quotient-refuses-identically = {
      expr = sccCorpus.results."H8C";
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: circular attribute on 'n' is still ascending after 2 steps, so the declared height of 1 is exceeded — the bound is derived from the declaration, and what this refutes is the declaration rather than an iteration budget";
      };
    };

    # TRIPLE reports the hand-derived column's OWN verdict, R-CLOSURE: the quotient pair's
    # re-entry closes the cycle at the armed level and fires FIRST, byte-identical to
    # TRIPLE-HONEST's text — so the under-declared member (`n.m`, height 1) is never reached, and
    # this cell keys on the CLOSURE seat rather than on the height one.
    # ★ THE CONTRAST THAT USED TO SIT HERE IS WITHDRAWN, AND IT IS REPLACED BY A DISTINCTION AND
    # NOT BY AN EQUIVALENCE. It read: "TRIPLE-NOQ, the same program with the pair removed, is
    # answered", which was the price of seats scoped to the demanded target's column. Under the
    # force gate the seats ride EVERY member, so BOTH programs now refuse — and they refuse AT
    # DIFFERENT SEATS: TRIPLE at the CYCLE-CLOSURE seat above, TRIPLE-NOQ at the HEIGHT seat, its
    # cell next door in this suite. Removing the quotient pair removes the closure, and what is
    # then left to refuse is `n.m`'s lie.
    test-triple-a-non-target-height-lie-does-not-pre-empt-the-closure = {
      expr = sccCorpus.results."TRIPLE";
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: circular demand re-entered 'n.q': the walked path closes the cycle [\"n.q\",\"n.r\"], and quotient declaration(s) [\"n.q\",\"n.r\"] are on it. A quotient carrier cannot be driven in a shared round — its convergence is an own-value comparison over classes, which a simultaneous ascent cannot answer — so the cycle is refused rather than iterated. Declare an antisymmetric order for the instances that read each other, or keep this instance out of the other's cycle.";
      };
    };

    # ★ THE FORCE GATE'S OWN VERDICT MOVEMENT, PINNED AS A CELL: with TRIPLE's quotient pair
    # removed there is no closure to fire, and the under-declared member (`n.m`, height 1, a
    # genuine chain of three) is a NON-TARGET whose iteration SETTLES before the composed bound —
    # so the settlement walk has nothing left to find. Seats scoped to the demanded target's
    # column ANSWERED this program, at exit 0, with the model of record refusing it; the seats now
    # ride every member the demand reaches, over the column (D3) completes, and the height seat
    # refutes the DECLARATION by name. ★ The expectation moved here from the VALUE suite when the
    # gate landed: coverage is preserved with INVERTED POLARITY, so this cell reds if the
    # mechanism ever answers a height lie again. H8B/H8C above pin the same lie ON THE TARGET, and
    # TRIPLE-HONEST pins that the refusal moves with the LIE and not with the seating.
    test-triple-noq-a-non-target-height-lie-that-settles-is-refused = {
      expr = sccCorpus.results."TRIPLE-NOQ";
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: circular attribute on 'n' is still ascending after 2 steps, so the declared height of 1 is exceeded — the bound is derived from the declaration, and what this refutes is the declaration rather than an iteration budget";
      };
    };

    # ★ A26 CELL 1 — A MEMBER OTHER THAN THE DEMANDED TARGET, DESCENDING ON ITS OWN TRAJECTORY,
    # IS REFUSED BY NAME. The fixture is multi-node (`tests/_fixtures/scc-force-gate.nix`)
    # because the `!ascends` text names the refusing instance by NODE, and naming the member is
    # the assertion: the target RATCHETS, so its own seat can never fire, and the message must
    # blame 'dsc' — the descending non-target — never 'tgt'. The cell was RED on the
    # target-column-scoped build (measured at `1b222fd`: EXIT 0, value 1, stderr empty), and the
    # value 1 is exactly what the monotone twin answers in the value suite, so a cell asserting
    # the returned value alone could not separate a least fixed point from a silent non-least
    # one — which is what makes this class silent and the message the only honest oracle.
    test-a-descending-non-target-member-is-refused-by-name = {
      expr = sccForceGate.refused;
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: circular attribute on 'dsc' took a step its declared order does not ascend, at iteration 2 — the step is not monotone on the declared carrier, so the iteration is not a Kleene ascent and no least fixed point is being computed";
      };
    };

    # A26's second control: the same program DEMANDED AT the descending member refuses on the
    # target-column-scoped build as well, so a harness that lost the seat outright cannot pass
    # as the capability — the refusal must move with the SEATING of the non-target, not with
    # whether any seat exists.
    test-control-the-same-program-demanded-at-the-descending-member-refuses = {
      expr = sccForceGate.refusedAtMember;
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: circular attribute on 'dsc' took a step its declared order does not ascend, at iteration 2 — the step is not monotone on the declared carrier, so the iteration is not a Kleene ascent and no least fixed point is being computed";
      };
    };

    # The honesty residue's ONE detector: a `leq` answering true everywhere, declared `quotient = false`, churns raw values the order cannot separate — still moving at the composed bound. The unread `n.b` is outside the demand cone and correctly outside the comparison.
    test-liar-a-coarse-order-declared-quotient-false-is-caught-at-the-bound = {
      expr = sccCorpus.results."LIAR";
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: a shared circular round is still moving at its derived bound: instance 'n.k' takes a step across levels 4 and 5 that its declared order cannot separate from movement, against the composed bound 5 (the sum of the declared heights over the round's universe, plus one). The bound is a theorem over the declared carriers, so what this refutes is a declaration — a carrier said `quotient = false` of an order too coarse to settle the states it serves. Declare a finer carrier.";
      };
    };

    # The attempted silent arm: the height over-declared so the run cap cannot fire, and the oscillation is caught LOUD at the bound instead.
    test-boundplateau-an-over-declared-height-cannot-mask-the-bound = {
      expr = sccCorpus.results."BOUNDPLATEAU";
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: a shared circular round is still moving at its derived bound: instance 'n.m' takes a step across levels 14 and 15 that its declared order cannot separate from movement, against the composed bound 15 (the sum of the declared heights over the round's universe, plus one). The bound is a theorem over the declared carriers, so what this refutes is a declaration — a carrier said `quotient = false` of an order too coarse to settle the states it serves. Declare a finer carrier.";
      };
    };

    # The priced loud refusal: a converging program whose quotient-gated ascent has not finished at the composed bound. The refusal is a stated price of the bound being a theorem over declared heights (the remedy is the fathomed twin next door).
    test-boundshort-a-gated-ascent-still-moving-at-the-bound-is-refused = {
      expr = sccCorpus.results."BOUNDSHORT";
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: a shared circular round is still moving at its derived bound: instance 'n.z' takes a step across levels 4 and 5 that its declared order cannot separate from movement, against the composed bound 5 (the sum of the declared heights over the round's universe, plus one). The bound is a theorem over the declared carriers, so what this refutes is a declaration — a carrier said `quotient = false` of an order too coarse to settle the states it serves. Declare a finer carrier.";
      };
    };

    # ★ The silent-wrong-answer class: the demanded value is stationary across the last two levels while members it depends on are still moving. A demanded-only settlement returns 0 at exit 0 against a true fixed point of 1; the cone-scoped comparison catches it LOUD — with nothing undemanded forced (BOUNDQUIET-NOOSC's cell next door).
    test-boundquiet-a-quiet-demanded-value-does-not-mask-moving-members = {
      expr = sccCorpus.results."BOUNDQUIET";
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: a shared circular round is still moving at its derived bound: instance 'n.z' takes a step across levels 6 and 7 that its declared order cannot separate from movement, against the composed bound 7 (the sum of the declared heights over the round's universe, plus one). The bound is a theorem over the declared carriers, so what this refutes is a declaration — a carrier said `quotient = false` of an order too coarse to settle the states it serves. Declare a finer carrier.";
      };
    };

    # ★ THE CLOSURE SEAT (E-a): a mutually-reading quotient pair inside an open round re-enters the walked path at the ARMED level, and the refusal names the re-entered instance, the cycle, the declaring instances and the remedy — where today's tree aborts with an uncatchable stack overflow. The height is declared honestly here, so the closure is the seat that fires.
    test-triple-honest-a-quotient-pair-closing-a-cycle-is-refused-by-name = {
      expr = sccCorpus.results."TRIPLE-HONEST";
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: circular demand re-entered 'n.q': the walked path closes the cycle [\"n.q\",\"n.r\"], and quotient declaration(s) [\"n.q\",\"n.r\"] are on it. A quotient carrier cannot be driven in a shared round — its convergence is an own-value comparison over classes, which a simultaneous ascent cannot answer — so the cycle is refused rather than iterated. Declare an antisymmetric order for the instances that read each other, or keep this instance out of the other's cycle.";
      };
    };

    # DEMERR — the control that isolates UNDEMANDEDNESS: the same erroring member as the
    # blind-spot cell, but READ by the target, so the death rides the demand itself. The error
    # is Nix's own (a division by zero is not a refusal of ours), which is the point: only an
    # UNDEMANDED erroring member is survivable, and only because it is never forced.
    test-control-demerr-a-demanded-erroring-member-dies-on-its-own-error = {
      expr = sccCorpus.results.DEMERR;
      expectedError = {
        type = "EvalError";
        msg = "division by zero";
      };
    };

    # ── THE FIRST-TRANSITION FAMILY (not corpus ports; fixtures and provenance at
    # `tests/_fixtures/first-transition.nix`) ──
    # A PERSISTENTLY non-monotone member whose first descent lands at the walk's own first
    # transition is still refused by name — one transition up, where the outer seat's clamp is
    # in-domain. At the first transition the seat is provisional by construction (the only
    # in-domain candidate for the earlier snapshot is the later one itself, and a step re-applied
    # to that clamp reproduces the value under test), so this cell is what says the provisional
    # first transition leaves NO REFUSAL HOLE.
    test-a-persistent-first-transition-descent-is-still-refused-by-name = {
      expr = firstTransition.desc2;
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: circular attribute on 'n' took a step its declared order does not ascend, at iteration 3 — the step is not monotone on the declared carrier, so the iteration is not a Kleene ascent and no least fixed point is being computed";
      };
    };

    # The unobserved-prefix control (13(e)): the SAME height lie the value suite answers when it
    # lives wholly below `f(x)` is refused by name when read from level one — the walk from 0
    # counts the run of ascents the late walk never observes. Without this cell the answering
    # twin's green is an absence claim with no live control.
    test-the-same-lie-observed-from-level-one-is-refused = {
      expr = firstTransition.p1lieCtl;
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: circular attribute on 'n' is still ascending after 2 steps, so the declared height of 1 is exceeded — the bound is derived from the declaration, and what this refutes is the declaration rather than an iteration budget (the still-moving members its step reads: [\"n.da\"])";
      };
    };
  };

  # ── THE MIGRATION'S OWN GUARDS — each new refusal shown able to fire, beside its clean path ──
  config.flake.testsError.scc-admission-refusals =
    let
      sccRun = sccCorpus.run;
      intCarrier = h: {
        bottom = 0;
        leq = a: b: a <= b;
        height = h;
        quotient = false;
      };
    in
    {
      # The fourth carrier term is REQUIRED and TOTAL: an absent `quotient` would decide the
      # shared round's admission question silently, and an absent declaration is itself a
      # decision.
      test-a-carrier-with-no-quotient-term-is-refused = {
        expr = sccRun {
          a = circular { carrier = builtins.removeAttrs (intCarrier 2) [ "quotient" ]; } (
            _self: _id: _prev:
            1
          );
        } "a";
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope: circular attribute on 'n' declares a `carrier` with no `quotient` (whether `leq` orders a quotient of the value space rather than the raw values — required and total, because a shared round admits only antisymmetric carriers and an absent declaration would decide that soundness question silently)";
        };
      };

      # The FIELD-SET CAP, carrier side: a fifth term is a return to the design sitting, and the
      # cell must red on a widening rather than pass any record carrying the four names.
      test-a-fifth-carrier-term-is-refused-by-the-cap = {
        expr = sccRun {
          a =
            circular
              {
                carrier = intCarrier 2 // {
                  widen = 1;
                };
              }
              (
                _self: _id: _prev:
                1
              );
        } "a";
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope: circular attribute on 'n' declares a `carrier` carrying [\"widen\"] beyond its four declared terms { bottom, leq, height, quotient } — the carrier's field set is capped by ruling, and a fifth term is a return to the design sitting rather than a refinement";
        };
      };

      # The cap, declaration side: the record `circular` returns is exactly { kind, carrier,
      # step }, and a hand-assembled extra field is refused rather than carried.
      test-a-fourth-declaration-field-is-refused-by-the-cap = {
        expr = sccRun {
          a =
            (circular { carrier = intCarrier 2; } (
              _self: _id: _prev:
              1
            ))
            // {
              extra = 1;
            };
        } "a";
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope: circular attribute on 'n' declares [\"extra\"] beyond the declaration's three fields — `circular { carrier = ...; } step` returns exactly { kind, carrier, step }, and the field set is capped: a term beyond it is a return to the design sitting rather than a refinement";
        };
      };

      # The classification's third arm: a record that is not a circular declaration is refused by
      # name rather than reaching Nix as an anonymous "attempt to call a set".
      test-a-record-that-is-not-a-circular-declaration-is-refused-by-name = {
        expr = sccRun {
          a = {
            not = "a-declaration";
          };
        } "a";
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope: attribute 'a' on 'n' is declared as a record that is not a circular declaration — an attribute is a function `self: id: value`, or the record `circular { carrier = { bottom; leq; height; quotient; }; } step` returns; anything else is refused by name rather than reaching Nix as an anonymous call error";
        };
      };

      # A child-bearing attribute may not be declared circular — the bootstrap ground: the
      # universe needs the walk, and the walk reads the child-bearing attributes.
      test-a-circular-children-declaration-is-refused-at-the-entry = {
        expr = sccRun {
          children =
            circular
              {
                carrier = {
                  bottom = { };
                  leq = _a: _b: true;
                  height = 1;
                  quotient = false;
                };
              }
              (
                _self: _id: _prev:
                { }
              );
        } "a";
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope.eval: `children` is declared circular, and a child-bearing attribute cannot be. The ground is bootstrap, not growth: a shared round's universe is derived from the materialized node set, the materialization walk reads the child-bearing attributes, and a circular one there would need a round whose bound needs the walk — measured as an uncatchable infinite recursion with this refusal removed. Every other structural attribute may be circular; this one selects the node set the universe is derived from.";
        };
      };

      # The height refusal NAMES THE STILL-MOVING MEMBERS the failing step reads — the
      # failure-path pass, run only when refusing. The corpus's own height cells exercise the
      # VACUOUS degeneration (the movers are the instance the text already names, and the landed
      # text stands byte-identically); this one is the arm with a genuine blame set.
      test-the-height-refusal-names-the-still-moving-members-its-step-reads = {
        expr = sccRun {
          a = circular { carrier = intCarrier 2; } (
            self: _id: _prev:
            self.get "n" "b"
          );
          b = circular { carrier = intCarrier 8; } (
            self: _id: _prev:
            let
              b = self.get "n" "b";
            in
            if b + 1 >= 6 then 6 else b + 1
          );
        } "a";
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope: circular attribute on 'n' is still ascending after 3 steps, so the declared height of 2 is exceeded — the bound is derived from the declaration, and what this refutes is the declaration rather than an iteration budget (the still-moving members its step reads: [\"n.b\"])";
        };
      };

      # A circular declaration in spawn-builder position is refused at REGISTRATION by the
      # shipped callability guard: under the kind-tagged declaration shape a builder that is a
      # declaration is inexpressible at definition time, never detected at firing — the node set
      # may not be a fixed point of its own iterate.
      test-a-circular-spawn-builder-is-refused-at-registration = {
        expr = mkKinds [
          (mkKind { } "ep")
          (mkKind {
            below = [ "ep" ];
            spawns.ep =
              circular
                {
                  carrier = {
                    bottom = { };
                    leq = _a: _b: true;
                    height = 1;
                    quotient = false;
                  };
                }
                (
                  _self: _id: _prev:
                  { }
                );
          } "host")
        ];
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope.mkKind: kind 'host' declares a spawn for kind(s) [\"ep\"] whose builder cannot be applied";
        };
      };

      # THE LIFETIME RULE: a round's memo is reachable only through the round's own accessor —
      # a body naming a child record's co-located `_eval` cache from inside an open round meets
      # a named, catchable refusal at the field the cache would have occupied. The clean path
      # (the same demand through `self.get`) answers in `tests/scc-round.nix`.
      test-the-eval-cache-refuses-by-name-inside-an-open-round = {
        expr = sccCorpus.lifetime.cacheRead;
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope: the `_eval` cache for 'plain' on 'c' is not readable inside an open circular round — a round's memo lives on the round's own accessor, and a value cached here would be an approximation wearing a final value's clothes. Read through `self.get`, which serves the round's current level.";
        };
      };
    };

  # ── THE DEBUG EVALUATOR'S COMPOSED-READ REFUSAL ──
  # The composed child-record read forces a node acquisition at the id whose children are asked
  # for — on the spawn channel, `(ev.node id).type` decides which builders run — and the debug
  # evaluator can satisfy that for a non-root id only through `parseParent`. Without it the read
  # refuses BY NAME. The message is asserted, not merely that something threw: several other
  # throws are reachable from the same fixture (the kindless `unknown attribute` among them), and
  # a `tryEval` cell would be equally satisfied by any of them. The clean arm — the same read with
  # `parseParent` supplied — answers in `tests/spawned-visibility.nix`, so the pair varies exactly
  # one formal.
  config.flake.testsError.spawned-visibility-refusals = {
    test-debug-composed-read-without-parseParent-refuses-by-name = {
      expr = genScope.childrenIds spawnedVisibility.debugNoParse "winnow";
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: evalDebug requires parseParent for non-root nodes";
      };
    };

    # ── THE MIS-POINTED PARENT, WHICH MESSAGE EACH ARM CARRIES ──
    # The boolean pair — that BOTH arms refuse catchably, where one used to diverge into an
    # uncatchable `stack overflow` — is `tests/spawned-visibility.nix`. Two throws are reachable
    # from the mis-pointed fixtures and they name different causes a caller must act differently
    # on, so a `tryEval` cell is equally satisfied by either and only these pin which fired.
    test-a-parent-that-does-not-carry-the-child-is-refused-by-name = {
      expr = spawnedVisibility.misPointedToChildless.node "winnow";
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: node 'winnow' not reachable (parent: husk)";
      };
    };
    test-a-parent-that-does-not-resolve-is-refused-by-name = {
      expr = spawnedVisibility.misPointedToUnresolvable.node "winnow";
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope: node 'winnow' not reachable (parent: nosuch) — 'nosuch' does not resolve either: its `parseParent` chain reaches no root. A parent naming a node the scope cannot ground is the same user error as a parent that does not carry the child, and it is refused the same way.";
      };
    };
  };

  # ── THE MATERIALIZATION WITH NO CONTAINMENT RELATION TO WALK ──
  # An evaluation declaring no `children` has nothing to descend, and it used to descend `{ }`
  # from every node and hand back the entry points as the tree. The catchability half and the
  # discriminating control — a graph whose nodes GENUINELY have no children, which must keep
  # answering — are in `tests/eval.nix`; what is pinned here is that the refusal names the
  # undeclared attribute rather than the node's own emptiness, since those are the two readings
  # the defect confused.
  config.flake.testsError.eval-refusals =
    let
      chainScope = genScope.buildRoots {
        parentGraph = genScope.overlays [
          (genScope.edge {
            from = "a";
            to = "root";
          })
          (genScope.edge {
            from = "c";
            to = "a";
          })
        ];
        decls = {
          root = { };
          a = { };
          c = { };
        };
      };
    in
    {
      test-materialization-without-a-children-attribute-refuses-by-name = {
        expr = builtins.attrNames ((genScope.eval { } { } chainScope).subtreeOf "root");
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope: cannot descend from 'root': this evaluation declares no `children` attribute, so there is no containment relation to walk and a materialization would answer the entry points alone — a partial tree with nothing marking it partial. A node that genuinely has no children is a declared `children` answering `{ }`, which is a different answer and stays available. Declare `children`, or read the node set through `scope.nodeOrder`, which needs no descent.";
        };
      };
    };

  # ── THE SEAL'S GUARDED TRACE LOOKUP ──
  # `trace.<id>` selection on a missing id is the interpreter's own `attribute missing` abort —
  # uncatchable and naming neither the id nor the relation — so the seal's accessor carries a
  # guarded lookup that refuses BY NAME (ADR-0025 item 1), in the same message family as its
  # sibling `accessor.dependencies <missing>`. The clean arm (a present id answering the sealed
  # entry unchanged, and the `trace.<id> or default` opt-out) is in `tests/fold-equations.nix`.
  config.flake.testsError.fold-equations-refusals =
    let
      sealCtx = genScope.foldEquations { } {
        scope = genScope.buildRoots {
          kinds = genScope.mkKinds [ (genScope.mkKind { } "host") ];
          parentGraph = genScope.edge {
            from = "kid";
            to = "top";
          };
          decls = {
            top = { };
            kid = { };
          };
          types = {
            top = "host";
            kid = "host";
          };
        };
        schedule = {
          equations = {
            children = {
              name = "children";
              kind = "nta";
              readsAttrs = [ ];
              stratum = "structural";
              compute = _self: _id: { };
            };
          };
        };
        parseParent = _: null;
        # The empty relation, contracted. It needs no node references and therefore no membership
        # authority, which is why this one is built inline rather than through
        # `tests/_fixtures/declared.nix`.
        declaredDependencies = genGraph.mkDeclaredEdges { };
      };
    in
    {
      test-the-seals-trace-lookup-on-a-missing-id-refuses-by-name = {
        expr = sealCtx.accessor.trace "ghost";
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope: no trace for node 'ghost' — node not reachable from roots";
        };
      };
    };

  # ── THE STARTING SET'S CARRIER, AND WHY THE TWO ARMS OWE THE SAME SENTENCE ──
  # A starting set is a SET OF GROUND ATOMS, and the two arms disagreed about a value outside that
  # carrier rather than refusing it: the closure arm reads a member's NAME and rebuilds its answer
  # canonically, the round arm carries the VALUE through. On `seed = { a = 42; }` they returned
  # `{ a = true; q = true; }` and `{ a = 42; q = true; }` — and since the door routes on the
  # program, ADDING AN UNRELATED BINARY RULE changed a seeded atom's reported value. Neither the
  # termination argument nor the two-arm equivalence covers that, so the seed is refused.
  #
  # THREE OF THESE FOUR ARE ABOUT THE MESSAGE AND CANNOT BE BOOLEANS. That each refuses is in
  # `tests/least-model.nix` beside its live control. That the two arms refuse with the IDENTICAL
  # sentence is the property the defect made false, and `tryEval` discards exactly the text that
  # carries it.
  #
  # ★ THE FOURTH IS THE ORDERING CELL, and it is why a `success = false` cell would not do. A
  # directly bound closure arm holding a conjunctive program AND a bad seed is the ONLY call at
  # which the order of the two refusals is observable — the door never routes a conjunctive program
  # to that arm. Under a seed-first ordering that caller still gets a REAL REFUSAL; they just get
  # the wrong one, and are told nothing about why fixing the seed will not make this arm answer.
  config.flake.testsError.least-model-refusals =
    let
      # `q :- a.` — the smallest program whose answer moves with the starting set.
      unary = genScope.mkProgram [
        {
          head = "q";
          pos = [ "a" ];
        }
      ];
      # The same program plus an UNRELATED binary rule. That rule is the whole of the difference:
      # it mentions neither `a` nor `q`, and it is what routes the door to the round arm.
      conj = genScope.mkProgram [
        {
          head = "q";
          pos = [ "a" ];
        }
        {
          head = "z";
          pos = [
            "m"
            "n"
          ];
        }
      ];
      # The payload refusal is a function of the SEED ALONE, so the two arms owe the same string.
      # It is written once here for that reason and not to save a line: two literals would be
      # equally satisfied by two arms that refuse DIFFERENTLY, which is the shape this row closes.
      payloadRefusal = ''gen-scope: the seed carries a value on ["a"], the first of them a int. A starting set is a SET OF GROUND ATOMS and `true` is the only value a member takes, so a payload is REFUSED rather than canonicalised: the closure arm reads a member's NAME and the round arm carries its VALUE through, so the two compute different things about a value the carrier does not contain'';
    in
    {
      test-the-round-arm-refuses-a-seed-carrying-a-value = {
        expr = genScope.leastModelRounds {
          a = 42;
        } conj;
        expectedError = {
          type = "ThrownError";
          msg = exactly payloadRefusal;
        };
      };

      test-the-closure-arm-refuses-the-same-seed-with-the-same-message = {
        expr = genScope.leastModelUnary {
          a = 42;
        } unary;
        expectedError = {
          type = "ThrownError";
          msg = exactly payloadRefusal;
        };
      };

      # The non-set arm names the TYPE it received and the encoding it wanted. Before the guard this
      # raised the EVALUATOR's `expected a set but found a list`, which is a `TypeError` that
      # `tryEval` does not contain and no cell could observe.
      test-a-non-set-seed-is-refused-by-name = {
        expr = genScope.leastModelUnary [ "a" ] unary;
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope: the seed is a list rather than a set of ground atoms — `lfp_{⊇S} T_P` is taken over subsets of the Herbrand base, and a starting set is written as an attribute set whose every value is `true`";
        };
      };

      # ★ THE ORDERING CELL. The same seed as the two above and a conjunctive program: the arm owes
      # the PROGRAM refusal, because fixing the seed would not make this arm answer.
      test-a-directly-bound-closure-arm-names-the-PROGRAM-before-the-seed = {
        expr = genScope.leastModelUnary {
          a = 42;
        } conj;
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope: leastModelUnary is unary-only: the rule for 'z' has a positive body of arity 2";
        };
      };
    };

  # ── THE DECLARED RELATION'S INPUT TYPE, AND THE TWO ENTRIES THAT STATE IT ──
  # `gen-graph` ships the CONSTRUCTOR, the shared TYPE and the discriminator, and deliberately no
  # refusal helper: a refusal minted there would name `gen-graph` for a defect at this library's
  # door. So each entry states its OWN, naming itself — and a discriminator no consumer calls is a
  # guard nobody calls, which is what these cells hold.
  #
  # BOTH DETAIL ARMS ARE EXERCISED, one per entry, because they are not interchangeable. A bare
  # relation is a `lambda` and the type names it usefully; a hand-assembled attrset carrying an
  # `index` and a `dependencies` has the right SHAPE — `builtins.typeOf` says `set` and tells the
  # reader nothing — so that arm names the CONSTRUCTOR that was missed instead. The second arm is
  # the one that matters: the predicate is NOMINAL on purpose, and this value is precisely the
  # bypass a structural predicate would admit.
  #
  # THE SUBJECT HERE IS THE MESSAGE. That the refusals FIRE, that the third state survives them, and
  # that a contracted relation is served are in `tests/declared-relation-contract.nix`, whose
  # controls are what separate "this entry refused" from "this entry refuses everything".
  config.flake.testsError.declared-relation-contract-refusals =
    let
      contractScope = genScope.buildRoots {
        parentGraph = genScope.vertex "solo";
        decls.solo.v = 1;
        types = { };
      };
      attributes = {
        children = _self: _id: { };
        self-v = self: id: (self.node id).decls.v;
      };
      # A hand-assembled value with the constructor's own field names and no tag: the bypass the
      # nominal predicate exists to refuse.
      forged = {
        index = { };
        dependencies = _: [ ];
      };
    in
    {
      # `foldEquations`, on a BARE relation — the shape every caller wrote before the contract
      # existed, and the one a consumer reaches for by habit.
      test-foldEquations-refuses-an-uncontracted-relation-by-name = {
        expr = genScope.foldEquations { } {
          scope = contractScope;
          parseParent = _: null;
          schedule.equations = {
            children = {
              name = "children";
              kind = "nta";
              readsAttrs = [ ];
              stratum = "structural";
              compute = _self: _id: { };
            };
          };
          declaredDependencies = _: [ ];
        };
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope.foldEquations: `declaredDependencies` must be the relation `gen-graph.mkDeclaredEdges` returns; received a lambda. Build it with `gen-graph.mkDeclaredEdges` and pass the result: the relation is contracted where it is constructed, so a value this entry cannot tell apart from a contracted one is one it must refuse.";
        };
      };

      # `eval`, on the FORGED attrset. The delegate names ITSELF rather than borrowing the fold's
      # name: an evaluator reached directly is a different door, and a message naming the wrong one
      # sends a reader to a call site they did not make.
      test-eval-refuses-a-forged-relation-by-name = {
        expr =
          (genScope.eval {
            declaredDependencies = forged;
          } attributes contractScope).get
            "solo"
            "self-v";
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope.eval: `declaredDependencies` must be the relation `gen-graph.mkDeclaredEdges` returns; received an attrset that `mkDeclaredEdges` did not build. Build it with `gen-graph.mkDeclaredEdges` and pass the result: the relation is contracted where it is constructed, so a value this entry cannot tell apart from a contracted one is one it must refuse.";
        };
      };
    };

  # ── THE KIND REGISTRY'S ADMISSION, BY MESSAGE ──
  # The registry doors decide a TYPE: every entry a kind `mkKinds` minted, filed under its own name,
  # and coherent with every resolved `below` that reaches it (`cascade.nix`, `kindSetDefect`). Each
  # door mints its OWN refusal naming ITSELF; a message naming the cascade for a defect at `eval`'s
  # door sends a reader to a call they did not make.
  #
  # THAT these fire, and that a minted registry and the no-kinds cases still pass, are in
  # `tests/registry-admission.nix`, whose `tryEval` cells carry the part no message can.
  #
  # ★ THE NON-ATTRSET ARM IS NOT COSMETIC. Before the guard, `kinds = [ … ]` reached
  # `unregisteredKinds`, whose `kinds.kinds or { }` falls back to `{ }` on a list — so a
  # mis-TYPED registry was reported as an unregistered KIND, naming the wrong defect at the wrong
  # argument.
  config.flake.testsError.registry-admission-refusals =
    let
      spawnOf = suffix: _self: id: {
        "${id}-${suffix}" = {
          id = "${id}-${suffix}";
          parent = id;
          decls = { };
        };
      };

      # G4: `mkKind` BUILDS this, and what it builds is a declaration the fold cannot mint.
      selfNaming = genScope.mkKind {
        below = [ "k" ];
        spawns.k = spawnOf "i";
      } "k";
      declarationRegistry = {
        kinds.k = selfNaming;
      };

      # G3: two registries built from disagreeing declarations, merged with `//`.
      okKinds = genScope.mkKinds [
        (genScope.mkKind { } "item")
        (genScope.mkKind {
          below = [ "item" ];
          spawns.item = spawnOf "i";
        } "k")
      ];
      upKinds = genScope.mkKinds [
        (genScope.mkKind { } "k")
        (genScope.mkKind {
          below = [ "k" ];
          spawns.k = spawnOf "i";
        } "item")
      ];
      merged = okKinds // {
        kinds = okKinds.kinds // {
          inherit (upKinds.kinds) item;
        };
      };

      # C4: a minted host updated with `//`, its `below` and its `spawns` both extended, so the
      # door admits it and the evaluator finds no resolved record for the new key.
      edited = okKinds // {
        kinds = okKinds.kinds // {
          k = okKinds.kinds.k // {
            below = okKinds.kinds.k.below ++ [ "extra" ];
            spawns = okKinds.kinds.k.spawns // {
              extra = spawnOf "e";
            };
          };
        };
      };

      # The hand-built record — the route the constructor does not stand in front of.
      handBuilt = kinds: {
        nodes.root = {
          id = "root";
          type = "k";
          parent = null;
          decls = { };
        };
        nodeOrder = [ "root" ];
        inherit kinds;
      };
      attributes.children = _self: _id: { };

      buildWith =
        kinds:
        genScope.buildRoots {
          parentGraph = genScope.vertex "root";
          types.root = "k";
          decls.root = { };
          inherit kinds;
        };

      # The invariant frame, with the entry name and the detail left to the cell.
      registryRefusal =
        entry: detail:
        "gen-scope.${entry}: `scope.kinds` must be a kind registry, whose `kinds` maps each name to the kind `mkKinds` minted under it; ${detail}. Mint the kinds with `mkKinds` over their declarations and pass the result.";

      declarationDetail = ''holds entries that are not minted kinds: ["`k` is a kind declaration built by `mkKind`, not a kind `mkKinds` minted: pass the declarations through `mkKinds`"]'';
      mergeDetail = "files under 'k' a kind that differs from the kind 'k' that entry 'item' resolved in its `below` (compared on `name`, `below`, `depth`, the `spawns`/`nta` key sets and the kind value's mark). Two different kinds share one name — a merge of registries built from different declarations";
    in
    {
      # G4 — the EVALUATOR, on a hand-built registry of declarations: a TYPE refusal naming it.
      test-G4-eval-refuses-a-registry-of-declarations-by-name = {
        expr = (genScope.eval { } attributes (handBuilt declarationRegistry)).allNodeIds;
        expectedError = {
          type = "ThrownError";
          msg = exactly (registryRefusal "eval" declarationDetail);
        };
      };

      # And on a NON-attrset, where the type is all there is to name.
      test-eval-names-the-type-of-a-registry-that-is-not-an-attrset = {
        expr = (genScope.eval { } attributes (handBuilt [ selfNaming ])).allNodeIds;
        expectedError = {
          type = "ThrownError";
          msg = exactly (registryRefusal "eval" "received a list");
        };
      };

      # G3 / C1 — the merge, refused by name at the evaluator's door.
      test-G3-eval-refuses-a-merge-filing-two-kinds-under-one-name = {
        expr = (genScope.eval { } attributes (handBuilt merged)).allNodeIds;
        expectedError = {
          type = "ThrownError";
          msg = exactly (registryRefusal "eval" mergeDetail);
        };
      };

      # C4 — the evaluator's own refusal of a spawn key with no resolved kind to stamp.
      test-C4-a-spawn-with-no-resolved-kind-names-host-key-and-kind = {
        expr = (genScope.eval { } attributes (handBuilt edited)).allNodeIds;
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope: node 'root' of kind 'k' spawns 'extra', and its kind resolves no kind 'extra' in its `below`: the kind record was updated after `mkKinds` minted it. A spawned node's kind is the minted record its host's kind resolved, so a spawn with none has no kind to stamp. Declare the kinds through `mkKinds` rather than editing a minted kind.";
        };
      };

      # The CONSTRUCTOR names itself: a record refused before it forms is a defect at a different
      # call site from one refused as it is read, and a caller fixes them in different places.
      test-G4-buildRoots-refuses-a-registry-of-declarations-by-name = {
        expr = (buildWith declarationRegistry).nodeOrder;
        expectedError = {
          type = "ThrownError";
          msg = exactly (registryRefusal "buildRoots" declarationDetail);
        };
      };

      test-buildRoots-names-the-type-of-a-registry-that-is-not-an-attrset = {
        expr = (buildWith [ selfNaming ]).nodeOrder;
        expectedError = {
          type = "ThrownError";
          msg = exactly (registryRefusal "buildRoots" "received a list");
        };
      };

      test-G3-buildRoots-refuses-the-same-merge-by-name = {
        expr = (buildWith merged).nodeOrder;
        expectedError = {
          type = "ThrownError";
          msg = exactly (registryRefusal "buildRoots" mergeDetail);
        };
      };

      # F-1 (den-hoag-n6dh7 landing gate): a hand-built registry whose kind carries a spawn named
      # `type`, outside its `below` and with a builder that throws, is refused BY NAME before any
      # builder is forced. The door's empty-set guard compares `{ } != k.spawns`; the other operand
      # order reads the left set's `type` attribute (Nix asks whether both sides are derivations)
      # and surfaces the caller's throw in place of this refusal, on every evaluator.
      test-F1-buildRoots-refuses-a-spawn-outside-below-without-forcing-its-builder = {
        expr =
          (buildWith (
            okKinds
            // {
              kinds = okKinds.kinds // {
                k = okKinds.kinds.k // {
                  spawns = okKinds.kinds.k.spawns // {
                    type = throw "a spawn builder the door must not force";
                  };
                };
              };
            }
          )).nodeOrder;
        expectedError = {
          type = "ThrownError";
          msg = exactly (
            registryRefusal "buildRoots" ''holds entries that are not minted kinds: ["`k` declares a spawn outside its own `below` set"]''
          );
        };
      };

      # The third evaluator entry, which shares the guard and must not borrow another's name.
      # Read through `node`, and the accessor is load-bearing. The guard fires when a field of
      # `requireScope`'s RESULT is selected: `trace` and `getTraced` are assembled without reaching
      # the scope and report "no error was caught" against a live guard, while `allNodes` and
      # `allNodeIds` throw this entry's OWN materialization refusal first and would pin this cell to
      # that message instead. Only a read that reaches a node reaches the registry.
      test-G4-evalDebug-refuses-a-registry-of-declarations-under-its-own-name = {
        expr = (genScope.evalDebug { } attributes (handBuilt declarationRegistry)).node "root";
        expectedError = {
          type = "ThrownError";
          msg = exactly (registryRefusal "evalDebug" declarationDetail);
        };
      };
    };

  # ── A KIND'S VALUE, REFUSED BY NAME AT EVERY DOOR IT CROSSES (den-hoag-l0y, arm (B′)) ──
  # Each cell pins its MESSAGE: before the value had a door, the name and the hand-written stand-in
  # were refused alike, by `mkKind`'s closed options, so a cell reading only that a refusal fired
  # stays green on the tree this suite exists to move off. The admitting half is `ci/tests/kind-value.nix`.
  config.flake.testsError.kind-value-refusals =
    let
      standIn = {
        kind = "host";
        options = { };
      };
      valueOf = name: mark: {
        kind = name;
        __mint.minted = mark;
      };
      plain = mkKinds [
        (mkKind { } "host")
        (mkKind { below = [ "host" ]; } "leaf")
      ];
      withValue = r: v: r // { kindValue = v; };
      buildWith =
        kinds:
        (genScope.buildRoots {
          types.a = "host";
          inherit kinds;
        }).nodes;
      registryRefusal =
        detail:
        "gen-scope.buildRoots: `scope.kinds` must be a kind registry, whose `kinds` maps each name to the kind `mkKinds` minted under it; ${detail}. Mint the kinds with `mkKinds` over their declarations and pass the result.";
    in
    {
      # c3: the hand-written stand-in carries no mint, so it is not a kind value.
      test-c3-mkKind-refuses-a-hand-written-stand-in = {
        expr = mkKind { kindValue = standIn; } "host";
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope.mkKind: kind 'host' carries a `kindValue` with no mint-backed mark (`__mint.minted`); a hand-written `{ kind = ...; ... }` is not a kind value: take the kind from a schema";
        };
      };
      # c4: a name is a reference, not a declaration.
      test-c4-mkKind-refuses-a-kind-name = {
        expr = mkKind { kindValue = "host"; } "host";
        expectedError = {
          type = "ThrownError";
          msg = exactly ''gen-scope.mkKind: kind 'host' carries the kind name "host" as its `kindValue`; a name is a reference, not a kind declaration: pass the kind value itself (e.g. `schema.widget`)'';
        };
      };
      test-mkKind-refuses-a-kind-value-of-another-type = {
        expr = mkKind { kindValue = 42; } "host";
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope.mkKind: kind 'host' carries a `kindValue` that is a int, not a kind value";
        };
      };
      # c10: a minted record edited past `mkKind` meets the same shape arm at the registry door.
      test-c10-buildRoots-refuses-a-forged-kind-value = {
        expr = buildWith { kinds.host = withValue plain.kinds.host standIn; };
        expectedError = {
          type = "ThrownError";
          msg = exactly (
            registryRefusal ''holds entries that are not minted kinds: ["`host` carries a `kindValue` with no mint-backed mark (`__mint.minted`); a hand-written `{ kind = ...; ... }` is not a kind value: take the kind from a schema"]''
          );
        };
      };
      # The presence arm: a record hand-built without the field is refused by naming it.
      test-buildRoots-refuses-a-kind-record-carrying-no-kind-value-field = {
        expr = buildWith { kinds.host = builtins.removeAttrs plain.kinds.host [ "kindValue" ]; };
        expectedError = {
          type = "ThrownError";
          msg = exactly (
            registryRefusal ''holds entries that are not minted kinds: ["`host` carries no `kindValue` field"]''
          );
        };
      };
      # C1: a spawn builder choosing its child's kind value, refused beside the builder `type` arm,
      # whether or not the produced kind declares one (it was admitted, or silently overwritten).
      test-C1-a-spawn-builder-carrying-a-kind-value-is-refused-by-name = {
        expr =
          (genScope.eval { } { children = _self: _id: { }; } (
            genScope.buildRoots {
              parentGraph = genScope.vertex "a";
              types.a = "host";
              kinds = mkKinds [
                (mkKind { } "svc")
                (mkKind {
                  below = [ "svc" ];
                  spawns.svc = _self: id: {
                    kid = {
                      id = "kid";
                      parent = id;
                      decls = { };
                      kindValue = valueOf "host" "host:b";
                    };
                  };
                } "host")
              ];
            }
          )).get
            "a"
            "derived-children";
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope: kind 'host' spawns 'svc' and its builder returned a child 'kid' carrying its own `kindValue`. A spawn does not choose its child's kind value any more than its kind: the value is the one the produced kind declares (`mkKind { kindValue = …; }`), stamped by the substrate with its `type` — a value chosen while the spawn fires is one no kind declared. Drop the field.";
        };
      };
      # C2: a hand-built node of registered `host` carrying a value `host` does not declare.
      test-C2-eval-refuses-a-node-whose-kind-value-contradicts-its-kind = {
        expr =
          (genScope.eval { } { children = _self: _id: { }; } {
            kinds = mkKinds [ (mkKind { kindValue = valueOf "host" "host:a"; } "host") ];
            nodeOrder = [ "a" ];
            nodes.a = {
              id = "a";
              type = "host";
              parent = null;
              decls = { };
              kindValue = valueOf "host" "host:b";
            };
          }).allNodeIds;
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope.eval: node 'a' of kind 'host' carries a `kindValue` that is not the one its kind declares (compared by the kind value's mark). A node of a registered kind carries its kind's value, and a different one gives the node two kinds that disagree. Build the scope with `buildRoots`, which stamps the value, or carry the kind's own value.";
        };
      };
      # c11: a merge filing under `host` a kind whose value differs from the one `leaf` resolved.
      test-c11-buildRoots-refuses-a-merge-whose-kind-values-differ = {
        expr = buildWith {
          kinds = {
            host = withValue plain.kinds.host (valueOf "host" "host:a");
            leaf = plain.kinds.leaf // {
              belowKinds.host = withValue plain.kinds.host (valueOf "host" "host:b");
            };
          };
        };
        expectedError = {
          type = "ThrownError";
          msg = exactly (
            registryRefusal "files under 'host' a kind that differs from the kind 'host' that entry 'leaf' resolved in its `below` (compared on `name`, `below`, `depth`, the `spawns`/`nta` key sets and the kind value's mark). Two different kinds share one name — a merge of registries built from different declarations"
          );
        };
      };
    };

  # ── THE IDENTIFIER DOORS (den-hoag-bkdkg) ──
  # A record handed where a node identifier goes — the node VALUE, typically — used to abort past
  # `tryEval` on an attribute lookup, or answer `false`/`[ ]` about a name no node carries. Each cell
  # names the door that refuses: the evaluators' `self.node`/`self.get`, which every structural query
  # reaches by composition; the three queries that hold a name they only compare; and the minting
  # entry. `evalDebug` builds its own accessor and `evalWarm` reaches `eval`'s, so each is driven here
  # rather than assumed from the production evaluator's cells.
  config.flake.testsError.identifier-door-refusals =
    let
      S = genScope;
      roots = S.buildRoots {
        parentGraph = S.edge {
          from = "b";
          to = "a";
        };
      };
      attributes = {
        x = self: id: 1;
        children =
          self: id:
          builtins.removeAttrs (builtins.intersectAttrs { b = 0; } roots.nodes) (
            if id == "a" then [ ] else [ "b" ]
          );
        imports = self: id: [ ];
        "edges-I" = self: id: [ ];
      };
      self = S.eval { } attributes roots;
      debug = S.evalDebug {
        parseParent = id: if id == "b" then "a" else null;
      } attributes roots;
      warm = S.evalWarm { } {
        scope = roots;
        inherit attributes;
        prior = self;
        decision = S.mkDecision {
          isClean = _: false;
          reusable = _: [ ];
        };
      };
      X = {
        name = "a";
      };
      mint =
        ident: relatum:
        S.mintStrata { } [
          {
            pass = 0;
            identifier = "pewter";
            kind = "thimble";
            relata = { };
            content = { };
            site = "p0";
          }
          {
            pass = 1;
            identifier = ident;
            kind = "basting";
            relata.warp = relatum;
            content = { };
            site = "p1";
          }
        ];
      refused = who: noun: {
        type = "ThrownError";
        msg = exactly "gen-scope.${who}: got set, expected ${noun} (a string)";
      };
      # gen-graph's identifier refusal, composed with this library's own literal door and value
      # (den-hoag-7jltk): the text is gen-graph's `notAnIdentifier`, the door is gen-scope's.
      refusedId = who: {
        type = "ThrownError";
        msg = exactly ((genGraph.key "gen-scope").notAnIdentifier who { });
      };
      node = refusedId "self.node";
      get = refusedId "self.get";
    in
    {
      test-self-node-refuses-a-record = {
        expr = self.node X;
        expectedError = node;
      };
      test-self-get-refuses-a-record = {
        expr = self.get X "x";
        expectedError = get;
      };
      test-evalDebug-node-refuses-a-record = {
        expr = debug.node X;
        expectedError = node;
      };
      test-evalDebug-get-refuses-a-record = {
        expr = debug.get X "x";
        expectedError = get;
      };
      test-evalDebug-getTraced-refuses-a-record = {
        expr = (debug.getTraced X "x").trace;
        expectedError = refusedId "self.getTraced";
      };
      test-evalWarm-node-refuses-a-record = {
        expr = warm.node X;
        expectedError = node;
      };
      test-evalWarm-get-refuses-a-record = {
        expr = warm.get X "x";
        expectedError = get;
      };
      test-parent-refuses-a-record-at-self-node = {
        expr = S.parent self X;
        expectedError = node;
      };
      test-ancestors-refuses-a-record-at-self-node = {
        expr = S.ancestors self X;
        expectedError = node;
      };
      test-children-refuses-a-record-at-self-get = {
        expr = S.children self X;
        expectedError = get;
      };
      test-childrenIds-refuses-a-record-at-self-get = {
        expr = S.childrenIds self X;
        expectedError = get;
      };
      test-descendants-refuses-a-record-at-self-get = {
        expr = S.descendants self X;
        expectedError = get;
      };
      test-followEdge-refuses-a-record-at-self-get = {
        expr = S.followEdge "I" self X;
        expectedError = refusedId "resolve";
      };
      test-collectImports-refuses-a-record-at-self-get = {
        expr = S.collectImports (_: _: [ ]) self X;
        expectedError = refusedId "resolve";
      };
      test-isAncestor-refuses-a-record-it-would-only-compare = {
        expr = S.isAncestor self X "b";
        expectedError = refusedId "isAncestor";
      };
      test-isDescendant-refuses-a-record-it-would-only-compare = {
        expr = S.isDescendant self X "a";
        expectedError = refusedId "isDescendant";
      };
      test-nodesByType-refuses-a-record-kind = {
        expr = S.nodesByType self X;
        expectedError = refused "nodesByType" "a kind name";
      };
      test-mintStrata-refuses-a-record-identifier = {
        expr = builtins.attrNames (mint X "pewter").nodes;
        expectedError = refusedId "mintStrata: an emitter's identifier";
      };
      test-mintStrata-refuses-a-record-relatum = {
        expr = builtins.attrNames (mint "b1" { name = "pewter"; }).nodes;
        expectedError = refusedId "mintStrata: relatum 'warp' of 'b1'";
      };
    };

  # ── THE `nta` CHANNEL'S REFUSALS (den-hoag-n6dh7 U1-e, U1-j, U1-l, U1-m, P-f) ──
  # Every refusal of the recursive NTA form carries the `nta:` token, so a reader tells its rule
  # apart from `spawns`' by the token and never by the builder's shape. The fixture is shared with
  # `tests/nta.nix`, whose value cells are the clean path over the same graph.
  config.flake.testsError.nta-refusals =
    let
      fx = import ./tests/_fixtures/nta.nix { inherit genScope; };
      inherit (genScope) mintNtaId;
      k = mkKind { } "t";
      loop =
        circular
          {
            carrier = {
              bottom = 0;
              leq = a: b: a <= b;
              height = 1;
              quotient = false;
            };
          }
          (
            _: _: _:
            { }
          );
      forced = v: builtins.deepSeq v v;
      seedRefusal = seed: forced (map (e: e.value) (fx.seedOfChild (fx.seeded seed)));
      at = "gen-scope.nta: kind 'raw' NTA 'x' on host 'r'";
      el = "${at}, child 'g'/'k', seed element 0";
      c = fx.child;
      err = msg: {
        type = "ThrownError";
        msg = exactly msg;
      };
    in
    {
      # ── item 1 · the declaration ladder, in order ──
      test-an-nta-that-is-not-an-attribute-set-is-refused = {
        expr = mkKind {
          nta = 3;
        } "t";
        expectedError = err "gen-scope.mkKind: nta: kind 't' declares an `nta` that is a int rather than an attribute set of builders keyed by NTA name";
      };
      # The circular arm precedes the applicability arm: a circular declaration is not `callable`,
      # so under `spawns`' order this message could never fire.
      test-a-circular-nta-builder-is-refused-as-circular = {
        expr = mkKind {
          nta.c = loop;
        } "t";
        expectedError = err "gen-scope.mkKind: nta: kind 't' declares NTA(s) [\"c\"] whose builder is a circular declaration. An `nta` builder computes the NODE SET, and a node set that is a fixed point of its own iterate is the per-step growth the spawn-read restriction refuses. A child's ATTRIBUTES may be circular; its EXISTENCE may not. Declare the builder as a plain function.";
      };
      test-an-nta-builder-that-cannot-be-applied-is-refused = {
        expr = mkKind {
          nta.c = 3;
        } "t";
        expectedError = err "gen-scope.mkKind: nta: kind 't' declares NTA(s) [\"c\"] whose builder cannot be applied";
      };

      # ── `notAKind`'s four arms ──
      test-registry-a-record-with-no-nta-field-is-refused = {
        expr = mkKinds [ (builtins.removeAttrs k [ "nta" ]) ];
        expectedError = err ''gen-scope.mkKinds: not every entry is a kind declaration: ["entry 0 nta: carries no `nta` field"]'';
      };
      test-registry-an-nta-that-is-not-an-attribute-set-is-refused = {
        expr = mkKinds [ (k // { nta = 3; }) ];
        expectedError = err ''gen-scope.mkKinds: not every entry is a kind declaration: ["entry 0 nta: carries an `nta` that is not an attribute set"]'';
      };
      test-registry-a-circular-nta-builder-is-refused = {
        expr = mkKinds [ (k // { nta.c = loop; }) ];
        expectedError = err ''gen-scope.mkKinds: not every entry is a kind declaration: ["entry 0 nta: carries an `nta` builder that is a circular declaration"]'';
      };
      test-registry-an-nta-builder-that-cannot-be-applied-is-refused = {
        expr = mkKinds [ (k // { nta.c = 3; }) ];
        expectedError = err ''gen-scope.mkKinds: not every entry is a kind declaration: ["entry 0 nta: carries an `nta` builder that cannot be applied"]'';
      };

      # ── item 2 · the seed is a list of addresses (U1-l, U1-m, P-f) ──
      test-U1l-a-constant-seed-is-refused = {
        expr = seedRefusal { x = 7; };
        expectedError = err "${at}, child 'g'/'k': a seed is a list of addresses into the host's evaluated definitions, and this builder returned a set. A builder points into its host's definitions and never supplies its child's definitions as a value, which is what makes a constant seed inexpressible.";
      };
      test-U1l-a-value-inside-the-list-is-not-an-address = {
        expr = seedRefusal [ { x = 7; } ];
        expectedError = err "${el}: a seed element is not an address { attr : string; def : int >= 0; at : [ name | index >= 0 ]; }";
      };
      test-U1l-an-ill-typed-address-is-not-an-address = {
        expr = seedRefusal [
          {
            attr = "defs";
            def = "0";
            at = [ "s" ];
          }
        ];
        expectedError = err "${el}: a seed element is not an address { attr : string; def : int >= 0; at : [ name | index >= 0 ]; }";
      };
      test-U1m-an-empty-path-is-refused = {
        expr = seedRefusal [ (fx.addr 0 [ ]) ];
        expectedError = err "${el}: an address with an empty path re-addresses a whole definition, which is not a strict sub-value of it. Name at least one step inside the definition.";
      };
      test-U1l-an-absent-path-does-not-resolve = {
        expr = seedRefusal [ (fx.addr 0 [ "absent" ]) ];
        expectedError = err "${el}: address does not resolve: the path [\"absent\"] is absent from definition 0 of 'defs'";
      };
      test-Pf-an-attribute-the-evaluation-does-not-declare-does-not-resolve = {
        expr = seedRefusal [
          {
            attr = "nosuch";
            def = 0;
            at = [ "s" ];
          }
        ];
        expectedError = err "${el}: address does not resolve: the evaluation declares no attribute 'nosuch' to carry the host's definitions";
      };
      test-an-attribute-that-is-not-a-list-does-not-resolve = {
        expr = seedRefusal [
          {
            attr = "notAList";
            def = 0;
            at = [ "s" ];
          }
        ];
        expectedError = err "${el}: address does not resolve: 'notAList' on the host is a set, not a list of definitions";
      };
      test-a-definition-out-of-range-does-not-resolve = {
        expr = seedRefusal [ (fx.addr 5 [ "s" ]) ];
        expectedError = err "${el}: address does not resolve: 'defs' on the host holds 1 definition(s), and the address names definition 5";
      };

      # ── item 3 · the firing-time shapes and the registered collision (U1-j) ──
      test-a-builder-output-that-is-not-an-attribute-set-is-refused = {
        expr = builtins.attrNames ((fx.rawRun (_: _: [ ])).get "r" "nta-children").x;
        expectedError = err "${at}: the builder returned a list rather than an attribute set of groups { <group> = { <key> = <seed>; }; }";
      };
      test-a-group-that-is-not-an-attribute-set-is-refused = {
        expr = builtins.attrNames ((fx.rawRun (_: _: { g = [ ]; })).get "r" "nta-children").x.g;
        expectedError = err "${at}: the builder's group 'g' is a list rather than an attribute set of seeds keyed by child key";
      };
      test-U1j-a-minted-id-a-registered-node-carries-is-refused = {
        expr =
          (fx.rawNodes (_: _: { g.k = [ (fx.addr 0 [ "s" ]) ]; }) {
            ${c} = {
              id = c;
              type = "raw";
              parent = null;
              decls = { };
            };
          }).allNodeIds;
        expectedError = err "${at}: group 'g' key 'k' mints the identifier '${c}', which is already a registered node's. A registered id is answered from the scope's roots, so this child would be discarded silently. Register the node under another id.";
      };

      # ── item 5 · an identifier the product does not carry ──
      test-an-absent-group-is-not-reachable = {
        expr = (fx.seeded [ (fx.addr 0 [ "s" ]) ]).node (mintNtaId {
          host = "r";
          name = "x";
          group = "nog";
          key = "k";
        });
        expectedError = err "gen-scope.nta: node '${
          mintNtaId {
            host = "r";
            name = "x";
            group = "nog";
            key = "k";
          }
        }' not reachable: NTA 'x' on host 'r' yields no group 'nog'";
      };
      test-an-absent-key-is-not-reachable = {
        expr = (fx.seeded [ (fx.addr 0 [ "s" ]) ]).node (mintNtaId {
          host = "r";
          name = "x";
          group = "g";
          key = "nokey";
        });
        expectedError = err "gen-scope.nta: node '${
          mintNtaId {
            host = "r";
            name = "x";
            group = "g";
            key = "nokey";
          }
        }' not reachable: NTA 'x' on host 'r' yields group 'g' with no key 'nokey'";
      };

      # ── item 6 · the carriage ──
      test-a-key-shared-across-the-halves-is-refused-at-enumeration = {
        expr =
          (genScope.eval { } fx.attributes (
            fx.scopeOf (mkKinds [
              (mkKind { } "leaf")
              (mkKind {
                below = [ "leaf" ];
                spawns.leaf = _: _: {
                  ${c} = {
                    id = c;
                    decls = { };
                  };
                };
                nta.x = _: id: if id == "r" then { g.k = [ (fx.addr 0 [ "s" ]) ]; } else { };
              } "raw")
            ]) (fx.root "raw" { defs = [ { s = { }; } ]; })
          )).allNodeIds;
        expectedError = err "gen-scope.nta: node 'r' carries an `nta` child '${c}' under a key its `children` or `derived-children` also carries. The three halves compose into one child map, and a shared key would discard one record silently. An `nta` identifier is minted by the substrate, so the other half chose it: choose a key that is not an `nta` identifier.";
      };
      test-a-hand-written-nta-children-is-refused = {
        expr =
          (genScope.eval { } (
            fx.attributes
            // {
              nta-children = _: _: { };
            }
          ) (fx.scopeOf (mkKinds [ fx.tree ]) (fx.root "tree" { defs = [ { } ]; }))).get
            "r"
            "defs";
        expectedError = err "gen-scope.eval: nta: `attributes` declares `nta-children` directly. An `nta` is declared on the KIND it grows from — `mkKind { nta = { <name> = builder; }; }` — so its children are stamped with the host's kind and minted from the host's coordinates. Move the builder onto its host kind's `nta`.";
      };
    };

  # ── `getNta`'s REFUSALS (den-hoag-n6dh7 Unit 2.0) ──
  # One cell per refusal. An absent NTA, group or key is refused with `ntaLookup`'s `nta:` text,
  # naming the host; an unknown or quotient attribute with `getNta`'s own door-named text (7gp66 R6,
  # den-hoag-n6dh7 C1) rather than `get`'s reused text; and a reader bound to no node — the
  # evaluation's record, or any reader of an evaluation running no `nta` channel — with its own.
  # The value cells are `tests/nta.nix`'s U2.0 block.
  config.flake.testsError.nta-getNta-refusals =
    let
      fx = import ./tests/_fixtures/nta.nix { inherit genScope; };
      inherit (genScope) mintNtaId;
      read =
        evaluator: body:
        (fx.nestWith evaluator {
          reads = body;
          q =
            circular
              {
                carrier = {
                  bottom = 0;
                  leq = a: b: a <= b;
                  height = 1;
                  quotient = true;
                };
              }
              (
                _: _: _:
                0
              );
        }).get
          "r"
          "reads";
      err = msg: {
        type = "ThrownError";
        msg = exactly msg;
      };
      unbound = "gen-scope.nta: `getNta` reads the reading node's own `nta` children, so it is answered only on a body's reader in an evaluation whose kinds declare an NTA. Outside a body, read a child by its identifier with `get`.";
    in
    {
      test-an-absent-nta-is-refused = {
        expr = read genScope.eval (self: _: self.getNta "nope" "g" "b" "v");
        expectedError = err "gen-scope.nta: `getNta`: host 'r' declares no NTA 'nope'";
      };
      test-an-absent-group-is-refused = {
        expr = read genScope.eval (self: _: self.getNta "sub" "nog" "b" "v");
        expectedError = err "gen-scope.nta: `getNta`: NTA 'sub' on host 'r' yields no group 'nog'";
      };
      test-an-absent-key-is-refused = {
        expr = read genScope.eval (self: _: self.getNta "sub" "g" "nokey" "v");
        expectedError = err "gen-scope.nta: `getNta`: NTA 'sub' on host 'r' yields group 'g' with no key 'nokey'";
      };
      # Depth 2: the host is itself an `nta` child, and the refusal names it.
      test-an-absent-key-under-a-child-host-is-refused = {
        expr =
          (fx.nestWith genScope.eval {
            inner = self: _: self.getNta "sub" "g" "nokey" "v";
            reads = self: _: self.getNta "sub" "g" "a" "inner";
          }).get
            "r"
            "reads";
        expectedError = err "gen-scope.nta: `getNta`: NTA 'sub' on host '${
          mintNtaId {
            host = "r";
            name = "sub";
            group = "g";
            key = "a";
          }
        }' yields group 'g' with no key 'nokey'";
      };
      test-an-unknown-attribute-is-refused-by-get = {
        expr = read genScope.eval (self: _: self.getNta "sub" "g" "b" "nosuch");
        expectedError = err "gen-scope.nta: `getNta`: unknown attribute 'nosuch' on NTA 'sub' group 'g' key 'b' of host 'r' (in self.get)";
      };
      test-a-quotient-attribute-is-refused-by-get = {
        expr = read genScope.eval (self: _: self.getNta "sub" "g" "b" "q");
        expectedError = err "gen-scope.nta: `getNta`: 'q' on NTA 'sub' group 'g' key 'b' of host 'r' demands a raw value of a quotient-converged instance — its carrier declares `quotient = true`, so what converged is a class representative under the declared order and not a fixed point of the step; `getNta` reads raw values only (in self.get)";
      };
      test-the-evaluations-own-record-is-unbound = {
        expr = (fx.nestWith genScope.eval { }).getNta "sub" "g" "b" "v";
        expectedError = err unbound;
      };
      test-a-reader-in-an-evaluation-running-no-nta-is-unbound = {
        expr =
          (genScope.eval { }
            {
              children = _: _: { };
              reads = self: _: self.getNta "sub" "g" "b" "v";
            }
            {
              nodes.r = {
                id = "r";
                parent = null;
                decls = { };
              };
              nodeOrder = [ "r" ];
            }
          ).get
            "r"
            "reads";
        expectedError = err unbound;
      };
      test-evalDebug-refuses-an-absent-group = {
        expr = read genScope.evalDebug (self: _: self.getNta "sub" "nog" "b" "v");
        expectedError = err "gen-scope.nta: `getNta`: NTA 'sub' on host 'r' yields no group 'nog'";
      };
      # `getNta`'s own door-named text, not `get`'s reused message: the OLD debug route resolved
      # the child by its minted id through the public `get`, so this cell reads
      # `gen-scope: unknown attribute 'nosuch' on node '<minted-id>'` — leaking the identifier the
      # caller never saw — until the debug accessor applies the attribute directly on the record
      # `ntaMember` already resolved (den-hoag-n6dh7, gate v0 §5 P5).
      test-evalDebug-refuses-an-unknown-attribute-by-getNta = {
        expr = read genScope.evalDebug (self: _: self.getNta "sub" "g" "b" "nosuch");
        expectedError = err "gen-scope.nta: `getNta`: unknown attribute 'nosuch' on NTA 'sub' group 'g' key 'b' of host 'r' (in self.get)";
      };
      test-evalDebug-refuses-a-quotient-attribute-by-getNta = {
        expr = read genScope.evalDebug (self: _: self.getNta "sub" "g" "b" "q");
        expectedError = err "gen-scope.nta: `getNta`: 'q' on NTA 'sub' group 'g' key 'b' of host 'r' demands a raw value of a quotient-converged instance — its carrier declares `quotient = true`, so what converged is a class representative under the declared order and not a fixed point of the step; `getNta` reads raw values only (in self.get)";
      };
      test-evalDebugs-own-record-is-unbound = {
        expr = (fx.nestWith genScope.evalDebug { }).getNta "sub" "g" "b" "v";
        expectedError = err unbound;
      };
    };

  # ── THE DECLARED-NAME TABLES' REFUSALS ──
  # `eval` classifies each attribute once per evaluation, and every reader tests "declared and not
  # quotient" as one selection with a default. The default IS the encoding of an undeclared name,
  # so each site that reads the tables has a cell here for the input its default decides: an
  # undeclared and a quotient name at an `nta` child's own reader (its record's `get`), an undeclared
  # name at `get`, and a record declaring `quotient` without being a circular declaration. The
  # `getNta` sites' cells are `nta-getNta-refusals` above.
  config.flake.testsError.eval-declared-name-refusals =
    let
      fx = import ./tests/_fixtures/nta.nix { inherit genScope; };
      child = genScope.mintNtaId {
        host = "r";
        name = "sub";
        group = "g";
        key = "b";
      };
      # The root reads its child's `probe` through `getNta`; the child's body reads `attr` at its
      # OWN identifier, so the read goes through the child's record reader.
      childReads =
        attr:
        (fx.nestWith genScope.eval {
          q =
            circular
              {
                carrier = {
                  bottom = 0;
                  leq = a: b: a <= b;
                  height = 1;
                  quotient = true;
                };
              }
              (
                _: _: _:
                0
              );
          probe = self: id: if id == "r" then self.getNta "sub" "g" "b" "probe" else self.get id attr;
        }).get
          "r"
          "probe";
      err = msg: {
        type = "ThrownError";
        msg = exactly msg;
      };
    in
    {
      test-an-undeclared-name-at-a-childs-own-reader-is-refused-by-name = {
        expr = childReads "nosuch";
        expectedError = err "gen-scope: unknown attribute 'nosuch' on node '${child}'";
      };
      test-a-quotient-name-at-a-childs-own-reader-is-refused = {
        expr = childReads "q";
        expectedError = err "gen-scope: self.get 'q' on '${child}' demands a raw value of a quotient-converged instance — its carrier declares `quotient = true`, so what converged is a class representative under the declared order and not a fixed point of the step. Read it with `getRepresentative`, which returns it tagged.";
      };
      test-an-undeclared-name-at-get-is-refused-as-unknown = {
        expr = (fx.nestWith genScope.eval { }).get "r" "nosuch";
        expectedError = err "gen-scope: unknown attribute 'nosuch' on node 'r'";
      };
      test-a-quotient-record-that-is-not-circular-is-refused-as-malformed = {
        expr = (fx.nestWith genScope.eval { m.carrier.quotient = true; }).get "r" "m";
        expectedError = err "gen-scope: attribute 'm' on 'r' is declared as a record that is not a circular declaration — an attribute is a function `self: id: value`, or the record `circular { carrier = { bottom; leq; height; quotient; }; } step` returns; anything else is refused by name rather than reaching Nix as an anonymous call error";
      };
    };

  # ── `getHostAt`'s REFUSALS (den-hoag-n6dh7 U2.0′) ──
  # The four refusals, total, in both evaluators: (1) a reader that is not an `nta` child's with no
  # round open, one cell per reader class; (2) an unknown attribute; (3) a quotient attribute, which
  # never reaches the host's accessor, so `get`'s by-id text cannot answer for it at a nested host;
  # (4) no entry at the child's coordinates. 2–4 on each entry path: through the host's `getNta`, and
  # by the child's identifier. The value cells are `tests/nta.nix`'s U2.0′ block.
  config.flake.testsError.nta-getHostAt-refusals =
    let
      fx = import ./tests/_fixtures/nta.nix { inherit genScope; };
      inherit (genScope) mintNtaId;
      q =
        circular
          {
            carrier = {
              bottom = 0;
              leq = a: b: a <= b;
              height = 1;
              quotient = true;
            };
          }
          (
            _: _: _:
            0
          );
      # `hx` is the child's body; `reads` reads child `b` through the root's `getNta`.
      withBody =
        evaluator: body: extra:
        fx.nestWith evaluator (
          {
            inherit (fx) pos;
            inherit q;
            onlyB = _: _: { sub.g.b = 0; };
            hx = body;
            reads = self: _: self.getNta "sub" "g" "b" "hx";
          }
          // extra
        );
      viaGetNta = evaluator: body: (withBody evaluator body { }).get "r" "reads";
      byId =
        evaluator: body:
        (withBody evaluator body { }).get (mintNtaId {
          host = "r";
          name = "sub";
          group = "g";
          key = "b";
        }) "hx";
      atGrandchild =
        evaluator: body:
        (withBody evaluator body {
          readK = self: _: self.getNta "sub" "g" "k" "hx";
          reads = self: _: self.getNta "sub" "g" "a" "readK";
        }).get
          "r"
          "reads";
      err = msg: {
        type = "ThrownError";
        msg = exactly msg;
      };
      unbound = "gen-scope.nta: `getHostAt` reads the reading node's HOST's attribute at the node's own `nta` coordinates, so it is answered only on an `nta` child's reader with no circular round open. A root's or a `children` child's reader, the evaluation's own record, a child's body applied while a round is open, and every reader of an evaluation whose kinds declare no NTA have no host to read.";
      unknown =
        host: key:
        "gen-scope.nta: `getHostAt`: unknown attribute 'nosuch' on host '${host}' of NTA 'sub' group 'g' key '${key}'";
      quotient =
        host: key:
        "gen-scope.nta: `getHostAt`: 'q' on host '${host}' of NTA 'sub' group 'g' key '${key}' demands a raw value of a quotient-converged instance — its carrier declares `quotient = true`, so what converged is a class representative under the declared order and not a fixed point of the step; `getHostAt` reads raw values only";
      noEntry =
        host: a: key:
        "gen-scope.nta: `getHostAt`: host '${host}' attribute '${a}' carries no entry at NTA 'sub' group 'g' key '${key}'";
      hostA = mintNtaId {
        host = "r";
        name = "sub";
        group = "g";
        key = "a";
      };
      noNta =
        evaluator:
        (evaluator { }
          {
            children = _: _: { };
            reads = self: _: self.getHostAt "pos";
          }
          {
            nodes.r = {
              id = "r";
              parent = null;
              decls = { };
            };
            nodeOrder = [ "r" ];
          }
        ).get
          "r"
          "reads";
    in
    {
      # (1) unbound, one cell per reader class.
      test-the-evaluations-own-record-is-unbound = {
        expr = (fx.nestWith genScope.eval { }).getHostAt "pos";
        expectedError = err unbound;
      };
      test-a-roots-reader-is-unbound = {
        expr =
          (withBody genScope.eval (_: _: 0) { reads = self: _: self.getHostAt "pos"; }).get "r"
            "reads";
        expectedError = err unbound;
      };
      # `c` is registered and selected by `children`, in an evaluation that runs the `nta` channel.
      test-a-children-childs-reader-is-unbound = {
        expr =
          let
            nodes = fx.root "tree" { defs = [ { } ]; } // {
              c = {
                id = "c";
                type = "tree";
                decls.defs = [ { } ];
                parent = "r";
              };
            };
          in
          (genScope.eval { } (
            fx.attributes
            // {
              children = _: id: if id == "r" then { inherit (nodes) c; } else { };
              reads = self: _: self.getHostAt "pos";
            }
          ) (fx.scopeOf (genScope.mkKinds [ fx.tree ]) nodes)).get
            "c"
            "reads";
        expectedError = err unbound;
      };
      # The child's body applied while a round is open runs on the base reader (`getNtaAt`'s
      # round-open arm). No module-tree attribute is `circular`, so Unit 2 never reaches it.
      test-a-childs-body-inside-an-open-round-is-unbound = {
        expr =
          (withBody genScope.eval (self: _: self.getHostAt "pos") {
            ring =
              circular
                {
                  carrier = {
                    bottom = 0;
                    leq = a: b: a <= b;
                    height = 3;
                    quotient = false;
                  };
                }
                (
                  self: id: _:
                  builtins.stringLength (self.get id "reads")
                );
          }).get
            "r"
            "ring";
        expectedError = err unbound;
      };
      test-a-reader-in-an-evaluation-running-no-nta-is-unbound = {
        expr = noNta genScope.eval;
        expectedError = err unbound;
      };
      test-evalDebugs-own-record-is-unbound = {
        expr = (fx.nestWith genScope.evalDebug { }).getHostAt "pos";
        expectedError = err unbound;
      };
      test-evalDebug-a-reader-of-an-id-that-is-no-nta-child-is-unbound = {
        expr =
          (withBody genScope.evalDebug (_: _: 0) { reads = self: _: self.getHostAt "pos"; }).get "r"
            "reads";
        expectedError = err unbound;
      };
      test-evalDebug-a-reader-in-an-evaluation-running-no-nta-is-unbound = {
        expr = noNta genScope.evalDebug;
        expectedError = err unbound;
      };

      # (2) unknown attribute.
      test-an-unknown-attribute-is-refused-through-getNta = {
        expr = viaGetNta genScope.eval (self: _: self.getHostAt "nosuch");
        expectedError = err (unknown "r" "b");
      };
      test-an-unknown-attribute-is-refused-by-id = {
        expr = byId genScope.eval (self: _: self.getHostAt "nosuch");
        expectedError = err (unknown "r" "b");
      };
      test-evalDebug-refuses-an-unknown-attribute-through-getNta = {
        expr = viaGetNta genScope.evalDebug (self: _: self.getHostAt "nosuch");
        expectedError = err (unknown "r" "b");
      };
      test-evalDebug-refuses-an-unknown-attribute-by-id = {
        expr = byId genScope.evalDebug (self: _: self.getHostAt "nosuch");
        expectedError = err (unknown "r" "b");
      };

      # (3) quotient attribute; at a nested host too, where the host's accessor would fall to `get`.
      test-a-quotient-attribute-is-refused-through-getNta = {
        expr = viaGetNta genScope.eval (self: _: self.getHostAt "q");
        expectedError = err (quotient "r" "b");
      };
      test-a-quotient-attribute-is-refused-by-id = {
        expr = byId genScope.eval (self: _: self.getHostAt "q");
        expectedError = err (quotient "r" "b");
      };
      test-a-quotient-attribute-under-a-child-host-is-refused = {
        expr = atGrandchild genScope.eval (self: _: self.getHostAt "q");
        expectedError = err (quotient hostA "k");
      };
      test-evalDebug-refuses-a-quotient-attribute-through-getNta = {
        expr = viaGetNta genScope.evalDebug (self: _: self.getHostAt "q");
        expectedError = err (quotient "r" "b");
      };
      test-evalDebug-refuses-a-quotient-attribute-by-id = {
        expr = byId genScope.evalDebug (self: _: self.getHostAt "q");
        expectedError = err (quotient "r" "b");
      };
      test-evalDebug-refuses-a-quotient-attribute-under-a-child-host = {
        expr = atGrandchild genScope.evalDebug (self: _: self.getHostAt "q");
        expectedError = err (quotient hostA "k");
      };

      # (4) no entry at the child's coordinates: the host's `onlyB` carries key `b` only, and its
      # `n` is not a set at all.
      test-no-entry-at-the-childs-coordinates-is-refused-through-getNta = {
        expr =
          (withBody genScope.eval (self: _: self.getHostAt "onlyB") {
            reads = self: _: self.getNta "sub" "g" "a" "hx";
          }).get
            "r"
            "reads";
        expectedError = err (noEntry "r" "onlyB" "a");
      };
      test-a-host-attribute-that-is-no-set-is-refused-by-id = {
        expr = byId genScope.eval (self: _: self.getHostAt "n");
        expectedError = err (noEntry "r" "n" "b");
      };
      test-no-entry-under-a-child-host-is-refused = {
        expr = atGrandchild genScope.eval (self: _: self.getHostAt "onlyB");
        expectedError = err (noEntry hostA "onlyB" "k");
      };
      test-evalDebug-refuses-no-entry-through-getNta = {
        expr =
          (withBody genScope.evalDebug (self: _: self.getHostAt "onlyB") {
            reads = self: _: self.getNta "sub" "g" "a" "hx";
          }).get
            "r"
            "reads";
        expectedError = err (noEntry "r" "onlyB" "a");
      };
      test-evalDebug-refuses-no-entry-by-id = {
        expr = byId genScope.evalDebug (self: _: self.getHostAt "n");
        expectedError = err (noEntry "r" "n" "b");
      };
      test-evalDebug-refuses-no-entry-under-a-child-host = {
        expr = atGrandchild genScope.evalDebug (self: _: self.getHostAt "onlyB");
        expectedError = err (noEntry hostA "onlyB" "k");
      };
    };

  # den-hoag-7gp66 P2: every door's refusals, each message pinned to the byte on the real path, over
  # the door table (`ci/doors.nix`). Per OPTIONS step: an unknown option and a non-set argument
  # refused naming the door. Per RECORD step: a missing field and a non-set argument refused naming
  # the door, and — behind an options step — each of that step's names given on the record refused
  # by name (`optionsStep`, G10). Catchability and the admitting halves are `tests/door-checks.nix`.
  config.flake.testsError.door-checks =
    let
      F = import ./doors.nix { inherit genScope genGraph; };
      thrown = expr: msg: {
        inherit expr;
        expectedError = {
          type = "ThrownError";
          msg = exactly msg;
        };
      };
      optionCells =
        name: d:
        let
          door = "gen-scope.${name}";
        in
        {
          "test-${name}-options-unknown-refused" = thrown (genScope.${name} { unknownField = 1; }) (
            refusals.unknownOption door d.optional "unknownField"
          );
          "test-${name}-options-non-set-refused" = thrown (genScope.${name} 1) (
            refusals.optionsNotASet door d.optional 1
          );
        };
      recordCells =
        name: d:
        let
          door = "gen-scope.${name}";
        in
        {
          "test-${name}-record-missing-field-refused" = thrown (d.step (
            builtins.removeAttrs d.good [ d.drop ]
          )) (refusals.missingField door d.required d.drop);
          "test-${name}-record-non-set-refused" = thrown (d.step 1) (
            refusals.recordNotASet door d.required 1
          );
        }
        // (
          if d ? guardedBy then
            builtins.listToAttrs (
              map (o: {
                name = "test-${name}-record-misplaced-option-${o}-refused";
                value = thrown (d.step (d.good // { ${o} = null; })) (
                  refusals.guardedField door "gen-scope.${d.guardedBy}" o
                );
              }) F.options.${d.guardedBy}.optional
            )
          else
            { }
        );
    in
    builtins.foldl' (acc: name: acc // optionCells name F.options.${name}) { } (
      builtins.attrNames F.options
    )
    // builtins.foldl' (acc: name: acc // recordCells name F.records.${name}) { } (
      builtins.attrNames F.records
    );

  # ── THE CALCULUS'S REFUSAL TABLE (den-hoag-gayc build spec §2.4), each row's text to the byte ──
  # The plants are `tests/_fixtures/calculus-refusals.nix`'s, shared with `tests/calculus.nix`, which
  # holds catchability and the unplanted twins. Row 18 is the edge read's OWN text: the calculus
  # never catches an edge read, so what reaches the caller is what the attribute threw.
  config.flake.testsError.calculus-refusals =
    let
      R = import ./tests/_fixtures/calculus-refusals.nix { inherit lib genScope; };
      pin = row: msg: {
        expr = builtins.deepSeq R.${row}.plant R.${row}.plant;
        expectedError = {
          type = "ThrownError";
          msg = exactly msg;
        };
      };
    in
    lib.mapAttrs'
      (row: msg: {
        name = "test-${row}";
        value = pin row msg;
      })
      {
        "row1-malformed-expression" = ''gen-scope.regex.parse: expected a label or '(' (in "a (")'';
        "row2-longer-than-maxLength" =
          ''gen-scope.regex.parse: pattern length 5 exceeds the stated cap of 3 characters; past it the parser's recursion meets the evaluator's call-depth ceiling, an abort tryEval cannot catch (lower the cap with parseWith { maxLength; } when calling from deep in a stack) (in "a b a")'';
        "row3-unknown-wellFormed-option" = (
          refusals.unknownOption "gen-scope.wellFormed" [ "alphabet" "expression" "maxLength" ] "depth"
        );
        "row4-not-a-constructor-term" =
          "gen-scope.regex: this value was not built by the regex constructors (eps, empty, any, lit, seq, alt, star, opt, plus, deriv, parse), so it has no canonical key";
        "row5-duplicate-letter" = "gen-scope.labelOrder: alphabet lists the letter 'a' more than once";
        "row5-letter-not-a-string" =
          "gen-scope.wellFormed: alphabet carries a int where a letter (a string) belongs";
        "row5-letter-outside-the-alphabet" =
          ''gen-scope.wellFormed: the expression names 'c', which is not a letter of the alphabet (["a","b"]); a path expression ranges over L and a name outside it would match nothing and say nothing'';
        "row5-reserved-letter" =
          "gen-scope.wellFormed: alphabet carries the reserved letter '$' — `_` is the any-label wildcard of the path-expression grammar and `$` the extended label marking the end of a path (van Antwerpen 2018 Fig. 1); neither can also name an edge";
        "row7-endOfPath-not-an-int" =
          "gen-scope.labelOrder: endOfPath must be an int; it is the rank of the extended label `$` and decides whether stopping outranks continuing";
        "row7-foreign-letter" =
          ''gen-scope.labelOrder: layers rank 'c', which is not a letter of the alphabet (["a","b"])'';
        "row7-label-outside-L-hat" = ''gen-scope.labelOrder: 'c' is not a label of L̂ (["a","b"], or `$`)'';
        "row7-layers-not-a-list-of-lists" =
          "gen-scope.labelOrder: layers must be a list of lists — each inner list is one rank, and two letters sharing a rank are incomparable, which is how a strict PARTIAL order is declared";
        "row7-step-without-to" =
          "gen-scope.labelOrder: pathPrecedes: step 0 has no `to`; a step is `{ label; from; to; }`, and the order reads the target scope at an equal label";
        "row7-step-without-label" =
          "gen-scope.labelOrder: pathPrecedes: step 0 is a set without `label`; a step is `{ label; from; to; }`";
        "row7-paths-from-two-origins" =
          ''gen-scope.labelOrder: pathPrecedes: the two paths start at different scopes ("s", "t"); Fig. 1 orders two paths from one origin only'';
        "row7-unranked-letter" =
          "gen-scope.labelOrder: letter 'b' is not ranked; the label order is total over the alphabet, and an unranked letter would otherwise take a default rank nobody declared";
        "row8-dataFilter-missing" = (
          refusals.missingField "gen-scope.resolve" [ "wf" "dataFilter" ] "dataFilter"
        );
        "row8-wf-missing" = (refusals.missingField "gen-scope.resolve" [ "wf" "dataFilter" ] "wf");
        "row9-visible-without-a-key" =
          ''gen-scope.resolve: mode "visible" requires a competition key, and it is never defaulted (den-hoag-l7af / ADR-0024 ruling 3): state `group = "k";` (a declared constant, lazy in shadowed data) or `groupBy = ans: …;` (a function of the answer, strict); a caller wanting the per-node reading states `groupBy = ans: ans.node;` explicitly'';
        "rowG1-group-and-groupBy" =
          "gen-scope.resolve: `group` and `groupBy` are both given; state exactly one competition key: `group`, a declared constant read before any datum (lazy in shadowed data), or `groupBy`, a function of the answer (strict: it forces every candidate it groups)";
        "rowG1-group-beside-a-null-groupBy" =
          "gen-scope.resolve: `group` and `groupBy` are both given; state exactly one competition key: `group`, a declared constant read before any datum (lazy in shadowed data), or `groupBy`, a function of the answer (strict: it forces every candidate it groups)";
        "rowG2-group-not-a-string" =
          "gen-scope.resolve: group is a int, not a string; `group` is the competition key as a declared constant (a key computed from the answer is `groupBy`)";
        "rowG3-group-outside-visible" =
          ''gen-scope.resolve: `group` is read only by mode "visible", and the mode is "witnesses"'';
        "rowG4-single-asks-another-group" =
          ''gen-scope.resolve: `single` is asked for group "y", but this resolution declares `group = "x"`: every candidate is in that one group, so any other name would answer null as if nothing were declared'';
        "rowG5-order-omits-a-wf-letter" =
          ''gen-scope.resolve: `order` does not rank 'imports', a letter of `wf`'s alphabet (["e","imports"]); mode "visible" ranks every letter the walk can step, so the label order must be total over the walk's alphabet'';
        "row10-groupBy-outside-visible" =
          ''gen-scope.resolve: `groupBy` is read only by mode "visible", and the mode is "witnesses"'';
        "row10-order-outside-visible" =
          ''gen-scope.resolve: `order` is read only by mode "visible", and the mode is "reachable"'';
        "row10-unknown-mode" =
          ''gen-scope.resolve: unknown mode "all" (one of ["reachable","witnesses","visible"])'';
        "row10-unknown-option" = (
          refusals.unknownOption "gen-scope.resolve" [
            "wf"
            "dataFilter"
            "mode"
            "order"
            "groupBy"
            "group"
            "bound"
            "direction"
          ] "follow"
        );
        "row10-unknown-direction" =
          ''gen-scope.resolve: unknown direction "sideways" (one of ["outbound","inbound"])'';
        "row10-visible-without-order" =
          ''gen-scope.resolve: mode "visible" requires `order`, a `labelOrder` value (<l over the alphabet, with `$`'s rank)'';
        "row11-admits-not-a-bool" =
          ''gen-scope.resolve: a mark's admits at node "a" on the label "e" returned a int, not a bool'';
        "row11-admits-not-callable" =
          ''gen-scope.resolve: a mark's admits (`marks` of node "a") is a int, not a function returning a bool'';
        "row11-dataFilter-not-callable" =
          (genGraph.key "gen-scope").notA "resolve" "dataFilter" "a function returning a datum or null"
            1;
        "row11-groupBy-not-a-string" =
          ''gen-scope.resolve: groupBy on the answer at "b" returned a int, not a string, the answer's competition key'';
        "row11-groupBy-not-callable" =
          "gen-scope.resolve: groupBy is a string, not a function returning a string, the answer's competition key";
        "row12-from-not-a-node-id" = (genGraph.key "gen-scope").notAnIdentifier "resolve" 1;
        "row13-edge-attribute-not-a-list" =
          ''gen-scope.resolve: node "a", letter 'e': the edge attribute is a string, not a list of node ids'';
        "row13-edge-target-not-a-string" =
          ''gen-scope.resolve: node "a", letter 'e': an edge target is a int, not a node id (a string)'';
        "row14-mark-with-no-admits" =
          ''gen-scope.resolve: the `marks` of node "a" carry a mark with no admits, not a mark { name; admits; }'';
        "row14-mark-with-no-name" =
          ''gen-scope.resolve: node "a" carries a mark with no name; `withheld` reports a mark by its name'';
        "row14-marks-not-a-list" =
          ''gen-scope.resolve: the `marks` of node "a" is a set, not a list of marks { name; admits; }'';
        "row15-ambiguity" =
          ''gen-scope.resolve: group "x" has more than one visible declaration, from ["b","c"]. That is an AMBIGUITY in the sense of Neron et al. 2015 (Fig. 3 rule (V); §2.2 Duplicate Declarations) — two declaration occurrences for one read. `single` answers with one declaration or REFUSES; read the group's `answers` to see every one'';
        "row16-parent-cycle" =
          ''gen-scope.resolve: node "a" is on a parent cycle: containment is a tree, and a parent chain that returns to itself is malformed data, not a scope to walk'';
        "row16-parent-cycle-inbound" =
          ''gen-scope.resolve: node "root" is on a parent cycle: containment is a tree, and a parent chain that returns to itself is malformed data, not a scope to walk'';
        "row16-parent-cycle-inbound-above" =
          ''gen-scope.resolve: node "s" is on a parent cycle: containment is a tree, and a parent chain that returns to itself is malformed data, not a scope to walk'';
        "row16-parent-cycle-inbound-marked" =
          ''gen-scope.resolve: node "r" is on a parent cycle: containment is a tree, and a parent chain that returns to itself is malformed data, not a scope to walk'';
        "row18-edge-read-refusal-propagates" = "planted: the edge read's own refusal";
        "row19-no-marks" =
          "gen-scope: node 'a' is read for its boundary marks, but this evaluation declares no `marks` attribute — a scope that declares no boundary mark; `_: _: [ ]` states none. An absent mark is never read as an open floor (ADR-0026).";
        "row19-no-marks-inbound" =
          "gen-scope: node 'a' is read for its boundary marks, but this evaluation declares no `marks` attribute — a scope that declares no boundary mark; `_: _: [ ]` states none. An absent mark is never read as an open floor (ADR-0026).";
        "row20-undeclared-letter" =
          "gen-scope: node 'a' is read for the edges of letter 'l1', but this evaluation declares no `edges-l1` attribute; an undeclared letter is refused rather than read as no edges (declare `edges-l1`, answering `[ ]` where a node has none).";
        "row21-reserved-lifted-label" =
          ''gen-scope.buildRoots: `edgeGraphs` carries reserved label(s) ["imports"]: 'imports' is the calculus's import letter, whose edges arrive as the `importGraph` argument. A reserved label is this library's own name for a relation it privileges, and `edgeGraphs` does not extend to it — supply those edges as the argument named, or relabel them.'';
      };

  # ── RESOLUTION STAYS LAZY IN DATA IT SHADOWS (den-hoag-gayc C1): what must STILL throw ──
  # Laziness is not skipping: an ancestor that IS the answer is forced (L4), and a key that reads the
  # datum is the strict form, forcing every candidate it groups (L5). The answers are
  # `tests/lazy-shadowing.nix`'s; the fixtures `tests/_fixtures/lazy-shadowing.nix`'s.
  # The walk's spine is lazy too (den-hoag-gayc U1 rework): the shadowed scope's edges answer in
  # `tests/lazy-shadowing.nix`; here, under the strict key they are forced, and a parent cycle whose
  # every field the selection reads is refused under `group`, under either rank order.
  config.flake.testsError.lazy-shadowing =
    let
      F = import ./tests/_fixtures/lazy-shadowing.nix { inherit lib genScope; };
      forced = expr: msg: {
        inherit expr;
        expectedError = {
          type = "ThrownError";
          msg = exactly msg;
        };
      };
    in
    {
      test-L4-an-unset-nearer-scope-forces-the-ancestor-inherit = forced (F.inherit' F.unset) "ANCESTOR-DATUM-FORCED";
      test-L4-an-unset-nearer-scope-forces-the-ancestor-group = forced (F.group F.unset) "ANCESTOR-DATUM-FORCED";
      test-L5-a-data-reading-key-is-strict = forced (F.dataKey F.shadowing) "ANCESTOR-DATUM-FORCED";
      test-L5-a-data-reading-key-forces-the-shadowed-spine = forced (F.dataKey F.edgeForcing) "ANCESTOR-EDGE-FORCED";
      test-D9-a-parent-cycle-the-selection-walks-is-refused-under-group = forced (F.group F.cycleMet) ''gen-scope.resolve: node "a" is on a parent cycle: containment is a tree, and a parent chain that returns to itself is malformed data, not a scope to walk'';
      test-D9-a-parent-cycle-the-selection-reads-is-refused-imports-first =
        forced
          (F.cycleReadUnder [
            [ "imports" ]
            [ "parent" ]
          ])
          ''gen-scope.resolve: node "p" is on a parent cycle: containment is a tree, and a parent chain that returns to itself is malformed data, not a scope to walk'';
      test-D9-a-parent-cycle-the-selection-reads-is-refused-parent-first =
        forced
          (F.cycleReadUnder [
            [ "parent" ]
            [ "imports" ]
          ])
          ''gen-scope.resolve: node "p" is on a parent cycle: containment is a tree, and a parent chain that returns to itself is malformed data, not a scope to walk'';
      test-kid-order-a-subtree-datum-before-a-later-leaf-datum = forced (builtins.deepSeq F.orderNonLeafFirst F.orderNonLeafFirst) "EARLIER-DATUM-FORCED";
      test-kid-order-a-leaf-datum-before-a-later-leaf-edge = forced (builtins.deepSeq F.orderLeafEdges F.orderLeafEdges) "EARLIER-DATUM-FORCED";
      test-kid-order-a-leaf-datum-before-a-later-subtree-edge = forced (builtins.deepSeq F.orderNonLeafEdges F.orderNonLeafEdges) "EARLIER-DATUM-FORCED";
      test-kid-order-a-subtree-datum-before-a-later-leaf-edge = forced (builtins.deepSeq F.orderSubtreeThenLeafEdges F.orderSubtreeThenLeafEdges) "EARLIER-DATUM-FORCED";
      test-D9-a-parent-cycle-through-a-batched-leaf-is-refused = forced (builtins.deepSeq F.cycleBatched F.cycleBatched) ''gen-scope.resolve: node "a" is on a parent cycle: containment is a tree, and a parent chain that returns to itself is malformed data, not a scope to walk'';
    };

  # ── THE FOUR COLLECTION WALKS ARE RESOLUTIONS (den-hoag-4or0a): what they refuse ──
  # Each walk refuses where `resolve` refuses: a parent cycle is malformed containment (D9), the
  # retired recursion state `_visited` is not an option, and a label that is not a string is not a
  # letter. The answering cells and the scopes are `tests/walks-through-resolve.nix` and
  # `tests/_fixtures/walks-through-resolve.nix`.
  config.flake.testsError.walks-through-resolve =
    let
      F = import ./tests/_fixtures/walks-through-resolve.nix { inherit genScope; };
      refused = expr: msg: {
        expr = builtins.deepSeq expr expr;
        expectedError = {
          type = "ThrownError";
          msg = exactly msg;
        };
      };
      cycle = ''gen-scope.resolve: node "a" is on a parent cycle: containment is a tree, and a parent chain that returns to itself is malformed data, not a scope to walk'';
      v = n: n.decls.v or null;
    in
    {
      test-A5-inheritAll-refuses-a-parent-cycle = refused (genScope.inheritAll { } v F.cycle "a") cycle;
      test-A5-ancestors-refuses-a-parent-cycle = refused (genScope.collectionAttr { } "ancestors" F.ex
        F.cycle
        "a"
      ) cycle;
      test-A5-neron-refuses-a-parent-cycle = refused (genScope.collectionAttr { } "neron" F.ex F.cycle
        "a"
      ) cycle;
      test-A6-inheritAll-refuses-the-retired-visited = refused (genScope.inheritAll {
        _visited = { };
      }) (refusals.unknownOption "gen-scope.inheritAll" [ "combine" ] "_visited");
      test-A6-inheritSet-refuses-the-retired-visited = refused (genScope.inheritSet {
        _visited = { };
      }) (refusals.unknownOption "gen-scope.inheritSet" [ "eq" ] "_visited");
      test-A7-followEdge-refuses-a-label-that-is-not-a-string = refused (genScope.followEdge 1 F.labelled
        "s"
      ) "gen-scope.followEdge: the label is a int, not a letter (a string)";

      # The one-hop reads (den-hoag-4or0a U2) refuse where `resolve` refuses.
      # E1: an evaluation declaring no `marks` is refused at the first read, at each of the five.
    }
    // builtins.listToAttrs (
      map
        (read: {
          name = "test-E1-${read}-refuses-an-undeclared-marks-floor";
          value =
            refused (F.five (F.hop { declareMarks = false; }) "s").${read}
              "gen-scope: node 's' is read for its boundary marks, but this evaluation declares no `marks` attribute — a scope that declares no boundary mark; `_: _: [ ]` states none. An absent mark is never read as an open floor (ADR-0026).";
        })
        [
          "imports"
          "label"
          "collectImports"
          "collectByLabel"
          "followEdge"
        ]
    )
    // {
      # E2, E3: a malformed edge list is refused by name.
      test-E2-followEdge-refuses-an-edge-attribute-that-is-not-a-list =
        refused (genScope.followEdge "include" (F.hop { edgesInclude.s = "r"; }) "s")
          ''gen-scope.resolve: node "s", letter 'include': the edge attribute is a string, not a list of node ids'';
      test-E3-followEdge-refuses-an-edge-target-that-is-not-an-id =
        refused (genScope.followEdge "include" (F.hop { edgesInclude.s = [ 7 ]; }) "s")
          ''gen-scope.resolve: node "s", letter 'include': an edge target is a int, not a node id (a string)'';
      # E4: the reserved letters `_` and `$` are WFL syntax and name no edge.
      test-E4-followEdge-refuses-the-reserved-letter-underscore =
        refused (genScope.followEdge "_" (F.hop { extra."edges-_" = _: _: [ "a" ]; }) "s")
          "gen-scope.wellFormed: alphabet carries the reserved letter '_' — `_` is the any-label wildcard of the path-expression grammar and `$` the extended label marking the end of a path (van Antwerpen 2018 Fig. 1); neither can also name an edge";
      test-E4-followEdge-refuses-the-reserved-letter-dollar =
        refused (genScope.followEdge "$" (F.hop { extra."edges-$" = _: _: [ "a" ]; }) "s")
          "gen-scope.wellFormed: alphabet carries the reserved letter '$' — `_` is the any-label wildcard of the path-expression grammar and `$` the extended label marking the end of a path (van Antwerpen 2018 Fig. 1); neither can also name an edge";
    };
}
