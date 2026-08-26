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
      parentGraph = genScope.edge "a" "root";
      importGraph = genScope.edge "a" "lib1";
      edgeGraphs = map (label: {
        inherit label;
        graph = genScope.edge "a" "HIJACKED";
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

  run = claims: resolveClaims { inherit kinds claims; };

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
        name = "b";
        resolve = _: _: { };
      })
      (mkKind {
        name = "a";
        below = [ "b" ];
        resolve = _: _: { claims = [ bad ]; };
      })
    ];
  runEmit =
    bad:
    resolveClaims {
      kinds = emitKinds bad;
      claims = [
        (mkClaim {
          kind = "a";
          subject = subjA;
        })
      ];
    };

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
    unresolvedRelatum
    conflictingContribution
    ;

  # ── THE CIRCULAR-NTA FIXTURE ──
  # Shared with `tests/circular-nta.nix`, which holds the same grammar's convergence cells. Both
  # seeded variants are defined there, so the grammar a refusal is earned on and the grammar the
  # clean path converges on are one value rather than two that agree while someone keeps them so.
  circularNta = import ./tests/_fixtures/circular-nta.nix { inherit genScope; };

  # The shared-round corpus: the tracked model of record's forty fixtures, ported. The refusing
  # fixtures are asserted here — WHICH refusal fires is a claim about a message — and the
  # answering fixtures next door in `tests/scc-round.nix`. Provenance and the hand-derived
  # expectations are documented at the fixture file.
  sccCorpus = import ./tests/_fixtures/scc-corpus.nix { inherit genScope; };
  sccForceGate = import ./tests/_fixtures/scc-force-gate.nix { inherit genScope; };

  # The spawned-visibility witness, shared with `tests/spawned-visibility.nix`: the refusal below
  # is earned on the same graph whose clean path answers there.
  spawnedVisibility = import ./tests/_fixtures/spawned-visibility.nix { inherit lib genScope; };
in
{
  # Same type as `flake.tests`, because it is the same kind of thing read by the same runner —
  # only the assertion the cells carry differs.
  options.flake.testsError = lib.mkOption {
    type = lib.types.lazyAttrsOf (lib.types.lazyAttrsOf lib.types.raw);
    default = { };
    description = "Test suites whose cells assert an ERROR: { suite.test = { expr; expectedError; }; }. Read by `nix-unit --flake ./ci#testsError`; deliberately outside `flake.tests`, which the batch asserter quantifies over.";
  };

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
      expr = resolveClaims {
        kinds = mkKinds [ (mkKind { name = "structural"; }) ];
        claims = [
          (mkClaim {
            kind = "structural";
            subject = subjA;
          })
        ];
      };
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope.resolveClaims: kind 'structural' at path [0] declares no `resolve`, so it cannot answer a demand — it is a registered kind and not a demand kind";
      };
    };
    # An explicit null and an omitted field are one case, which is the sentinel's whole cost and its
    # whole point: nothing legitimate is collapsed, because null is not a resolver on any reading.
    test-an-explicitly-null-resolver-is-refused-the-same-way = {
      expr = resolveClaims {
        kinds = mkKinds [
          (mkKind {
            name = "structural";
            resolve = null;
          })
        ];
        claims = [
          (mkClaim {
            kind = "structural";
            subject = subjA;
          })
        ];
      };
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
        name = "host";
        below = [ "low" ];
        spawns.sideways = _self: _id: { };
      };
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
        name = "host";
        spawns.child = _self: _id: { };
      };
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
        name = "k";
        resolve = 5;
      };
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
        name = "k";
        resolve = _: { };
        dedupKey = _: "d";
      };
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
          _type = "gen-scope/kind";
          name = "ghost";
          below = [ ];
          dedupKey = null;
          fold = null;
        }
      ];
      expectedError = {
        type = "ThrownError";
        msg = exactly ''gen-scope.mkKinds: not every entry is a kind record: ["entry 0 carries no `resolve` field"]'';
      };
    };

    # ── THE PASS-THROUGH DOOR NAMES THE ENTRY'S KEY, WHICH IS HOW THE RUN INDEXES IT ──
    # A kind-set record handed over whole never met the registration checks, so the run asks the
    # same question of its entries. The key is what the message carries — not the record's own
    # `name` field — because the key is what a claim's `kind` resolves through, and on a forged
    # record the two need not agree.
    test-pass-through-door-names-the-entry-key-and-the-missing-field = {
      expr = resolveClaims {
        kinds = {
          _type = "gen-scope/kind-set";
          kinds = {
            l = {
              _type = "gen-scope/kind";
              name = "l";
              below = [ ];
              dedupKey = null;
              fold = null;
            };
          };
          depth = {
            l = 0;
          };
          maxDepth = 0;
        };
        claims = [ ];
      };
      expectedError = {
        type = "ThrownError";
        msg = exactly ''gen-scope.resolveClaims: the kind set holds entries that are not kind records: ["`l` carries no `resolve` field"]'';
      };
    };

    # ── APPLICABILITY IS NAMED AS SUCH, NOT AS A MISSING FIELD ──
    # A caller whose resolver is an integer and one whose resolver is absent have different bugs
    # and must not read the same message.
    test-a-resolve-that-cannot-be-applied-says-so = {
      expr = mkKinds [
        {
          _type = "gen-scope/kind";
          name = "l";
          below = [ ];
          resolve = 42;
          spawns = { };
          dedupKey = null;
          fold = null;
        }
      ];
      expectedError = {
        type = "ThrownError";
        msg = exactly ''gen-scope.mkKinds: not every entry is a kind record: ["entry 0 carries a `resolve` that cannot be applied"]'';
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
        msg = exactly ''gen-scope.mkKinds: not every entry is a kind record: ["entry 0 is a int rather than a kind record"]'';
      };
    };
    # A record that could be a kind but never met the constructor, which is a different repair
    # from a value that could not be one at all.
    test-a-record-without-the-constructor-marker-says-so = {
      expr = mkKinds [ { } ];
      expectedError = {
        type = "ThrownError";
        msg = exactly ''gen-scope.mkKinds: not every entry is a kind record: ["entry 0 was not built by `mkKind`"]'';
      };
    };
    test-a-name-that-is-not-a-string-is-named-as-such = {
      expr = mkKinds [
        {
          _type = "gen-scope/kind";
          name = 42;
        }
      ];
      expectedError = {
        type = "ThrownError";
        msg = exactly ''gen-scope.mkKinds: not every entry is a kind record: ["entry 0 carries a `name` that is not a string"]'';
      };
    };
    # The container and its elements are two repairs, and the folds' refusals draw the same line
    # for the same reason.
    test-a-below-that-is-not-a-list-names-the-container = {
      expr = mkKinds [
        {
          _type = "gen-scope/kind";
          name = "l";
          below = 42;
        }
      ];
      expectedError = {
        type = "ThrownError";
        msg = exactly ''gen-scope.mkKinds: not every entry is a kind record: ["entry 0 carries a `below` that is not a list"]'';
      };
    };
    test-a-below-holding-a-non-string-names-the-element = {
      expr = mkKinds [
        {
          _type = "gen-scope/kind";
          name = "l";
          below = [ 42 ];
        }
      ];
      expectedError = {
        type = "ThrownError";
        msg = exactly ''gen-scope.mkKinds: not every entry is a kind record: ["entry 0 carries a `below` holding a name that is not a string"]'';
      };
    };
    # The other two missing-field arms. WHICH field is absent is the coordinate the caller acts
    # on, and the three arms are interchangeable without it: a registry is a list, and a message
    # naming the entry but not the field leaves the caller bisecting a record they already wrote.
    test-a-missing-spawns-names-that-field = {
      expr = mkKinds [
        {
          _type = "gen-scope/kind";
          name = "l";
          below = [ ];
          resolve = _: _: { };
        }
      ];
      expectedError = {
        type = "ThrownError";
        msg = exactly ''gen-scope.mkKinds: not every entry is a kind record: ["entry 0 carries no `spawns` field"]'';
      };
    };
    test-a-missing-dedupkey-names-that-field = {
      expr = mkKinds [
        {
          _type = "gen-scope/kind";
          name = "l";
          below = [ ];
          resolve = _: _: { };
          spawns = { };
        }
      ];
      expectedError = {
        type = "ThrownError";
        msg = exactly ''gen-scope.mkKinds: not every entry is a kind record: ["entry 0 carries no `dedupKey` field"]'';
      };
    };
    test-a-missing-fold-names-that-field = {
      expr = mkKinds [
        {
          _type = "gen-scope/kind";
          name = "l";
          below = [ ];
          resolve = _: _: { };
          spawns = { };
          dedupKey = null;
        }
      ];
      expectedError = {
        type = "ThrownError";
        msg = exactly ''gen-scope.mkKinds: not every entry is a kind record: ["entry 0 carries no `fold` field"]'';
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
          name = "l";
          resolve = _: _: { };
          dedupKey = 42;
          fold = _: _: { };
        })
      ];
      expectedError = {
        type = "ThrownError";
        msg = exactly ''gen-scope.mkKinds: not every entry is a kind record: ["entry 0 carries a `dedupKey` that is neither null nor applicable"]'';
      };
    };
    test-a-fold-that-cannot-be-applied-says-so = {
      expr = mkKinds [
        (mkKind {
          name = "l";
          resolve = _: _: { };
          dedupKey = _: "k";
          fold = 42;
        })
      ];
      expectedError = {
        type = "ThrownError";
        msg = exactly ''gen-scope.mkKinds: not every entry is a kind record: ["entry 0 carries a `fold` that is neither null nor applicable"]'';
      };
    };

    # ── A RESOLVER'S ANSWER NAMES THE KIND AND THE PATH ──
    # Both halves. What the evaluator would have said instead — "expected a set but found a list" —
    # names no library, no kind and no path, and for the silent half it says nothing at all.
    test-a-result-that-is-not-a-set-names-the-kind-and-the-path = {
      expr = resolveClaims {
        kinds = mkKinds [
          (mkKind {
            name = "g";
            resolve = _: _: [ 1 ];
          })
        ];
        claims = [
          (mkClaim {
            kind = "g";
            subject = {
              id_hash = "id-a";
            };
          })
        ];
      };
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope.resolveClaims: kind 'g' at path [0] returned a list rather than an attribute set";
      };
    };
    test-a-container-of-the-wrong-type-names-which-container = {
      expr = resolveClaims {
        kinds = mkKinds [
          (mkKind {
            name = "g";
            resolve = _: _: { resources = [ 1 ]; };
          })
        ];
        claims = [
          (mkClaim {
            kind = "g";
            subject = {
              id_hash = "id-a";
            };
          })
        ];
      };
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
      expr = resolveClaims {
        kinds = mkKinds [
          (mkKind {
            name = "g";
            resolve = _: _: { resourcez.ok = 1; };
          })
        ];
        claims = [
          (mkClaim {
            kind = "g";
            subject = {
              id_hash = "id-a";
            };
          })
        ];
      };
      expectedError = {
        type = "ThrownError";
        msg = exactly ''gen-scope.resolveClaims: kind 'g' at path [0] returned unrecognised result key(s) ["resourcez"]: this record is closed to ["resources","wiring","claims"], and a key outside that set is read by nothing here — correct the spelling or drop it'';
      };
    };
    # An identity that is present but cannot be an attribute name is named as such, distinctly from
    # one that is absent — two different bugs for the caller.
    test-an-unusable-id-hash-is-named-distinctly-from-a-missing-one = {
      expr = resolveClaims {
        kinds = mkKinds [
          (mkKind {
            name = "g";
            resolve = _: _: { };
          })
        ];
        claims = [
          (mkClaim {
            kind = "g";
            subject = {
              id_hash = [ 1 ];
              name = "s";
            };
          })
        ];
      };
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
      expr = resolveClaims {
        kinds = mkKinds [
          (mkKind {
            name = "l";
            resolve = x: x;
          })
        ];
        claims = [
          (mkClaim {
            kind = "l";
            subject = {
              id_hash = "id-a";
            };
          })
        ];
      };
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
      pg = genScope.edge "a" "root";
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
                graph = genScope.edge "n" "m";
              }
              {
                label = "M";
                graph = genScope.edge "d" "c";
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
        expr =
          (genScope.eval {
            scope = built.nodes;
            attributes = attrs;
          }).allNodeIds;
        expectedError = {
          type = "ThrownError";
          msg = scopeRefusal "eval" "received an attrset with no `nodes`";
        };
      };

      # O14, limb 2 — the ADVERSARIAL graph, whose node ids are literally `nodes` and `nodeOrder`.
      # Its key set is IDENTICAL to the record's, so only the TYPE discriminates.
      test-O14-the-adversarial-node-map-is-refused-on-type = {
        expr =
          (genScope.eval {
            scope =
              (genScope.buildRoots {
                parentGraph = genScope.overlays [
                  (genScope.vertex "nodes")
                  (genScope.vertex "nodeOrder")
                ];
              }).nodes;
            attributes = attrs;
          }).allNodeIds;
        expectedError = {
          type = "ThrownError";
          msg = scopeRefusal "eval" "received an attrset whose `nodeOrder` is a set, not a list";
        };
      };

      # O14, limb 3 — not an attrset at all.
      test-O14-a-non-attrset-is-refused-with-its-type-named = {
        expr =
          (genScope.eval {
            scope = [ ];
            attributes = attrs;
          }).allNodeIds;
        expectedError = {
          type = "ThrownError";
          msg = scopeRefusal "eval" "received a list";
        };
      };

      # O14 — the refusal is the ENTRY's, so the message names the entry the caller wrote.
      test-O14-the-message-names-the-entry-that-was-called = {
        expr =
          (genScope.evalDebug {
            scope = built.nodes;
            attributes = attrs;
          }).node
            "a";
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
        expr = genScope.childrenIds (genScope.eval {
          scope = selectionScope;
          attributes = {
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
          };
        }) "host";
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope: node 'host' declares child(ren) [\"alpha\",\"zeta\"] that the scope does not carry. `children` SELECTS among the nodes the scope already registered — it is not a growth channel, and a record under an unregistered key is a node minted while the attribute is read, whose kind nothing can have checked descends its host's. Growth is the spawn channel's: declare it on the host's kind as `mkKind { spawns = { <produced-kind> = builder; }; }` with the produced kind named in that kind's `below`. To keep a node here, register it in the scope and select it.";
        };
      };

      # A kind that spawns its own kind. `mkKind` accepts `spawns.a` when `below` carries `a` —
      # `elem "a" [ "a" ]` holds — so the refusal is the REGISTRY's, and what it now names is the
      # descent that is missing rather than the cycle that is present.
      test-a-self-spawning-kind-names-descent-rather-than-a-cycle = {
        expr = builtins.seq (mkKinds [
          (mkKind {
            name = "a";
            below = [ "a" ];
            spawns.a = _self: _id: { };
          })
        ]) null;
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope.mkKinds: kind(s) [\"a\"] name themselves in their own `below` set. `below` is a STRICT descent order — what a kind expands into ranks strictly under it, and that is the decreasing measure the cascade terminates on. A kind cannot rank under itself, so a kind spawning its own kind expands into something no smaller than its host and descends nothing. Give the produced kind its own name and rank that below this one.";
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
        interpretation:
        (genScope.wellFoundedModel {
          program = genScope.mkProgram { rules = [ ]; };
          inherit interpretation;
        }).trueAtoms;
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
          (genScope.mkKind { name = "low"; })
          (genScope.mkKind {
            name = "high";
            below = [ "low" ];
            spawns.low = spawn;
          })
        ];
      runWith =
        kinds: attributes:
        builtins.deepSeq
          (genScope.eval {
            scope = genScope.buildRoots {
              inherit kinds;
              parentGraph = genScope.vertex "h";
              types.h = "high";
            };
            attributes = {
              children = _self: _id: { };
              imports = _self: _id: [ ];
            }
            // attributes;
          }).allNodes
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
              kinds = genScope.mkKinds [ (genScope.mkKind { name = "host"; }) ];
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
            (genScope.eval {
              scope = {
                nodes.n = {
                  id = "n";
                  parent = null;
                  type = "ghost";
                  decls = { };
                };
                nodeOrder = [ "n" ];
                kinds = genScope.mkKinds [ (genScope.mkKind { name = "high"; }) ];
              };
              attributes = {
                children = _self: _id: { };
                imports = _self: _id: [ ];
              };
            }).allNodes
            null;
        expectedError = {
          type = "ThrownError";
          msg = exactly "gen-scope: node 'n' carries kind 'ghost', which the supplied registry does not carry. A node's kind is a name in a registered vocabulary — register it with `mkKinds`, or build the scope through `buildRoots`, which refuses an unregistered kind at the door.";
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
        (genScope.eval {
          scope = genScope.buildRoots {
            parentGraph = genScope.vertex "n";
            importGraph = genScope.empty;
            decls.n = { };
            types = { };
          };
          attributes = {
            children = _self: _id: { };
            imports = _self: _id: [ ];
            probe = circular carrierArg f;
          };
        }).get
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

  # ── THE SHARED ROUND'S REFUSALS — the corpus's refusing fixtures, each by its own text ──
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
          (mkKind { name = "ep"; })
          (mkKind {
            name = "host";
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
          })
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
  };
}
