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

    # ── THE CONSTRUCTOR REFUSES A KIND WITH NO RESOLVER, BY NAME, AND CATCHABLY ──
    # `resolve` used to be a bare required formal, so omitting it was refused by NIX at application
    # — `called without required argument 'resolve'`, an EvalError that terminates the evaluation,
    # that `tryEval` does not contain, and that arrives before any arm in `mkKind` can run. The
    # caller got no name and no library text, at the ordinary door, for the most ordinary mistake.
    # These cells exist because a `ThrownError` assertion is only expressible once the throw is the
    # library's: the pre-fix behaviour could not be written as a cell at all, which is exactly what
    # made it worth fixing rather than documenting.
    test-constructor-refuses-a-kind-with-no-resolve = {
      expr = mkKind { name = "k"; };
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope.mkKind: kind 'k' declares no `resolve` (a kind must say how a demand of its kind resolves)";
      };
    };
    # An explicit null takes the same arm, and that is the sentinel's whole cost: `resolve = null`
    # and an omitted `resolve` are one case here. Nothing legitimate is collapsed — null is not a
    # resolver on any reading, and the registry already refuses it through `callable`.
    test-constructor-refuses-an-explicitly-null-resolve-the-same-way = {
      expr = mkKind {
        name = "k";
        resolve = null;
      };
      expectedError = {
        type = "ThrownError";
        msg = exactly "gen-scope.mkKind: kind 'k' declares no `resolve` (a kind must say how a demand of its kind resolves)";
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
    test-a-missing-dedupkey-names-that-field = {
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
}
