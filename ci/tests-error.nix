# THE SECOND TEST OUTPUT — cells whose subject is an ERROR MESSAGE, and why they cannot live in
# `flake.tests`.
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
    # ── THE FOUR ARMS OF THE CLAIM CHAIN, EACH BY ITS OWN TEXT ──
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

    # ── THE CASCADE'S OWN REFUSAL, WHICH MUST NOT READ LIKE ANY OF THE FOUR ──
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
}
