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
# agree with the very rewording they exist to catch. Every pattern below is therefore anchored at
# both ends and built by ESCAPING THE LITERAL TEXT rather than by hand: a hand-written pattern is
# one forgotten backslash away from a metacharacter matching something it was meant to spell.
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
}
