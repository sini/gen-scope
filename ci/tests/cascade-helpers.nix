# The cascade's consumer accessors — `wiringFor`, `spliceWiring` — and the fold vocabulary both
# they and a kind's resource fold are written against.
#
# ★ THE ORDER CELL IS THE ONE THAT CANNOT BE WRITTEN ON A SMALL FIXTURE. What `wiringFor` exists
# to preserve is GLOBAL SCHEDULE ORDER ACROSS KINDS, and the only construction that could get it
# wrong in a way worth catching is one that reads the per-kind lists in kind order instead. On a
# subject wired by one kind those two answers are identical, so a one-kind fixture pins nothing.
# The fixture below wires `sonarr` from FIVE kinds whose emissions interleave — the composite
# stratum's `route` and `database`, then the leaf stratum's `secret`, `connect` and `storage`,
# including sub-claims each composite emitted — so the two answers DIFFER on it, and the expected
# list below is the one that is not the concatenation of the per-kind lists.
#
# ★ That difference is a claim about the fixture, so it is MEASURED rather than asserted here:
# `ci/bench/wiring-scan.sh` computes the kind-grouped order over this same fixture and reports it
# beside the global one, and calls the sweep INVALID if they agree. A cell cannot host that
# control without changing what the suite counts, and the same sweep already has to exist for the
# recursion arm below.
#
# ★ THE RECURSION ARM IS ALSO NOT A CELL, AND FOR A HARDER REASON. `wiringFor` is written as an
# indexed scan rather than as a list walk that calls itself on the tail. What makes that a
# construction rather than a preference is that the walk ABORTS on a long trace — and both of the
# aborts it can reach (`max-call-depth exceeded`, and the C-stack overflow past a raised guard)
# terminate the evaluation rather than producing a value, so `tryEval` holds neither and no
# `didThrow` cell can observe either. That control is an exit-code arm in the same sweep.
{
  genScope,
  ...
}:
let
  inherit (genScope)
    folds
    wiringFor
    spliceWiring
    ;
  k8s = import ./_fixtures/k8s.nix { inherit genScope; };
  r = k8s.resolution;

  didThrow = e: !(builtins.tryEval (builtins.deepSeq e null)).success;

  # api-key secret fold spec, exercised directly.
  secretByKey = folds.byKey {
    generator = folds.same;
    stringData = folds.mergeAttrs;
  };
in
{
  flake.tests.cascade-helpers = {
    # ── stock fold semantics ──
    test-folds-list = {
      expr = folds.list "k" [
        1
        2
        3
      ];
      expected = [
        1
        2
        3
      ];
    };
    test-folds-same-agrees = {
      expr = folds.same "k" [
        7
        7
        7
      ];
      expected = 7;
    };
    test-folds-same-conflict-throws = {
      expr = didThrow (
        folds.same "k" [
          1
          2
        ]
      );
      expected = true;
    };
    test-folds-one-single = {
      expr = folds.one "k" [ 42 ];
      expected = 42;
    };
    test-folds-one-second-throws = {
      expr = didThrow (
        folds.one "k" [
          1
          2
        ]
      );
      expected = true;
    };
    test-folds-mergeattrs-disjoint = {
      expr = folds.mergeAttrs "k" [
        { a = 1; }
        { b = 2; }
      ];
      expected = {
        a = 1;
        b = 2;
      };
    };
    test-folds-mergeattrs-collision-throws = {
      expr = didThrow (
        folds.mergeAttrs "k" [
          { a = 1; }
          { a = 2; }
        ]
      );
      expected = true;
    };

    # ── folds.byKey: per-key dispatch, skipped-key, unknown-key, non-attrset ──
    test-bykey-per-key-dispatch = {
      expr = secretByKey "media-arr-api-keys" [
        {
          generator = "hex-secret";
          stringData.sonarr = "s";
        }
        {
          generator = "hex-secret";
          stringData.radarr = "r";
        }
      ];
      expected = {
        generator = "hex-secret";
        stringData = {
          sonarr = "s";
          radarr = "r";
        };
      };
    };
    # A fragment omitting a spec key is skipped (pinned order preserved among those that define it).
    test-bykey-skipped-key = {
      expr = secretByKey "k" [
        { generator = "g"; }
        {
          generator = "g";
          stringData.a = 1;
        }
      ];
      expected = {
        generator = "g";
        stringData = {
          a = 1;
        };
      };
    };
    # `generator` disagreement inside byKey routes to folds.same → throws.
    test-bykey-subfold-conflict-throws = {
      expr = didThrow (
        secretByKey "k" [
          { generator = "g1"; }
          { generator = "g2"; }
        ]
      );
      expected = true;
    };
    test-bykey-unknown-fragment-key-throws = {
      expr = didThrow (secretByKey "k" [ { rogue = 1; } ]);
      expected = true;
    };
    test-bykey-non-attrset-fragment-throws = {
      expr = didThrow (secretByKey "k" [ 7 ]);
      expected = true;
    };

    # ── wiringFor: global schedule order across kinds for one subject ──
    # Five kinds, interleaved: `secret` appears at positions 2, 3 and 5 with `connect` between the
    # second and third, so this list is NOT the per-kind lists concatenated in any kind order.
    test-wiringfor-global-order = {
      expr = map (e: e.kind) (wiringFor r k8s.apps.sonarr);
      expected = [
        "route"
        "database"
        "secret"
        "secret"
        "connect"
        "secret"
        "storage"
      ];
    };
    # each wiringFor entry carries its contributing claim path.
    test-wiringfor-carries-claim-path = {
      expr = map (e: e.claim) (wiringFor r k8s.apps.sonarr);
      expected = [
        [ 0 ]
        [ 1 ]
        [
          0
          1
        ]
        [
          1
          0
        ]
        [
          1
          1
        ]
        [ 2 ]
        [ 3 ]
      ];
    };

    # ── spliceWiring: default folds.one is single-writer-per-key (disjoint splice) ──
    test-splice-default-disjoint = {
      expr = spliceWiring {
        resolution = r;
        subject = k8s.apps.radarr;
      };
      # radarr has only storage (persistence) + secret(api-key env) wiring — disjoint top-level keys.
      expected = {
        env = {
          RADARR__AUTH__APIKEY = {
            secretKeyRef = "media-arr-api-keys";
            key = "radarr";
          };
        };
        persistence = {
          "/data" = {
            mount = "/data";
            claim = "media-data-nfs";
          };
        };
      };
    };
    # default folds.one collision: sonarr multi-writes `env` (database + secret) ⇒ loud error.
    test-splice-default-collision-throws = {
      expr = didThrow (spliceWiring {
        resolution = r;
        subject = k8s.apps.sonarr;
      });
      expected = true;
    };
    # explicit per-key combine: env/persistence merged, egress list-collected.
    test-splice-explicit-combine = {
      expr =
        let
          s = spliceWiring {
            resolution = r;
            subject = k8s.apps.sonarr;
            combine =
              key: vs:
              if key == "env" || key == "persistence" then
                folds.mergeAttrs key vs
              else if key == "egress" then
                folds.list key vs
              else
                folds.one key vs;
          };
        in
        {
          keys = builtins.attrNames s;
          envKeys = builtins.attrNames s.env;
          egressLen = builtins.length s.egress;
          backendRef = s.backendRef;
        };
      expected = {
        keys = [
          "backendRef"
          "egress"
          "env"
          "persistence"
        ];
        envKeys = [
          "OIDC_CLIENT_SECRET"
          "SONARR__AUTH__APIKEY"
          "sonarr__POSTGRES__HOST"
          "sonarr__POSTGRES__PASSWORD"
          "sonarr__POSTGRES__PORT"
        ];
        egressLen = 1;
        backendRef = {
          name = "sonarr";
          port = "http";
        };
      };
    };
  };
}
