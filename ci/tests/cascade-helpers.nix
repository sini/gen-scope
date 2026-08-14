# The consumer side of the cascade's published wiring — `resolution.wiring.<id>.entries`, and the
# splice a caller assembles from it — plus the fold vocabulary both that splice and a kind's
# resource fold are written against.
#
# ★ THE ORDER CELL IS THE ONE THAT CANNOT BE WRITTEN ON A SMALL FIXTURE. What the published field
# exists to preserve is GLOBAL SCHEDULE ORDER ACROSS KINDS, and the only construction that could
# get it wrong in a way worth catching is one that reads the per-kind lists in kind order instead.
# On a subject wired by one kind those two answers are identical, so a one-kind fixture pins
# nothing. The fixture below wires `sonarr` from FIVE kinds whose emissions interleave — the
# composite stratum's `route` and `database`, then the leaf stratum's `secret`, `connect` and
# `storage`, including sub-claims each composite emitted — so the two answers DIFFER on it, and the
# expected list below is the one that is not the concatenation of the per-kind lists.
#
# ★ That difference is a claim about the fixture, so it is MEASURED rather than asserted here:
# `ci/bench/wiring-scan.sh` computes the kind-grouped order over this same fixture and reports it
# beside the global one, and calls the sweep INVALID if they agree. A cell cannot host that
# control without changing what the suite counts, and the same sweep already has to exist for the
# ill-formed-input arms below.
#
# ★ THE ILL-FORMED-INPUT ARMS ARE ALSO NOT CELLS, AND FOR A HARDER REASON. The field replaced an
# accessor that rebuilt this list from two lossy views, and every way those two views could
# disagree reached the evaluator rather than a refusal — a missing attribute, an out-of-range
# `elemAt`, a list position holding a set. None of those is a value: each terminates the
# evaluation, so `tryEval` holds none of them and no `didThrow` cell can observe one. What the
# retirement buys is that there is no longer a function to hand such a resolution to, and an
# absence is not something a cell can assert either. Both halves — the retired construction still
# aborting, and the surface no longer being there — are exit-code arms in the same sweep.
{
  genScope,
  lib,
  ...
}:
let
  inherit (genScope) folds;
  k8s = import ./_fixtures/k8s.nix { inherit genScope; };
  consumer = import ./_fixtures/consumer.nix { inherit lib; };
  inherit (consumer) wiringOf erasingWiringOf splice;
  r = k8s.resolution;

  didThrow = e: !(builtins.tryEval (builtins.deepSeq e null)).success;

  # ── a run in which a subject IS claimed and IS NOT wired ──
  # The k8s fixture cannot host this case: every one of its claim subjects is wired, so a subject
  # drawn from it is FOREIGN to the run rather than unwired, and a cell pointed at one measures the
  # never-claimed case twice. This kind set emits resources and no wiring, which is the only way to
  # reach a subject the run registered and left empty.
  unwiredKinds = genScope.mkKinds [
    (genScope.mkKind {
      name = "noWire";
      resolve = c: _ctx: {
        resources.${c.subject.name} = {
          ok = true;
        };
      };
    })
  ];
  unwiredSubject = {
    id_hash = "id-q";
    name = "q";
  };
  neverClaimedSubject = {
    id_hash = "id-never-claimed";
    name = "never";
  };
  unwiredRun = genScope.resolveClaims {
    kinds = unwiredKinds;
    claims = [
      (genScope.mkClaim {
        kind = "noWire";
        subject = unwiredSubject;
      })
    ];
  };

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

    # ── the published entry list: global schedule order across kinds for one subject ──
    # Five kinds, interleaved: `secret` appears at positions 2, 3 and 5 with `connect` between the
    # second and third, so this list is NOT the per-kind lists concatenated in any kind order.
    test-published-entries-global-order = {
      expr = map (e: e.kind) (wiringOf r k8s.apps.sonarr).entries;
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
    # each published entry carries its contributing claim path.
    test-published-entries-carry-claim-path = {
      expr = map (e: e.claim) (wiringOf r k8s.apps.sonarr).entries;
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
    # ★ THE RELOCATION, PINNED WHOLE RATHER THAN BY PROJECTION. The two cells above assert the two
    # projections a reconstructing accessor used to be checked on; this one asserts the entry list
    # itself, VALUES INCLUDED, against the list that accessor returned over this same fixture. It is
    # the cell that would redden if publishing the field had changed the answer rather than moved
    # it, which the order and provenance projections alone cannot see.
    test-published-entries-equal-the-retired-scan = {
      expr = (wiringOf r k8s.apps.sonarr).entries;
      expected = [
        {
          claim = [ 0 ];
          kind = "route";
          wiring.backendRef = {
            name = "sonarr";
            port = "http";
          };
        }
        {
          claim = [ 1 ];
          kind = "database";
          wiring.env = {
            sonarr__POSTGRES__HOST = "media-pg";
            sonarr__POSTGRES__PORT = "5432";
          };
        }
        {
          claim = [
            0
            1
          ];
          kind = "secret";
          wiring.env.OIDC_CLIENT_SECRET = {
            key = "sonarr";
            secretKeyRef = "sonarr-oidc-client";
          };
        }
        {
          claim = [
            1
            0
          ];
          kind = "secret";
          wiring.env.sonarr__POSTGRES__PASSWORD = {
            key = "sonarr";
            secretKeyRef = "sonarr-pg-password";
          };
        }
        {
          claim = [
            1
            1
          ];
          kind = "connect";
          wiring.egress = {
            port = 5432;
            to = "media-pg";
          };
        }
        {
          claim = [ 2 ];
          kind = "secret";
          wiring.env.SONARR__AUTH__APIKEY = {
            key = "sonarr";
            secretKeyRef = "media-arr-api-keys";
          };
        }
        {
          claim = [ 3 ];
          kind = "storage";
          wiring.persistence."/data" = {
            claim = "media-data-nfs";
            mount = "/data";
          };
        }
      ];
    };

    # ── the record is TOTAL, and the read a consumer is told to use keeps that ──
    # A subject a claim named but nothing wired KEEPS its key, carrying an empty entry list; a
    # subject no claim ever named has no key at all. Absence therefore means NOT REGISTERED, and
    # the two observations stay two at the surface a consumer reads.
    test-registered-but-unwired-subject-keeps-its-record = {
      expr = wiringOf unwiredRun unwiredSubject;
      expected = {
        registered = true;
        entries = [ ];
      };
    };
    test-never-claimed-subject-has-no-record = {
      expr = wiringOf unwiredRun neverClaimedSubject;
      expected = {
        registered = false;
      };
    };
    # ARMED: the distinction above is genuinely losable, so the cells claiming it are not reading a
    # difference no construction could erase. Defaulting the record answers the same empty list for
    # both subjects — which is the erasure the published field's totality exists to rule out,
    # re-created one call outward by the caller.
    test-armed-the-erasing-read-loses-the-distinction = {
      expr = {
        unwired = erasingWiringOf unwiredRun unwiredSubject;
        neverClaimed = erasingWiringOf unwiredRun neverClaimedSubject;
      };
      expected = {
        unwired = [ ];
        neverClaimed = [ ];
      };
    };

    # ── the consumer's splice: folds.one is single-writer-per-key (disjoint splice) ──
    test-splice-default-disjoint = {
      expr = splice {
        resolution = r;
        subject = k8s.apps.radarr;
        combine = folds.one;
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
    # folds.one collision: sonarr multi-writes `env` (database + secret) ⇒ loud error.
    test-splice-default-collision-throws = {
      expr = didThrow (splice {
        resolution = r;
        subject = k8s.apps.sonarr;
        combine = folds.one;
      });
      expected = true;
    };
    # explicit per-key combine: env/persistence merged, egress list-collected.
    test-splice-explicit-combine = {
      expr =
        let
          s = splice {
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
