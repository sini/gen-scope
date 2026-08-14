# The five-kind claim cascade as an executable golden: composite cascades observed in the trace,
# shared-group folding, private-secret coexistence, shared storage provisioned once, connect dedup
# with port-distinct groups, and the per-app wiring splice.
#
# ★ THIS IS THE END-TO-END SUITE AND IT IS THE ONLY ONE THAT READS THE COMPOSITE STRATUM'S OWN
# ARTIFACTS. `cascade-dedup` and `cascade-helpers` import the same fixture, but they read the leaf
# fabric and the accessor's view of it; nothing before this file asserts that `route` and
# `database` cascade into the sub-claims they emit, or what the spliced result of that cascade is.
#
# ★ THE SPLICE CELL IS NOT A DUPLICATE OF `cascade-helpers`' `test-splice-explicit-combine`, which
# asserts a PROJECTION of the same call — key names, env key names, egress length, backendRef. This
# one asserts the whole value, so the secret bodies and the persistence mount are pinned rather
# than counted. A construction that answered the right shape with the wrong contents passes there
# and fails here.
{ lib, genScope, ... }:
let
  inherit (genScope)
    mkClaim
    resolveClaims
    folds
    ;
  k8s = import ./_fixtures/k8s.nix { inherit genScope; };
  inherit (import ./_fixtures/consumer.nix { inherit lib; }) splice;
  r = k8s.resolution;

  entry = name: {
    id_hash = "id-${name}";
    inherit name;
  };
  a = entry "a";
  b = entry "b";

  # ── two databases sharing a provider: private pg-password secrets must coexist (subject-namespaced) ──
  twoDbs = resolveClaims {
    inherit (k8s) kinds ctx;
    claims = [
      (mkClaim {
        kind = "database";
        subject = k8s.apps.sonarr;
        provider = k8s.apps.media-pg;
        dbs = [ "main" ];
      })
      (mkClaim {
        kind = "database";
        subject = k8s.apps.radarr;
        provider = k8s.apps.media-pg;
        dbs = [ "main" ];
      })
    ];
  };

  # ── connect dedup + port-distinctness (folds.same collapses identical edges; port splits groups) ──
  connectClaims = [
    (mkClaim {
      kind = "connect";
      subject = a;
      to = b;
      port = 80;
    })
    (mkClaim {
      kind = "connect";
      subject = a;
      to = b;
      port = 80;
    }) # identical ⇒ folds.same collapses to one
    (mkClaim {
      kind = "connect";
      subject = a;
      to = b;
      port = 443;
    }) # different port ⇒ distinct group + distinct key
  ];
  connects = resolveClaims {
    inherit (k8s) kinds ctx;
    claims = connectClaims;
  };
in
{
  flake.tests.cascade-instance-k8s = {
    # ── route → connect(gateways-ns→sonarr) + secret(oidc); database → secret(pg) + connect(→pg) ──
    test-route-cascade-in-trace = {
      expr = lib.filter (c: c.parent == [ 0 ]) (map (c: { inherit (c) kind parent; }) r.trace.claims);
      expected = [
        {
          kind = "connect";
          parent = [ 0 ];
        }
        {
          kind = "secret";
          parent = [ 0 ];
        }
      ];
    };
    test-database-cascade-in-trace = {
      expr = lib.filter (c: c.parent == [ 1 ]) (map (c: { inherit (c) kind parent; }) r.trace.claims);
      expected = [
        {
          kind = "secret";
          parent = [ 1 ];
        }
        {
          kind = "connect";
          parent = [ 1 ];
        }
      ];
    };

    # ── shared api-key group folds N claimants into ONE Secret (byKey: generator same, stringData merge) ──
    test-shared-api-key-single-secret = {
      expr =
        r.resources.secret."media-arr-api-keys" == {
          generator = "hex-secret";
          stringData = {
            sonarr = "secret://sonarr/arr-api-key";
            radarr = "secret://radarr/arr-api-key";
          };
        };
      expected = true;
    };

    # ── two databases' private pg-password secrets coexist (subject-namespaced keys, no collision) ──
    test-private-secrets-coexist = {
      expr = builtins.attrNames twoDbs.resources.secret;
      expected = [
        "radarr-pg-password"
        "sonarr-pg-password"
      ];
    };

    # ── shared storage claim provisioned once ──
    test-shared-storage-once = {
      expr = builtins.attrNames r.resources.storage;
      expected = [ "media-data-nfs" ];
    };
    test-shared-storage-single-contributor-list = {
      # folds.same over two claimants (sonarr + radarr) ⇒ one provisioned value, both paths traced.
      expr = r.trace.resources.storage."media-data-nfs".claims;
      expected = [
        [ 3 ]
        [ 5 ]
      ];
    };

    # ── connect dedup via folds.same; same-pair different-port stays distinct ──
    test-connect-dedup-and-port-distinct = {
      expr = builtins.attrNames connects.resources.connect;
      expected = [
        "cnp:a->b:443"
        "cnp:a->b:80"
      ];
    };
    test-connect-dedup-collapses-identical = {
      # the two identical :80 edges collapse to one group; both intake paths traced.
      expr = connects.trace.resources.connect."cnp:a->b:80".claims;
      expected = [
        [ 0 ]
        [ 1 ]
      ];
    };

    # ── per-app wiring splice golden (explicit per-key combine) ──
    test-sonarr-wiring-splice = {
      expr = splice {
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
      expected = {
        backendRef = {
          name = "sonarr";
          port = "http";
        };
        egress = [
          {
            to = "media-pg";
            port = 5432;
          }
        ];
        env = {
          OIDC_CLIENT_SECRET = {
            secretKeyRef = "sonarr-oidc-client";
            key = "sonarr";
          };
          SONARR__AUTH__APIKEY = {
            secretKeyRef = "media-arr-api-keys";
            key = "sonarr";
          };
          sonarr__POSTGRES__HOST = "media-pg";
          sonarr__POSTGRES__PORT = "5432";
          sonarr__POSTGRES__PASSWORD = {
            secretKeyRef = "sonarr-pg-password";
            key = "sonarr";
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

    # ── ARMING: the dedup cells are about a COLLAPSE, so the input has to be bigger than the output ──
    # Three claims in, two resource keys out. Both dedup cells above read the output alone and are
    # green on a construction that never grouped anything, because two of the three inputs are
    # byte-identical and a pass-through would still answer two distinct keys.
    test-control-three-connect-claims-produce-two-resource-keys = {
      expr = {
        claimsIn = builtins.length connectClaims;
        keysOut = builtins.length (builtins.attrNames connects.resources.connect);
        tracedIntoTheCollapsedKey = builtins.length connects.trace.resources.connect."cnp:a->b:80".claims;
      };
      expected = {
        claimsIn = 3;
        keysOut = 2;
        tracedIntoTheCollapsedKey = 2;
      };
    };
  };
}
