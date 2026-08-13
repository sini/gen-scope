# The five k8s claim kinds as an executable fixture: connect/secret/storage are leaves (depth 0),
# database/route are composites (depth 1). The resource bodies are simplified stand-ins for real
# derivers — they exercise the cascade discipline (grouping, folds, dedup, sub-claim emission,
# wiring) without a live cluster context. Subjects are registry entries carrying `id_hash`.
#
# NOT A SUITE. It sits under `_fixtures/` because the tree importer ignores any path containing
# `/_`, so this file is reached only by the suites that import it and never as a flake module.
{ genScope }:
let
  inherit (genScope)
    mkKind
    mkKinds
    mkClaim
    folds
    ;

  # ── entity fixtures (registry entries: id_hash + name) ──
  entry = name: {
    id_hash = "id-${name}";
    inherit name;
  };
  apps = {
    sonarr = entry "sonarr";
    radarr = entry "radarr";
    media-pg = entry "media-pg";
  };
  gatewaysNs = entry "gateways-ns";

  # A minimal static context, passed verbatim to every resolver.
  ctx = {
    marker = "CTX-VERBATIM";
    optional = cond: v: if cond then [ v ] else [ ];
  };

  kinds = mkKinds [
    # ── floor: connect (leaf) ──
    (mkKind {
      name = "connect";
      dedupKey = c: "${c.subject.id_hash}->${c.to.id_hash}:${toString (c.port or "any")}";
      fold = folds.same; # duplicate edges must agree, provision once
      resolve = c: _ctx: {
        resources."cnp:${c.subject.name}->${c.to.name}:${toString (c.port or "any")}" = {
          from = c.subject.name;
          to = c.to.name;
          port = c.port or null;
        };
        wiring.egress = {
          to = c.to.name;
          port = c.port or null;
        };
      };
    })

    # ── leaf fabric: secret ──
    (mkKind {
      name = "secret";
      dedupKey = c: c.shared or "private:${c.subject.id_hash}:${c.name}";
      fold = folds.byKey {
        generator = folds.same; # all claimants must agree on the generator
        stringData = folds.mergeAttrs; # one stringData entry per claimant
      };
      resolve = c: _ctx: {
        resources.${c.shared or "${c.subject.name}-${c.name}"} = {
          generator = c.generator;
          stringData.${c.subject.name} = "secret://${c.subject.name}/${c.name}";
        };
        wiring.env.${c.consumeAs.env} = {
          secretKeyRef = c.shared or "${c.subject.name}-${c.name}";
          key = c.subject.name;
        };
      };
    })

    # ── leaf fabric: storage ──
    (mkKind {
      name = "storage";
      dedupKey = c: c.claim or "provision:${c.subject.id_hash}:${c.path}";
      fold = folds.same; # a shared PV+PVC is provisioned once
      resolve = c: _ctx: {
        resources.${c.claim or "pvc:${c.subject.name}:${c.path}"} = {
          claim = c.claim or null;
          inherit (c) path;
        };
        wiring.persistence.${c.path} = {
          mount = c.path;
          claim = c.claim or "pvc:${c.subject.name}:${c.path}";
        };
      };
    })

    # ── composite: database (depth 1) ──
    (mkKind {
      name = "database";
      below = [
        "secret"
        "connect"
      ];
      resolve = c: _ctx: {
        resources."cnpg:${c.subject.name}" = {
          role = c.subject.name;
          inherit (c) dbs;
        };
        wiring.env = {
          "${c.subject.name}__POSTGRES__HOST" = c.provider.name;
          "${c.subject.name}__POSTGRES__PORT" = "5432";
        };
        claims = [
          (mkClaim {
            kind = "secret";
            inherit (c) subject;
            name = "pg-password";
            generator = "rfc3986-secret";
            consumeAs.env = "${c.subject.name}__POSTGRES__PASSWORD";
          })
          (mkClaim {
            kind = "connect";
            inherit (c) subject;
            to = c.provider;
            port = 5432;
          })
        ];
      };
    })

    # ── composite: route (depth 1) ──
    (mkKind {
      name = "route";
      below = [
        "secret"
        "connect"
      ];
      resolve = c: cx: {
        resources."httproute:${c.subject.name}" = {
          inherit (c) domain backendPort;
        };
        wiring.backendRef = {
          name = c.subject.name;
          port = c.backendPort;
        };
        claims = [
          (mkClaim {
            kind = "connect";
            subject = gatewaysNs;
            to = c.subject;
            port = c.backendPort;
          })
        ]
        ++ cx.optional (c.oidc or false) (mkClaim {
          kind = "secret";
          inherit (c) subject;
          name = "oidc-client";
          generator = "rfc3986-secret";
          consumeAs.env = "OIDC_CLIENT_SECRET";
        });
      };
    })
  ];

  # The canonical root-claim list: a sonarr route + database + shared api-key secret + storage
  # claim; radarr shares the api-key group and the storage claim.
  claims = [
    (mkClaim {
      kind = "route";
      subject = apps.sonarr;
      domain = "sonarr";
      backendPort = "http";
      oidc = true;
    })
    (mkClaim {
      kind = "database";
      subject = apps.sonarr;
      provider = apps.media-pg;
      dbs = [
        "main"
        "log"
      ];
    })
    (mkClaim {
      kind = "secret";
      subject = apps.sonarr;
      name = "arr-api-key";
      generator = "hex-secret";
      shared = "media-arr-api-keys";
      consumeAs.env = "SONARR__AUTH__APIKEY";
    })
    (mkClaim {
      kind = "storage";
      subject = apps.sonarr;
      claim = "media-data-nfs";
      path = "/data";
    })
    (mkClaim {
      kind = "secret";
      subject = apps.radarr;
      name = "arr-api-key";
      generator = "hex-secret";
      shared = "media-arr-api-keys";
      consumeAs.env = "RADARR__AUTH__APIKEY";
    })
    (mkClaim {
      kind = "storage";
      subject = apps.radarr;
      claim = "media-data-nfs";
      path = "/data";
    })
  ];

  resolution = genScope.resolveClaims { inherit kinds claims ctx; };
in
{
  inherit
    kinds
    claims
    ctx
    apps
    gatewaysNs
    resolution
    ;
}
