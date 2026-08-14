# `resolveClaims` is a pure, deterministic function of its inputs: repeated evaluation is
# byte-identical, structurally-equal inputs yield equal outputs, the claim list's order is
# significant, and the engine manufactures no value — resources and wiring pass through untouched.
#
# ★ THE TWO EQUALITY CELLS CANNOT ARM THEMSELVES. `toJSON a == toJSON b` is green on a construction
# that returns the same empty record for every input, so the value cells beside them are what make
# the equalities mean anything: they pin what a run actually carries. The `test-control-…` cell
# below closes the other half — that the predicate is capable of returning false at all — because
# an equality that never fails is not evidence of determinism.
{ genScope, ... }:
let
  inherit (genScope)
    mkKinds
    mkKind
    mkClaim
    resolveClaims
    ;
  k8s = import ./_fixtures/k8s.nix { inherit genScope; };
  r = k8s.resolution;

  entry = name: {
    id_hash = "id-${name}";
    inherit name;
  };

  # A small deterministic set, resolved twice from independently-constructed but structurally-equal
  # inputs. Values pass straight through — the engine adds nothing.
  simpleKinds = mkKinds [
    (mkKind {
      name = "leaf";
      resolve = c: _: {
        resources.${c.subject.name} = {
          tag = c.tag;
        };
        wiring.env.${c.subject.name} = c.tag;
      };
    })
  ];
  buildClaims =
    tags:
    map (
      t:
      mkClaim {
        kind = "leaf";
        subject = entry t;
        tag = t;
      }
    ) tags;
  resA = resolveClaims {
    kinds = simpleKinds;
    claims = buildClaims [
      "x"
      "y"
    ];
  };
  resB = resolveClaims {
    kinds = simpleKinds;
    claims = buildClaims [
      "x"
      "y"
    ];
  };
  # Same kinds, DIFFERENT claims — the arming comparand for the two equality cells.
  resC = resolveClaims {
    kinds = simpleKinds;
    claims = buildClaims [
      "x"
      "z"
    ];
  };
in
{
  flake.tests.cascade-determinism = {
    # ── byte-identical output on repeated resolveClaims (k8s fixture) ──
    test-k8s-repeated-eval-identical = {
      expr =
        let
          again = (import ./_fixtures/k8s.nix { inherit genScope; }).resolution;
        in
        builtins.toJSON again == builtins.toJSON r;
      expected = true;
    };

    # ── structurally-equal input sets → equal outputs ──
    test-structurally-equal-inputs-equal-output = {
      expr = builtins.toJSON resA == builtins.toJSON resB;
      expected = true;
    };

    # ── the engine manufactures no value: resources pass through untouched ──
    test-resource-value-passes-through = {
      expr = resA.resources.leaf.x;
      expected = {
        tag = "x";
      };
    };
    test-wiring-value-passes-through = {
      expr = resA.wiring."id-x".byKind.leaf;
      expected = [
        {
          env = {
            x = "x";
          };
        }
      ];
    };

    # ── golden {resources; wiring} shape on the k8s fixture ──
    test-k8s-resource-kinds-golden = {
      expr = builtins.attrNames r.resources;
      expected = [
        "connect"
        "database"
        "route"
        "secret"
        "storage"
      ];
    };
    test-k8s-shared-secret-golden = {
      expr = r.resources.secret."media-arr-api-keys";
      expected = {
        generator = "hex-secret";
        stringData = {
          radarr = "secret://radarr/arr-api-key";
          sonarr = "secret://sonarr/arr-api-key";
        };
      };
    };
    # storage shared claim provisioned ONCE (folds.same across sonarr + radarr).
    test-k8s-shared-storage-golden = {
      expr = r.resources.storage."media-data-nfs";
      expected = {
        claim = "media-data-nfs";
        path = "/data";
      };
    };

    # ── claim list order is significant: swapping two roots reorders the trace ──
    test-order-significant = {
      expr =
        map (c: c.subject.rendered)
          (resolveClaims {
            kinds = simpleKinds;
            claims = buildClaims [
              "y"
              "x"
            ];
          }).trace.claims;
      expected = [
        "y"
        "x"
      ];
    };

    # ── ARMING: the equality predicate can return false ──
    # Two runs over the same kinds and a claim list differing in one tag must NOT compare equal. A
    # construction that answered the same record regardless of input passes both equality cells
    # above and fails this one.
    test-control-differing-inputs-do-not-compare-equal = {
      expr = builtins.toJSON resA == builtins.toJSON resC;
      expected = false;
    };
  };
}
