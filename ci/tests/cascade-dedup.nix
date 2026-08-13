# dedup — grouping is a pure function of the claim's own fields; folds receive fragments in pinned
# schedule order (never sorted, never reordered); nothing is silently deduplicated (undeclared
# duplication is a loud collision); a singleton group still passes through the fold.
{
  genScope,
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
  k8s = import ./_fixtures/k8s.nix { inherit genScope; };

  didThrow = e: !(builtins.tryEval (builtins.deepSeq e null)).success;

  entry = name: {
    id_hash = "id-${name}";
    inherit name;
  };

  # An `item` kind: group by `c.group`, one resource key per group, fold = list (records order).
  itemKinds = mkKinds [
    (mkKind {
      name = "item";
      dedupKey = c: c.group;
      fold = folds.list;
      resolve = c: _: { resources.${c.group} = c.tag; };
    })
  ];
  runItems =
    tags:
    resolveClaims {
      kinds = itemKinds;
      claims = map (
        t:
        mkClaim {
          kind = "item";
          subject = entry t;
          group = "g";
          tag = t;
        }
      ) tags;
    };

  # A `same`-folded kind producing a group-CONSTANT resource key ⇒ a cross-group collision when two
  # distinct groups both write it.
  collideKinds = mkKinds [
    (mkKind {
      name = "c";
      dedupKey = c: c.group;
      fold = folds.same;
      resolve = c: _: { resources.constant = c.v; };
    })
  ];

  # A fold-less kind: two claims writing the same resource key is a loud error.
  foldlessKinds = mkKinds [
    (mkKind {
      name = "f";
      resolve = _: _: { resources.dup = 1; };
    })
  ];
in
{
  flake.tests.dedup = {
    # ── group membership golden (a shared group folds N claimants into one resource) ──
    test-shared-group-single-key = {
      expr = builtins.attrNames k8s.resolution.resources.secret;
      expected = [
        "media-arr-api-keys"
        "sonarr-oidc-client"
        "sonarr-pg-password"
      ];
    };
    test-shared-group-contributors = {
      expr = k8s.resolution.trace.resources.secret."media-arr-api-keys".claims;
      expected = [
        [ 2 ]
        [ 4 ]
      ];
    };

    # ── the fold receives fragments in schedule (intake) order ──
    test-fold-order-is-schedule-order = {
      expr =
        (runItems [
          "a"
          "b"
          "c"
        ]).resources.item.g;
      expected = [
        "a"
        "b"
        "c"
      ];
    };
    # ── permuting the input permutes the fold order (no silent sort) ──
    test-fold-order-follows-permutation = {
      expr =
        (runItems [
          "c"
          "a"
          "b"
        ]).resources.item.g;
      expected = [
        "c"
        "a"
        "b"
      ];
    };

    # ── a singleton group still passes through the fold (one-element list) ──
    test-singleton-passes-through-fold = {
      expr = (runItems [ "solo" ]).resources.item.g;
      expected = [ "solo" ];
    };

    # ── no silent dedup — a `folds.same` conflict is a loud error ──
    test-folds-same-conflict-throws = {
      expr = didThrow (resolveClaims {
        kinds = collideKinds;
        claims = [
          (mkClaim {
            kind = "c";
            subject = entry "x";
            group = "same-group";
            v = 1;
          })
          (mkClaim {
            kind = "c";
            subject = entry "y";
            group = "same-group";
            v = 2; # differs ⇒ folds.same throws
          })
        ];
      });
      expected = true;
    };
    # ── a cross-group resource-key collision is a loud error ──
    test-cross-group-collision-throws = {
      expr = didThrow (resolveClaims {
        kinds = collideKinds;
        claims = [
          (mkClaim {
            kind = "c";
            subject = entry "x";
            group = "g1";
            v = 1;
          })
          (mkClaim {
            kind = "c";
            subject = entry "y";
            group = "g2"; # a distinct group writing the same "constant" key ⇒ collision
            v = 1;
          })
        ];
      });
      expected = true;
    };
    # ── a fold-less duplicate resource key is a loud error ──
    test-foldless-duplicate-throws = {
      expr = didThrow (resolveClaims {
        kinds = foldlessKinds;
        claims = [
          (mkClaim {
            kind = "f";
            subject = entry "x";
          })
          (mkClaim {
            kind = "f";
            subject = entry "y";
          })
        ];
      });
      expected = true;
    };
    # A non-string dedupKey result is a loud error.
    test-nonstring-dedupkey-throws = {
      expr = didThrow (resolveClaims {
        kinds = mkKinds [
          (mkKind {
            name = "b";
            dedupKey = _: 42;
            fold = folds.same;
            resolve = _: _: { resources.k = 1; };
          })
        ];
        claims = [
          (mkClaim {
            kind = "b";
            subject = entry "x";
          })
        ];
      });
      expected = true;
    };
  };
}
