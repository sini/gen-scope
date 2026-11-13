# THE CONTAINMENT LABEL IS STAMPED ON EVERY CONTAINMENT EDGE GEN-SCOPE BUILDS (den-hoag-f77c8 U1a).
# A spawned child carries its entry's label, an `nta` child its NTA name, and a root the label
# `buildRoots`' `containedAs` gives it. The refusals are message cells in `ci/tests-error.nix`'s
# `contained-as-refusals`; these are the admitting half, with each refusal's boolean beside it.
{ genScope, ... }:
let
  S = genScope;
  inherit (S) mkKind mkKinds buildRoots;

  leafAt = label: key: _self: id: {
    "${id}/${label}/${key}" = {
      decls = { };
    };
  };
  entry = produced: label: key: {
    inherit produced;
    builder = leafAt label key;
  };

  # A host declaring the given entries over `below`; one root `h` of that kind.
  evWith =
    below: spawns:
    let
      kinds = mkKinds [
        (mkKind { } "needle")
        (mkKind { } "thread")
        (mkKind { inherit below spawns; } "host")
      ];
    in
    S.eval { parseParent = id: if id == "h" then null else "h"; } { children = _: _: { }; }
      (buildRoots {
        inherit kinds;
        parentGraph = S.vertex "h";
        types.h = "host";
      });

  # A2: two labels producing one kind on one host.
  twoLabels = evWith [ "needle" ] {
    needles = entry "needle" "needles" "m";
    pins = entry "needle" "pins" "p";
  };
  labelOf = ev: id: (ev.node id).containedAs;

  # A7: the order entries compose in — `below` position of their produced kind, then label bytewise.
  orderOf = below: spawns: S.childrenIds (evWith below spawns) "h";
  four = {
    zeta = entry "needle" "zeta" "1";
    alpha = entry "thread" "alpha" "2";
    mid = entry "needle" "mid" "3";
    beta = entry "thread" "beta" "4";
  };

  # A4: an `nta` child of NTA `sub`.
  ntaKinds = mkKinds [
    (mkKind {
      nta.sub = _: id: if id == "r" then { g.k1 = [ ]; } else { };
    } "host")
  ];
  ntaEv = S.eval { } { children = _: _: { }; } (buildRoots {
    kinds = ntaKinds;
    parentGraph = S.vertex "r";
    types.r = "host";
  });
  ntaKid = S.mintNtaId {
    host = "r";
    name = "sub";
    group = "g";
    key = "k1";
  };

  # A5: roots `r` and `s`; only `r` is labelled.
  labelledRoots = buildRoots {
    parentGraph = S.overlays [
      (S.vertex "r")
      (S.vertex "s")
    ];
    containedAs.r = "hosts";
  };
  refused = v: !(builtins.tryEval (builtins.deepSeq v v)).success;
in
{
  flake.tests.contained-as = {
    # ── A1: a spawned child carries its entry's label ──
    test-A1-a-spawned-child-carries-its-entrys-label = {
      expr = labelOf twoLabels "h/needles/m";
      expected = "needles";
    };
    # ── A2: two labels of one kind on one host are two edges ──
    test-A2-two-same-kind-labels-stamp-their-own-children = {
      expr = {
        ids = S.childrenIds twoLabels "h";
        labels = map (labelOf twoLabels) (S.childrenIds twoLabels "h");
        types = map (id: (twoLabels.node id).type) (S.childrenIds twoLabels "h");
      };
      expected = {
        ids = [
          "h/needles/m"
          "h/pins/p"
        ];
        labels = [
          "needles"
          "pins"
        ];
        types = [
          "needle"
          "needle"
        ];
      };
    };
    # ── A3's boolean: a builder asserting the label is refused ──
    test-A3-a-builder-asserting-the-label-is-refused = {
      expr = refused (
        (evWith [ "needle" ] {
          needles = {
            produced = "needle";
            builder = _: id: {
              "${id}/x" = {
                containedAs = "asserted";
                decls = { };
              };
            };
          };
        }).node
          "h/x"
      );
      expected = true;
    };
    # ── A4: an `nta` child carries its NTA name ──
    test-A4-an-nta-child-carries-its-nta-name = {
      expr = (ntaEv.node ntaKid).containedAs;
      expected = "sub";
    };
    # ── A5: a root carries the label `buildRoots` gives it, and only that root ──
    test-A5-a-labelled-root-carries-its-label = {
      expr = labelledRoots.nodes.r.containedAs;
      expected = "hosts";
    };
    test-A5-an-unlabelled-root-carries-no-label-field = {
      expr = labelledRoots.nodes.s ? containedAs;
      expected = false;
    };
    test-A5-a-scope-declaring-no-label-carries-no-field = {
      expr = (buildRoots { parentGraph = S.vertex "r"; }).nodes.r ? containedAs;
      expected = false;
    };
    test-A5-a-label-naming-no-vertex-is-refused = {
      expr = refused (buildRoots {
        parentGraph = S.vertex "r";
        containedAs.nowhere = "hosts";
      });
      expected = true;
    };
    # ── A6's booleans: the retired kind-keyed form, and a malformed entry ──
    test-A6-the-retired-kind-keyed-form-is-refused = {
      expr = refused (
        mkKind {
          below = [ "needle" ];
          spawns.needle = leafAt "needle" "m";
        } "host"
      );
      expected = true;
    };
    test-A6-an-entry-with-a-third-field-is-refused = {
      expr = refused (
        mkKind {
          below = [ "needle" ];
          spawns.needles = entry "needle" "needles" "m" // {
            extra = null;
          };
        } "host"
      );
      expected = true;
    };
    # ── A7: below order across kinds, label order within one; 2, 3 and 4 entries, both orders ──
    test-A7-two-entries-of-one-kind-order-by-label = {
      expr = orderOf [ "needle" ] {
        pins = entry "needle" "pins" "1";
        needles = entry "needle" "needles" "2";
      };
      expected = [
        "h/needles/2"
        "h/pins/1"
      ];
    };
    test-A7-three-entries-follow-below-then-label = {
      expr = {
        nt = orderOf [ "needle" "thread" ] (builtins.removeAttrs four [ "beta" ]);
        tn = orderOf [ "thread" "needle" ] (builtins.removeAttrs four [ "beta" ]);
      };
      expected = {
        nt = [
          "h/mid/3"
          "h/zeta/1"
          "h/alpha/2"
        ];
        tn = [
          "h/alpha/2"
          "h/mid/3"
          "h/zeta/1"
        ];
      };
    };
    test-A7-four-entries-follow-below-then-label = {
      expr = {
        nt = orderOf [ "needle" "thread" ] four;
        tn = orderOf [ "thread" "needle" ] four;
      };
      expected = {
        nt = [
          "h/mid/3"
          "h/zeta/1"
          "h/alpha/2"
          "h/beta/4"
        ];
        tn = [
          "h/alpha/2"
          "h/beta/4"
          "h/mid/3"
          "h/zeta/1"
        ];
      };
    };
  };
}
