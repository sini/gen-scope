# The cascade's trace: every claim's parent chain reaches a root, every artifact maps to at least
# one contributing path, the wiring trace aligns positionally with `byKind`, and the global order
# is stratum-major rather than path-lexicographic.
#
# THEORY: why/derivation provenance — Cheney, Chiticariu & Tan 2009, *Provenance in Databases: Why,
# How, and Where* — each artifact maps to the claim instances that produced it, extended here with
# parent chains to the roots. The engine records the chain; it does not compute a semiring
# annotation, and the carried citation is to the why/derivation reading only. The name is taken from
# the literature rather than checked: that survey is not in the project archive, and what these cells
# assert is the recorded chain, which needs no paper to be true.
#
# ★ FOUR OF THESE CELLS ARE UNIVERSALLY QUANTIFIED OVER A DOMAIN THE FIXTURE SUPPLIES, so each is
# green on an empty domain. The three `test-control-…` cells below pin those domains by COUNT, not
# by non-emptiness: a fixture that shrank to one claim would still be non-empty, and the cells that
# read it would still say nothing. They are the arming for the quantified cells beside them and are
# not part of the absorbed set.
{ lib, genScope, ... }:
let
  k8s = import ./_fixtures/k8s.nix { inherit genScope; };
  r = k8s.resolution;

  inherit (builtins)
    all
    attrNames
    elem
    length
    map
    ;

  claims = r.trace.claims;
  pathsPresent = map (c: c.path) claims;

  # `init` of a non-empty list (drop last element).
  parentPrefix = p: lib.init p;

  # Every claim's parent is either null (a root) or the direct-prefix path of an existing claim.
  parentChainsSound = all (
    c:
    if c.parent == null then
      length c.path == 1
    else
      c.parent == parentPrefix c.path && elem c.parent pathsPresent
  ) claims;

  # The stratum-major golden: locate route[0], database[1], and the connect sub-claim [0 0].
  idxOfPath =
    p:
    lib.foldl (
      acc: i: if (builtins.elemAt claims i).path == p then i else acc
    ) (throw "path ${builtins.toJSON p} not in trace") (lib.range 0 (length claims - 1));
in
{
  flake.tests.cascade-provenance = {
    # ── every parent chain reaches a root ──
    test-parent-chains-reach-root = {
      expr = parentChainsSound;
      expected = true;
    };

    # ── every resource artifact maps to ≥1 contributing path ──
    test-resource-artifacts-have-paths = {
      expr = all (
        kn: all (k: length r.trace.resources.${kn}.${k}.claims >= 1) (attrNames r.trace.resources.${kn})
      ) (attrNames r.trace.resources);
      expected = true;
    };
    # ── every wiring artifact maps to ≥1 contributing claim ──
    test-wiring-artifacts-have-paths = {
      expr = all (id: length r.trace.wiring.${id} >= 1) (attrNames r.trace.wiring);
      expected = true;
    };

    # ── wiring trace aligns positionally with byKind lists (per subject, per kind, same length) ──
    test-wiring-trace-aligns-with-bykind = {
      expr = all (
        id:
        let
          traceKinds = map (e: e.kind) r.trace.wiring.${id};
          byKind = r.wiring.${id}.byKind;
        in
        all (kn: length (builtins.filter (k: k == kn) traceKinds) == length byKind.${kn}) (attrNames byKind)
      ) (attrNames r.trace.wiring);
      expected = true;
    };

    # ── global schedule order: stratum-major, NOT global path-lex ──
    # sub-claim [0 0] (stratum 0) must list AFTER root [1] (stratum 1), even though [0 0] is
    # path-lex-before [1].
    test-substratum-after-higher-root = {
      expr =
        idxOfPath [
          0
          0
        ] > idxOfPath [ 1 ];
      expected = true;
    };
    test-roots-of-higher-stratum-first = {
      expr =
        idxOfPath [ 0 ] < idxOfPath [
          0
          0
        ];
      expected = true;
    };

    # ── full-trace golden: the exact global sequence of (path, kind) ──
    test-full-trace-sequence = {
      expr = map (c: {
        inherit (c) kind;
        p = c.path;
      }) claims;
      expected = [
        {
          kind = "route";
          p = [ 0 ];
        }
        {
          kind = "database";
          p = [ 1 ];
        }
        {
          kind = "connect";
          p = [
            0
            0
          ];
        }
        {
          kind = "secret";
          p = [
            0
            1
          ];
        }
        {
          kind = "secret";
          p = [
            1
            0
          ];
        }
        {
          kind = "connect";
          p = [
            1
            1
          ];
        }
        {
          kind = "secret";
          p = [ 2 ];
        }
        {
          kind = "storage";
          p = [ 3 ];
        }
        {
          kind = "secret";
          p = [ 4 ];
        }
        {
          kind = "storage";
          p = [ 5 ];
        }
      ];
    };

    # ── trace is a pure function of the inputs: byte-identical across repeated evaluation ──
    test-trace-pure-across-eval = {
      expr =
        let
          again = (import ./_fixtures/k8s.nix { inherit genScope; }).resolution;
        in
        builtins.toJSON again.trace == builtins.toJSON r.trace;
      expected = true;
    };

    # ── ARMING: the domains the four quantified cells above range over ──
    # Pinned by count. Six roots cascade into four sub-claims, and the parent-chain cell is only
    # about chains at all because four of the ten carry a non-null parent.
    test-control-the-claim-trace-domain-is-ten-claims-four-of-them-children = {
      expr = {
        total = length claims;
        children = length (builtins.filter (c: c.parent != null) claims);
      };
      expected = {
        total = 10;
        children = 4;
      };
    };
    # Five kinds contribute resources, eight artifacts between them.
    test-control-the-resource-trace-domain-is-five-kinds-and-eight-artifacts = {
      expr = {
        kinds = length (attrNames r.trace.resources);
        artifacts = length (
          builtins.concatMap (kn: attrNames r.trace.resources.${kn}) (attrNames r.trace.resources)
        );
      };
      expected = {
        kinds = 5;
        artifacts = 8;
      };
    };
    # Three subjects are wired, and the alignment cell reads a `byKind` on each of them — an empty
    # `byKind` would leave its inner quantifier vacuous while the outer one still ranged over three.
    test-control-every-wired-subject-has-a-non-empty-bykind = {
      expr = {
        subjects = length (attrNames r.trace.wiring);
        allNonEmpty = all (id: length (attrNames r.wiring.${id}.byKind) >= 1) (attrNames r.trace.wiring);
      };
      expected = {
        subjects = 3;
        allNonEmpty = true;
      };
    };
  };
}
