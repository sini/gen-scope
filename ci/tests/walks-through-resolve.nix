# THE FOUR COLLECTION WALKS ARE RESOLUTIONS (den-hoag-4or0a) — `inheritAll`, `inheritSet` and
# `collectionAttr`'s `"ancestors"` and `"neron"` are each a `resolve`, so each inherits the
# calculus's contract: a boundary mark withholds through them exactly as through `inherit'`
# (ADR-0026's fail-closed floor), a store-context id or label answers rather than aborting, and
# `"neron"` gathers every scope `neron.wf` reaches, once, in `<p` order. The refusals (a parent
# cycle, the retired `_visited`, a non-string label) are `tests-error.nix`'s `walks-through-resolve`.
# The scopes are `_fixtures/walks-through-resolve.nix`'s.
{ genScope, ... }:
let
  S = genScope;
  F = import ./_fixtures/walks-through-resolve.nix { inherit genScope; };
  has = builtins.hasContext;
in
{
  flake.tests.walks-through-resolve = {
    # A1: `s` carries a mark admitting no label, so every edge leaving it is withheld — the four walks
    # answer nothing, as `inherit'` does over the same scope.
    test-A1-a-mark-withholds-through-every-walk = {
      expr = F.walks F.shut "s" // {
        inherited = S."inherit'" { } (n: n.decls.v or null) F.shut "s";
      };
      expected = {
        all = [ ];
        set = [ ];
        ancestors = [ ];
        neron = [ ];
        inherited = null;
      };
    };
    # A1c: the live twin, the same scope with no mark — every walk answers, so A1's `[ ]` is the mark.
    test-A1c-the-unmarked-twin-answers = {
      expr = F.walks F.open "s";
      expected = {
        all = [
          "vp"
          "vg"
        ];
        set = [
          "vp"
          "vg"
        ];
        ancestors = [
          "vp"
          "vg"
        ];
        neron = [
          "vx"
          "vp"
          "vg"
        ];
      };
    };
    # Each walk equals the question put to `resolve` directly, marked and unmarked.
    test-A1-every-walk-is-its-resolve-reference = {
      expr = {
        shut = F.walks F.shut "s" == F.refs F.shut "s";
        open = F.walks F.open "s" == F.refs F.open "s";
      };
      expected = {
        shut = true;
        open = true;
      };
    };

    # A2: a label carrying store-path context is keyed by its text at every site that builds an edge
    # attribute name; the target is answered.
    test-A2-a-context-label-answers-at-followEdge = {
      expr = S.followEdge F.contextLabel F.labelled "s";
      expected = [ "r" ];
    };
    test-A2-a-context-label-answers-at-collectByLabel = {
      expr = S.collectByLabel F.contextLabel F.ids F.labelled "s";
      expected = [ "r" ];
    };
    test-A2-a-context-label-answers-at-collectionAttr-label = {
      expr = S.collectionAttr { } "label:${F.contextLabel}" F.ids F.labelled "s";
      expected = [ "r" ];
    };
    test-A2c-the-plain-label-answers = {
      expr = S.followEdge "include" F.labelled "s";
      expected = [ "r" ];
    };

    # A3: a store-context node id answers through each walk, and the id it answers keeps its context.
    test-A3-a-context-id-answers-through-every-walk =
      let
        inherit (F.contextId) ev ctx;
        v = n: n.decls.v or null;
        ancestors = S.collectionAttr { } "ancestors" F.ids ev "leaf";
        neron = S.collectionAttr { } "neron" F.ids ev "leaf";
      in
      {
        expr = {
          all = S.inheritAll { } v ev "leaf";
          set = S.inheritSet { } v ev "leaf";
          inherit ancestors neron;
          ancestorsContext = map has ancestors;
          neronContext = map has neron;
        };
        expected = {
          all = [
            7
            1
          ];
          set = [
            7
            1
          ];
          ancestors = [
            ctx
            "root"
          ];
          neron = [
            "leaf"
            ctx
            "root"
          ];
          ancestorsContext = [
            true
            false
          ];
          neronContext = [
            false
            true
            false
          ];
        };
      };

    # A4a: `s` imports its own parent `p`. `neron.wf` (`parent* imports?`) still reaches `g` by
    # `parent parent`; a scope seen as an import target is still walked as a chain member.
    test-A4a-neron-reaches-past-a-self-imported-parent = {
      expr = S.collectionAttr { } "neron" F.ex F.selfImport "s";
      expected = [
        "vp"
        "vg"
      ];
    };
    # A4b: the diamond. `x` is reached by `imports` and by `parent imports`; it answers once, at its
    # `<p`-least path, so the order is self → imports → parent with no repeat.
    test-A4b-neron-gathers-each-scope-once-in-visibility-order = {
      expr = S.collectionAttr { } "neron" F.ex F.diamond "s";
      expected = [
        "vs"
        "vx"
        "vp"
      ];
    };
  };
}
