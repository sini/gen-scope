# PRODUCER-BOUNDED DELEGATION — a reader handed out as a value (den-hoag-9pt45, ruled arm (a)).
#
# The routes and their bound, cold, read off `_fixtures/reader-delegation.nix`. The warm half (gen-memo's
# real warm fold: the target edited, warm = a fresh cold fold) is gen-memo's, in its
# `warm-reader-delegation` cells, because the plane that decides is gen-memo's. The refusal texts,
# which name whose relation the guard consulted, are pinned in `../tests-error.nix`
# (`reader-delegation-refusals`).
{
  genScope,
  genGraph,
  genPreludeLib,
  ...
}:
let
  d = import ./_fixtures/reader-delegation.nix { inherit genScope genGraph; };
  R = "REFUSED";
  prelude = genPreludeLib;
in
{
  flake.tests.reader-delegation = {
    # POSITIVE: a consumer declaring only the producer reads the producer's declared target
    test-positive-direct-reader-reads-the-producers-target = {
      expr = d.cold.cDirect;
      expected = {
        node = 1;
        get = 1;
      };
    };
    # FORWARDING: the consumer declares neither the producer nor kid
    test-forwarded-one-hop-reads-the-producers-target = {
      expr = d.cold.cFwd;
      expected = {
        node = 1;
        get = 1;
      };
    };
    test-forwarded-two-hops-reads-the-producers-target = {
      expr = d.cold.cFwd2;
      expected.get = 1;
    };
    test-forwarding-consumers-declare-neither-producer-nor-target = {
      # read off the fold's own relation, not the fixture's literal
      expr = prelude.genAttrs [ "cFwd" "cFwd2" ] (d.fold d.live { }).accessor.dependencies;
      expected = {
        cFwd = [ "relay" ];
        cFwd2 = [ "relay2" ];
      };
    };
    test-reader-in-a-child-record-and-a-list-reads-the-producers-target = {
      expr = d.cold.cRec;
      expected = {
        inner = 1;
        list = 1;
      };
    };
    test-returned-closure-reads-the-producers-target = {
      expr = d.cold.cFn;
      expected.call = 1;
    };
    # REFUSAL: the consumer's own undeclared read stays refused
    test-own-undeclared-read-is-refused = {
      expr = d.cold.cOwn;
      expected = {
        node = R;
        get = R;
      };
    };
    # THE BOUND: the handed reader reaches only its producer's relation; gk exists (the control)
    test-a-target-the-producer-did-not-declare-is-refused = {
      expr = d.cold.cBeyond;
      expected = {
        node = R;
        get = R;
      };
    };
    test-control-the-bound-target-exists-and-answers-its-own-declarer = {
      expr = d.cold.cGkOwn;
      expected.get = 5;
    };
    # the empty relation refuses every read of every route, the cold answers' shape kept
    test-the-empty-relation-refuses-every-route = {
      expr = d.empty;
      expected = builtins.mapAttrs (_: builtins.mapAttrs (_: _: R)) d.cold;
    };
  };
}
