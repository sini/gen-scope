# `structuralEdges` — the structural partition read as a RELATION, at the real substrate.
#
# The projection's own mechanism is armed in gen-graph, against injected predicates. What THESE
# cells hold is what that suite cannot see: that the two facts the constructor takes are wired to
# the substrate's OWN, and that the resulting relation has the properties the substrate makes
# possible — a spawned node reached, a membership authority larger than the registration set, and a
# check whose domain excludes the descent channels even though they are in the record it reads.
#
# THE SPAWN CHANNEL IS WHAT MAKES THESE CELLS DISCRIMINATING. `a-spawned` is NOT in `scope.nodes`
# and IS in `allNodeIds`, so a projection reading the registration set would refuse it and a
# projection reading `children` alone would never see it. Both are held below, in both directions.
{ lib, genScope, ... }:
let
  mkNode = id: parent: decls: {
    inherit id parent decls;
    type = "t";
  };

  roots = {
    a = mkNode "a" null {
      owns = [ "b" ];
      imports = [ "c" ];
    };
    b = mkNode "b" null { };
    c = mkNode "c" null { };
  };

  # The spawn declares what it produces, so `derived-children` arrives through the kind rather than
  # as an attribute. `a-spawned` exists only after the walk — which is the whole point.
  spawnOne =
    _self: id:
    if id == "a" then
      {
        a-spawned = {
          id = "a-spawned";
          parent = "a";
          decls = { };
        };
      }
    else
      { };

  kinds = genScope.mkKinds [
    (genScope.mkKind { name = "d"; })
    (genScope.mkKind {
      name = "t";
      below = [ "d" ];
      spawns.d = spawnOne;
    })
  ];

  scope = {
    nodes = roots;
    nodeOrder = builtins.attrNames roots;
    inherit kinds;
  };

  # Every family of the partition, plus two resolutional attributes so the strictness cell has
  # something to poison. `children` SELECTS among registered nodes; it cannot mint one.
  attrs = {
    children = _self: id: if id == "a" then { inherit (roots) b; } else { };
    "edges-owns" = self: id: (self.node id).decls.owns or [ ];
    imports = self: id: (self.node id).decls.imports or [ ];
    includes = _self: _id: [ ];
    label = _self: id: "fresh-${id}";
    owned = genScope.collectByLabel "owns" (_self: id: [ id ]);
  };

  evalWith =
    extra:
    genScope.eval {
      inherit scope;
      attributes = attrs // extra;
    };

  ev = evalWith { };

  didThrow = v: !(builtins.tryEval (builtins.deepSeq v true)).success;
  sorted = builtins.sort builtins.lessThan;

  # A family-2 equation seeded with each violation mode, and with each admitting control.
  seeded = value: evalWith { "edges-owns" = _self: _id: value; };

  # Both resolutional attributes poisoned. The projection reads the structural partition, so it
  # never reaches these; the control below shows they really throw when read.
  poisonedResolutional = evalWith {
    label = _self: _id: throw "gen-scope: resolutional attribute forced";
    owned = _self: _id: throw "gen-scope: resolutional attribute forced";
  };

  # A descent channel broken on `c`, which has NO relation to `a`. Forcing the node set walks it.
  brokenDescent = "gen-scope: the unrelated node's descent is broken";
  poisonedElsewhere = evalWith {
    children = _self: id: if id == "c" then throw brokenDescent else { };
  };
  # The same shape with the poison removed, so the refusal above is attributable to the poison.
  noChildrenAnywhere = evalWith { children = _self: _id: { }; };
in
{
  flake.tests.structural-edges = {

    # ── THE RELATION, OVER BOTH FAMILIES OF ONE REAL GRAPH ──
    # `b` arrives through `children` AND through `edges-owns`; it appears ONCE, because a relational
    # projection is set-valued. `c` arrives through `imports` alone and survives, which is what
    # makes the cell a duplicate test rather than a length test.
    test-structural-edges-covers-both-families = {
      expr = sorted (ev.structuralEdges "a");
      expected = [
        "a-spawned"
        "b"
        "c"
      ];
    };
    test-control-a-leaf-projects-empty = {
      expr = ev.structuralEdges "b";
      expected = [ ];
    };

    # ── THE SPAWNED NODE IS REACHED ──
    # The projection enumerates the partition rather than naming a member of it.
    test-spawned-node-is-reached = {
      expr = builtins.elem "a-spawned" (ev.structuralEdges "a");
      expected = true;
    };
    # The seed, and it is live code elsewhere in this library: reading `children` alone. It is the
    # same host, the same evaluation, and it cannot see the spawned node.
    test-seed-children-alone-cannot-see-the-spawned-node = {
      expr = builtins.attrNames (ev.structuralAttributes "a").children;
      expected = [ "b" ];
    };
    # ★ THE DISCRIMINATING FACT the two cells above rest on: `a-spawned` is outside the registration
    # set and inside the evaluated one. Without this, both cells could pass on a graph where the
    # two sets coincide and nothing would have been measured.
    test-control-the-spawned-node-is-outside-the-registration-set = {
      expr = {
        registered = builtins.elem "a-spawned" (builtins.attrNames roots);
        evaluated = builtins.elem "a-spawned" ev.allNodeIds;
      };
      expected = {
        registered = false;
        evaluated = true;
      };
    };

    # ── THE CHECK'S DOMAIN EXCLUDES THE DESCENT CHANNELS ──
    # ★ THE ANCHOR, IN TWO HALVES. `children` and `derived-children` ARE in the record the check
    # reads, and their values are ATTRSETS — so an ungated check would report both as "got set,
    # expected a list of node ids". The clean node reports NOTHING. Together these say the gate
    # fired, and they say it about `derived-children`, the member a check gated on the literal name
    # `children` would still govern.
    test-control-both-descent-channels-are-in-the-record = {
      expr = builtins.attrNames (ev.structuralAttributes "a");
      expected = [
        "children"
        "derived-children"
        "edges-owns"
        "imports"
        "includes"
      ];
    };
    test-control-both-descent-channel-values-are-attrsets = {
      expr = map (n: builtins.isAttrs (ev.structuralAttributes "a").${n}) [
        "children"
        "derived-children"
      ];
      expected = [
        true
        true
      ];
    };
    test-findings-are-empty-on-a-clean-node = {
      expr = ev.projectionFindings "a";
      expected = [ ];
    };

    # ── THE CODOMAIN IS REFUSED WHEN VIOLATED, AND THE ASSERTION IS ON THE RETURNED MESSAGE ──
    test-non-list-is-refused = {
      expr = didThrow ((seeded "not-a-list").structuralEdges "a");
      expected = true;
    };
    test-non-list-message-names-node-family-and-type = {
      expr = (seeded "not-a-list").projectionFindings "a";
      expected = [
        "gen-graph.mkEndpointProjection: node 'a' structural attribute 'edges-owns': got string, expected a list of node ids"
      ];
    };
    test-junk-element-is-refused = {
      expr = didThrow (
        (seeded [
          42
          { nope = 1; }
        ]).structuralEdges
          "a"
      );
      expected = true;
    };
    # Neither message interpolates its offender — naming a non-string is the coercion abort that
    # would make this very cell unable to fire.
    test-junk-element-messages-name-position-and-type = {
      expr =
        (seeded [
          42
          { nope = 1; }
        ]).projectionFindings
          "a";
      expected = [
        "gen-graph.mkEndpointProjection: node 'a' structural attribute 'edges-owns' element 0: got int, expected a node id"
        "gen-graph.mkEndpointProjection: node 'a' structural attribute 'edges-owns' element 1: got set, expected a node id"
      ];
    };
    test-phantom-id-is-refused = {
      expr = didThrow ((seeded [ "ghost" ]).structuralEdges "a");
      expected = true;
    };
    test-phantom-message-names-the-offending-id = {
      expr = (seeded [ "ghost" ]).projectionFindings "a";
      expected = [
        "gen-graph.mkEndpointProjection: node 'a' structural attribute 'edges-owns': 'ghost' is not a node of the evaluated graph"
      ];
    };

    # ★ THE CONTROL THAT MATTERS MOST HERE, because it is the one only the real substrate can pose:
    # the authority is the EVALUATED set, so a family-2 equation naming a SPAWNED node is admitted.
    # A projection wired to the registration set would refuse every product of the spawn channel,
    # and its refusal would be indistinguishable from a correct one without this cell.
    test-control-a-spawned-id-is-admitted-as-an-endpoint = {
      expr = sorted ((seeded [ "a-spawned" ]).structuralEdges "a");
      expected = [
        "a-spawned"
        "b"
        "c"
      ];
    };
    # ★ AND AN EMPTY LIST IS ADMITTED — without it the cells above pass a check that refuses every
    # list, which is a refuse-everything guard wearing a contract's name.
    test-control-an-empty-family-2-attribute-is-admitted = {
      expr = sorted ((seeded [ ]).structuralEdges "a");
      expected = [
        "a-spawned"
        "b"
        "c"
      ];
    };
    test-control-an-empty-family-2-attribute-has-no-findings = {
      expr = (seeded [ ]).projectionFindings "a";
      expected = [ ];
    };
    test-control-a-well-formed-family-2-attribute-is-admitted = {
      expr = sorted ((seeded [ "b" ]).structuralEdges "a");
      expected = [
        "a-spawned"
        "b"
        "c"
      ];
    };

    # ── STRICTNESS: NO RESOLUTIONAL ATTRIBUTE IS FORCED ──
    test-projection-forces-no-resolutional-attribute = {
      expr = sorted (poisonedResolutional.structuralEdges "a");
      expected = [
        "a-spawned"
        "b"
        "c"
      ];
    };
    # The poison really throws when read directly — without this the cell passes against a poison
    # that never fired.
    test-control-the-poisoned-resolutional-attribute-really-throws = {
      expr = didThrow (poisonedResolutional.get "a" "label");
      expected = true;
    };

    # ── FAIL-CLOSED: THE ANSWER IS A GLOBAL CLAIM, SO A BROKEN AUTHORITY REFUSES ──
    # Membership is a statement about the whole graph, so the projection forces the node set and one
    # poisoned descent channel ANYWHERE aborts every projection read. That is the ruled design's
    # behaviour and the right direction of failure: a projection that answered while the authority
    # it checks against was broken would assert a membership it could not verify.
    test-an-unrelated-broken-descent-channel-refuses-the-projection = {
      expr = didThrow (poisonedElsewhere.structuralEdges "a");
      expected = true;
    };
    # The poison is real …
    test-control-the-unrelated-poison-really-throws = {
      expr = didThrow (poisonedElsewhere.structuralAttributes "c");
      expected = true;
    };
    # … and the same shape WITHOUT the poison answers, so the refusal above is the poison and not a
    # projection that refuses everything.
    test-control-the-same-shape-without-the-poison-answers = {
      expr = sorted (noChildrenAnywhere.structuralEdges "a");
      expected = [
        "a-spawned"
        "b"
        "c"
      ];
    };
  };
}
