# The evaluator↔plane interface, armed.
#
# THE MATRIX. Each structural-name row asserts THREE things about a decision that names a
# structural attribute: the value is byte-identical to a cold evaluation; the attribute was
# RECOMPUTED rather than served (the prior answers a distinguishable value, so a serve would
# show); and the debug validator FIRED on the out-of-vocabulary name. The last row is a
# decision naming a RESOLUTIONAL attribute and is the LIVE CONTROL — it is served, and the
# validator does not fire. Without it every row above would also pass against an evaluator
# that reuses nothing at all.
{ lib, genScope, ... }:
let
  mkNode = id: parent: decls: {
    inherit id parent decls;
    type = "t";
  };

  roots = {
    a = mkNode "a" null {
      owns = [ "b" ];
      includes = [ "b" ];
      labels = [ "owns" ];
    };
    b = mkNode "b" null {
      owns = [ ];
      includes = [ ];
      labels = [ "owns" ];
    };
  };

  # Every family of the partition, plus two resolutional attributes.
  attrs = {
    children = self: id: { };
    derived-children = self: id: { };
    "edges-owns" = self: id: (self.node id).decls.owns or [ ];
    includes = self: id: (self.node id).decls.includes or [ ];
    label = self: id: "fresh-${id}";
    owned = genScope.collectByLabel "owns" (self: id: [ id ]);
  };

  # The same program answered with values a cold run never produces, so a serve is visible.
  priorAttrs = attrs // {
    children =
      self: id:
      if id == "a" then
        {
          POISON = mkNode "POISON" "a" { };
        }
      else
        { };
    derived-children =
      self: id:
      if id == "a" then
        {
          POISON-D = mkNode "POISON-D" "a" { };
        }
      else
        { };
    "edges-owns" = self: id: [ "POISON" ];
    includes = self: id: [ "POISON" ];
    label = self: id: "cached-${id}";
  };

  cold = genScope.eval {
    inherit roots;
    attributes = attrs;
  };
  prior = genScope.eval {
    inherit roots;
    attributes = priorAttrs;
  };

  # A graph that actually materializes a child, for the facade-residual cells: `children` is
  # what hands a raw node record back through `get`.
  childCold = genScope.eval {
    roots.p = mkNode "p" null { };
    attributes = {
      children =
        self: id:
        if id == "p" then
          {
            kid = mkNode "kid" "p" { secret = "reachable"; };
          }
        else
          { };
      label = self: id: "fresh-${id}";
    };
    parseParent = id: if id == "kid" then "p" else null;
  };

  # One warm evaluation per row, everything clean, reusing exactly the named attributes.
  row =
    names:
    genScope.evalWarm {
      inherit roots prior;
      attributes = attrs;
      decision = genScope.mkDecision {
        isClean = _: true;
        reusable = _: names;
      };
    };

  # A decision whose attribute NAME is constructed during evaluation, from graph data — the
  # shape `followEdge` and `collectionAttr`'s `label:` traversal issue. No enumeration could
  # have anticipated it.
  dynamicRow = genScope.evalWarm {
    inherit roots prior;
    attributes = attrs;
    decision = genScope.mkDecision {
      isClean = _: true;
      reusable = nodeId: [ "edges-${builtins.head (cold.node nodeId).decls.labels}" ];
    };
  };

  # value · recomputed-and-identical-to-cold · validator fired
  cell = w: attrName: {
    value = w.get "a" attrName;
    coldValue = cold.get "a" attrName;
    fired = builtins.any (f: f.attrName == attrName) w.decisionFindings;
  };
in
{
  flake.tests."plane-structural-matrix" = {
    test-children-recomputed = {
      expr = cell (row [ "children" ]) "children";
      expected = {
        value = { };
        coldValue = { };
        fired = true;
      };
    };
    test-derived-children-recomputed = {
      expr = cell (row [ "derived-children" ]) "derived-children";
      expected = {
        value = { };
        coldValue = { };
        fired = true;
      };
    };
    test-edge-label-recomputed = {
      expr = cell (row [ "edges-owns" ]) "edges-owns";
      expected = {
        value = [ "b" ];
        coldValue = [ "b" ];
        fired = true;
      };
    };
    # The edge-label name built at evaluation time, not written into the decision as a literal.
    test-dynamic-edge-label-recomputed = {
      expr = cell dynamicRow "edges-owns";
      expected = {
        value = [ "b" ];
        coldValue = [ "b" ];
        fired = true;
      };
    };
    test-includes-recomputed = {
      expr = cell (row [ "includes" ]) "includes";
      expected = {
        value = [ "b" ];
        coldValue = [ "b" ];
        fired = true;
      };
    };
    # THE LIVE CONTROL: a resolutional attribute IS served, and the validator stays silent.
    test-resolutional-attribute-is-served = {
      expr = cell (row [ "label" ]) "label";
      expected = {
        value = "cached-a";
        coldValue = "fresh-a";
        fired = false;
      };
    };
    # A structural name reaches the always-recompute branch even when the plane is reusing a
    # resolutional attribute in the same decision — the branches are independent.
    test-mixed-decision-serves-only-the-resolutional-half = {
      expr =
        let
          w = row [
            "label"
            "edges-owns"
          ];
        in
        [
          (w.get "a" "label")
          (w.get "a" "edges-owns")
        ];
      expected = [
        "cached-a"
        [ "b" ]
      ];
    };
    # A combinator that reads an edge label through `get` sees the recomputed relation.
    test-edge-reading-combinator-sees-recomputed-edges = {
      expr = (row [ "edges-owns" ]).get "a" "owned";
      expected = cold.get "a" "owned";
    };
  };

  flake.tests."plane-facade" = {
    # The closed enumeration, asserted by name, so a widening fails a cell rather than passing
    # silently. There is no `node`, no `allNodes`, no combinator: a read outside these three
    # names is not refused at run time — it is absent from the record.
    test-facade-carries-exactly-three-names = {
      expr = builtins.attrNames cold.facade;
      expected = [
        "get"
        "nodeIds"
        "resolutional"
      ];
    };
    test-library-facade-constructor-agrees = {
      expr = genScope.facadeNames;
      expected = builtins.attrNames cold.facade;
    };
    test-facade-has-no-node-accessor = {
      expr = map (n: cold.facade ? ${n}) [
        "node"
        "allNodes"
        "allNodeIds"
        "structuralEdges"
        "facade"
      ];
      expected = [
        false
        false
        false
        false
        false
      ];
    };

    # ════ THE RESIDUAL, AS MEASURED FACT ════
    #
    # The three cells above close the facade's KEY SET. They say nothing about what is
    # reachable through the values `get` returns, and the two cells below record what is —
    # asserting the channels EXIST rather than asserting they do not. A containment claim these
    # refute would be worse than no claim at all, because the next reader would trust it.

    # 1. A child-bearing attribute hands back NODE RECORDS. Each carries `decls` / `parent` and
    #    the co-located `_eval` cache, so a caller holding one evaluates through `_eval` without
    #    passing through `get` at all — a complete parallel channel — and reads the raw
    #    declarations straight off the record.
    test-child-records-reached-through-get-carry-a-parallel-channel = {
      expr =
        let
          kid = (childCold.facade.get "p" "children").kid;
        in
        {
          keys = builtins.attrNames kid;
          viaParallelChannel = kid._eval.label;
          viaGet = childCold.facade.get "kid" "label";
          rawDecls = kid.decls.secret;
          rawParent = kid.parent;
        };
      expected = {
        keys = [
          "_eval"
          "decls"
          "id"
          "parent"
          "type"
        ];
        viaParallelChannel = "fresh-kid";
        viaGet = "fresh-kid";
        rawDecls = "reachable";
        rawParent = "p";
      };
    };

    # 2. `get` accepts ANY string. Withholding the combinators withholds the combinators; it
    #    does not stop a caller building the name itself, so a dynamically constructed
    #    attribute name is issuable through the facade.
    test-dynamically-constructed-name-is-issuable-through-the-facade = {
      expr = cold.facade.get "a" (genScope.edgePrefix + "owns");
      expected = [ "b" ];
    };

    # What survives the residual: the property reuse rests on is the evaluator's branch order,
    # not this record's key set, so reaching through a returned value does not weaken it.
    test-residual-does-not-reach-the-reuse-property = {
      expr =
        let
          w = row [ "edges-owns" ];
        in
        [
          (w.get "a" "edges-owns")
          (w.facade.get "a" "edges-owns")
        ];
      expected = [
        [ "b" ]
        [ "b" ]
      ];
    };
    test-facade-nodeIds-is-the-node-set = {
      expr = cold.facade.nodeIds;
      expected = cold.allNodeIds;
    };
    # The vocabulary the reuse intersection is taken against: this attribute set minus the
    # structural partition.
    test-facade-resolutional-vocabulary = {
      expr = cold.facade.resolutional "a";
      expected = [
        "label"
        "owned"
      ];
    };
    # Asked for a structural attribute the facade answers with a RECOMPUTED value. The prior
    # here is itself a warm evaluation whose decision named `edges-owns`, so a served answer
    # would carry the poison forward; it carries the recomputation instead.
    test-facade-structural-read-recomputes = {
      expr =
        let
          warmPrior = row [ "edges-owns" ];
        in
        warmPrior.facade.get "a" "edges-owns";
      expected = [ "b" ];
    };
    test-facade-resolutional-read-answers = {
      expr = cold.facade.get "a" "label";
      expected = "fresh-a";
    };
  };

  flake.tests."plane-exposures" = {
    # The structural edge set the substrate constructed, readable without forcing any
    # resolutional attribute — pinned by making every resolutional attribute throw.
    test-structural-edges-force-no-resolutional-attribute = {
      expr =
        let
          e = genScope.eval {
            inherit roots;
            attributes = attrs // {
              label = self: id: throw "resolutional attribute forced";
              owned = self: id: throw "resolutional attribute forced";
            };
          };
          s = e.structuralEdges "a";
        in
        {
          names = builtins.attrNames s;
          owns = s."edges-owns";
          includes = s.includes;
        };
      expected = {
        names = [
          "children"
          "derived-children"
          "edges-owns"
          "includes"
        ];
        owns = [ "b" ];
        includes = [ "b" ];
      };
    };
    test-served-is-the-intersection = {
      expr =
        (row [
          "label"
          "children"
          "edges-owns"
          "nonexistent"
        ]).served
          "a";
      expected = [ "label" ];
    };
    test-cold-decision-serves-nothing = {
      expr = cold.served "a";
      expected = [ ];
    };
    test-cold-decision-finds-nothing = {
      expr = cold.decisionFindings;
      expected = [ ];
    };
    # A decision naming an attribute that is not in the set at all is a finding too.
    test-unknown-name-is-a-finding = {
      expr = map (f: f.attrName) (row [ "nonexistent" ]).decisionFindings;
      expected = [
        "nonexistent"
        "nonexistent"
      ];
    };
  };

  flake.tests."plane-decision" = {
    test-cold-decision-is-total = {
      expr = [
        (genScope.coldDecision.isClean "anything")
        (genScope.coldDecision.reusable "anything")
      ];
      expected = [
        false
        [ ]
      ];
    };
    test-decision-carries-exactly-two-fields = {
      expr = builtins.attrNames (
        genScope.mkDecision {
          isClean = _: false;
          reusable = _: [ ];
        }
      );
      expected = [
        "isClean"
        "reusable"
      ];
    };
    # A Decision cannot carry values: the constructor's argument set is CLOSED, so a field
    # holding results is refused by name at construction rather than accepted silently. The
    # cell reads the argument set itself — `false` here means "no default", i.e. required — so
    # both the closure and the totality are pinned, and a widening reddens this cell.
    #
    # The refusal is an ARITY error, which `tryEval` does not catch: it cannot be caught and
    # worked around, only fixed. That is why this cell states the closure positively.
    test-decision-argument-set-is-closed-and-required = {
      expr = builtins.functionArgs genScope.mkDecision;
      expected = {
        isClean = false;
        reusable = false;
      };
    };
    test-facade-argument-set-is-closed-and-required = {
      expr = builtins.functionArgs genScope.mkFacade;
      expected = {
        get = false;
        nodeIds = false;
        resolutional = false;
      };
    };
    # A decision that reuses without a prior to read from is a NAMED refusal, not an
    # unattributed error.
    test-reuse-without-a-prior-refuses-by-name = {
      expr =
        let
          r = builtins.tryEval (
            (genScope.eval {
              inherit roots;
              attributes = attrs;
              decision = genScope.mkDecision {
                isClean = _: true;
                reusable = _: [ "label" ];
              };
            }).get
              "a"
              "label"
          );
        in
        r.success;
      expected = false;
    };
  };

  flake.tests."plane-provenance" = {
    # The field rides the RESULT. Always present, so its absence is never how a caller learns
    # there is nothing to report.
    test-provenance-is-present-and-empty-by-default = {
      expr = cold.provenance;
      expected = [ ];
    };
    test-provenance-is-carried-to-the-caller = {
      expr =
        (genScope.eval {
          inherit roots;
          attributes = attrs;
          provenance = [
            {
              fact = "input-past-verified-bound";
              observed = 41;
              bound = 32;
            }
          ];
        }).provenance;
      expected = [
        {
          fact = "input-past-verified-bound";
          observed = 41;
          bound = 32;
        }
      ];
    };
    test-provenance-survives-the-warm-entry-point = {
      expr =
        (genScope.evalWarm {
          inherit roots prior;
          attributes = attrs;
          decision = genScope.coldDecision;
          provenance = [ { fact = "carried"; } ];
        }).provenance;
      expected = [ { fact = "carried"; } ];
    };
  };

  flake.tests."plane-cold-parity" = {
    # With the decision saying nothing is clean, the evaluator answers exactly what it answers
    # with no decision at all — across every attribute of every node.
    test-cold-decision-matches-plain-eval = {
      expr =
        let
          w = genScope.evalWarm {
            inherit roots prior;
            attributes = attrs;
            decision = genScope.coldDecision;
          };
          names = builtins.attrNames attrs;
          shot = e: lib.genAttrs e.allNodeIds (id: lib.genAttrs names (n: e.get id n));
        in
        shot w == shot cold;
      expected = true;
    };
    test-node-set-is-unchanged = {
      expr = (row [ "label" ]).allNodeIds;
      expected = cold.allNodeIds;
    };
  };
}
