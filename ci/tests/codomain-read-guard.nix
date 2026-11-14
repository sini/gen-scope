# THE READ SEAM'S COVERAGE GUARD — R§2.4, O4.
#
# A body may not demand another node's attribute across an edge its node did not declare. The
# record seam (`self.node`) is `codomain-seam-guard`'s; this cell governs the two demand forms
# beside it, `self.get` and `self.getRepresentative`, on every path a body enters the evaluator by:
# the ordinary application and both circular ascents. The guard consults the DECLARED relation and
# never the structural one, so a child reading its parent across a structural edge nobody declared
# is refused too.
#
# The refusals are `tryEval` facts; their content is the validator's, which returns the reason
# rather than throwing it, and the text each seam raises is pinned in `../tests-error.nix`
# (`codomain-read-guard-refusals`). Live controls: the declared arms answer, a self-read answers
# under the empty relation, and an evaluator reached with no relation at all is outside the contract.
#
# The warm entry is armed the same way: `evalWarm` takes the relation as `eval` does, and a node the
# decision does not call clean is recomputed through the guarded reader.
{ genScope, genGraph, ... }:
let
  inherit (genScope)
    buildRoots
    circular
    eval
    foldEquations
    seamAcquisitionDefect
    ;

  # `a` and `b` are siblings under `root`, so an edge between them is one only a declaration supplies.
  scope = buildRoots {
    parentGraph = genScope.overlays [
      (genScope.edge {
        from = "a";
        to = "root";
      })
      (genScope.edge {
        from = "b";
        to = "root";
      })
    ];
    decls = {
      root.v = 0;
      a.v = 1;
      b.v = 2;
    };
    types = { };
  };
  peerOf = id: if id == "a" then "b" else "a";
  contracted = import ./_fixtures/declared.nix { inherit genGraph scope; };
  peerRelation = contracted {
    root = [ "a" ];
    a = [ "b" ];
    b = [ "a" ];
  };
  emptyRelation = contracted { };
  childOfRoot = contracted { a = [ "root" ]; };

  carrierWith = quotient: {
    bottom = 0;
    leq = x: y: x <= y;
    height = 2;
    inherit quotient;
  };

  attributes = {
    children =
      _self: id:
      builtins.listToAttrs (
        map (cid: {
          name = cid;
          value = scope.nodes.${cid};
        }) (builtins.filter (cid: scope.nodes.${cid}.parent == id) (builtins.attrNames scope.nodes))
      );
    imports = _self: _id: [ ];
    own-v = self: id: (self.node id).decls.v;
    # THE SEED: a cross-node attribute demand
    peer-get = self: id: self.get (peerOf id) "own-v";
    # THE STRUCTURAL SEED: a child reads its parent's attribute across the containment edge
    parent-get = self: id: self.get "root" "own-v";
    # THE CLEAN PATH: a node demands its own attribute
    self-get = self: id: self.get id "own-v";
    # a quotient own-value, and a body demanding a PEER's representative of it
    own-rep = circular { carrier = carrierWith true; } (
      self: id: _prev:
      (self.node id).decls.v
    );
    peer-rep = self: id: (self.getRepresentative (peerOf id) "own-rep").representative;
  };
  kindOf =
    name:
    if name == "children" then
      "nta"
    else if name == "own-rep" || name == "peer-reach" then
      "circular"
    else
      "synthesized";
  foldWith =
    declaredDependencies: attrs:
    foldEquations { } {
      inherit scope declaredDependencies;
      schedule.equations = builtins.mapAttrs (name: compute: {
        inherit name compute;
        kind = kindOf name;
        readsAttrs = [ ];
        stratum = if name == "children" then "structural" else "resolution";
      }) attrs;
      parseParent = id: scope.nodes.${id}.parent or null;
    };
  emptyCtx = foldWith emptyRelation attributes;
  # Nothing is clean, so every node is recomputed through the reader the relation arms.
  warmWith =
    declaredDependencies:
    genScope.evalWarm { inherit declaredDependencies; } {
      inherit scope attributes;
      prior = eval { } attributes scope;
      decision = genScope.mkDecision {
        isClean = _: false;
        reusable = _: [ ];
      };
    };
  declaredCtx = foldWith peerRelation attributes;
  refused = v: !(builtins.tryEval (builtins.deepSeq v v)).success;

  # the step reads its peer's attribute outright, so it converges in one step when admitted and the
  # only throw left to it is the guard's
  circularFold =
    quotient: rel:
    foldWith rel (
      attributes
      // {
        peer-reach = circular { carrier = carrierWith quotient; } (
          self: id: _prev:
          self.get (peerOf id) "own-v"
        );
      }
    );
in
{
  flake.tests."codomain-read-guard" = {
    test-O4-undeclared-cross-node-get-is-refused = {
      expr = refused (emptyCtx.eval.get "a" "peer-get");
      expected = true;
    };
    test-O4-undeclared-cross-node-getRepresentative-is-refused = {
      expr = refused (emptyCtx.eval.get "a" "peer-rep");
      expected = true;
    };
    test-O4-a-structural-edge-is-no-licence-to-read = {
      expr = refused (emptyCtx.eval.get "a" "parent-get");
      expected = true;
    };
    test-O4-the-guard-reaches-a-shared-rounds-step = {
      expr = refused ((circularFold false emptyRelation).eval.get "a" "peer-reach");
      expected = true;
    };
    test-O4-the-guard-reaches-a-nested-ascents-step = {
      expr = refused ((circularFold true emptyRelation).eval.getRepresentative "a" "peer-reach");
      expected = true;
    };
    test-O4-evalWarm-armed-refuses-an-undeclared-get-on-a-recomputed-node = {
      expr = refused ((warmWith emptyRelation).get "a" "peer-get");
      expected = true;
    };
    test-O4-the-refusal-names-reader-attribute-target-and-relation = {
      expr = seamAcquisitionDefect {
        reader = "a";
        target = "b";
        attrName = "own-v";
        through = "self.get";
        declared = [ ];
      };
      expected = "gen-scope: node 'a' read attribute 'own-v' of node 'b' through `self.get`, and 'b' is not in the dependency relation 'a' declared: []. A body may not read across an edge its node did not declare — the relation a grammar gate runs over is contracted at every firing, so an undeclared read would make the declaration false while the evaluation still answered. Declare 'b' among 'a's dependencies; a traversal that ranges over the graph declares the range it ranges over.";
    };

    # ── CONTROLS ──
    test-control-a-declared-get-answers = {
      expr = declaredCtx.eval.get "a" "peer-get";
      expected = 2;
    };
    test-control-a-declared-getRepresentative-answers = {
      expr = declaredCtx.eval.get "a" "peer-rep";
      expected = 2;
    };
    test-control-a-declared-structural-read-answers = {
      expr = (foldWith childOfRoot attributes).eval.get "a" "parent-get";
      expected = 0;
    };
    test-control-a-declared-get-converges-in-a-shared-round = {
      expr = (circularFold false peerRelation).eval.get "a" "peer-reach";
      expected = 2;
    };
    test-control-a-declared-get-converges-in-a-nested-ascent = {
      expr = ((circularFold true peerRelation).eval.getRepresentative "a" "peer-reach").representative;
      expected = 2;
    };
    test-control-evalWarm-armed-answers-a-declared-get = {
      expr = (warmWith peerRelation).get "a" "peer-get";
      expected = 2;
    };
    test-control-a-self-get-is-not-refused = {
      expr = emptyCtx.eval.get "a" "self-get";
      expected = 1;
    };
    test-control-an-unarmed-evaluator-still-answers-the-get = {
      expr = (eval { } attributes scope).get "a" "peer-get";
      expected = 2;
    };

    # ── THE GUARD AND ITS VALIDATORS AGREE ──
    # The guard spells the coverage condition on the hot path; the validators spell it as a value.
    # Over the self, declared and undeclared cases, each validator is null exactly where its seam
    # admits, so the two spellings cannot drift apart unseen in their NULL-NESS. The text a seam
    # raises is a separate fact, pinned in `../tests-error.nix`.
    test-the-validators-are-null-exactly-where-the-seams-admit = {
      expr =
        map
          (c: {
            node =
              seamAcquisitionDefect {
                inherit (c) reader target declared;
              } == null;
            get =
              seamAcquisitionDefect {
                inherit (c) reader target declared;
                attrName = "own-v";
                through = "self.get";
              } == null;
            admitted =
              !(refused (
                (foldWith (contracted { ${c.reader} = c.declared; }) attributes).eval.get c.reader (
                  if c.reader == c.target then "self-get" else "peer-get"
                )
              ));
          })
          [
            {
              reader = "a";
              target = "a";
              declared = [ ];
            }
            {
              reader = "a";
              target = "b";
              declared = [ "b" ];
            }
            {
              reader = "a";
              target = "b";
              declared = [ ];
            }
          ];
      expected = [
        {
          node = true;
          get = true;
          admitted = true;
        }
        {
          node = true;
          get = true;
          admitted = true;
        }
        {
          node = false;
          get = false;
          admitted = false;
        }
      ];
    };
  };
}
