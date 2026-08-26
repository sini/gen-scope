# THE SPAWNED-VISIBILITY WITNESS — one declared child and TWO spawned children, shared between
# the query-surface suite (`tests/spawned-visibility.nix`) and the debug refusal cell in
# `tests-error.nix`, so the graph a refusal is earned on and the graph the clean path answers
# over are one value.
#
# The shape is the whole point. `children` selects among registered nodes and every registered
# node answers from the root evaluation, so a node reachable ONLY by descending a structural
# attribute is necessarily a spawned one — the DELTA between the declared read and the composed
# read is exactly the spawn set. The declared child (`husk`) is what makes `siblings` answerable
# at all; the SECOND spawned child (`groat`) is what lets a spawned node's `siblings` change:
# a spawned node already sees its declared siblings today (it reads the PARENT's children, and
# the parent is declared), so with one spawned child that cell could not fail.
#
# Every spawn record writes `parent`, as a PRECONDITION: the substrate stamps a spawned child's
# `type` and nothing else, `siblings` reads `.parent` off the record, and the missing-field
# failure is an `attribute missing` abort `tryEval` does not catch.
{ lib, genScope }:
let
  spawnKinds = genScope.mkKinds [
    (genScope.mkKind { name = "chaff"; })
    (genScope.mkKind {
      name = "quern";
      below = [ "chaff" ];
      spawns.chaff = _self: id: {
        winnow = {
          id = "winnow";
          parent = id;
          decls = { };
        };
        groat = {
          id = "groat";
          parent = id;
          decls = { };
        };
      };
    })
  ];

  nodes = {
    millstone = {
      id = "millstone";
      type = "quern";
      parent = null;
      decls = { };
    };
    husk = {
      id = "husk";
      type = "chaff";
      parent = "millstone";
      decls = { };
    };
  };

  roots = {
    inherit nodes;
    nodeOrder = [
      "millstone"
      "husk"
    ];
    kinds = spawnKinds;
  };

  attributes = {
    children = _self: id: lib.filterAttrs (_: n: n.parent == id) nodes;
    imports = _self: _id: [ ];
    # The two resolver traversals under test, declared on the fixture so the cells read them as
    # ordinary attributes. The siblings gather is asserted on the DECLARED child: on a spawned
    # host the traversal inherits the sibling asymmetry and gathers something pre-fix too.
    gather-children = genScope.collectionAttr {
      traverse = "children";
      extract = _self: id: [ id ];
    };
    gather-siblings = genScope.collectionAttr {
      traverse = "siblings";
      extract = _self: id: [ id ];
    };
  };

  # Both spawned ids resolve through the parent: the spawn builder keys them under `millstone`.
  parseParent = id: (nodes.${id} or { parent = "millstone"; }).parent;
in
{
  # Cold production evaluation — the visibility question needs no decision, no prior.
  result = genScope.eval {
    scope = roots;
    inherit attributes;
  };

  # The debug pair varies exactly one thing, the `parseParent` formal: the composed read forces a
  # node acquisition at the spawned id, which the debug evaluator can only satisfy through it.
  debugWithParse = genScope.evalDebug {
    scope = roots;
    inherit attributes parseParent;
  };
  debugNoParse = genScope.evalDebug {
    scope = roots;
    inherit attributes;
  };
}
