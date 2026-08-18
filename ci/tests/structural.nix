# The structural partition: one syntactic predicate, total over every attribute name.
#
# The cells below pin both halves of its STATED DOMAIN. What it decides: the two child
# attributes, the whole reserved `edges-` namespace including members whose labels are built
# during evaluation, and the consumer-level `includes` boundary mark. What it does NOT decide:
# whether an attribute is structural in MEANING. A consumer that invents a structurally
# meaningful attribute under a name outside the namespace is classified resolutional, and the
# residual cell below records that as a measured fact rather than leaving it to be discovered.
{ genScope, ... }:
{
  flake.tests."structural" = {
    test-children-is-structural = {
      expr = genScope.structural "children";
      expected = true;
    };
    test-derived-children-is-structural = {
      expr = genScope.structural "derived-children";
      expected = true;
    };
    test-includes-is-structural = {
      expr = genScope.structural "includes";
      expected = true;
    };
    # THE IMPORT RELATION. The resolver reaches the import edges of Neron et al. (2015) by NAME
    # (`self.get id imports`), and the classifier reserves that same name through the one
    # traversal binding both modules read — so this cell reads a JOIN rather than a name written
    # down twice. A resolutional import relation is servable from a prior evaluation, which is a
    # stale reachability relation answered without a symptom.
    test-the-import-relation-is-structural = {
      expr = genScope.structural "imports";
      expected = true;
    };
    # The cell above beside controls in the same instrument and the same run. A reading of `true`
    # is worth nothing next to a predicate that cannot answer `false`, so the last name is a token
    # no attribute set carries.
    test-the-import-relation-reading-carries-its-controls = {
      expr = map genScope.structural [
        "imports"
        "children"
        "includes"
        "edges-M"
        "wjbq3nx7205"
      ];
      expected = [
        true
        true
        true
        true
        false
      ];
    };
    # The consequence the partition exists to produce: the import relation is absent from the
    # reuse vocabulary, so there is nothing for a decision naming it to intersect with.
    test-the-import-relation-is-absent-from-the-reuse-vocabulary = {
      expr = genScope.resolutionalNames [
        "imports"
        "label"
        "children"
        "value"
      ];
      expected = [
        "label"
        "value"
      ];
    };
    # The open family: no enumeration could hold these, which is why the predicate is
    # syntactic. The last name is built the way `followEdge` builds one.
    test-edge-namespace-is-structural = {
      expr = map genScope.structural [
        "edges-owns"
        "edges-R"
        "edges-"
        "edges-${builtins.head [ "dyn" ]}"
      ];
      expected = [
        true
        true
        true
        true
      ];
    };
    # THE STATED RESIDUAL, as a cell. A structurally meaningful attribute under a name outside
    # the reserved namespace classifies resolutional and may be reused. The substrate cannot
    # detect semantic structurality; the parity oracle is what catches this class.
    test-structural-meaning-outside-the-namespace-is-not-detected = {
      expr = map genScope.structural [
        "myEdges"
        "enriched-context"
        "parent"
      ];
      expected = [
        false
        false
        false
      ];
    };
    # Total over any string, including ones no attribute set would carry.
    test-predicate-is-total = {
      expr = map genScope.structural [
        ""
        "edge"
        "edges"
        "CHILDREN"
      ];
      expected = [
        false
        false
        false
        false
      ];
    };
    test-resolutional-names-is-the-complement = {
      expr = genScope.resolutionalNames [
        "children"
        "label"
        "edges-owns"
        "includes"
        "derived-children"
        "value"
      ];
      expected = [
        "label"
        "value"
      ];
    };
    test-reserved-prefix = {
      expr = genScope.edgePrefix;
      expected = "edges-";
    };
  };
}
