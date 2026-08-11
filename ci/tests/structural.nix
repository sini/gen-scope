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
