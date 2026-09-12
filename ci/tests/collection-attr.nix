{ lib, genScope, ... }:
let
  inherit (genScope) collectionAttr collectImports;

  # Tree: root → {a, b}; a imports b
  roots = genScope.buildRoots {
    parentGraph = genScope.overlays [
      (genScope.edge "a" "root")
      (genScope.edge "b" "root")
    ];
    importGraph = genScope.edge "a" "b";
    decls = {
      root = {
        tags = [ "root-tag" ];
      };
      a = {
        tags = [ "a-tag" ];
      };
      b = {
        tags = [ "b-tag" ];
      };
    };
    types = { };
  };

  result = genScope.eval {
    scope = roots;
    attributes = {
      children = self: id: lib.filterAttrs (_: n: n.parent == id) roots.nodes;
      imports = self: id: (self.node id).decls.__edges.I or [ ];

      tags = self: id: (self.node id).decls.tags or [ ];

      # Collect tags from imports
      import-tags = collectionAttr {
        traverse = "imports";
        extract = self: id: (self.node id).decls.tags or [ ];
      };

      # Collect tags from children
      child-tags = collectionAttr {
        traverse = "children";
        extract = self: id: (self.node id).decls.tags or [ ];
      };

      # Collect tags from siblings
      sibling-tags = collectionAttr {
        traverse = "siblings";
        extract = self: id: (self.node id).decls.tags or [ ];
      };

      # Collect from ancestors
      ancestor-tags = collectionAttr {
        traverse = "ancestors";
        extract = self: id: (self.node id).decls.tags or [ ];
      };

      # Filtered collection
      filtered-child-tags = collectionAttr {
        traverse = "children";
        extract = self: id: (self.node id).decls.tags or [ ];
        filter = node: node.id != "b";
      };

      # A SUPPLIED `combine`, which nothing in the suite reached before. The default is the sentinel
      # `null` — the ordered-list discipline taken in one pass — so this is the arm that says the
      # fold is still there for a caller who asks for it. `bracket` is non-associative on purpose:
      # it pins the LEFT association `combine (combine [ ] t0) t1`, which is what `foldl'` gives and
      # what a right fold would not.
      bracketed-child-tags = collectionAttr {
        traverse = "children";
        extract = self: id: (self.node id).decls.tags or [ ];
        combine = a: b: [ "<" ] ++ a ++ b ++ [ ">" ];
      };

      # collectImports convenience
      import-tags-simple = collectImports (self: id: (self.node id).decls.tags or [ ]);
    };
    parseParent = id: (roots.nodes.${id} or { parent = null; }).parent;
  };
in
{
  flake.tests."collection-attr" = {
    test-traverse-imports = {
      expr = result.get "a" "import-tags";
      expected = [ "b-tag" ];
    };

    test-traverse-children = {
      expr = builtins.sort builtins.lessThan (result.get "root" "child-tags");
      expected = [
        "a-tag"
        "b-tag"
      ];
    };

    # The supplied-`combine` arm, and the association is the assertion. `foldl'` over `[ ]` gives
    # `combine (combine [ ] a-tag) b-tag`; the value was derived by running it, not read off the
    # source. Nothing in the suite reached this arm before the default became the `null` sentinel.
    test-traverse-children-supplied-combine-folds-left = {
      expr = result.get "root" "bracketed-child-tags";
      expected = [
        "<"
        "<"
        "a-tag"
        ">"
        "b-tag"
        ">"
      ];
    };

    test-traverse-siblings = {
      expr = result.get "a" "sibling-tags";
      expected = [ "b-tag" ];
    };

    test-traverse-siblings-symmetric = {
      expr = result.get "b" "sibling-tags";
      expected = [ "a-tag" ];
    };

    test-traverse-ancestors = {
      expr = result.get "a" "ancestor-tags";
      expected = [ "root-tag" ];
    };

    test-traverse-ancestors-root-empty = {
      expr = result.get "root" "ancestor-tags";
      expected = [ ];
    };

    test-filtered-collection = {
      expr = result.get "root" "filtered-child-tags";
      expected = [ "a-tag" ];
    };

    test-collectImports-convenience = {
      expr = result.get "a" "import-tags-simple";
      expected = [ "b-tag" ];
    };

    test-no-imports-empty = {
      expr = result.get "b" "import-tags";
      expected = [ ];
    };

    test-traverse-children-leaf = {
      expr = result.get "a" "child-tags";
      expected = [ ];
    };
  };
}
