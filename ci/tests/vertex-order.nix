# THE DECLARED VERTEX ORDER — the acceptance surface for the constructor's order and its input type.
#
# Every fixture here declares its vertices REVERSE-ALPHABETICALLY, so the declared order and the
# codepoint order differ on every arm. A fixture whose declaration happens to agree with codepoint
# cannot fail, and the one place that agreement is the POINT carries its own control below.
{ lib, genScope, ... }:
let
  # A FLAT kind vocabulary: names, and no order between them, so no kind expands into another.
  # These fixtures declare types and never spawn, which is exactly what an empty `below` says.
  flatKinds = names: genScope.mkKinds (map (name: genScope.mkKind { inherit name; }) names);

  # Declared z, y, b, a — against a codepoint a, b, root, y, z.
  declared = [
    "z"
    "y"
    "b"
    "a"
  ];
  pg = genScope.overlays (map (v: genScope.edge v "root") declared);

  # Two labelled dimensions, each declaring its vertices reverse-alphabetically.
  gM = genScope.edge "n" "m";
  gN = genScope.edge "d" "c";
  contribution = label: graph: { inherit label graph; };

  ordered = genScope.buildRoots {
    parentGraph = pg;
    edgeGraphs = [
      (contribution "M" gM)
      (contribution "N" gN)
    ];
  };
  renamed = genScope.buildRoots {
    parentGraph = pg;
    edgeGraphs = [
      (contribution "Z" gM)
      (contribution "A" gN)
    ];
  };
  reordered = genScope.buildRoots {
    parentGraph = pg;
    edgeGraphs = [
      (contribution "N" gN)
      (contribution "M" gM)
    ];
  };

  # The evaluator fixtures: two importers of one target, declared order ≠ codepoint.
  importers = genScope.overlays [
    (genScope.edge "z" "t")
    (genScope.edge "m" "t")
  ];
  agreeing = genScope.overlays [
    (genScope.edge "m" "t")
    (genScope.edge "z" "t")
  ];
  attrs = {
    children = _self: _id: { };
    imports = self: id: (self.node id).decls.__edges.I or [ ];
    needed-by = genScope.queryReverse { dataFilter = node: node.id; };
  };
  walkOf =
    scope:
    (genScope.eval {
      inherit scope;
      attributes = attrs;
    }).allNodeIds;
  answerOf =
    scope:
    (genScope.eval {
      inherit scope;
      attributes = attrs;
    }).get
      "t"
      "needed-by";

  # O15's subject: the library's own source, read the way `purity` reads it, so the closure is
  # asserted over the tree rather than over a list someone maintains.
  libDir = ../../lib;
  libFiles = lib.filter (n: lib.hasSuffix ".nix" n) (lib.attrNames (builtins.readDir libDir));
  rootsFormals = lib.filter (
    n:
    lib.any (l: (lib.match "^ *roots,$" l) != null) (
      lib.splitString "\n" (builtins.readFile (libDir + "/${n}"))
    )
  ) libFiles;
  scopeFormals = lib.filter (
    n:
    lib.any (l: (lib.match "^ *scope,$" l) != null) (
      lib.splitString "\n" (builtins.readFile (libDir + "/${n}"))
    )
  ) libFiles;
in
{
  flake.tests.vertex-order = {
    # ── O1 — the order is the DECLARED sequence, not the residue of a collapse ──
    # The seeded defect is the collapse this construction exists to stop doing: `attrNames` over the
    # node map, which is what the codepoint arm below spells out.
    test-O1-nodeOrder-is-the-declared-sequence = {
      expr = (genScope.buildRoots { parentGraph = pg; }).nodeOrder;
      expected = [
        "z"
        "root"
        "y"
        "b"
        "a"
      ];
    };
    test-O1-seed-the-collapse-and-the-order-becomes-codepoint = {
      expr = builtins.attrNames (genScope.buildRoots { parentGraph = pg; }).nodes;
      expected = [
        "a"
        "b"
        "root"
        "y"
        "z"
      ];
    };

    # ── O2 — invariant under LABEL SPELLING ──
    # Necessary and not sufficient: it also passes on the collapse, because the collapse sorts by
    # vertex name. O3 is its other half and neither may ship alone.
    test-O2-order-is-invariant-under-label-spelling = {
      expr = ordered.nodeOrder == renamed.nodeOrder;
      expected = true;
    };

    # ── O3 — the order FOLLOWS the contribution list ──
    # This is what a sort-by-id implementation fails and O2 alone would certify.
    test-O3-order-follows-the-contribution-list = {
      expr = {
        asDeclared = ordered.nodeOrder;
        reordered = reordered.nodeOrder;
      };
      expected = {
        asDeclared = [
          "z"
          "root"
          "y"
          "b"
          "a"
          "n"
          "m"
          "d"
          "c"
        ];
        reordered = [
          "z"
          "root"
          "y"
          "b"
          "a"
          "d"
          "c"
          "n"
          "m"
        ];
      };
    };

    # ── O4a — node VALUES, not merely the id set ──
    # An `attrNames`-only check passes on an index that drops `I`, because the id set is identical.
    test-O4a-node-values-carry-the-import-label = {
      expr =
        let
          r = genScope.buildRoots {
            parentGraph = genScope.edge "a" "root";
            importGraph = genScope.edge "a" "lib1";
            edgeGraphs = [ (contribution "M" (genScope.edge "a" "m1")) ];
          };
        in
        {
          labels = builtins.attrNames r.nodes.a.decls.__edges;
          importTargets = r.nodes.a.decls.__edges.I;
          parent = r.nodes.a.parent;
        };
      expected = {
        labels = [
          "I"
          "M"
        ];
        importTargets = [ "lib1" ];
        parent = "root";
      };
    };

    # ── O4b — the EMPTY-importGraph arm, which O4a's fixture cannot see ──
    # Including `I` unconditionally would emit `__edges.I = [ ]` on every node of every import-free
    # graph: a node-value divergence under an identical id set.
    test-O4b-an-empty-import-graph-contributes-no-label = {
      expr =
        builtins.attrNames
          (genScope.buildRoots {
            parentGraph = genScope.edge "a" "root";
            importGraph = genScope.empty;
            edgeGraphs = [ (contribution "M" (genScope.edge "a" "m1")) ];
          }).nodes.a.decls.__edges;
      expected = [ "M" ];
    };

    # ── O8 — the walk enters at the declared order ──
    test-O8-the-walk-enters-at-nodeOrder = {
      expr = walkOf (genScope.buildRoots { parentGraph = pg; });
      expected = [
        "z"
        "root"
        "y"
        "b"
        "a"
      ];
    };
    # Seeded: a hand-built scope stating the codepoint order gets the codepoint walk, which is what
    # the constructor used to hand over unconditionally.
    test-O8-seed-a-codepoint-order-and-the-walk-follows-it = {
      expr =
        let
          built = genScope.buildRoots { parentGraph = pg; };
        in
        walkOf {
          inherit (built) nodes;
          nodeOrder = builtins.attrNames built.nodes;
        };
      expected = [
        "a"
        "b"
        "root"
        "y"
        "z"
      ];
    };

    # ── O9 — the codepoint TAIL, and the three properties it has ──
    # `decls` and `types` are attrset formals, so a vertex known only from their keys has no
    # declared position: it lands after the graph segments, decls before types, each ascending —
    # and a vertex named in BOTH a graph and `decls` keeps its GRAPH position.
    test-O9-the-tail-follows-the-graph-segments = {
      expr =
        (genScope.buildRoots {
          parentGraph = pg;
          decls = {
            d2 = { };
            d1 = { };
            a = { };
          };
          kinds = flatKinds [ "x" ];
          types = {
            t2 = "x";
            t1 = "x";
          };
        }).nodeOrder;
      expected = [
        "z"
        "root"
        "y"
        "b"
        "a"
        "d1"
        "d2"
        "t1"
        "t2"
      ];
    };

    # ── O11 — queryReverse's ANSWER ORDER, the contract this remedy changes ──
    # `queryReverse` enumerates `allNodeIds`, so the declared order reaches a published answer.
    test-O11-the-answer-follows-the-declared-order = {
      expr = answerOf (genScope.buildRoots { importGraph = importers; });
      expected = [
        "z"
        "m"
      ];
    };
    # CONTROL, same suite: a declaration that AGREES with codepoint must not move the answer. This
    # is the arm that could have failed and is why the arm above is evidence of the declaration
    # rather than of an unconditional reordering.
    test-O11-control-a-declaration-agreeing-with-codepoint-does-not-move-it = {
      expr = answerOf (genScope.buildRoots { importGraph = agreeing; });
      expected = [
        "m"
        "z"
      ];
    };

    # ── O13 — the rename-only migration is REFUSED, not silently served ──
    # Renaming the call is the minimal edit that clears the tombstone; with the input type it is
    # still refused, because `roots` is not a formal of any entry. ★ That refusal is a MISSING
    # ARGUMENT, which is not a `throw` and which `tryEval` therefore cannot observe — the cell
    # asserting it is `vertex-order-refusals` in the message suite. What lives here is its control.
    test-O13-control-the-correct-migration-evaluates = {
      expr =
        (builtins.tryEval (builtins.deepSeq (walkOf (genScope.buildRoots { parentGraph = pg; })) 1))
        .success;
      expected = true;
    };

    # ── O15 — THE CLASS CLOSURE, asserted over the library tree ──
    # The membership command is `roots,` as a formal across `lib/`. After the change it must return
    # EMPTY, with the sibling-formal control still firing — a list of four names would rot; this
    # does not.
    test-O15-no-entry-takes-a-bare-roots-formal = {
      expr = rootsFormals;
      expected = [ ];
    };
    # POSITIVE CONTROL, same read, same run: the instrument finds a formal that IS there. Without
    # it the cell above is satisfied by a broken predicate exactly as by a clean closure.
    test-O15-control-the-formal-predicate-fires = {
      expr = scopeFormals;
      expected = [
        "eval.nix"
        "fold-equations.nix"
      ];
    };
  };
}
