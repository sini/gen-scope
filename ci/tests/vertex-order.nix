# THE DECLARED VERTEX ORDER — the acceptance surface for the constructor's order and its input type.
#
# Every fixture here declares its vertices REVERSE-ALPHABETICALLY, so the declared order and the
# codepoint order differ on every arm. A fixture whose declaration happens to agree with codepoint
# cannot fail, and the one place that agreement is the POINT carries its own control below.
{
  lib,
  genScope,
  genPreludeLib,
  genGraph,
  ...
}:
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

  # ── O10's fixture: two roots synthesizing the SAME id through one shared spawn ──
  # `attributes."derived-children"` cannot be hand-written — `effectiveAttributes` refuses it
  # unconditionally (`hoag.nix`'s `test-a-hand-written-spawn-attribute-is-refused`) — so the
  # ambiguity is built the only legal way: a kind's `spawns` producing the same id `shared` no
  # matter which of its two instances fires it, with `decls.origin` recording which one did.
  # `shared` is registered nowhere in `scope.nodes`, so resolving it falls through to
  # `genericResolve` — the site §2.5 excludes from the constructor's declared-order guarantee.
  # Declared reverse-alphabetically ("z" before "a"), like every fixture in this file.
  o10Kinds = genScope.mkKinds [
    (genScope.mkKind { name = "leaf"; })
    (genScope.mkKind {
      name = "root";
      below = [ "leaf" ];
      spawns.leaf = _handle: id: {
        shared = {
          id = "shared";
          decls = {
            origin = id;
          };
        };
      };
    })
  ];
  o10Roots = genScope.buildRoots {
    parentGraph = genScope.vertices [
      "z"
      "a"
    ];
    importGraph = genScope.empty;
    kinds = o10Kinds;
    decls = {
      z = { };
      a = { };
    };
    types = {
      z = "root";
      a = "root";
    };
  };
  o10Attrs = {
    children = _self: _id: { };
  };
  o10Build =
    evalFn: extra:
    evalFn (
      {
        scope = o10Roots;
        attributes = o10Attrs;
      }
      // extra
    );

  # A genuinely patched COPY of `eval.nix`, built the way the round-1 gate built its
  # (`reports/den-hoag-u1sf-gate-v1.md`, C-5): the source is read, its four sibling imports are
  # pointed at a store copy of `lib/` so the patched file resolves outside `lib/`, an optional
  # `rootOrder` formal is threaded through, and it is consumed at EXACTLY ONE site —
  # genericResolve's fold over `attrNames roots` — never at `allNodesWhere`, which §2.5 excludes
  # on different (and, per the gate, overstated) grounds and which this fixture must not seed.
  #
  # ★ THE SIBLING IMPORTS CARRY STRING CONTEXT. Interpolating the path (`"${libDir}"`) copies
  # `lib/` into the store and names the copy WITH context, so the `toFile` below records the copy
  # as a reference and pure evaluation may read it. `builtins.toString libDir` names the flake
  # source's own `lib/` WITHOUT context: `toFile` then warns that its file "references the store
  # path … without a proper context", and under an evaluator that keeps the flake source as a lazy
  # tree that path is never materialised, so importing the patched file dies `access to absolute
  # path … is forbidden in pure evaluation mode` — a death only the hosted check sees, since a Nix
  # that has already copied the source to the store reads the bare path anyway. The WHOLE directory
  # is copied rather than the four files, because two of them import siblings of their own
  # (`structural.nix` → `traversal-names.nix`, `interface.nix` → `structural.nix`) that resolve
  # only beside them. A derivation writing the patched file beside real siblings would need no
  # rewrite, but `flake.tests` is system-agnostic — there is no `pkgs` in this module to build one
  # — so the rewrite stays and targets the context-carrying copy.
  #
  # Occurrence counts use `replaceStrings`-length-diffing rather than `builtins.split`: `split`'s
  # pattern is a POSIX ERE, and both anchors below contain regex metacharacters (`?`, `(`, `)`), so
  # a split-based count would silently count something other than the literal text.
  o10CountOccurrences =
    needle: haystack:
    (
      builtins.stringLength haystack
      - builtins.stringLength (builtins.replaceStrings [ needle ] [ "" ] haystack)
    )
    / builtins.stringLength needle;
  o10EvalSrc = builtins.readFile (libDir + "/eval.nix");
  o10Abs = name: "${libDir}/${name}";
  o10WithAbsoluteImports =
    builtins.replaceStrings
      [
        "import ./structural.nix"
        "import ./interface.nix"
        "import ./callable.nix"
        "import ./least-model.nix"
      ]
      [
        "import ${o10Abs "structural.nix"}"
        "import ${o10Abs "interface.nix"}"
        "import ${o10Abs "callable.nix"}"
        "import ${o10Abs "least-model.nix"}"
      ]
      o10EvalSrc;
  o10FormalAnchor = "declaredDependencies ? null,\n    }:";
  o10ThreadedFormal =
    builtins.replaceStrings
      [ o10FormalAnchor ]
      [ "declaredDependencies ? null,\n      rootOrder ? null,\n    }:" ]
      o10WithAbsoluteImports;
  o10FoldSite = "found = prelude.foldl' (acc: rootId: if acc != null then acc else walkChildren rootId) null (\n                  builtins.attrNames roots\n                );";
  o10FoldSiteThreaded = "found = prelude.foldl' (acc: rootId: if acc != null then acc else walkChildren rootId) null (\n                  if rootOrder != null then rootOrder else builtins.attrNames roots\n                );";
  o10AnchorCounts = {
    formalAnchor = o10CountOccurrences o10FormalAnchor o10WithAbsoluteImports;
    foldAnchor = o10CountOccurrences o10FoldSite o10EvalSrc;
  };
  o10PatchedText = builtins.replaceStrings [ o10FoldSite ] [ o10FoldSiteThreaded ] o10ThreadedFormal;
  o10PatchedFile = builtins.toFile "eval-o10-patched.nix" o10PatchedText;
  o10RequireScope =
    (import (libDir + "/require-scope.nix") { prelude = genPreludeLib; }).requireScope;
  o10RequireDeclaredDependencies =
    (import (libDir + "/require-declared-dependencies.nix") { graph = genGraph; })
    .requireDeclaredDependencies;
  o10PatchedEval =
    (import o10PatchedFile {
      prelude = genPreludeLib;
      requireScope = o10RequireScope;
      requireDeclaredDependencies = o10RequireDeclaredDependencies;
      graph = genGraph;
    }).eval;
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

    # ── O10 — a node id producible by TWO roots' derived-children resolves to the SAME node ──
    # §2.5 excludes `genericResolve`'s fold over `attrNames roots` from the declared-order
    # guarantee: the id it picks between two ambiguous producers is an ANSWER, not an ORDER, so
    # `first-match wins` is not itself a claim about vertex order and needs no seeding at
    # `nodeOrder`. What follows measures that exclusion on a genuinely patched evaluator, not a
    # simulation of one.

    # The provenance check: both source-text patches must land at exactly one site each. A patch
    # that silently missed its anchor (0 occurrences) or hit an unintended second one (>1) would
    # make every cell below pass or fail for the wrong reason.
    test-O10-the-two-source-patches-anchor-to-exactly-one-site-each = {
      expr = o10AnchorCounts;
      expected = {
        formalAnchor = 1;
        foldAnchor = 1;
      };
    };

    # CONTROL: the patch alone, at its default (unthreaded) `rootOrder`, changes nothing — its
    # answer for the ambiguous id and its full materialization both match the real, unpatched
    # `genScope.eval` exactly. Without this arm, a moved answer under threading (below) would be
    # equally consistent with an edit that broke something else.
    test-O10-patch-is-inert-at-default = {
      expr = {
        node = (o10Build o10PatchedEval { }).node "shared";
        allNodeIds = (o10Build o10PatchedEval { }).allNodeIds;
      };
      expected = {
        node = (o10Build genScope.eval { }).node "shared";
        allNodeIds = (o10Build genScope.eval { }).allNodeIds;
      };
    };

    # The default answer is governed by CODEPOINT order of `attrNames roots` ("a" before "z"), not
    # by the fixture's declared (reverse-alphabetical) order, which puts "z" first. Field-projected
    # rather than a whole-record comparison: `.node` also carries the `_eval` memoization cache
    # (`eval.nix`'s co-located `_eval`), which is not this exclusion's concern.
    test-O10-default-selects-the-codepoint-first-root = {
      expr =
        let
          n = (o10Build o10PatchedEval { }).node "shared";
        in
        {
          inherit (n) id type parent;
          origin = n.decls.origin;
        };
      expected = {
        id = "shared";
        type = "leaf";
        parent = "a";
        origin = "a";
      };
    };

    # SEEDED DEFECT: threading `rootOrder` into genericResolve's fold — the one thing §2.5 says
    # must not happen — moves the selected root from "a" to "z". This is what makes the exclusion
    # falsifiable: an implementation that let a caller-supplied order override the fold would fail
    # this cell where the real library, unthreaded, does not.
    test-O10-seeded-threading-moves-the-selected-root = {
      expr =
        let
          n =
            (o10Build o10PatchedEval {
              rootOrder = [
                "z"
                "a"
              ];
            }).node
              "shared";
        in
        {
          inherit (n) id type parent;
          origin = n.decls.origin;
        };
      expected = {
        id = "shared";
        type = "leaf";
        parent = "z";
        origin = "z";
      };
    };

    # AND THE MATERIALIZATION WALK DOES NOT MOVE under the same seed: `allNodeIds` is byte-identical
    # between the default and threaded arms, which is what makes genericResolve's pick an ANSWER
    # rather than an ORDER — the property `:270` (`allNodesWhere`) rides as a consequence rather
    # than carrying independently, per the round-1 gate's C-5 finding. `:270` itself is not seeded
    # here: its own enumeration is inert to this threading, and seeding it would test nothing.
    test-O10-allNodeIds-is-unmoved-by-the-same-seed = {
      expr =
        (o10Build o10PatchedEval {
          rootOrder = [
            "z"
            "a"
          ];
        }).allNodeIds;
      expected = (o10Build o10PatchedEval { }).allNodeIds;
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
