# Purity invariant (gen-prelude design §5): gen-scope depends only on gen-prelude and
# must import NO `nixpkgs.lib`. This pins "pure" as a checked property, not an
# aspiration — a stray `lib.foo` / `lib.types` / `evalModules` / nixpkgs input creeping
# back into the library source fails CI.
#
# Scope: every `.nix` file under lib/, at any depth, plus the root flake.nix and default.nix
# (the library + its flake). NOT ci/ — the test harness legitimately uses nixpkgs.lib
# (including, here, to do this scan). The walk descends, so a file added under a new lib/
# subdirectory is in scope by construction; a flat listing would let it leave the invariant
# silently, which is the failure this scope is written to exclude rather than to survive.
#
# Labels are repo-root-relative paths, never bare basenames. `lib/default.nix` and the root
# `default.nix` are both in scope, and a bare basename names them with the same string — so a
# violation in one is indistinguishable from a violation in the other, and a red CI names a
# file the reader cannot open. The walk therefore carries a prefix down from the root it was
# handed, and every label it emits is a path relative to the repository root.
#
# AN EMPTINESS IS NOT EVIDENCE. Three mechanisms stand between this library and a silent
# nixpkgs tether — the walk that finds the files, the read that strips their comments, and the
# token scan that judges them — and every one of them reports "clean" when it is dead. Each is
# therefore held to a cell whose expectation is a literal:
#
#   * The SUBJECT is asserted along both of its axes, membership and content, because a scan can
#     be severed from the tree either way. MEMBERSHIP — which files the scan reads — is the label
#     list itself, not its size: disconnection is an identity defect and a non-emptiness guard is
#     a cardinality predicate, so the two do not meet, and a scan that has dropped the whole
#     library tree and kept only the two root entries is non-empty, has non-empty content, and
#     reports the invariant clean over a set containing none of the library. Asserting the list
#     also makes a new library file arrive as a red rather than being absorbed silently, which
#     is the point — the scope of an invariant is a declared surface, not a default.
#   * CONTENT is the axis the manifest is silent on, and it is severable on its own: a read that
#     returned some fixed text for every library file would satisfy the membership list exactly
#     while carrying none of the library's source, and a live tether sitting on disk would go
#     unseen through every other cell here. So the reads are held to a token the library really
#     contains, at the exact labels where it really occurs.
#   * The DETECTOR is exercised over the real subject with one known-bad entry appended, so the
#     cell that proves it fires and the cell that proves the tree is clean are one measurement
#     over one source list rather than two unrelated ones. A detector proven only against a
#     synthetic list says nothing about the pipeline that reads disk.
#   * The WALK's recursion runs against a fixture tree that is nested on purpose, because lib/
#     is flat and a walk that quietly stopped descending would keep every other cell green.
{ genPrelude, lib, ... }:
let
  libDir = ../../lib;

  # Comment-stripped source: drop everything from the first `#` on each line. Safe here
  # because `#` appears only in comments across these files (no `#` in string literals);
  # documentation may freely mention forbidden tokens without tripping the invariant.
  stripComments =
    text:
    lib.concatStringsSep "\n" (
      map (line: lib.head (lib.splitString "#" line)) (lib.splitString "\n" text)
    );

  # walk : string -> path -> [ { name; path; } ], `name` being `prefix` extended by the
  # entry's position in the tree — so a violation is reported at a repo-root-relative path a
  # reader can act on, rather than at the store path the sources happen to be evaluated from.
  walk =
    prefix: dir:
    lib.concatLists (
      lib.mapAttrsToList (
        entry: type:
        if type == "directory" then
          walk "${prefix}${entry}/" (dir + "/${entry}")
        else if lib.hasSuffix ".nix" entry then
          [
            {
              name = "${prefix}${entry}";
              path = dir + "/${entry}";
            }
          ]
        else
          [ ]
      ) (builtins.readDir dir)
    );

  read =
    entries:
    map (e: {
      inherit (e) name;
      code = stripComments (builtins.readFile e.path);
    }) entries;

  sources = read (walk "lib/" libDir) ++ [
    {
      name = "flake.nix";
      code = stripComments (builtins.readFile ../../flake.nix);
    }
    {
      name = "default.nix";
      code = stripComments (builtins.readFile ../../default.nix);
    }
  ];

  # Tokens that signal a nixpkgs-lib tether or the module-system (Korora-class) tier.
  forbidden = [
    "nixpkgs" # a nixpkgs flake input / reference
    "lib." # any nixpkgs lib call (lib.types, lib.genAttrs, …)
    "{ lib }" # the old `{ lib }` parameter signature
    "{ lib," # `{ lib, … }` parameter signature
    "evalModules" # module-system tier
    "mkOption" # module-system tier
  ];

  # The live counterpart to `forbidden`: the name this library reaches for where a tether would
  # reach for nixpkgs. Every gen-scope source but one carries it — `lib/graph.nix` is the
  # algebraic graph core (Mokhov, 2017), written in builtins alone and depending on nothing, so
  # it names no prelude. That single exclusion is what gives the assertion its teeth: the
  # expected list is a PROPER subset of the manifest, so a read returning one fixed text for
  # every file lands outside it either way — without the token the list collapses toward empty,
  # with it the list swells to every source.
  liveToken = "prelude";
  liveReads = map (src: src.name) (lib.filter (src: genPrelude.hasInfix liveToken src.code) sources);

  # scan : [ { name; code; } ] -> [ "file: 'tok'" ]
  scan =
    srcs:
    lib.concatMap (
      src:
      map (tok: "${src.name}: '${tok}'") (lib.filter (tok: genPrelude.hasInfix tok src.code) forbidden)
    ) srcs;
in
{
  flake.tests.purity.test-library-source-is-nixpkgs-lib-free = {
    expr = scan sources;
    expected = [ ];
  };

  # What the cell above is a statement ABOUT. Its `[ ]` is produced just as readily by a scan
  # that reads the wrong tree, or no tree, as by a library that is clean, and neither the
  # detector cells below nor a guard on the source list's size can tell those apart — the first
  # never touch `sources`, and the second answers a question about how many rather than which.
  # The library tree is small and its membership is a deliberate surface, so it is written down.
  flake.tests.purity.test-scan-subject-is-the-library-tree = {
    expr = map (s: s.name) sources;
    expected = [
      "lib/acceptance.nix"
      "lib/build-nodes.nix"
      "lib/cascade.nix"
      "lib/default.nix"
      "lib/engine.nix"
      "lib/eval.nix"
      "lib/fold-equations.nix"
      "lib/folds.nix"
      "lib/graph.nix"
      "lib/interface.nix"
      "lib/least-model.nix"
      "lib/merge-surface.nix"
      "lib/mint.nix"
      "lib/program.nix"
      "lib/queries.nix"
      "lib/resolve.nix"
      "lib/stratify.nix"
      "lib/structural.nix"
      "lib/well-founded.nix"
      "flake.nix"
      "default.nix"
    ];
  };

  # And that those labels carry their files' text. The manifest above pins membership and is
  # silent on content: a `read` that handed every library entry one fixed string would satisfy it
  # exactly, and a live `lib.types.str` sitting in a real library file would pass through all of
  # the other cells here at exit 0. This is the same shape as the manifest — an exact list, not a
  # count — asked of a token that is genuinely present rather than genuinely absent, so the reads
  # are shown to carry this repository's source and not a constant.
  flake.tests.purity.test-scan-reads-are-live = {
    expr = liveReads;
    expected = [
      "lib/acceptance.nix"
      "lib/build-nodes.nix"
      "lib/cascade.nix"
      "lib/default.nix"
      "lib/engine.nix"
      "lib/eval.nix"
      "lib/fold-equations.nix"
      "lib/folds.nix"
      "lib/interface.nix"
      "lib/least-model.nix"
      "lib/merge-surface.nix"
      "lib/mint.nix"
      "lib/program.nix"
      "lib/queries.nix"
      "lib/resolve.nix"
      "lib/stratify.nix"
      "lib/structural.nix"
      "lib/well-founded.nix"
      "flake.nix"
      "default.nix"
    ];
  };

  # The detector has teeth, and it grows them on the real subject: the scan runs over exactly
  # the source list the cell above asserts, with one synthetic entry appended. So the firing is
  # proven by the same call that reports the tree clean, and the expectation states both halves
  # at once — the library contributes nothing and the planted tether contributes precisely this.
  #
  # The expectation is the violation LIST, not merely that one was produced: a detector that
  # fires on the wrong token, or whose `file: 'tok'` message has decayed into something a reader
  # cannot act on, is broken in the way that matters and a bare non-emptiness check would pass
  # it. The synthetic entry is never written to disk, and its label is bracketed so it cannot be
  # read as one of the repo-root-relative paths it now sits beside.
  flake.tests.purity.test-detector-catches-injected-violation = {
    expr = scan (
      sources
      ++ [
        {
          name = "<injected>";
          code = stripComments "  foo = lib.types.str; # comment mentioning nixpkgs is stripped";
        }
      ]
    );
    expected = [ "<injected>: 'lib.'" ];
  };

  # And it does not "catch" a token that only appears inside a comment. This is the other half
  # of the same instrument, and it is asked in isolation because what it discriminates is
  # comment from code: the strip is load-bearing on real source — the root flake.nix and
  # default.nix both discuss nixpkgs in prose, as do two library modules — so a strip that
  # silently stopped running would red the library cell for reasons that are not tethers.
  flake.tests.purity.test-comments-are-stripped = {
    expr = scan [
      {
        name = "<comment-only>";
        code = stripComments "  x = 1; # this line mentions mkOption and nixpkgs but is a comment";
      }
    ];
    expected = [ ];
  };

  # The walk descends, and carries its prefix while doing so. lib/ is flat today, so the library
  # cell exercises the recursive branch not at all and would keep passing if the walk quietly
  # flattened; the fixture tree is nested on purpose and carries a planted tether at each of its
  # two depths. Handing it a non-empty prefix — its own real position in the repository — pins
  # both halves of the naming rule: the prefix the walk is given is threaded through, and the
  # prefix it builds for a subdirectory extends that one rather than replacing it.
  flake.tests.purity.test-walk-descends-into-subdirectories = {
    expr = scan (read (walk "ci/tests/_fixtures/purity-walk/" ./_fixtures/purity-walk));
    expected = [
      "ci/tests/_fixtures/purity-walk/nested/tethered.nix: 'lib.'"
      "ci/tests/_fixtures/purity-walk/surface.nix: 'mkOption'"
    ];
  };
}
