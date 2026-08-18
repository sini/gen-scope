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
# AN EMPTINESS IS NOT EVIDENCE. Four mechanisms stand between this library and a silent
# nixpkgs tether — the walk that finds the files, the read that hands over their text, the strip
# that removes their comments, and the token scan that judges them — and every one of them
# reports "clean" when it is dead. Each is therefore held to a cell whose expectation is a
# literal:
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
#   * The STRIP's PREMISE is asserted rather than assumed. Cutting each line at its first `#` is
#     sound only while no `#` opens inside a string literal; where one does, live code is
#     truncated to the end of that line and every cell here goes blind on what was removed, with
#     no signal at all. So the premise is checked over the RAW text, with a live control for the
#     predicate itself and a declared list of the files a line-local test cannot conclude about.
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

  # The premise that strip rests on, made checkable. `firstHashInString` is line-local and
  # deliberately conservative: it asks whether the text before a line's first `#` has closed
  # every double quote it opened, and an odd count means that `#` stands inside one. Being
  # line-local it cannot conclude about string content that spans lines — an indented `''…''`
  # block — so those files are declared as a list of their own rather than silently trusted.
  # Asserting the premise is preferred to tokenizing strings inside the strip: a Nix lexer here
  # would be a larger, unverified instrument needing its own premise, and its cheap form (cut
  # only at a `#` with even quote parity) is blind to exactly the `''` case anyway.
  countQuotes = s: (lib.length (lib.splitString "\"" s)) - 1;
  firstHashInString =
    line:
    let
      parts = lib.splitString "#" line;
    in
    lib.length parts > 1 && lib.mod (countQuotes (lib.head parts)) 2 == 1;

  # premiseBreaches : [ { name; text; } ] -> [ "file:line" ]. A breach is reported at its line
  # as well as its file, because what it says is that one particular line's code was truncated.
  premiseBreaches =
    srcs:
    lib.concatMap (
      src:
      lib.concatLists (
        lib.imap1 (i: line: lib.optional (firstHashInString line) "${src.name}:${toString i}") (
          lib.splitString "\n" src.text
        )
      )
    ) srcs;

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

  # The read and the strip are separate stages, one `readFile` per file feeding both. The
  # premise cell has to speak about the RAW text, which is only a value once the strip stops
  # happening inside the read; and `sources` is then a total per-element function of
  # `rawSources` — `name` passes through, `code` is the strip of `text` — so pinning either one
  # pins the other, and the cells over each COMPOSE instead of hoping two independent reads of
  # the same tree agree with one another.
  raw =
    entries:
    map (e: {
      inherit (e) name;
      text = builtins.readFile e.path;
    }) entries;

  strip =
    entries:
    map (e: {
      inherit (e) name;
      code = stripComments e.text;
    }) entries;

  # The scanned subject is exactly the library plus its two roots, and nothing else. In
  # particular the walk fixtures under ci/tests/_fixtures/purity-walk/ are NOT members: they
  # carry planted tethers by design — `lib.types.str` and `mkOption { }`, both live post-strip —
  # so admitting them would make the library cell red on this suite's own instruments, and a
  # planted tether inside a purity subject is a contradiction in terms. What pins them instead
  # is the walk cell's exact two-element expectation, which asserts both which files the walk
  # found and that each planted token survives the strip; a premise breach on a fixture line
  # would truncate that line and red it. The exclusion therefore costs no coverage.
  rawSources = raw (walk "lib/" libDir) ++ [
    {
      name = "flake.nix";
      text = builtins.readFile ../../flake.nix;
    }
    {
      name = "default.nix";
      text = builtins.readFile ../../default.nix;
    }
  ];

  sources = strip rawSources;

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
  # reach for nixpkgs. Every gen-scope source but two carries it, and both exclusions are files
  # that depend on nothing and so name no prelude — `lib/graph.nix` is the algebraic graph core
  # (Mokhov, 2017), written in builtins alone, and `lib/traversal-names.nix` is the traversal
  # vocabulary, a bare attribute set of names taking no argument at all. Those exclusions are what
  # give the assertion its teeth: the expected list is a PROPER subset of the manifest, so a read
  # returning one fixed text for every file lands outside it either way — without the token the
  # list collapses toward empty, with it the list swells to every source.
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
      "lib/traversal-names.nix"
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

  # Named because the subject-pinning pair is a COMPOSITION: this cell is the residual content floor
  # for the labels the live list cannot reach — lib/graph.nix and lib/traversal-names.nix — whose
  # text no other cell here pins. Both depend on nothing and so name no prelude: the first is the
  # algebraic graph core (Mokhov, 2017), written in builtins alone, the second the traversal
  # vocabulary, a bare attribute set of names. Their exclusion is exactly what makes the live list a
  # proper subset of the manifest and so what gives that list its teeth, and it is the same
  # exclusion that leaves those files' text unpinned. The cell is here because the composition
  # leaves that gap, NOT because a non-empty read is evidence of anything. What it closes is the
  # empty-text case for those files; a non-empty constant substituted for a source passes this cell
  # exactly as it passes every other cell here, and that residue is named rather than removed. The `sources != [ ]`
  # conjunct is this cell's own vacuity guard — `all` over an empty list is true, so without it the
  # floor would report clean on the very degeneracy it is written to bound — not a second copy of
  # the manifest's literal.
  flake.tests.purity.test-scan-reads-non-empty-sources = {
    expr = sources != [ ] && lib.all (s: s.code != "") sources;
    expected = true;
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

  # And the premise that strip rests on holds of the text that was actually scanned. The cut at
  # each line's first `#` removes live code wherever that `#` stands inside a string literal,
  # and the loss is silent: the scan simply stops seeing the rest of the line, so a tether
  # sitting past one would pass every cell here. A breach reds this cell at the file and line.
  #
  # This is an absence claim about text read from disk, and it is NOT non-vacuous on its own —
  # its expectation is `[ ]`, which an emptied or constant subject satisfies exactly as a sound
  # corpus does. What arms it is the pair asserted over the same read,
  # `test-scan-subject-is-the-library-tree` for membership and `test-scan-reads-are-live` for
  # content, together with `test-scan-reads-non-empty-sources` for the one label that pair
  # cannot reach. Green here means the premise holds of the text those cells pin, and nothing
  # more; the composition is what carries it, not this cell alone.
  flake.tests.purity.test-strip-premise-holds = {
    expr = premiseBreaches rawSources;
    expected = [ ];
  };

  # And the predicate that says so is capable of saying no. Its subject is a literal written
  # inside this cell rather than anything on disk, so what it establishes is exactly that the
  # test discriminates an in-string `#` from an ordinary trailing comment — it says nothing
  # whatever about what the cell above was pointed at, which is why that cell names its pair
  # instead of leaning on this one. Both directions ride in one expectation: the first line must
  # be caught and the second must not, so a predicate stuck at either constant reds here.
  flake.tests.purity.test-strip-premise-scan-is-live = {
    expr = premiseBreaches [
      {
        name = "<in-string-hash>";
        text = ''
          url = "https://example.com/x#frag";
          x = 1; # an ordinary trailing comment
        '';
      }
    ];
    expected = [ "<in-string-hash>:1" ];
  };

  # The declared surface: the files the line-local predicate cannot conclude about. An indented
  # `''…''` block carries string content across line boundaries, where a per-line quote count
  # cannot follow it, so those files are written down rather than trusted in silence. No scanned
  # file contains such a block today, and the empty expectation is what makes this a live
  # declaration instead of a footnote — the first file to grow one arrives as a red and gets a
  # reading, exactly as a new library file arrives as a red on the manifest.
  flake.tests.purity.test-strip-premise-multiline-strings = {
    expr = map (src: src.name) (lib.filter (src: genPrelude.hasInfix "''" src.text) rawSources);
    expected = [ ];
  };

  # The walk descends, and carries its prefix while doing so. lib/ is flat today, so the library
  # cell exercises the recursive branch not at all and would keep passing if the walk quietly
  # flattened; the fixture tree is nested on purpose and carries a planted tether at each of its
  # two depths. Handing it a non-empty prefix — its own real position in the repository — pins
  # both halves of the naming rule: the prefix the walk is given is threaded through, and the
  # prefix it builds for a subdirectory extends that one rather than replacing it.
  flake.tests.purity.test-walk-descends-into-subdirectories = {
    expr = scan (strip (raw (walk "ci/tests/_fixtures/purity-walk/" ./_fixtures/purity-walk)));
    expected = [
      "ci/tests/_fixtures/purity-walk/nested/tethered.nix: 'lib.'"
      "ci/tests/_fixtures/purity-walk/surface.nix: 'mkOption'"
    ];
  };
}
