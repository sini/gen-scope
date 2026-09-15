# THE README'S SUITE FIGURES, BOUND TO THE SUITES THEMSELVES (den-hoag-7q7r4).
#
# WHAT WENT WRONG. README.md's "Testing" section recorded `850 tests across 55 suites` and
# `125 tests across 15 suites` while the planes measured 928/61 and 141/19 — all four numbers stale,
# and stale SILENTLY, because prose does not evaluate. The cost is not cosmetic: a builder baselining
# a no-cell-decrease oracle off the README compares against 850, reads a 78-cell increase as
# catastrophic, or masks a real decrease inside the gap. A figure with no oracle is the drift class
# this corpus has already paid for in `ARCHITECTURE.md`'s library graph and in the bench headers
# `bench-denotation.nix` beside this file binds.
#
# ★ THE DOMAIN IS THE WHOLE DOCUMENT, NOT A MARKED REGION. The ecosystem's other doc binding —
# `agents-md-citations` — reads only what sits between its markers, and a second copy of a figure
# outside the region drifts unseen; measured, and the reason that check could not be reused here.
# Every rule below scans all of README.md, so a figure restated anywhere in the file is in reach.
#
# ★★ EVERY RULE IS ASSERTED TO REACH ITS SPAN, and that arm is the load-bearing one. A rule whose
# pattern no longer matches anything reads `[ ] == [ ]` — indistinguishable from agreement — so a
# sentence reworded past the pattern would take its figure OUT of the oracle while the suite stayed
# green. `test-readme-figures-every-rule-reaches-its-span` is what refuses that, and it names the
# rule rather than counting, so the remedy is the pattern or the sentence rather than a denial.
#
# ★ WHAT THIS DOES NOT BIND, stated because a green here is otherwise read as more than it is.
# (a) The REVERSE direction of the name arm: a suite named in the README that no longer exists is
#     invisible. Classifying it would mean deciding, for every backticked token in the section —
#     `lib/graph.nix`, `below`, `d`, `''` — whether it is a suite name, and an alternation over the
#     spellings that happen to exist today is the same defect one layer out.
# (b) The PROSE around each figure: that `entry` covers the standalone root entry is a claim no
#     count can check.
{
  config,
  genPrelude,
  lib,
  ...
}:
let
  doc = builtins.readFile ../../README.md;

  # Every occurrence of a pattern's capture list, not just the first: `builtins.match` answers about
  # the whole string, so the repeated read comes from `split`'s capture lists. The same idiom
  # `bench-denotation.nix` uses, minus its `head` — a rule here may carry two groups. No lookaround:
  # `builtins.split` is a POSIX ERE, and a literal `*` is written `[*]` for the same reason that file
  # writes `[?]`.
  spansOf = re: s: lib.filter builtins.isList (builtins.split re s);

  # The README states a small group count as a WORD (`the six ` + backtick + `plane-*` + backtick +
  # ` suites`) and a headline figure as digits. Both are read here rather than forcing the prose into
  # one voice. An unknown token yields `null`, which equals no expected number — so a count written
  # in a spelling this table cannot read REDS naming the rule, instead of passing unread.
  words = {
    one = 1;
    two = 2;
    three = 3;
    four = 4;
    five = 5;
    six = 6;
    seven = 7;
    eight = 8;
    nine = 9;
    ten = 10;
    eleven = 11;
    twelve = 12;
    thirteen = 13;
    fourteen = 14;
    fifteen = 15;
    sixteen = 16;
    seventeen = 17;
    eighteen = 18;
    nineteen = 19;
    twenty = 20;
  };
  numOf =
    tok:
    if tok == null then
      null
    else if builtins.match "[0-9]+" tok != null then
      lib.toInt tok
    else
      words.${lib.toLower tok} or null;

  # ── the suites, counted from the planes the harness actually runs ──
  #
  # `attrNames` on a plane returns SUITE names, one level above the cells nix-unit collects, so the
  # cell count is the `test`-prefixed leaves under each suite — the set nix-unit itself collects, and
  # the reason a suite count and a cell count are two figures rather than one. Reading names forces
  # no cell's `expr`, so this costs nothing the gate was not already paying.
  suitesOf = plane: lib.attrNames plane;
  cellsOf =
    plane:
    lib.concatMap (s: lib.filter (lib.hasPrefix "test") (lib.attrNames plane.${s})) (suitesOf plane);

  tests = config.flake.tests;
  testsError = config.flake.testsError;

  testsSuites = suitesOf tests;
  errorSuites = suitesOf testsError;

  # ── the tree, read from the tree ──
  testsDir = builtins.readDir ./.;
  fixturesDir = builtins.readDir ./_fixtures;
  countIn = dir: p: lib.length (lib.filter p (lib.attrNames dir));

  suiteFiles = countIn testsDir (n: lib.hasSuffix ".nix" n && testsDir.${n} == "regular");
  fixtureFiles = countIn fixturesDir (n: fixturesDir.${n} == "regular");
  fixtureDirs = countIn fixturesDir (n: fixturesDir.${n} == "directory");

  # The fold-and-cascade group, named rather than counted: the set is `folds`, `dedup` and whatever
  # carries the `cascade-` prefix, so a new cascade suite moves the figure without anyone editing a
  # constant here.
  foldCascade = lib.filter (
    s: lib.hasPrefix "cascade-" s || s == "folds" || s == "dedup"
  ) testsSuites;

  # ── the rules ──
  #
  # `expected` is a LIST OF SPANS, each span a list of numbers, so a rule states both what each
  # occurrence must say AND how many occurrences there are. `figure-spans` is the totality rule: the
  # two anchored rules above it pin each pair to its own sentence, and this one refuses a THIRD
  # `N tests across M suites` anywhere in the file — the shape in which a stale second copy hides.
  rules = [
    {
      label = "tests-plane-figure";
      pattern = "Requires nix-unit[.] [*][*]([0-9]+) tests across ([0-9]+) suites[*][*]";
      expected = [
        [
          (lib.length (cellsOf tests))
          (lib.length testsSuites)
        ]
      ];
    }
    {
      label = "tests-error-plane-figure";
      pattern = "own output — [*][*]([0-9]+) tests across ([0-9]+) suites[*][*]";
      expected = [
        [
          (lib.length (cellsOf testsError))
          (lib.length errorSuites)
        ]
      ];
    }
    {
      label = "figure-spans";
      pattern = "([0-9]+) tests across ([0-9]+) suites";
      expected = [
        [
          (lib.length (cellsOf tests))
          (lib.length testsSuites)
        ]
        [
          (lib.length (cellsOf testsError))
          (lib.length errorSuites)
        ]
      ];
    }
    {
      label = "suite-files";
      pattern = "([A-Za-z0-9]+) suite files under";
      expected = [ [ suiteFiles ] ];
    }
    {
      label = "fixture-entries";
      pattern = "([A-Za-z0-9]+) further entries sit in";
      expected = [ [ (fixtureFiles + fixtureDirs) ] ];
    }
    {
      label = "fixture-files";
      pattern = "([A-Za-z0-9]+) fixture files";
      expected = [ [ fixtureFiles ] ];
    }
    {
      label = "fixture-directories";
      pattern = "([A-Za-z0-9]+) directory, `purity-walk`";
      expected = [ [ fixtureDirs ] ];
    }
    {
      label = "refusals-suites";
      pattern = "([A-Za-z0-9]+) `[*]-refusals` suites";
      expected = [ [ (lib.length (lib.filter (lib.hasSuffix "-refusals") errorSuites)) ] ];
    }
    {
      label = "plane-suites";
      pattern = "([A-Za-z0-9]+) `plane-[*]` suites";
      expected = [ [ (lib.length (lib.filter (lib.hasPrefix "plane-") testsSuites)) ] ];
    }
    {
      label = "cascade-suites";
      pattern = "([A-Za-z0-9]+) `cascade-[*]`";
      expected = [ [ (lib.length (lib.filter (lib.hasPrefix "cascade-") testsSuites)) ] ];
    }
    {
      label = "fold-cascade-suites";
      pattern = "([A-Za-z0-9]+) further suites cover the fold vocabulary";
      expected = [ [ (lib.length foldCascade) ] ];
    }
  ];

  # A rule's reading of a document: every occurrence, every capture, as numbers.
  readingOf = d: rule: map (span: map numOf span) (spansOf rule.pattern d);

  # The two refusals, each returning offending rules BY LABEL with both sides of the disagreement, so
  # a red says which sentence to edit and to what.
  unreachedIn = d: map (r: r.label) (lib.filter (r: readingOf d r == [ ]) rules);
  disagreeingIn =
    d:
    map (
      r:
      "${r.label}: README says ${builtins.toJSON (readingOf d r)}, the suites say ${builtins.toJSON r.expected}"
    ) (lib.filter (r: readingOf d r != [ ] && readingOf d r != r.expected) rules);

  # ── the name arm ──
  #
  # A suite whose count is right can still be one nobody documented: the figures move together when a
  # suite lands, but a RENAME moves neither. Every suite must be named in the README, except where the
  # document names its group instead — the two group forms it actually uses, and no others.
  allSuites = testsSuites ++ errorSuites;
  namedByGroup = s: lib.hasPrefix "plane-" s || lib.hasSuffix "-refusals" s;
  # `genPrelude.hasInfix`, not `lib.hasInfix`: README.md is ~173 KB and the nixpkgs one overflows the
  # C stack on a whole-file scan.
  namedInDoc = s: genPrelude.hasInfix "`${s}`" doc;
  undocumented = lib.filter (s: !(namedByGroup s) && !(namedInDoc s)) allSuites;

  # ── the negative control the figure rules ship with ──
  #
  # A synthetic document carrying one figure sentence, and the same sentence with the figure moved by
  # one. The arms differ in that digit and in nothing else, so a run in which the scan stopped
  # discriminating fails the pair rather than reading two clean empties.
  syntheticFresh = "Requires nix-unit. **${toString (lib.length (cellsOf tests))} tests across ${toString (lib.length testsSuites)} suites** (x).";
  syntheticStale = "Requires nix-unit. **${
    toString (lib.length (cellsOf tests) + 1)
  } tests across ${toString (lib.length testsSuites)} suites** (x).";
  firstRule = lib.head rules;
in
{
  flake.tests.readme-figures = {
    # THE FIGURES. Every rule's reading of the shipped README equals what the planes and the tree
    # report, occurrence for occurrence.
    test-readme-figures-agree-with-the-suites = {
      expr = disagreeingIn doc;
      expected = [ ];
    };

    # THE ORACLE'S OWN REACH — the arm without which the one above reads `[ ] == [ ]` on a sentence
    # reworded past its pattern. Every rule matches at least one span of the shipped README.
    test-readme-figures-every-rule-reaches-its-span = {
      expr = unreachedIn doc;
      expected = [ ];
    };

    # THE SCAN DISCRIMINATES — the same rule over a synthetic pair differing only in the figure:
    # clean on the correct one, and naming the rule on the one that is off by a single cell. Without
    # this pair the two cells above are a predicate nobody has seen fail.
    test-readme-figures-scan-accepts-a-correct-figure = {
      expr = readingOf syntheticFresh firstRule == firstRule.expected;
      expected = true;
    };
    test-readme-figures-scan-refuses-a-wrong-figure = {
      expr =
        lib.length (readingOf syntheticStale firstRule) == 1
        && readingOf syntheticStale firstRule != firstRule.expected;
      expected = true;
    };

    # THE NAMES. Every suite on either plane is named in the README, or named by the group form the
    # README uses for it.
    test-readme-figures-every-suite-is-named = {
      expr = undocumented;
      expected = [ ];
    };

    # THE NAME ARM'S LIVE CONTROL, in the same run: drop the group exemption and the predicate must
    # FIRE. A `hasInfix` stuck true returns `[ ]` here while the cell above still reads clean — the
    # exact shape in which a dead scan passes for a clean document — and the cell above, which the
    # same predicate answers `true` for on every individually named suite, is the other arm. The
    # second key is what keeps the exemption honest: everything the unexempted scan catches is a
    # suite the README names by GROUP, so the exemption is covering nothing else.
    test-readme-figures-name-scan-fires-without-the-group-exemption =
      let
        caught = lib.filter (s: !(namedInDoc s)) allSuites;
      in
      {
        expr = {
          fires = caught != [ ];
          all-covered-by-a-group-form = lib.all namedByGroup caught;
        };
        expected = {
          fires = true;
          all-covered-by-a-group-form = true;
        };
      };
  };
}
