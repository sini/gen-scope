# THE BENCH HEADERS' DENOTATION CLAIMS, DERIVED RATHER THAN TYPED (den-hoag-wmrpf).
#
# WHAT WAS WRONG. Every complexity bench under `ci/bench/` opens by saying the suite already pins
# its constructor's DENOTATION, and names the cells that do it. That sentence is COPIED when the
# next bench is written, so it arrives naming the PREVIOUS constructor while sitting above the new
# one — wrong by construction on every copy. It was caught twice by the same agent re-reading its
# own header, which is not a control: a stale glob names cells that really exist, so nothing about
# the claim looks false from inside the file.
#
# ★ THE ORACLE IS NOT "THE GLOB MATCHES SOMETHING". That is exactly the check a stale glob passes.
# The tie is to the constructor THIS BENCH MEASURES, and the only statement of that which is not
# itself copied prose is the bench's own ARM DISPATCH: `arm ? "inheritSet"` and `arm == "inheritSet"`
# are what the driver passes and what the bench throws on, so a copied header sits above arms the
# copier had to rewrite for the bench to run at all. Every arm is therefore named for the
# constructor it reaches, and the cited cells must belong to one of them.
#
# TWO WAYS A CELL BELONGS TO AN ARM, because a constructor's cells are not always named for it.
#   BY NAME — `test-clique-empty` belongs to the `clique` arm, the common case.
#   BY FILE — `ci/tests/collection-attr.nix` is `collectionAttr`'s denotation whole, and names its
#             cells for the traverse modes (`test-traverse-children-…`) rather than for the
#             constructor. A cell defined in the file named for an arm belongs to that arm.
# Both are ties to the constructor. Neither is satisfied by a sibling's glob, which is the point.
#
# ★ THE NEGATIVE CONTROL IS IN THE SUITE, not in a count someone maintains: the last cell runs this
# same predicate over a synthetic header carrying a sibling's glob and asserts it is REFUSED, beside
# the same header with the glob corrected and passing. A run in which the scan stopped reaching the
# bench tree reds `test-bench-denotation-scan-reaches-its-population` rather than reading `[ ] == [ ]`
# clean.
{ config, lib, ... }:
let
  benchDir = ../bench;
  benchNames = lib.filter (n: lib.hasSuffix ".nix" n) (lib.attrNames (builtins.readDir benchDir));
  benchSrc = n: builtins.readFile (benchDir + "/${n}");

  # Every occurrence of a capture, not just the first: `builtins.match` answers about the whole
  # string, so the repeated read has to come from `split`'s capture lists. Each pattern below
  # carries exactly ONE group, and the group is what is wanted rather than the whole match — the
  # `=` and the quotes are context. No lookaround: `builtins.split` is a POSIX ERE.
  captures = re: s: map builtins.head (lib.filter builtins.isList (builtins.split re s));

  # The bench's own statement of what it measures. The default and the dispatch are read together
  # so a bench is covered whether its driver passes an arm or leans on the default.
  armsOf =
    src:
    lib.unique (
      captures ''arm [?] "([A-Za-z0-9-]+)"'' src ++ captures ''arm == "([A-Za-z0-9-]+)"'' src
    );

  # Every cell name or glob prefix the file cites. `test-inheritSet-*` reads as `test-inheritSet-`,
  # which is the prefix the collected-cell check wants anyway.
  citedOf = src: lib.unique (captures "(test-[A-Za-z0-9-]+)" src);

  # `collectionAttr` -> `collection-attr`, the file-naming convention `ci/tests/` already follows.
  kebab =
    s:
    lib.concatStrings (
      map (p: if builtins.isList p then "-" + lib.toLower (builtins.head p) else p) (
        builtins.split "([A-Z])" s
      )
    );

  # Which file defines which cell, read from the tree rather than from a list someone maintains.
  testNames = lib.filter (n: lib.hasSuffix ".nix" n) (lib.attrNames (builtins.readDir ./.));
  cellFileOf = lib.listToAttrs (
    lib.concatMap (
      f:
      map (c: {
        name = c;
        value = f;
      }) (captures "(test-[A-Za-z0-9-]+) =" (builtins.readFile (./. + "/${f}")))
    ) testNames
  );

  # The COLLECTED set, taken from the suite the harness actually runs rather than from the source.
  collected = lib.concatMap lib.attrNames (lib.attrValues config.flake.tests);
  collectedUnder = t: lib.filter (c: lib.hasPrefix t c) collected;

  nameTie = arms: t: lib.any (a: t == "test-${a}" || lib.hasPrefix "test-${a}-" t) arms;
  fileTie =
    arms: t:
    let
      cells = collectedUnder t;
      files = lib.unique (map (c: cellFileOf.${c} or "<undefined>") cells);
    in
    cells != [ ] && lib.all (f: lib.any (a: f == "${kebab a}.nix") arms) files;

  # The two refusals, each returning the offending (bench, citation) pairs so a red NAMES them.
  untiedIn =
    label: src:
    let
      arms = armsOf src;
    in
    map (t: "${label}: ${t}") (lib.filter (t: !(nameTie arms t || fileTie arms t)) (citedOf src));
  uncollectedIn =
    label: src: map (t: "${label}: ${t}") (lib.filter (t: collectedUnder t == [ ]) (citedOf src));

  overBenches = f: lib.concatMap (b: f b (benchSrc b)) benchNames;

  # The synthetic pair the negative control runs on: one header, one constructor, one glob — the
  # second is the first with the glob corrected, so the arms are identical and the citation is the
  # only term that moves.
  syntheticArms = ''
    arm ? "inheritSet",
    if arm == "inheritSet" then
  '';
  staleHeader =
    syntheticArms + "# pins this constructor's DENOTATION: the seven `test-inheritAll-*` cells\n";
  freshHeader =
    syntheticArms + "# pins this constructor's DENOTATION: the seven `test-inheritSet-*` cells\n";
in
{
  flake.tests."bench-denotation" = {
    # THE ROW ITSELF: no bench may cite a cell belonging to a constructor it has no arm for.
    test-bench-header-cells-belong-to-this-bench-own-arms = {
      expr = overBenches untiedIn;
      expected = [ ];
    };
    # The other half of the claim, and the one a glob hides: the cited cells must EXIST in the
    # collected suite. A header claiming seven cells where one is collected fails here.
    test-bench-header-cells-are-collected = {
      expr = overBenches uncollectedIn;
      expected = [ ];
    };
    # THE REACH CONTROL. Four benches make a denotation claim; the arm reader must reach all of
    # them plus every bench that makes none. A scan that stopped matching reds here instead of
    # returning two empty offender lists above. ★ A NEW BENCH THAT CITES CELLS REDS THIS CELL BY
    # DESIGN — the population of coverage claims is what this row exists to hold, so a bench
    # joining it is a thing to read rather than a figure to bump.
    test-bench-denotation-scan-reaches-its-population = {
      expr = {
        benchesCiting = builtins.length (lib.filter (b: citedOf (benchSrc b) != [ ]) benchNames);
        benchesWithoutArms = lib.filter (b: armsOf (benchSrc b) == [ ]) benchNames;
        collectedIsNonEmpty = collected != [ ];
        cellIndexIsNonEmpty = cellFileOf != { };
      };
      expected = {
        benchesCiting = 4;
        benchesWithoutArms = [ ];
        collectedIsNonEmpty = true;
        cellIndexIsNonEmpty = true;
      };
    };
    # THE NEGATIVE CONTROL, both arms in one cell: the stale glob names cells that really exist and
    # is still refused, because it names cells for a constructor this bench has no arm for.
    test-bench-denotation-refuses-a-siblings-glob = {
      expr = {
        stale = untiedIn "synthetic" staleHeader;
        fresh = untiedIn "synthetic" freshHeader;
      };
      expected = {
        stale = [ "synthetic: test-inheritAll-" ];
        fresh = [ ];
      };
    };
  };
}
