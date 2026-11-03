# THE COUNTED-RUN CENSUS (den-hoag-y0l9q): every evaluation in ci/ whose `NIX_SHOW_STATS` counters are
# read is serial, and no other evaluation is pinned. A thunk count is defined only for a serial run, and
# Determinate's parallel evaluator (`eval-cores`) makes it a random sample, so each counted evaluation
# carries gen-harness `lib.serialEval`'s options; the column's correctness cells keep its own evaluator.
#
# A lexical census over the files under ci/ that name `NIX_SHOW_STATS` (ci/tests/ is out of reach: a test
# module is evaluated in-process and starts no evaluator). Each logical command (continuation lines joined,
# full-line comments dropped, a Nix string's `''${` read as `${`) that calls an evaluator — `"$ni"`,
# `"$MODULES_SH_NIX_INSTANTIATE"`, `nix-instantiate` or `nix eval` as a word — is one of three:
#
#   counted  a `NIX_SHOW_STATS=1` prefix on the command: carries "${SERIAL_EVAL[@]}" unconditionally (a
#            prefix assignment is not visible to an expansion on its own command line, so never keyed);
#   keyed    an evaluation (`--eval`, `nix eval`) in a file that EXPORTS the stats around one shared
#            `evalArm`: carries ${NIX_SHOW_STATS:+"${SERIAL_EVAL[@]}"}, so only its counted calls pin;
#   plain    any other evaluation: carries no SERIAL_EVAL.
#
# The census table is pinned exactly (its positive control: the known sites are found), and each of the
# three rules is driven red by a planted violation, on a copy of a real file where one of this member's
# sites exercises the rule and on a synthetic one-file census where none does.
{ lib, ... }:
let
  ciDir = ../.;

  # walk : path -> string -> [ string ], the .bash / .sh / .nix files under `dir`, named from ci/.
  walk =
    dir: prefix:
    lib.concatLists (
      lib.mapAttrsToList (
        n: t:
        if t == "directory" then
          (if prefix == "" && n == "tests" then [ ] else walk (dir + "/${n}") "${prefix}${n}/")
        else if t == "regular" && builtins.match ".*\\.(bash|sh|nix)" n != null then
          [ "${prefix}${n}" ]
        else
          [ ]
      ) (builtins.readDir dir)
    );

  # A search, never a `.*x.*` match: a 600 KB file overflows the matcher's stack on the anchored form.
  names = needle: text: builtins.length (builtins.split needle text) > 1;

  sources = map (n: {
    name = n;
    text = builtins.readFile (ciDir + "/${n}");
  }) (lib.filter (n: names "NIX_SHOW_STATS" (builtins.readFile (ciDir + "/${n}"))) (walk ciDir ""));

  # commands : string -> [ string ], the logical commands of a file, each padded with a space either side.
  commands =
    text:
    let
      lines = lib.filter (l: builtins.match "[[:space:]]*#.*" l == null) (
        lib.splitString "\n" (builtins.replaceStrings [ "''\${" ] [ "\${" ] text)
      );
      step =
        acc: l:
        if acc.open then
          {
            done = acc.done;
            cur = acc.cur + " " + l;
            open = lib.hasSuffix "\\" l;
          }
        else
          {
            done = acc.done ++ lib.optional (acc.cur != null) acc.cur;
            cur = l;
            open = lib.hasSuffix "\\" l;
          };
      end = builtins.foldl' step {
        done = [ ];
        cur = null;
        open = false;
      } lines;
    in
    map (c: " ${c} ") (end.done ++ lib.optional (end.cur != null) end.cur);

  word = "[^-[:alnum:]_]";
  callsEvaluator =
    c:
    lib.hasInfix "\"$ni\"" c
    || lib.hasInfix "\"$MODULES_SH_NIX_INSTANTIATE\"" c
    || builtins.match ".*${word}nix-instantiate${word}.*" c != null
    || builtins.match ".*${word}nix eval${word}.*" c != null;
  evaluates = c: builtins.match ".*(--eval|${word}nix eval)${word}.*" c != null;
  prefixed =
    c:
    builtins.match ".*[^[:alnum:]_]NIX_SHOW_STATS=1[[:space:]].*" c != null
    && !(lib.hasInfix "export NIX_SHOW_STATS" c);
  keyedForm = "\${NIX_SHOW_STATS:+\"\${SERIAL_EVAL[@]}\"}";
  keyed = c: lib.hasInfix keyedForm c;
  unconditional = c: lib.hasInfix "\"\${SERIAL_EVAL[@]}\"" c && !(keyed c);
  pinned = c: lib.hasInfix "SERIAL_EVAL" c;

  # census : [ { name; text; } ] -> { table = [ { file; counted; keyed; plain; } ]; violations = [ string ]; }
  census =
    srcs:
    let
      per =
        src:
        let
          cs = lib.filter callsEvaluator (commands src.text);
          exports = names "export NIX_SHOW_STATS" src.text;
          counted = lib.filter prefixed cs;
          evals = lib.filter (c: !(prefixed c) && evaluates c) cs;
          keyedSites = if exports then evals else [ ];
          plainSites = if exports then [ ] else evals;
          bad =
            rule: ok: sites:
            map (c: "${src.name}: ${rule}: ${lib.substring 0 120 (lib.trim c)}") (
              lib.filter (c: !(ok c)) sites
            );
        in
        {
          row = {
            file = src.name;
            counted = lib.length counted;
            keyed = lib.length keyedSites;
            plain = lib.length plainSites;
          };
          violations =
            bad "a counted evaluation is not serial" unconditional counted
            ++ bad "an evaluation in a plane exporting the stats does not key its pin on them" keyed keyedSites
            ++ bad "an uncounted evaluation is pinned" (c: !(pinned c)) plainSites;
        };
      results = map per srcs;
    in
    {
      table = map (r: r.row) results;
      violations = lib.concatMap (r: r.violations) results;
    };

  clean = census sources;

  # plant <file> <from> <to>: the sources with one replacement in one file, refused when it writes nothing
  # (a seed that no-ops leaves the census green, which would read as a census that cannot red).
  plant =
    file: from: to:
    map (
      s:
      if s.name != file then
        s
      else
        let
          text = builtins.replaceStrings [ from ] [ to ] s.text;
        in
        assert lib.assertMsg (text != s.text) "counted-runs: the plant in ${file} wrote nothing";
        s // { inherit text; }
    ) sources;
  # The rules on a synthetic file, for a rule no site of this member's exercises: the census of one file.
  synthetic =
    name: text:
    map (v: lib.head (lib.splitString ": " v)) (census [ { inherit name text; } ]).violations;
in
{
  flake.tests.counted-runs.test-every-counted-evaluation-is-serial-and-no-other-is-pinned = {
    expr = clean.violations;
    expected = [ ];
  };

  # The three rules, each driven red by a planted violation, and each plant's spliced twin held green.
  flake.tests.counted-runs.test-plant-unspliced-counted-prefix-reds = {
    expr = synthetic "plant.sh" "out=$(NIX_SHOW_STATS=1 nix-instantiate --eval x.nix)\n";
    expected = [ "plant.sh" ];
  };
  flake.tests.counted-runs.test-plant-spliced-counted-prefix-holds = {
    expr = synthetic "plant.sh" "out=$(NIX_SHOW_STATS=1 nix-instantiate \"\${SERIAL_EVAL[@]}\" --eval x.nix)\n";
    expected = [ ];
  };
  flake.tests.counted-runs.test-plant-pinned-uncounted-evaluation-reds = {
    expr = synthetic "plant.sh" "nix-instantiate \"\${SERIAL_EVAL[@]}\" --eval x.nix\n";
    expected = [ "plant.sh" ];
  };
  # The positive control: the census finds every known site, and only those.
  flake.tests.counted-runs.test-census-finds-the-known-sites = {
    expr = clean.table;
    expected = [
      {
        file = "bench/graph-clique.nix";
        counted = 0;
        keyed = 0;
        plain = 0;
      }
      {
        file = "bench/graph-clique.sh";
        counted = 1;
        keyed = 0;
        plain = 0;
      }
      {
        file = "bench/graph-overlays.sh";
        counted = 1;
        keyed = 0;
        plain = 0;
      }
      {
        file = "bench/resolve-folds.nix";
        counted = 0;
        keyed = 0;
        plain = 0;
      }
      {
        file = "bench/resolve-folds.sh";
        counted = 1;
        keyed = 0;
        plain = 0;
      }
      {
        file = "bench/resolve-inherit-set.nix";
        counted = 0;
        keyed = 0;
        plain = 0;
      }
      {
        file = "bench/resolve-inherit-set.sh";
        counted = 1;
        keyed = 0;
        plain = 0;
      }
      {
        file = "bench/resolve-one-hop.sh";
        counted = 1;
        keyed = 0;
        plain = 0;
      }
      {
        file = "bench/resolve-parent-chain.sh";
        counted = 1;
        keyed = 0;
        plain = 0;
      }
      {
        file = "bench/resolve-visible-fanout.sh";
        counted = 1;
        keyed = 0;
        plain = 0;
      }
      {
        file = "tests-process.nix";
        counted = 0;
        keyed = 1;
        plain = 0;
      }
    ];
  };

  # The keyed rule on the real plane: its splice removed, and its splice made unconditional.
  flake.tests.counted-runs.test-plant-unspliced-keyed-site-reds = {
    expr =
      map (v: lib.head (lib.splitString ": " v))
        (census (
          plant "tests-process.nix" "''\${NIX_SHOW_STATS:+\"''\${SERIAL_EVAL[@]}\"} --eval" "--eval"
        )).violations;
    expected = [ "tests-process.nix" ];
  };
  flake.tests.counted-runs.test-plant-unconditional-pin-in-exporting-plane-reds = {
    expr =
      map (v: lib.head (lib.splitString ": " v))
        (census (
          plant "tests-process.nix" "''\${NIX_SHOW_STATS:+\"''\${SERIAL_EVAL[@]}\"}"
            "\"''\${SERIAL_EVAL[@]}\""
        )).violations;
    expected = [ "tests-process.nix" ];
  };

  # The counted rule on a real bench: its splice removed.
  flake.tests.counted-runs.test-plant-unspliced-counted-bench-reds = {
    expr =
      map (v: lib.head (lib.splitString ": " v))
        (census (plant "bench/graph-clique.sh" "\"\${SERIAL_EVAL[@]}\" --eval" "--eval")).violations;
    expected = [ "bench/graph-clique.sh" ];
  };
}
