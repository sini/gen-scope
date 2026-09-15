# THE STANDALONE ENTRY, EXERCISED. The root `default.nix` is the non-flake path `AGENTS.md`
# documents, and every OTHER cell in this suite takes `genScope` from `ci/flake.nix`, which builds it
# with `import ../lib` from ci's own inputs and so never evaluates the root shim. This is the cell
# that does — the L1 migration replaced this file's PREDECESSOR (the pre-arm-B shape) with the
# resolver-seam shape below: four dependencies, wired the same three-channel way every other library
# in this roster now is.
#
# ★ THIS FILE'S FORMALS ARE `genPreludeLib`, `genGraph`, `genSchema`, `genIdentity` — NOT bare
# `prelude`/`graph`/`schema`/`identity`. `ci/flake.nix`'s `specialArgs` supplies them under those
# names (`genPreludeLib = prelude;` and three bare `inherit`s), the harness's own naming, which
# diverges from every other member of this migration's batch: gen-bind and gen-dispatch supply bare
# `prelude`, gen-graph supplies `genPrelude`, and this library alone supplies `genPreludeLib` and
# names the other three siblings directly rather than through one shared instance. The SHIM's own
# dependency formals stay `prelude`, `graph`, `identity`, `schema`; `entryArgs` below is the one place
# the harness names and the shim names meet.
#
# ★★ THE CELL IS PURE, AND THE PURITY IS A CONSEQUENCE OF HOW IT IS CALLED. The shim's four
# dependency defaults each `builtins.fetchTree` the flake-locked revision; supplying every one
# explicitly means none of those defaults is ever forced, so this reaches the network not at all.
# What it tests is the shim's SIGNATURE and its DELEGATION — which is precisely where the defect
# lives. The bare `import ../.. { }` form does NOT have this property, and the difference is measured
# rather than assumed: with the shim's `src` formal replaced by a `throw`, the bare form aborts —
# reported at the `prelude` key — while the supplied form evaluates clean with that same `throw`
# installed.
#
# THREE KEYS, BECAUSE THIS SHIM CONSTRUCTS FOUR SIBLINGS AND THIS LIBRARY READS THREE OF THEM:
#   prelude  — `mkProgram`'s atom fold runs through `prelude.listToAttrs`/`prelude.genList` over the
#              rule list, so forcing its result is what drives the call through gen-prelude rather
#              than merely returning the caller-supplied rules unread.
#   graph    — `engine.solve`'s condensation runs through `graph.condensation` over the program's
#              dependency accessor, so forcing `.condensationDepth` is what drives the call through
#              gen-graph rather than merely returning the program unexamined.
#   identity — `mint.mintStrata`'s per-record mint runs through `hashIdentity` (destructured out of
#              `identity` by `lib/default.nix` and threaded into `mint.nix`), so forcing a minted
#              node's `.identity` is what drives the call through gen-identity rather than merely
#              echoing the caller-supplied record back.
#
# ★★★ `schema` HAS NO KEY HERE, AND THAT IS A MEASURED FACT RATHER THAN AN OVERSIGHT. Grepping
# `\bschema\b` across every file in `lib/` finds exactly one occurrence — the formal's own
# declaration at `lib/default.nix` — never referenced again in that file's `let…in` body and absent
# from the final `mergeSurface { … }` call. So there is no expression in `lib/` this cell could force
# to observe gen-schema through the library the way the three keys above observe their siblings; a
# key here would be exercising nothing. This is NOT a claim that `schema` is safe to drop —
# `den-hoag-ams0d` fences removal on exactly this measurement's narrower predecessor (the minting path
# alone) and states in terms that the wider claim, unread across gen-scope's whole PUBLISHED surface,
# is not established by it; `0pk67-injection-test` is dispatched on that wider claim. `schema`'s
# protection against silent removal from THIS file rests instead on the three structural/totality
# cells below (`test-every-wired-dependency-defaults-to-its-own-node`,
# `test-the-wired-dependency-set-is-the-libs-own-formals`,
# `test-the-defaulted-entry-forces-every-dependency`), each of which is total over every wired
# dependency BY CONSTRUCTION and would name `schema` on a silent drop precisely because it asks
# nothing about whether `lib/` reads it.
{
  genScope,
  genPreludeLib,
  genGraph,
  genSchema,
  genIdentity,
  lib,
  ...
}:
let
  # ★ ONE binding, read by BOTH cells. Duplicating the literal makes the control guard its own copy
  # and nothing else — measured: main copy broken ⇒ 2/2 exit 0 on a tree carrying a real member.
  needle = ''}/lib"[[:space:]]*\{'';

  # The same construction `ci/tests/purity.nix` uses, over the same file, for the same stated reason.
  stripComments =
    text:
    lib.concatStringsSep "\n" (
      map (line: lib.head (lib.splitString "#" line)) (lib.splitString "\n" text)
    );

  # ★ THE FOUR dependency formals, from the SAME bindings `ci/flake.nix` builds its `lib` output
  # from. That is what keeps this cell offline, and it is also what makes the cell a reading of the
  # SHIM: over two different substrate builds it would be exercising two libraries.
  # ★★ THE ARGUMENT SET IS BOUND ONCE, AND BOTH THE APPLICATION AND THE TOTALITY CELL READ THIS
  # BINDING — `needle`'s rule above, carried to the argument set. Two literals spelled the same are
  # TWO PREDICATES, and the totality cell would then be comparing the shim against a copy nothing
  # applies.
  entryArgs = {
    prelude = genPreludeLib;
    graph = genGraph;
    identity = genIdentity;
    schema = genSchema;
    # The shim's own plumbing, which this cell is now obliged to CHOOSE rather than inherit. The
    # `throw` is what makes non-hermeticity IMPOSSIBLE for this application rather than merely
    # detected — but it is NOT the guard: a shim carrying `...` would swallow these keys unread and
    # unreported. The guard is the pair of cells below.
    #
    # ★ THE SEAM IS `src`, AND IT IS PATH-SHAPED. The shim reads its own `ci/flake.lock` as local
    # DATA, so there is no `lock` formal left to neutralise and a cell passing one neither needed to
    # nor could; what remains injectable is the single expression that fetches. `dep` is the
    # arity-dispatching resolver built over it and is closed for the same reason — a formal left at
    # its default is a channel this application did not choose.
    #
    # ★ `wire` IS THE THIRD SEAM AND IT IS CHOSEN, NOT CLOSED. It is the shim's own wiring of
    # `./lib`, restated here because the totality rule below admits no formal left at its default —
    # closing it with a `throw` would leave this application with nothing to exercise. The hermetic
    # cells at the foot of this file are where it is INJECTED rather than reproduced.
    inputs = { };
    src = segs: throw "the entry cell must not fetch: ${builtins.concatStringsSep "." segs}";
    dep = segs: throw "the entry cell must not build: ${builtins.concatStringsSep "." segs}";
    wire = { deps, resolve }: import ../../lib deps;
  };

  entry = import ../.. entryArgs;

  # ★★ THE SEAM-CLOSING ARGUMENT SET FOR THE HERMETIC PAIR AT THE FOOT OF THIS FILE, BOUND RATHER
  # THAN WRITTEN AT THE APPLICATION — `entryArgs`' own rule, for the same reason. `dep` stops the
  # resolver at the PATH instead of fetching it, and replacing `wire` publishes the whole record the
  # shim's body hands TO `wire` — its `deps` half is the attrset `./lib` receives only while `wire`'s
  # own default is `{ deps, resolve }: import ./lib deps`, which the cell at the foot of this file is
  # what holds, and its `resolve` half is the shim's own `follows` rule, which is why nothing below
  # transcribes that rule. So this application is hermetic by CONSTRUCTION. Nothing else is supplied:
  # every dependency formal is left at its default, which is the point — the defaults are the
  # subject.
  pathArgs = {
    dep = segs: segs;
    wire = args: args;
  };
  seam = import ../.. pathArgs;
  paths = seam.deps;

  # ★★★ THE SHIM'S OWN RESOLVER, READ RATHER THAN RETRANSCRIBED. `default.nix` holds the ONE
  # declaration of the `follows` rule in this library and publishes it in the record its body hands
  # to `wire`; this is that binding and not a copy of it. So the fixture control below drives the
  # expression the shim itself resolves with, and `…-defaults-to-its-own-node` resolves the shim's
  # declared paths by the shim's own rule rather than by a second copy that can agree with its own
  # expectation while both are wrong.
  shimResolve = seam.resolve;

  # ★ THE ci LOCK, READ AS PURE DATA — and the rule that walks it is NOT TRANSCRIBED HERE:
  # `shimResolve` above IS `default.nix`'s binding. A direct edge IS the node key; a `follows` value
  # is a PATH resolved segment by segment from this lock's own root. Never `lock.nodes.<label>` — a
  # last-segment shortcut reads a DIFFERENT node, and this library's OWN `ci/flake.lock` is a live
  # instance of exactly that: its `gen-prelude` root input resolves to a different node under the
  # walked rule than the bare label `gen-prelude` names. Reading the lock is pure data; nothing here
  # fetches.
  lock = builtins.fromJSON (builtins.readFile ../flake.lock);

  # ★★ THE RESOLVER IS BOUND OVER ITS LOCK, AND THAT IS WHAT MAKES ITS CONTROL EXPRESSIBLE AT ALL. A
  # `repoOf` closed over THIS lock has no free parameter, so a control could only re-assert the main
  # arm's own value; taking the lock as an argument is what puts the control AT AN INPUT THE MAIN ARM
  # DOES NOT USE. `shimResolve` takes its lock the same way and for the same reason — which is why
  # `default.nix` publishes the LOCK-PARAMETERISED rule rather than its own applied `fetch`. The
  # `lock` formal here deliberately shadows the binding above.
  #
  # ★★★ AND THE CONTROL IS NOT CEREMONY, IT IS THE ENTIRE ORACLE FOR THIS RULE — which this library
  # declares EXACTLY ONCE, in `default.nix`, so *this rule* now names one expression and not two. A
  # hermetic fixture is the only thing that can discriminate the resolver rule where `repoOf`'s
  # `.locked.repo` reading cannot — and MEASURED, this is that library: `default.nix`'s own comment
  # records that the walked path and the last-segment shortcut resolve `gen-prelude` to different
  # NODES at this library's real `ci/flake.lock`, but both nodes are `gen-prelude` revisions, so
  # `repoOf lock ["gen-prelude"]` reads `"gen-prelude"` under EITHER rule — a RED-drive on the real
  # resolver (corrupted to the last-segment shortcut) left `test-every-wired-dependency-…` GREEN and
  # only this fixture cell went RED, in the same run. The fixture below is transcribed verbatim
  # regardless, because the rule this suite protects is declared once and the same hermetic
  # construction is what makes it total over every member of the roster — here it is the ONLY member
  # of the pair that can discriminate the rule at all, elsewhere it is the one that generalizes past
  # whatever the real lock happens to agree on today.
  repoOf = lock: segs: lock.nodes.${shimResolve lock segs}.locked.repo;

  # ★ THE FIXTURE LOCK, AND IT IS TWO CLAIMS IN ONE SHAPE. `root → a` is a DIRECT edge, where the
  # value IS the node key; `a-node → b` is a `follows` PATH resolved from the lock's own root — so
  # both branches of `following` are exercised. Walking `[ "a" "b" ]` lands on `the-walked-node`;
  # indexing the last segment lands on the unrelated node keyed `b`. The two rules disagree BY
  # CONSTRUCTION, which is what makes the control total over every library rather than over the ones
  # whose own lock happens to disagree. It is a literal: nothing here reads a file or fetches.
  followsFixture = {
    root = "root";
    nodes = {
      root.inputs = {
        a = "a-node";
        elsewhere = "the-walked-node";
      };
      a-node.inputs.b = [ "elsewhere" ];
      the-walked-node.locked.repo = "gen-walked";
      b.locked.repo = "gen-indexed";
    };
  };

  # ★★ THE SHIM'S `wire` DEFAULT, COUNTED AS TEXT. `[[:space:]]` spans the newline a formatter may
  # put anywhere inside the default, and COMMENTS ARE STRIPPED FIRST — load-bearing here rather than
  # prophylactic, because the shim's own prose quotes this default, so an unstripped scan keeps
  # reading 1 on a file whose CODE has been rewired. Bound once and read by BOTH cells below: two
  # literals spelled the same are two predicates, and the control would then guard only its own copy.
  wireNeedle = ''wire[[:space:]]*\?[[:space:]]*[{][[:space:]]*deps[[:space:]]*,[[:space:]]*resolve[[:space:]]*[}][[:space:]]*:[[:space:]]*import[[:space:]]+\./lib[[:space:]]+deps[[:space:]]*,'';
  countWire =
    text:
    builtins.length (
      builtins.filter builtins.isList (
        builtins.split wireNeedle (
          builtins.concatStringsSep "" (builtins.filter builtins.isString (builtins.split "#[^\n]*" text))
        )
      )
    );

  # ★★ THE READER IS BOUND, NOT ITS READING, AND THAT IS THE FIRST CONJUNCT OF THE ARMING RULE
  # RATHER THAN THE WHOLE OF IT. A bound READING (`shimFormals = builtins.attrNames
  # (builtins.functionArgs (import ../..))`) has no free parameter, so its control has nowhere else
  # to exercise it and can only re-assert the main arm's own value: MEASURED, that shape reads
  # `10/10 successful, exit 0` under the very tamper it exists to catch. Binding the READER is what
  # makes the control's DIFFERENT INPUT expressible at all.
  formalsOf = f: builtins.attrNames (builtins.functionArgs f);

  # ★ THE SECOND NEEDLE, bound once and read by both arms below for the same reason `needle` is.
  # `[[:space:]]*` spans the newline a formatter may put between `../..` and `{`. It does not match
  # `formalsOf (import ../..)` (a `)` follows, not a `{`) nor a path one segment longer (a `/`
  # follows), so the one thing it counts is an entry application to a literal.
  entryNeedle = ''\.\./\.\.[[:space:]]*\{'';
  countEntry =
    text: builtins.length (builtins.filter builtins.isList (builtins.split entryNeedle text));
in
{
  flake.tests.entry.test-standalone-entry-constructs-its-siblings =
    let
      chain = entry.mkProgram {
        rules = [
          { head = "a0"; }
          {
            head = "a1";
            pos = [ "a0" ];
          }
        ];
      };
      minted = entry.mintStrata {
        emitters = [
          {
            pass = 0;
            identifier = "a";
            kind = "widget";
            relata = { };
            content = { };
            site = "s";
          }
        ];
        kinds = {
          widget = { };
        };
      };
    in
    {
      expr = {
        prelude = (entry.mkProgram { rules = [ { head = "a"; } ]; }).atoms;
        graph =
          (entry.solve {
            program = chain;
            interpretation = [ ];
          }).condensationDepth;
        # ★ THE PREFIX, NOT `isString` — a corrupted `hashIdentity` returning a constant string of
        # the wrong shape (e.g. `""`) would still satisfy `isString`. `mint.nix`'s own IDENTITY
        # vocabulary states the output shape as `"<kind>:" + digest`; the prefix is what a caller
        # of gen-identity's authority actually observes and is what a corruption there disturbs.
        identity = builtins.substring 0 7 minted.nodes.a.identity;
      };
      expected = {
        prelude = [ "a" ];
        graph = 1;
        identity = "widget:";
      };
    };

  # ★ THE CELL ABOVE CANNOT SEE THIS CLASS, and the reason is the property that makes it hermetic: it
  # supplies every dependency formal explicitly, so the shim's `fetch`-backed DEFAULTS — which is
  # where the divergence lives — are never forced. Forcing them would put `builtins.fetchTree` inside
  # the suite. This cell reads the CONSTRUCTION instead of the outcome, which is strictly wider: it
  # also catches the member that never throws (a defaulted formal on the far side turns the loud arm
  # of the class silent) and the member that has not yet drifted.
  #
  # ★★ COMMENTS ARE STRIPPED FIRST, AND THAT IS LOAD-BEARING RATHER THAN TIDY. `ci/tests/purity.nix`
  # states the same property for the same reason and over this same file: the house convention for a
  # FIXED member is a comment explaining why not `/lib`, and a raw scan reds on that comment while
  # the file is correct. The strip is PROPHYLACTIC — it stops the next correctly-written comment from
  # reddening a correct file.
  #
  # ★ `[[:space:]]*` spans the newline a formatter may put between `/lib"` and `{` — measured: a
  # line-anchored form misses exactly that.
  #
  # ★★ THE NEEDLE IS BOUND ONCE AND BOTH CELLS READ THAT BINDING. Two literals spelled the same are
  # TWO PREDICATES, and the control would then guard only its own copy.
  flake.tests.entry.test-no-dependency-is-built-past-its-own-entry =
    let
      parts = builtins.split needle (stripComments (builtins.readFile ../../default.nix));
    in
    {
      expr = {
        count = builtins.length (builtins.filter builtins.isList parts);
        reaches = map builtins.head (
          builtins.filter (m: m != null) (
            map (p: builtins.match ''.*"(gen-[a-z-]+)"[[:space:]]*]$'' p) (
              builtins.filter builtins.isString parts
            )
          )
        );
      };
      expected = {
        count = 0;
        reaches = [ ];
      };
    };

  # ★★ THE DETECTOR IS SHOWN ABLE TO FIRE, IN THE SAME RUN, ON THE SAME PREDICATE. Without it,
  # `count = 0` is equally consistent with a needle that cannot match.
  flake.tests.entry.test-control-the-entry-shape-check-discriminates = {
    expr = builtins.length (
      builtins.filter builtins.isList (
        builtins.split needle (stripComments ''
          {
            graph ? import "''${fetch "gen-graph"}/lib"
              { inherit prelude; },
          }: null
        '')
      )
    );
    expected = 1;
  };

  # ★★★ THE HERMETICITY OF THIS CELL BECOMES AN INVARIANT HERE, AND IT TAKES TWO CELLS BECAUSE THEY
  # ANSWER DIFFERENT QUESTIONS. Everything above is offline only because the argument set happens to
  # supply every `fetch`-backed formal, and that was a property of the file's TEXT which nothing
  # asserted. The broken state would look exactly like the correct one without an invariant rather
  # than one more reading of it.
  #
  # ★★ THE OBLIGATION IS TOTAL — every formal the shim DECLARES. "Harmless" is not a property of a
  # formal but of its DEFAULT EXPRESSION, which changes without notice.
  #
  # ★ IT IS HERMETIC, MEASURED: `builtins.functionArgs` does not force defaults. Reading a signature
  # never reaches the network.
  #
  # ★ EQUALITY, NOT CONTAINMENT: a key the shim does not declare would be accepted, unread and
  # unreported under `...`, so containment would pass a stale key forever. Equality reds on it,
  # loudly, naming it.
  flake.tests.entry.test-the-entry-application-is-total = {
    expr = formalsOf (import ../..);
    expected = builtins.attrNames entryArgs;
  };

  # ★★★ AN ARMED PAIR IS A CONJUNCTION: the two arms SHARE the operand (`formalsOf`), AND the control
  # exercises that operand AT AN INPUT THE MAIN ARM DOES NOT USE. Either half alone detects nothing.
  #
  # ★ THE FIXTURE NAMES `a` AND `b`, which are the formals of a lambda THIS CELL WRITES and no shim
  # supplies. That is the different input, not an exception to "no formal OF THE SHIM is hardcoded":
  # a control written to avoid every literal name would have to reach for the shim's own formals,
  # which puts it at the main arm's input and makes it blind.
  flake.tests.entry.test-control-the-formals-reader-discriminates = {
    expr = formalsOf (
      {
        a,
        b ? null,
      }:
      null
    );
    expected = [
      "a"
      "b"
    ];
  };

  # ★★ THE STRUCTURAL CELL — the one the semantic instrument above cannot replace, because the edit
  # that reintroduces the defect is the same edit that removes the semantic instrument. It reads THIS
  # file's own text and refuses the bare application outright, so the property survives tomorrow's
  # edit instead of describing today's.
  #
  # ★★ COMMENTS ARE STRIPPED FIRST, AND ACROSS THIS DOMAIN THAT IS LIVE RATHER THAN PROPHYLACTIC.
  flake.tests.entry.test-the-entry-is-never-applied-to-a-literal = {
    expr = countEntry (stripComments (builtins.readFile ./entry.nix));
    expected = 0;
  };

  # ★★ THE FIXTURE IS ASSEMBLED, AND THAT IS THE MECHANISM RATHER THAN A FLOURISH. The cell above
  # reads THIS FILE, unlike `needle`'s cell which reads the shim — so a fixture written as a plain
  # literal would appear in the very text the main arm scans and red it.
  flake.tests.entry.test-control-the-literal-application-check-discriminates = {
    expr = countEntry ("  entry = import ../" + ".. { };");
    expected = 1;
  };

  # ★★★ THE DEFAULT ITSELF — the cell this suite is otherwise blind to by the property that makes the
  # cells above hermetic. `entry` supplies every dependency formal, so the shim's `ci/flake.lock`-backed
  # defaults never fire there; nothing is supplied here.
  #
  # ★★ THE CALL IS ARITY-DISPATCHED, NOT `import ../.. { }`. A dependency-free library publishes its
  # root as a bare VALUE rather than a function, so the literal application is wrong at those roots by
  # design; the dispatch below is the one form total over the roster, and it is the same construct the
  # shim's own `dep` uses. ★ It also keeps the structural cell above honest: the dispatch reads
  # `import ../..` UNAPPLIED, which the literal-application needle does not count.
  flake.tests.entry.test-the-defaulted-entry-publishes-the-flake-surface =
    let
      root = import ../..;
      dispatched = if builtins.isFunction root then root { } else root;
    in
    {
      expr = builtins.attrNames dispatched;
      expected = builtins.attrNames genScope;
    };

  # ★★ EVERY WIRED DEPENDENCY RESOLVES, AND RESOLVES TO A NODE OF ITS OWN REPOSITORY. The shim states
  # its intent as a PATH; this resolves that path through the same lock by the same rule and asks
  # which repository the node it lands on belongs to. A path repointed at a live-but-wrong dependency
  # reds here, naming the formal and the repository it reached. It is HERMETIC: `pathArgs` closes
  # `dep`, so the map is read and resolved without a fetch.
  #
  # ★ STATED CEILING: `locked.repo` is neither `owner` nor node identity. A same-named repository
  # under another owner passes, and so does a path repointed at a DIFFERENT NODE of the right
  # repository. Recorded open rather than repaired.
  flake.tests.entry.test-every-wired-dependency-defaults-to-its-own-node = {
    expr = builtins.mapAttrs (_: repoOf lock) paths;
    expected = builtins.mapAttrs (formal: _: "gen-" + formal) paths;
  };

  # ★★★ THE DISCRIMINATING HALF OF THE CELL ABOVE — and for the `follows` rule it is the whole
  # oracle, not a supplement to one, because the rule has ONE declaration and `repoOf` is built over
  # it. The two arms SHARE `repoOf`, hence share `shimResolve`, hence share `default.nix`'s own fold;
  # this one exercises it AT AN INPUT THE MAIN ARM DOES NOT USE — a hand-written lock whose path walk
  # and whose last-segment shortcut land on different nodes by construction. Transcribed verbatim
  # rather than simplified, and MEASURED rather than assumed: with the resolver corrupted in place to
  # the last-segment shortcut, `repoOf lock ["gen-prelude"]` (the cell above) stayed GREEN — the
  # shortcut node and the walked node are both real `gen-prelude` revisions, so `locked.repo` reads
  # "gen-prelude" either way, and the cell above cannot see a same-repo different-revision divergence
  # by construction (its own stated ceiling) — while this fixture cell, whose two candidate nodes
  # carry DIFFERENT repo names, went RED on the same corruption in the same run. So at THIS library
  # the fixture is not redundant with the cell above, it is the ONLY one of the two that discriminates
  # the resolver rule at all; a second RED-drive repointing the `prelude` FORMAL itself at the wrong
  # dependency (`dep ["gen-graph"]`) confirmed the cell above does its own, different job — catching a
  # formal wired to the wrong sibling entirely — which the fixture cell does not cover.
  flake.tests.entry.test-control-the-follows-resolver-discriminates = {
    expr = repoOf followsFixture [
      "a"
      "b"
    ];
    expected = "gen-walked";
  };

  # ★★ THE DENOMINATOR, TAKEN INDEPENDENTLY — without it the cell above is vacuous over an empty map.
  # `paths` is what the root WIRES; `functionArgs (import ../../lib)` is what the library REQUIRES,
  # read from a different file by a different builtin. A dependency dropped from the shim's body reds
  # here even though every surviving path still resolves.
  flake.tests.entry.test-the-wired-dependency-set-is-the-libs-own-formals = {
    expr = builtins.attrNames paths;
    expected = builtins.attrNames (builtins.functionArgs (import ../../lib));
  };

  # ★★★ THE DEFAULT FORCED — the one cell in this file that is NOT hermetic. Forcing it IS
  # `builtins.fetchTree`: the accepted price of measuring the non-flake contract at all, and it
  # remains PURE, because `fetchTree` on a locked node is narHash-addressed with no channel and no
  # `<…>`. `builtins.seq` of the dispatched root runs the shim's eager body, which forces every wired
  # dependency to WHNF before `./lib` sees it, so a nonexistent node, an unresolvable follows path or
  # a throwing root is loud at the BOUNDARY rather than wherever a consumer first happens to reach it.
  #
  # ★ THE FORCE STOPS AT WHNF, DELIBERATELY: `seq` of an attrset does not force its members, so this
  # never reaches into a dependency's own surface — `schema` included.
  flake.tests.entry.test-the-defaulted-entry-forces-every-dependency =
    let
      root = import ../..;
      dispatched = if builtins.isFunction root then root { } else root;
    in
    {
      expr = builtins.seq dispatched "forced";
      expected = "forced";
    };

  # ★★★ THE SHIM'S OWN `wire` DEFAULT, AND IT IS WHAT EVERY HERMETIC CELL ABOVE RESTS ON. `paths` is
  # the `deps` half of the record the shim's body hands to `wire` — it is the attrset `./lib`
  # RECEIVES only while `wire`'s own default is `{ deps, resolve }: import ./lib deps`, and no cell
  # above reads that default: the two hermetic cells REPLACE `wire` with `args: args`, the forcing
  # cell stops at WHNF of whatever `wire` returned, and the surface cell compares `attrNames`, which
  # `./lib`'s structure fixes independently of its arguments.
  #
  # ★★ THE READING IS IRREDUCIBLY TEXTUAL, AND THAT IS THE SEAM'S OWN REASON FOR EXISTING: Nix
  # publishes WHETHER a formal has a default and never WHAT it is, so there is no semantic
  # construction to compare against.
  flake.tests.entry.test-the-wire-default-is-the-librarys-own-application = {
    expr = countWire (builtins.readFile ../../default.nix);
    expected = 1;
  };

  # ★★★ THE DISCRIMINATING HALF, IN THREE ARMS BECAUSE THE PREDICATE HAS THREE WAYS TO BE DEAD. Both
  # cells read the one `countWire` binding, and this one exercises it AT AN INPUT THE MAIN ARM DOES
  # NOT USE — assembled fixtures, never `../../default.nix`. `exact` proves it can count the real
  # default at all; `rewired` proves it refuses the one-token corruption the main arm exists to catch;
  # `commented` proves the comment strip is LIVE.
  flake.tests.entry.test-control-the-wire-default-check-discriminates = {
    expr = {
      exact = countWire "wire ? { deps, resolve }: import ./lib deps,";
      rewired = countWire ''wire ? { deps, resolve }: import ./lib (deps // { x = throw "no"; }),'';
      commented = countWire ''
        # wire ? { deps, resolve }: import ./lib deps,
        wire ? { deps, resolve }: import ./lib (deps // { }),
      '';
    };
    expected = {
      exact = 1;
      rewired = 0;
      commented = 0;
    };
  };

  # ★★★ CHANNEL 2 — THE `inputs` OVERRIDE BAG. The shim declares three channels and one precedence: a
  # named formal wins, the bag is next, tested by attrset membership, and the ci lock is the default.
  # Every cell above exercises the LOCK, so a formal transcribed as `x ? dep [ … ]` instead of
  # `x ? inputs.gen-x or (dep [ … ])` leaves its override silently ignored.
  #
  # ★★ TOTAL OVER THE WIRED SET BY CONSTRUCTION. `expr` and `expected` are both derived from `paths`,
  # so the domain is whatever the root wires and never a hand-written list, and the denominator is
  # taken independently by `…-is-the-libs-own-formals`, so an empty map cannot read as a pass.
  flake.tests.entry.test-the-inputs-bag-overrides-every-wired-default =
    let
      overrides = builtins.mapAttrs (formal: _: "the ${formal} override, from the inputs bag") paths;
      bag = builtins.listToAttrs (
        map (formal: {
          name = "gen-" + formal;
          value = overrides.${formal};
        }) (builtins.attrNames paths)
      );
    in
    {
      expr = (import ../.. (pathArgs // { inputs = bag; })).deps;
      expected = overrides;
    };
}
