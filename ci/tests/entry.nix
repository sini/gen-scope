# THE STANDALONE ROOT ENTRY — the plain-import path, which no other cell in this suite reaches.
#
# ★ WHY THIS FILE EXISTS. Every other suite here builds the library by importing `../lib` directly
# with injected values, so the ROOT `default.nix` — the entry a non-flake consumer actually uses —
# is evaluated by nothing. A shim can therefore forward fewer arguments than the library it
# delegates to, promise lockstep with the flake in its own comment, and stay green forever: the
# flake path and the plain-import path are two signatures with nothing comparing them, so the second
# one rots silently the first time `lib/default.nix` grows a formal.
#
# ★★ THE CELL IS PURE, AND THE PURITY IS A CONSEQUENCE OF HOW IT IS CALLED. The shim's defaults
# `builtins.fetchTree` the flake-locked revs; supplying EVERY dependency formal explicitly means
# those defaults are never forced, so this reaches the network not at all. What it tests is the
# shim's SIGNATURE and its delegation — which is precisely where the defect lives.
#
# ★ WHICH DIRECTION OF THE DRIFT THIS CATCHES HERE, stated because this shim's formals end in an
# ellipsis and that changes the answer. A shim that FORWARDS fewer arguments than `lib` requires is
# refused inside it (`called without required argument 'schema'`), and that is the direction this
# cell arms. The other direction — a shim naming fewer FORMALS than it is applied with — is
# swallowed by the `...` rather than refused by name, so an argument this cell passes and the shim
# does not name goes unread and surfaces as an unbound variable in the delegation instead. Both are
# uncatchable evaluator refusals, so either turns this cell ☢️ rather than ❌ — a crash is the
# loudest reading available and is the right one for an entry point that does not exist.
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

  # ★★ THE ARGUMENT SET IS BOUND ONCE, AND BOTH THE APPLICATION AND THE TOTALITY CELL READ THIS
  # BINDING — `needle`'s rule above, carried to the argument set. Two literals spelled the same are
  # TWO PREDICATES, and the totality cell would then be comparing the shim against a copy nothing
  # applies.
  entryArgs = {
    prelude = genPreludeLib;
    graph = genGraph;
    schema = genSchema;
    identity = genIdentity;
  };

  standalone = import ../.. entryArgs;

  # ★★ THE READER IS BOUND, NOT ITS READING, AND THAT IS THE FIRST CONJUNCT OF THE ARMING RULE
  # RATHER THAN THE WHOLE OF IT. A bound READING (`shimFormals = builtins.attrNames
  # (builtins.functionArgs (import ../..))`) has no free parameter, so its control has nowhere else
  # to exercise it and can only re-assert the main arm's own value: MEASURED, that shape reads
  # `10/10 successful, exit 0` under the very tamper it exists to catch. Binding the READER is what
  # makes the control's DIFFERENT INPUT expressible at all.
  formalsOf = f: builtins.attrNames (builtins.functionArgs f);

  # ★ THE SECOND NEEDLE, bound once and read by both arms below for the same reason `needle` is.
  # `[[:space:]]*` spans the newline a formatter may put between `../..` and `{`. It does not match
  # `formalsOf (import ../..)` (a `)` follows, not a `{`) nor `import ../../examples/…` (a `/`
  # follows), so the one thing it counts is an entry application to a literal.
  entryNeedle = ''\.\./\.\.[[:space:]]*\{'';
  countEntry =
    text: builtins.length (builtins.filter builtins.isList (builtins.split entryNeedle text));
in
{
  # ★ The assertion is over the APPLIED surfaces, not over the entries themselves: both are
  # functions of their injected substrate, and two Nix lambdas are never equal — so `entry == entry`
  # would read `false` on a correct library and could not distinguish drift from the language. The
  # applied form is also the stronger claim: it is the surface a consumer actually receives.
  flake.tests.entry.test-standalone-entry-matches-lib = {
    expr = builtins.attrNames standalone;
    expected = builtins.attrNames genScope;
  };

  # The surface is not merely equal but non-trivial, so the cell above cannot pass by both sides
  # being empty.
  flake.tests.entry.test-control-the-compared-surface-is-non-trivial = {
    expr = builtins.length (builtins.attrNames standalone) > 50;
    expected = true;
  };

  # ★ THE COMPARISON IS SHOWN ABLE TO FAIL, in the same run. Without this, an `attrNames` equality
  # between two values that happen to be the same import is a tautology nobody has checked.
  flake.tests.entry.test-control-the-comparison-discriminates = {
    expr = builtins.attrNames standalone == builtins.attrNames (removeAttrs genScope [ "eval" ]);
    expected = false;
  };

  # And the library reached THROUGH the shim actually works, rather than merely having the right
  # keys — a delegation that forwarded the wrong value would satisfy an `attrNames` check. This one
  # builds an algebraic graph and queries it, so the construction runs rather than merely being
  # named.
  flake.tests.entry.test-the-shims-library-is-live = {
    expr = standalone.hasVertex "a" (standalone.vertex "a");
    expected = true;
  };

  # ★ THE FOUR CELLS ABOVE CANNOT SEE THIS CLASS, and the reason is the property that makes them
  # hermetic: they supply every dependency formal explicitly, so the shim's `fetch`-backed DEFAULTS —
  # which is where the divergence lives — are never forced. Forcing them would put `builtins.fetchTree`
  # inside the suite. This cell reads the CONSTRUCTION instead of the outcome, which is strictly wider:
  # it also catches the member that never throws (a defaulted formal on the far side turns the loud arm
  # of the class silent) and the member that has not yet drifted.
  #
  # ★★ COMMENTS ARE STRIPPED FIRST, AND THAT IS LOAD-BEARING RATHER THAN TIDY. `ci/tests/purity.nix`
  # states the same property for the same reason and over this same file (`stripComments (builtins.readFile
  # ../../default.nix)`): the house convention for a FIXED member is a comment explaining why not `/lib`,
  # and a raw scan reds on that comment while the file is correct. MEASURED, in-suite, on a tree whose
  # member had just been fixed — with a comment PLANTED in the house idiom, because no live site reds
  # today: every existing such comment happens to write `` `./lib` `` (relative, uninterpolated), and
  # raw ≡ stripped across all 14 domain files at HEAD. The strip is PROPHYLACTIC, and that is the
  # point — it stops the next correctly-written comment from reddening a correct file.
  #
  # ★ `[[:space:]]*` spans the newline a formatter may put between `/lib"` and `{` — measured: a
  # line-anchored form misses exactly that.
  #
  # ★★ THE NEEDLE IS BOUND ONCE AND BOTH CELLS READ THAT BINDING. Two literals spelled the same are
  # TWO PREDICATES, and the control would then guard only its own copy: MEASURED — with the needle
  # duplicated, breaking the MAIN copy by one character gave `2/2 successful, exit 0` over a tree
  # carrying a real member, with the control still ✅ in the same run. That is §1.5's class — a second
  # signature nothing compares against the first — committed by the instrument built to detect it.
  # With the shared binding the same one-character break REDS THE CONTROL.
  #
  # ★ A bare `.../lib` with NO argument set is EXCLUDED, and the exclusion is a claim about the FAR SIDE
  # AT ITS PIN rather than about this file: it holds only while the target's `lib` is a value. All
  # nineteen such sites in this domain reach gen-prelude / gen-identity / gen-algebra, each measured
  # `"set"` 2026-08-29. It is NOT a property of the spelling — `den-hoag-jhsb` measured
  # `select ? import "${fetch "gen-select"}/lib"` in gen-pipe yielding a LAMBDA (gen-select's `lib` takes
  # `{ algebra }`), a silent member this predicate does not count — and this cell cannot observe its own
  # premise going false. See §4.4.
  flake.tests.entry.test-no-dependency-is-built-past-its-own-entry =
    let
      parts = builtins.split needle (stripComments (builtins.readFile ../../default.nix));
    in
    {
      # ★ THE ASSERTION IS ON THE COUNT. `reaches` is a diagnostic so a failure names the dependency,
      # but it is derived by a second match that a non-`fetch` spelling defeats — asserting on names
      # alone would read `[ ]` on a real member and pass.
      expr = {
        count = builtins.length (builtins.filter builtins.isList parts);
        reaches = map builtins.head (
          builtins.filter (m: m != null) (
            map (p: builtins.match ''.*fetch "(gen-[a-z-]+)"$'' p) (builtins.filter builtins.isString parts)
          )
        );
      };
      expected = {
        count = 0;
        reaches = [ ];
      };
    };

  # ★★ THE DETECTOR IS SHOWN ABLE TO FIRE, IN THE SAME RUN, ON THE SAME PREDICATE — `purity.nix`'s
  # standing rule and `den-hoag-e421`'s landed remedy. Without it, `count = 0` is equally consistent
  # with a needle that cannot match: MEASURED — one character changed in the needle reads
  # `{ count = 0; reaches = [ ]; }` on a file carrying three real members, i.e. byte-identical to this
  # cell's own `expected`. The planted member is REFLOWED, so it also pins the `[[:space:]]*` span.
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
  # asserted. MEASURED before these two cells existed: with the bare form seeded and nothing else
  # touched, the whole entry suite passed, exit 0. The broken state looked exactly like the correct
  # one, which is why the property needs an invariant rather than one more reading of it.
  #
  # ★★ THE SEMANTIC INSTRUMENT CANNOT CARRY A FILE-LEVEL CLAIM, and that is measured rather than
  # argued: with this totality cell in place and the application rewritten to a literal, the totality
  # cell reads GREEN — it is still checking a binding that nothing applies — and the `fetch` throw
  # goes with the argument set that carried it. The structural cell below is the only detector left,
  # which is why neither cell is ceremony for the other.
  #
  # ★★ THE OBLIGATION IS TOTAL — every formal the shim DECLARES, never "the `fetch`-backed ones" and
  # never "the harmless defaults". "Harmless" is not a property of a formal but of its DEFAULT
  # EXPRESSION, which changes without notice: `lock` is the most obviously harmless formal on this
  # roster and it is the source of every fetch coordinate in the shims that declare it. A rule that
  # supplied only the fetch-backed formals would have to re-derive harmlessness at every shim edit,
  # or freeze a name list — a second signature nothing compares against the first. Totality needs no
  # classification at all, so the bad state cannot form rather than being filtered after it does.
  #
  # ★ IT IS HERMETIC, MEASURED: `builtins.functionArgs` does not force defaults —
  # `builtins.functionArgs ({ a ? throw "FORCED", b }: null)` reads `{ a = true; b = false; }` with
  # no throw. Reading a signature never reaches the network.
  #
  # ★ EQUALITY, NOT CONTAINMENT, because six of the fourteen shims in this domain carry `...`: there
  # a key the shim does not declare is accepted, unread and unreported, so containment would pass a
  # stale key forever. Equality reds on it, loudly, naming it.
  flake.tests.entry.test-the-entry-application-is-total = {
    expr = formalsOf (import ../..);
    expected = builtins.attrNames entryArgs;
  };

  # ★★★ AN ARMED PAIR IS A CONJUNCTION: the two arms SHARE the operand (`formalsOf`), AND the control
  # exercises that operand AT AN INPUT THE MAIN ARM DOES NOT USE. Either half alone detects nothing,
  # and both halves were driven one variable at a time by neutering the shared operand — operand
  # spelled twice, control at a different input: `10/10`, exit 0, UNDETECTED; operand shared, control
  # moved to the main arm's own input (`formalsOf (import ../..)`): `10/10`, exit 0, UNDETECTED;
  # operand shared AND control at a different input: `9/10`, exit 1, THIS cell ❌. Known-answer versus
  # relative is not the axis — a relative control at a different input catches the same tamper.
  #
  # ★ THE FIXTURE NAMES `a` AND `b`, which are the formals of a lambda THIS CELL WRITES and no shim
  # supplies. That is the different input, not an exception to "no formal OF THE SHIM is hardcoded":
  # a control written to avoid every literal name would have to reach for the shim's own formals,
  # which puts it at the main arm's input and makes it blind. Its literal expectation is convenience;
  # the different input is the mechanism.
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
  # MEASURED over the fourteen files carrying this cell: three of them quote the bare application in
  # prose, so an unstripped scan reads 1 there and reds a correct file; the other eleven read 0
  # either way. The strip is what stops the next correctly-written comment — this one included —
  # from reddening the file it explains.
  flake.tests.entry.test-the-entry-is-never-applied-to-a-literal = {
    expr = countEntry (stripComments (builtins.readFile ./entry.nix));
    expected = 0;
  };

  # ★★ THE FIXTURE IS ASSEMBLED, AND THAT IS THE MECHANISM RATHER THAN A FLOURISH. The cell above
  # reads THIS FILE, unlike `needle`'s cell which reads the shim — so a fixture written as a plain
  # literal would appear in the very text the main arm scans and red it. MEASURED, both arms: the
  # assembled form's VALUE matches (1) while its own SOURCE BYTES do not (0); the naive literal's
  # source bytes match (1) and red the correct file.
  flake.tests.entry.test-control-the-literal-application-check-discriminates = {
    expr = countEntry ("  standalone = import ../" + ".. { };");
    expected = 1;
  };
}
