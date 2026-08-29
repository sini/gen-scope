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

  standalone = import ../.. {
    prelude = genPreludeLib;
    graph = genGraph;
    schema = genSchema;
    identity = genIdentity;
  };
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
}
