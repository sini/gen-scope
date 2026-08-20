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
  ...
}:
let
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
}
