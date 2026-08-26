# THE PER-PROCESS RUNNER — a check that evaluates each cell in `tests-process-cells.nix` in its
# OWN evaluator process and asserts on the EXIT STATUS and the printed value.
#
# ★ WHY A CHECK DERIVATION AND NOT A THIRD nix-unit OUTPUT. Every cell here observes an abort
# `tryEval` does not catch — an uncatchable death takes a whole evaluation down, so any suite
# hosting one of these cells would lose every other cell in the same process. The runner invokes
# `nix-instantiate --eval` once per arm inside the build sandbox (pure evaluation needs no store
# access; sources arrive as derivation inputs), so the isolation is per-process by construction
# and the whole thing rides `nix flake check` — the same gate CI already runs — rather than a
# side instrument someone must remember to invoke.
#
# ★ THE `hctl2` ARM PATCHES A COPY OF THE LIBRARY, AND THE PATCH IS ASSERTED TO LAND EXACTLY
# ONCE. The shadow ladder's seed — `shadow[1] = levelsRaw[1]` — is legal only because
# `levelsChecked[0]` IS `bottoms`, so `levelsRaw[1]` carries no seat in its transitive
# dependency. The control moves the seed one level up (`levelsRaw[2]`, whose checked predecessor
# CARRIES seats) and must die `infinite recursion encountered`: the seed LEVEL is load-bearing,
# and if a later revision ever seats level 0, the shipped seed becomes this arm's shape — this
# cell is what says so loudly. Its live control is the `lrp2-ctl` cell above it: the SAME
# fixture, the unpatched library, answering 3.
{ inputs, ... }:
{
  perSystem =
    { pkgs, ... }:
    {
      checks.tests-process =
        pkgs.runCommand "gen-scope-tests-process"
          {
            nativeBuildInputs = [ pkgs.nix ];
            cells = ./tests-process-cells.nix;
            libSrc = ../lib;
            genPreludeSrc = inputs.gen-prelude;
            genGraphSrc = inputs.gen-graph;
          }
          ''
            export NIX_STATE_DIR=$TMPDIR/nix-state NIX_LOG_DIR=$TMPDIR/nix-log
            ran=0
            die() {
              echo "tests-process: FAILED at cell $1: $2" >&2
              exit 1
            }
            # evalArm <arm> <libdir>: runs one cell in its own process; leaves rc/val set. The
            # value variable is `val`, never `out` — `out` is the derivation's own output path.
            evalArm() {
              rc=0
              val=$(nix-instantiate --eval --strict --readonly-mode \
                --argstr arm "$1" \
                --argstr genPreludeSrc "$genPreludeSrc" \
                --argstr genGraphSrc "$genGraphSrc" \
                --argstr libSrc "$2" \
                "$cells" 2> "$TMPDIR/err") || rc=$?
              ran=$((ran + 1))
            }
            answers() { # <arm> <libdir> <value>: exit 0 and exactly the hand-derived answer
              evalArm "$1" "$2"
              [ "$rc" -eq 0 ] || die "$1" "expected exit 0, got $rc"
              [ "$val" = "$3" ] || die "$1" "expected value $3, got '$val'"
            }
            diesAnonymously() { # <arm> <libdir>: non-zero exit, division by zero, NO named refusal
              evalArm "$1" "$2"
              [ "$rc" -ne 0 ] || die "$1" "expected a death, got exit 0 with '$val'"
              grep -q 'division by zero' "$TMPDIR/err" || die "$1" "death is not the division-by-zero channel"
              if grep -q 'gen-scope:' "$TMPDIR/err"; then
                die "$1" "death is NOT anonymous — a named refusal fired"
              fi
            }
            traceCount() { # <arm> <n>: the F1 probe fired exactly n times
              n=$(grep -c 'trace: F1-PROBE' "$TMPDIR/err" || true)
              [ "$n" = "$2" ] || die "$1" "expected $2 F1-PROBE firing(s), saw $n"
            }

            # A27 cell 2 — the D ∖ N measurement: (D3)'s completion reaches the poisoned q and
            # the answer becomes an anonymous uncatchable abort. Built TO FIRE.
            diesAnonymously lrp2 "$libSrc"
            # LATEREAD-CTL — same wiring, total late step: the walk completes and answers.
            answers lrp2-ctl "$libSrc" 3
            # UNDEMERR — a member the demand reaches at no level has its step applied at no level.
            answers undemerr "$libSrc" 2

            # The (F1) residual pair, trace arms: the clamp at the first live transition forces
            # shadow[f(m) − 1] — the probe fires exactly once on the descending arm and never on
            # the monotone twin, at the same answer.
            answers f1-trace "$libSrc" 3
            traceCount f1-trace 1
            answers f1-trace-ctl "$libSrc" 3
            traceCount f1-trace-ctl 0
            # The (F1) residual pair, div arms: the same below-f(m) coordinate poisoned — the
            # descent turns answer 3 into an anonymous abort; the monotone twin never reads it.
            diesAnonymously f1-div "$libSrc"
            answers f1-div-ctl "$libSrc" 3

            # hctl2 — the seed-level control. Patch a copy of lib/, assert the patch landed
            # exactly once, and require the mis-seeded ladder to die by infinite recursion.
            cp -r "$libSrc" lib-patched
            chmod -R u+w lib-patched
            if grep -q 'elemAt levelsRaw 2' lib-patched/eval.nix; then
              die hctl2 "patch target already present"
            fi
            sed -z -i 's/if j == 1 then\(\s*\)builtins\.elemAt levelsRaw 1/if j == 2 then\1builtins.elemAt levelsRaw 2/' lib-patched/eval.nix
            n=$(grep -c 'elemAt levelsRaw 2' lib-patched/eval.nix || true)
            [ "$n" = "1" ] || die hctl2 "patch landed $n times, wanted exactly 1"
            evalArm lrp2-ctl "$PWD/lib-patched"
            [ "$rc" -ne 0 ] || die hctl2 "mis-seeded ladder answered '$val' — the seed level is not load-bearing"
            grep -q 'infinite recursion' "$TMPDIR/err" || die hctl2 "death is not the infinite-recursion channel"

            # 0/0 is a false pass: the runner must have executed every cell above.
            [ "$ran" = "8" ] || die runner "expected 8 evaluations, ran $ran"
            echo "tests-process: 8 cells, every exit read unpiped, every death on its named channel" > $out
          '';
    };
}
