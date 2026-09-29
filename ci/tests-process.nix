# THE PER-PROCESS RUNNER — a program that evaluates each cell in `tests-process-cells.nix` in its
# OWN evaluator process and asserts on the EXIT STATUS and the printed value.
#
# ★ WHY A PROGRAM AND NOT A THIRD nix-unit OUTPUT. Every cell here observes an abort `tryEval` does
# not catch. nix-unit catches such an abort per cell in its own C++ loop and a sibling cell survives
# it (measured: den-hoag-n6dh7 fix round), so the reason is not that a hosting suite would lose its
# other cells; it is the verdict's SHAPE — an exit status, a Nix channel on stderr and the ABSENCE of
# a named refusal, which is a process predicate and this runner's own.
#
# ★ WHY A PROGRAM AND NOT A CHECK. The verdicts are an evaluator's abort channels, so they are
# evidence only for the evaluator that computed them. Inside a build sandbox that evaluator is a
# derivation input — one drvPath, one verdict, in every CI column (den-hoag-jutgv). As
# `apps.<system>.tests-process` the cells call the `nix-instantiate` on PATH, and gen-harness's
# `ci --tests-process` runs it in every column of `evaluators.yml`, refusing a program whose closure
# carries an evaluator — so none may enter it. Locally:
#   nix develop ./ci --command ci --tests-process
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
      apps.tests-process.program = pkgs.writeShellScriptBin "tests-process" (
        ''
          set -e
          # The tools the body calls, declared rather than ambient — and never an evaluator.
          export PATH=${
            pkgs.lib.makeBinPath [
              pkgs.coreutils
              pkgs.gnugrep
              pkgs.gnused
            ]
          }:$PATH
          export cells=${./tests-process-cells.nix} libSrc=${../lib}
          export genPreludeSrc=${inputs.gen-prelude} genGraphSrc=${inputs.gen-graph}
          # A FRESH working directory per run: the `hctl2` arm copies lib/ into the CWD, and a second
          # run in the same directory finds the first run's patched copy (measured, den-hoag-jutgv).
          TMPDIR=$(mktemp -d) out=$(mktemp)
          export TMPDIR out
          trap 'rm -rf "$TMPDIR" "$out"' EXIT
          cd "$TMPDIR"
          # The evaluator the cells run under, from this process and the binary they call.
          echo "evaluator: $(nix-instantiate --version | sed -n 1p)"
        ''
        + ''
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
            val=$(nix-instantiate --eval --strict --readonly-mode ''${3:+"$3"} \
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
          # <arm> <libdir> <node>: non-zero exit, division by zero, AND the outer seat's
          # context line naming the node — the positive twin of diesAnonymously on the same
          # predicate, in the same run. `--show-trace` so a step with deep internal
          # evaluation cannot push the context frame into the trace's truncated middle —
          # and NEVER on diesAnonymously arms, where a full trace prints source snippets
          # that could carry the literal `gen-scope:` from eval.nix's own throw texts and
          # false-trip the absence assertion.
          diesNamed() {
            evalArm "$1" "$2" --show-trace
            [ "$rc" -ne 0 ] || die "$1" "expected a death, got exit 0 with '$val'"
            grep -q 'division by zero' "$TMPDIR/err" || die "$1" "death is not the division-by-zero channel"
            grep -Fq "gen-scope: the outer seat is re-applying the walked member's step on '$3'" "$TMPDIR/err" || die "$1" "death does not carry the outer seat's context naming '$3'"
          }
          # <arm> <libdir>: the `nta` cycle price — non-zero exit, one of Nix's two anonymous
          # aborts, and ZERO lines anchored `error: gen-scope[.:]` (which covers the
          # `gen-scope.<entry>:` family). No `--show-trace`, per diesNamed's note: a full trace
          # prints source frames that can carry a throw text.
          diesOnNixAbort() {
            evalArm "$1" "$2"
            [ "$rc" -ne 0 ] || die "$1" "expected a death, got exit 0 with '$val'"
            grep -Eq 'max-call-depth exceeded|infinite recursion encountered' "$TMPDIR/err" || die "$1" "death is neither Nix abort channel"
            if grep -Eq 'error: gen-scope[.:]' "$TMPDIR/err"; then
              die "$1" "death is NOT anonymous — a named refusal fired"
            fi
            grep -Eo 'max-call-depth exceeded|infinite recursion encountered' "$TMPDIR/err" | head -n 1 > "$TMPDIR/channel-$1"
          }
          # <arm> <stat>: runs one cell with the evaluator's statistics on, requires exit 0, and
          # leaves the process's own count `<stat>` in `stat` (`callsOf`: nrFunctionCalls in
          # `calls`). A stats file with no count is a broken instrument and dies as one, never a zero.
          statOf() {
            export NIX_SHOW_STATS=1 NIX_SHOW_STATS_PATH="$TMPDIR/stats"
            rm -f "$TMPDIR/stats"
            evalArm "$1" "$libSrc"
            unset NIX_SHOW_STATS NIX_SHOW_STATS_PATH
            [ "$rc" -eq 0 ] || die "$1" "expected exit 0, got $rc"
            stat=$(tr -d ' \n' < "$TMPDIR/stats" | grep -o "\"$2\":[0-9]*" | cut -d: -f2 || true)
            [ -n "$stat" ] || die "$1" "the evaluator wrote no $2 to $TMPDIR/stats: cannot measure"
          }
          callsOf() {
            statOf "$1" nrFunctionCalls
            calls=$stat
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

          # The (F1) floor pair, trace arms: the clamp is floored at the walk's own seed, so
          # the probe on shadow[f(m) − 1] never fires — on the descending arm or the monotone
          # twin — at the same answer. The f1-within cell below is the channel's live control.
          answers f1-trace "$libSrc" 3
          traceCount f1-trace 0
          answers f1-trace-ctl "$libSrc" 3
          traceCount f1-trace-ctl 0
          # The (F1) floor pair, div arms: the same below-f(m) coordinate poisoned — and the
          # descending arm ANSWERS, because the floored clamp never reads it (pre-floor this
          # arm died anonymously; the flip is the floor's engineered signature).
          answers f1-div "$libSrc" 3
          answers f1-div-ctl "$libSrc" 3
          # The trace-channel positive control: the probe AT f(m) — the level-2 entry, inside
          # the domain, demanded by the walked program itself — fires exactly once, invariant
          # across the clamp floor: the live-channel proof beside the trace arms' counts.
          answers f1-within "$libSrc" 3
          traceCount f1-within 1

          # EG-B — the outer seat's hybrid death carries the seat's name. The honest probe
          # (the walked member is the ONLY descending instance in the universe) and the mask
          # bound (a descending non-target beside it) both die on the div-zero channel WITH
          # the outer-seat context naming the node (the single-node message family names the
          # node; member attribution rests on the fixture); the ctl arms are the SAME universe refusing
          # BY NAME at iteration 1 — z's mere membership forces nothing. The anti-masking
          # fence is this run's own pairing: a re-masked death would surface on the THROW
          # channel blaming a non-target and fail diesNamed's predicate, and the
          # `diesAnonymously lrp2` cell above is the live control that the name did NOT leak
          # into the (P2) walk channel.
          diesNamed egb "$libSrc" n
          evalArm egb-ctl-noz "$libSrc"
          [ "$rc" -ne 0 ] || die egb-ctl-noz "expected a by-name refusal, got exit 0 with '$val'"
          grep -q 'does not ascend, at iteration 1' "$TMPDIR/err" || die egb-ctl-noz "refusal is not the by-name non-ascent at iteration 1"
          evalArm egb-ctl-plain "$libSrc"
          [ "$rc" -ne 0 ] || die egb-ctl-plain "expected a by-name refusal, got exit 0 with '$val'"
          grep -q 'does not ascend, at iteration 1' "$TMPDIR/err" || die egb-ctl-plain "refusal is not the by-name non-ascent at iteration 1"
          diesNamed egb-mask "$libSrc" n

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

          # U1-h — the `nta` cycle pays the stated price (den-hoag-n6dh7 item 8): anonymous and
          # uncatchable in the production evaluator; refused BY NAME in the debug evaluator on
          # the same fixture (the absence clause's live control); and the constant-keyed twin
          # answers 1, which proves the `nta` path is reached and grows.
          diesOnNixAbort nta-cyc "$libSrc"
          evalArm nta-cyc-dbg "$libSrc"
          [ "$rc" -ne 0 ] || die nta-cyc-dbg "expected a by-name refusal, got exit 0 with '$val'"
          grep -q 'error: gen-scope: cycle detected' "$TMPDIR/err" || die nta-cyc-dbg "refusal is not the debug evaluator's named cycle"
          answers nta-cyc-ctl "$libSrc" 1
          # U1-i — one memo per `nta` child attribute: four reads, one application.
          answers nta-memo "$libSrc" 1
          traceCount nta-memo 1
          # U2.0-c — one evaluation per node (den-hoag-n6dh7 Unit 2.0): three children, each read
          # through the host's record with `getNta` and by identifier, in either order, at depth 1
          # and at depth 2 (the grandchild read inside its host's own body), apply their probe 3
          # times; the live control reads by identifier through a second evaluation, 6.
          for c in once-d1-record once-d1-id once-d2-record once-d2-id; do
            answers "$c" "$libSrc" 6
            traceCount "$c" 3
          done
          for c in once-d1-ctl once-d2-ctl; do
            answers "$c" "$libSrc" 6
            traceCount "$c" 6
          done

          # U2.0-f — the host attribute is evaluated once however many children read it
          # (den-hoag-n6dh7 U2.0′): three children read it through `getHostAt`, and it applies
          # once — gen-scope's per-node memo, which the host's accessor reaches; the live control
          # reads it through a second evaluation per child, 3.
          answers hostat-once "$libSrc" 3
          traceCount hostat-once 1
          answers hostat-once-ctl "$libSrc" 3
          traceCount hostat-once-ctl 3

          # U2.0-g — enumeration and by-id resolution down a same-kind `nta` chain grow linearly in
          # depth (den-hoag-n6dh7): doubling the depth from 6 to 12 must multiply the evaluator's
          # function calls by less than 2.5, where linear growth reads about 1.8x and quadratic
          # tends to 4x. A host resolved twice per level, 2^depth, read 63x (ids) and 51x (by id)
          # at d62b595. Each value is the
          # hand-derived answer, so a cell that stopped reaching the chain cannot pass on its count.
          for w in ids byid; do
            [ "$w" = ids ] && v6=7 v12=13 || v6=6 v12=12
            callsOf "chain-$w-6"
            [ "$val" = "$v6" ] || die "chain-$w-6" "expected value $v6, got '$val'"
            c6=$calls
            callsOf "chain-$w-12"
            [ "$val" = "$v12" ] || die "chain-$w-12" "expected value $v12, got '$val'"
            [ $((2 * calls)) -lt $((5 * c6)) ] || die "chain-$w-12" "function calls grew from $c6 at depth 6 to $calls at depth 12, not under 2.5x: enumeration is superlinear in depth"
          done

          # U2.0-h — the `nta` channel's cost per child (den-hoag-n6dh7 D2): the evaluator's thunks
          # at 400 children less those at 100, over 300, is at most 36 — measured 36 on upstream Nix,
          # Determinate and Lix alike, where c93a5c0 read 68 and the per-application attribute
          # classification read 38. A binding paid per child that the channel does not need moves
          # it; each value is the hand-derived 2n.
          statOf child-cost-100 nrThunks
          [ "$val" = "200" ] || die child-cost-100 "expected value 200, got '$val'"
          t100=$stat
          statOf child-cost-400 nrThunks
          [ "$val" = "800" ] || die child-cost-400 "expected value 800, got '$val'"
          [ $((stat - t100)) -le $((36 * 300)) ] || die child-cost-400 "the nta channel costs $((stat - t100)) thunks over 300 children, above 36 per child"

          # 0/0 is a false pass: the runner must have executed every cell above.
          [ "$ran" = "31" ] || die runner "expected 31 evaluations, ran $ran"
          echo "tests-process: 31 cells, every exit read unpiped, every death on its named channel; nta-cyc channel: $(cat "$TMPDIR/channel-nta-cyc")" > $out
        ''
        + ''
          cat "$out"
        ''
      );
    };
}
