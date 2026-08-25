#!/usr/bin/env bash
# Reads the `eval-memo.nix` arms and reports, per arm, HOW MANY TIMES the traced body ran.
#
#   ./ci/bench/eval-memo.sh     -> arm rc traces want verdict value
#
# WHAT THE COLUMNS MEAN. `rc` is the evaluator's exit code, read IMMEDIATELY and never through a
# pipe. `traces` is the number of `trace: EVAL-P` lines on stderr — the evaluation count, which is
# the whole measurement: no wall-clock number is read. The value column must be `[ 3 3 3 ]` on both
# arms, because an arm that errored would print zero traces and read like perfect memoization.
#
# ★ THE DEFECT ARM IS A LIVE CONTROL AND IT MUST COUNT 3. It is the naive form the memo law names —
# a fresh self per `get`, which is `evalDebug`'s shape — run in this same invocation on the same
# fixture. A table in which the shipped arm counts 1 and no arm counts higher measured nothing: it
# would read identically if the trace never fired more than once by construction.
set -u
cd "$(dirname "$0")/../.." || exit 99

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

# arm | expected trace count
cells=(
  "eval|1"
  "evalDebug|3"
)

fail=0
printf '%-12s %3s %7s %5s %-8s %s\n' arm rc traces want verdict value
for cell in "${cells[@]}"; do
  IFS='|' read -r arm want <<<"$cell"
  out=$(nix-instantiate --eval --strict --argstr arm "$arm" ./ci/bench/eval-memo.nix 2>"$tmp/err")
  rc=$?
  traces=$(grep -c 'trace: EVAL-P' "$tmp/err")
  verdict=ok
  [ "$rc" -eq 0 ] || verdict=RC
  [ "$traces" -eq "$want" ] || verdict=COUNT
  grep -qE '^\[ 3 3 3 \]$' <<<"$out" || verdict=VALUE
  [ "$verdict" = ok ] || fail=1
  printf '%-12s %3s %7s %5s %-8s %s\n' "$arm" "$rc" "$traces" "$want" "$verdict" "${out:0:40}"
done

echo
if [ "$fail" -eq 0 ]; then
  echo "memoization survives the guard — one evaluation for three reads, and the naive form counts three"
else
  echo "AT LEAST ONE ARM DISAGREED WITH ITS EXPECTATION"
fi
exit "$fail"
