#!/usr/bin/env bash
# Reads the `stratify-forcing.nix` arms and reports, per arm, WHETHER THE EVALUATION ENDED.
#
#   ./ci/bench/stratify-forcing.sh     -> arm rc want verdict value/message
#
# WHAT THE COLUMNS MEAN. `rc` is the evaluator's exit code, read IMMEDIATELY and never through a
# pipe — `$?` after a pipe reads the pipe's last stage and is a false green. rc 0 means the arm
# produced a VALUE: either the walk returned, or a named refusal was caught by the `tryEval`
# wrapper the arm carries. rc 1 means the evaluation ENDED — the outcome a suite cell cannot
# report, which is the whole reason this file exists.
#
# ★ THE UNFORCED ROWS ARE LIVE CONTROLS AND THEY MUST FAIL. They are the driver's own loop without
# its per-round forcing, run in this same invocation on the same fixture. A table in which the
# forced row returns and no unforced row ends the evaluation is a table that measured nothing: it
# would read identically if the forcing were deleted.
#
# ★ THE `-small` ROWS ARE THE CONTROL ON THAT CONTROL. Below the chain's boundary the unforced
# construction returns, and returns the SAME value as the forced one — so the long row's abort is
# the accumulated chain and not a fixture that never ran.
#
# ★ THE MESSAGE COLUMN IS CHECKED ON THE ABORTING ROWS, because an exit code alone cannot tell a
# stack overflow from a typo in a path. The abort this measures says "stack overflow"; a row that
# exits 1 with any other sentence is a different finding wearing the expected exit code.
set -u
cd "$(dirname "$0")/../.." || exit 99

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

# arm | expected rc | pattern the message or value must match (empty = unchecked)
cells=(
  "forced|0|^\{ settled = 1; strata = 100000; \}$"
  "unforced|1|stack overflow"
  "unforced-wrapped|1|stack overflow"
  "forced-small|0|^\{ settled = 1; strata = 1000; \}$"
  "unforced-small|0|^\{ settled = 1; strata = 1000; \}$"
  "plain-throw-wrapped|0|^true$"
)

fail=0
printf '%-24s %3s %4s %-8s %s\n' arm rc want verdict 'value / message'
for cell in "${cells[@]}"; do
  IFS='|' read -r arm want pat <<<"$cell"
  out=$(nix-instantiate --eval --strict --argstr arm "$arm" ./ci/bench/stratify-forcing.nix 2>"$tmp/err")
  rc=$?
  if [ "$rc" -eq 0 ]; then
    shown=$out
  else
    # The abort's own sentence: the last `error:` line the evaluator printed.
    shown=$(grep -o 'error: .*' "$tmp/err" | tail -1)
  fi
  verdict=ok
  [ "$rc" -eq "$want" ] || verdict=RC
  if [ -n "$pat" ] && ! grep -qE "$pat" <<<"$shown"; then
    [ "$verdict" = ok ] && verdict=MSG || verdict=RC+MSG
  fi
  [ "$verdict" = ok ] || fail=1
  printf '%-24s %3s %4s %-8s %s\n' "$arm" "$rc" "$want" "$verdict" "${shown:0:120}"
done

echo
if [ "$fail" -eq 0 ]; then
  echo "all arms as expected — the forced walk returns where the unforced one ends the evaluation"
else
  echo "AT LEAST ONE ARM DISAGREED WITH ITS EXPECTATION"
fi
exit "$fail"
