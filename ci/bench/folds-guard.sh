#!/usr/bin/env bash
# Reads the `folds-guard.nix` arms and reports, per arm, WHETHER THE EVALUATION ENDED.
#
#   ./ci/bench/folds-guard.sh          -> arm rc want verdict value/message
#
# WHAT THE COLUMNS MEAN. `rc` is the evaluator's exit code, read IMMEDIATELY and never through a
# pipe — `$?` after a pipe reads the pipe's last stage and is a false green. rc 0 means the arm
# produced a VALUE: either the fold returned, or a named refusal was caught by the `tryEval`
# wrapper the arm carries. rc 1 means the evaluation ENDED — the outcome a suite cell cannot
# report, which is the whole reason this file exists.
#
# ★ THE UNGUARDED ROWS ARE LIVE CONTROLS AND THEY MUST FAIL. They are the folds without their
# preconditions, built inside the bench file, run in this same invocation on the same inputs. A
# table in which every guarded row passes and no unguarded row ends the evaluation is a table that
# measured nothing: it would read identically if the inputs never reached the fold.
#
# ★ AND `plain-conflict-wrapped` IS THE CONTROL ON THE INSTRUMENT ITSELF. It wraps an ordinary
# named refusal exactly as the unguarded rows are wrapped, and it must be CAUGHT (rc 0). Without
# it, an rc of 1 on an unguarded row is equally explained by a `tryEval` idiom that never held
# anything.
#
# A row whose message column is checked names the LIBRARY AND THE FOLD: "refuses by name" is a
# claim about what the caller is told, and an exit code alone cannot distinguish a refusal from
# the evaluator giving up.
set -u
cd "$(dirname "$0")/../.." || exit 99

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

# arm | expected rc | pattern the message or value must match (empty = unchecked)
cells=(
  "guarded-wrapped|0|^true$"
  "guarded-bare|1|gen-scope\.folds\.same: key 'k' has a fragment carrying a function, at fragment-list position \[0\]\.gen"
  "unguarded-wrapped|1|cannot convert a function to JSON"
  "unguarded-bare|1|cannot convert a function to JSON"
  "guarded-shared|0|^true$"
  "unguarded-shared|0|^\"set\"$"
  "plain-conflict-wrapped|0|^true$"
  "plain-agree|0|^\{ a = 1; \}$"
  "bykey-wrapped|0|^true$"
  "unguarded-bykey-wrapped|1|cannot convert a function to JSON"
  "mergeattrs-wrapped|0|^true$"
  "unguarded-mergeattrs-wrapped|1|expected a set but found a function"
)

fail=0
printf '%-30s %3s %4s %-8s %s\n' arm rc want verdict 'value / message'
for cell in "${cells[@]}"; do
  IFS='|' read -r arm want pat <<<"$cell"
  out=$(nix-instantiate --eval --strict --argstr arm "$arm" ./ci/bench/folds-guard.nix 2>"$tmp/err")
  rc=$?
  if [ "$rc" -eq 0 ]; then
    shown=$out
  else
    # The refusal's own sentence: the last `error:` line the evaluator printed.
    shown=$(grep -o 'error: .*' "$tmp/err" | tail -1)
  fi
  verdict=ok
  [ "$rc" -eq "$want" ] || verdict=RC
  if [ -n "$pat" ] && ! grep -qE "$pat" <<<"$shown"; then
    [ "$verdict" = ok ] && verdict=MSG || verdict=RC+MSG
  fi
  [ "$verdict" = ok ] || fail=1
  printf '%-30s %3s %4s %-8s %s\n' "$arm" "$rc" "$want" "$verdict" "${shown:0:120}"
done

echo
if [ "$fail" -eq 0 ]; then
  echo "all arms as expected — guarded arms return, unguarded controls end the evaluation"
else
  echo "AT LEAST ONE ARM DISAGREED WITH ITS EXPECTATION"
fi
exit "$fail"
