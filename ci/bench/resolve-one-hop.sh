#!/usr/bin/env bash
# Reads the `resolve-one-hop.nix` arms and REFUSES if a one-hop edge read grows faster than linearly
# in the edges it reads (`fan-*`) or in the calls made across a graph (`every-*`).
#
#   ./ci/bench/resolve-one-hop.sh   -> arm n rc nrThunks list.elements value, then the exponents
#
# TWO AXES, BOTH BUDGETED. `nrThunks` alone is blind to a quadratic ALLOCATION — a dedup that
# rebuilds its kept list per target (`acc ++ [ x ]`) allocates n²/2 list elements and creates no
# extra thunk — so `list.elements` is read beside it and held to the same budget.
#
# THE BUDGET is an exponent of 1.15 per doubling of n, read on each arm's cost ABOVE its n = 0 cell,
# so the evaluator's fixed start-up cost does not flatten the ratio: a linear arm reads ~1.00. As an
# exact integer ratio, 2^1.15 = 2.2191, i.e. 10000*c2 <= 22191*c1 over the deltas.
#
# ★ THE `*-raw` ARMS ARE THE LIVE CONTROL and are held to the SAME budget: they read the same edges
# as the authored attribute, with no resolution, so a control over budget means the instrument or
# the fixture moved, and the run is REFUSED as unmeasured whatever the reads measured.
#
# ★ USE `nix-instantiate --arg`, NEVER `nix eval --file` (see `resolve-inherit-set.sh`).
set -u
cd "$(dirname "$0")/../.." || exit 99

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

sizes="0 1000 2000 4000"
arms="fan-followEdge fan-imports fan-raw every-followEdge every-collectImports every-raw"
axes="thunks list"

declare -A cost

fail=0
refuse() {
  echo "REFUSED: $*"
  fail=1
}

printf '%-22s %5s %3s %10s %14s  %s\n' arm n rc nrThunks list.elements value
for arm in $arms; do
  for n in $sizes; do
    rm -f "$tmp/stats.json"
    NIX_SHOW_STATS=1 NIX_SHOW_STATS_PATH="$tmp/stats.json" \
      nix-instantiate --eval --strict --argstr arm "$arm" --arg n "$n" \
      ./ci/bench/resolve-one-hop.nix >"$tmp/out" 2>"$tmp/err"
    rc=$?
    tr -d ' \n' <"$tmp/stats.json" >"$tmp/flat" 2>/dev/null || : >"$tmp/flat"
    t=$(sed -n 's/.*"nrThunks":\([0-9]*\).*/\1/p' "$tmp/flat")
    l=$(sed -n 's/.*"list":{[^}]*"elements":\([0-9]*\).*/\1/p' "$tmp/flat")
    val=$(tr -d '\n' <"$tmp/out")
    cost[$arm,$n,thunks]=${t:-}
    cost[$arm,$n,list]=${l:-}
    printf '%-22s %5s %3s %10s %14s  %s\n' "$arm" "$n" "$rc" "${t:-<none>}" "${l:-<none>}" "${val:-<no value>}"
    [ "$rc" -eq 0 ] || refuse "$arm n=$n exited $rc -- $(head -c 300 "$tmp/err")"
    [ -n "$t" ] && [ -n "$l" ] || refuse "$arm n=$n produced no stats table"
    [ "$val" = "$n" ] || refuse "$arm n=$n answered ${val:-<no value>}, expected $n"
  done
done

echo
printf '%-22s %-6s %s\n' arm axis 'per-doubling exponents above n = 0 (budget 1.15; *-raw is the control and is held to it too)'
for arm in $arms; do
  for axis in $axes; do
    base=${cost[$arm,0,$axis]:-}
    line=""
    prev=""
    for n in $sizes; do
      [ "$n" -eq 0 ] && continue
      cur=${cost[$arm,$n,$axis]:-}
      if [ -z "$base" ] || [ -z "$cur" ]; then
        prev=""
        continue
      fi
      cur=$((cur - base))
      if [ -n "$prev" ]; then
        if [ "$prev" -le 0 ]; then
          refuse "$arm $axis has a cell no costlier than n = 0 -- no ratio is defined"
        else
          line="$line $(awk -v a="$prev" -v b="$cur" 'BEGIN { printf "%.2f", log(b / a) / log(2) }')"
          if [ $((10000 * cur)) -gt $((22191 * prev)) ]; then
            case "$arm" in
              *-raw) refuse "CONTROL $arm $axis $prev -> $cur exceeds the budget -- the instrument, not the read" ;;
              *) refuse "$arm $axis $prev -> $cur exceeds the budget" ;;
            esac
          fi
        fi
      fi
      prev=$cur
    done
    printf '%-22s %-6s %s\n' "$arm" "$axis" "${line# }"
  done
done

echo
if [ "$fail" -eq 0 ]; then
  echo "every one-hop read is linear in its edges and in its calls -- and so is the raw-read control"
else
  echo "AT LEAST ONE ARM IS OUT OF CLASS, OR THE INSTRUMENT DID NOT MEASURE WHAT IT PRINTED"
fi
exit "$fail"
