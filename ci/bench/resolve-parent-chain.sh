#!/usr/bin/env bash
# Reads the `resolve-parent-chain.nix` arms and REFUSES if a `parent`-letter resolution grows faster
# than linearly in the chain it walks.
#
#   ./ci/bench/resolve-parent-chain.sh   -> arm d rc nrThunks value, then the per-step exponents
#
# THE DEPTHS ARE FIXED at 10, 100 and 400: the gate's C2 isolate (den-hoag-gayc U1 landing gate),
# where the per-read D9 chain walk measured `inherit'` at 3,247 / 51,307 / 679,507 thunks.
#
# THE BUDGET is an exponent of 1.15 on `nrThunks` per step, as exact integer ratios so the refusal
# never depends on a float tool: 10 -> 100 is ratio <= 10^1.15 = 14.125, and 100 -> 400 is ratio
# <= 4^1.15 = 4.925. The per-read form read x15.8 and x13.3 on `parent*` visible, so it overran
# both steps; a linear walk reads about x4 and x3.5.
#
# ★ THE `up-*` ARMS ARE THE LIVE CONTROL and are held to the SAME budget. They walk the same chain
# as an edge letter, where D9 never runs, so a control over budget means the instrument or the
# fixture moved, and the run is REFUSED as unmeasured, whatever the `parent` arms read.
#
# ★ USE `nix-instantiate --arg`, NEVER `nix eval --file`: the latter drops the argument and still
# writes a full stats table for the unapplied lambda (see `resolve-inherit-set.sh`).
set -u
cd "$(dirname "$0")/../.." || exit 99

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

depths="10 100 400"
arms="parent-reachable parent-witnesses parent-visible inherit neron up-reachable up-witnesses up-visible"

declare -A cost

fail=0
refuse() {
  echo "REFUSED: $*"
  fail=1
}

# The step budget, numerator over 1000, keyed by the step's two depths.
declare -A budget=([10,100]=14125 [100,400]=4925)

printf '%-18s %4s %3s %10s  %s\n' arm d rc nrThunks value
for arm in $arms; do
  case "$arm" in
    inherit | neron) want='"hit"' ;;
    *) want='[ "n0" ]' ;;
  esac
  for d in $depths; do
    rm -f "$tmp/stats.json"
    NIX_SHOW_STATS=1 NIX_SHOW_STATS_PATH="$tmp/stats.json" \
      nix-instantiate --eval --strict --argstr arm "$arm" --arg d "$d" \
      ./ci/bench/resolve-parent-chain.nix >"$tmp/out" 2>"$tmp/err"
    rc=$?
    tr -d ' \n' <"$tmp/stats.json" >"$tmp/flat" 2>/dev/null || : >"$tmp/flat"
    t=$(sed -n 's/.*"nrThunks":\([0-9]*\).*/\1/p' "$tmp/flat")
    val=$(tr -d '\n' <"$tmp/out")
    cost[$arm,$d]=${t:-}
    printf '%-18s %4s %3s %10s  %s\n' "$arm" "$d" "$rc" "${t:-<none>}" "${val:-<no value>}"
    [ "$rc" -eq 0 ] || refuse "$arm d=$d exited $rc -- $(head -c 300 "$tmp/err")"
    [ -n "$t" ] || refuse "$arm d=$d produced no stats table"
    [ "$val" = "$want" ] || refuse "$arm d=$d answered ${val:-<no value>}, expected $want"
  done
done

echo
printf '%-18s %s\n' arm 'per-step exponents (budget 1.15; up-* is the control and is held to it too)'
for arm in $arms; do
  line=""
  prev=""
  prevd=""
  for d in $depths; do
    cur=${cost[$arm,$d]:-}
    if [ -n "$prev" ] && [ -n "$cur" ]; then
      if [ "$prev" -le 0 ]; then
        refuse "$arm has a zero cell -- no ratio is defined"
      else
        line="$line $(awk -v a="$prev" -v b="$cur" -v x="$prevd" -v y="$d" 'BEGIN { printf "%.2f", log(b / a) / log(y / x) }')"
        if [ $((1000 * cur)) -gt $((${budget[$prevd,$d]} * prev)) ]; then
          case "$arm" in
            up-*) refuse "CONTROL $arm $prev -> $cur (d $prevd -> $d) exceeds the budget -- the instrument, not the letter" ;;
            *) refuse "$arm $prev -> $cur (d $prevd -> $d) exceeds the budget" ;;
          esac
        fi
      fi
    fi
    prev=$cur
    prevd=$d
  done
  printf '%-18s %s\n' "$arm" "${line# }"
done

echo
if [ "$fail" -eq 0 ]; then
  echo "every parent-letter resolution is linear in the chain -- and so is its edge-letter control"
else
  echo "AT LEAST ONE ARM IS OUT OF CLASS, OR THE INSTRUMENT DID NOT MEASURE WHAT IT PRINTED"
fi
exit "$fail"
