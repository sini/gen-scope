#!/usr/bin/env bash
# Reads the `graph-overlays.nix` arms and REFUSES if `overlays` is not linear in its segments.
#
#   ./ci/bench/graph-overlays.sh [sizes...]   -> arm n rc list.elements sets.elements nrLookups digest
#                                             -> then the per-doubling exponent per arm per axis
#
# WHAT THE COLUMNS MEAN. `rc` is the evaluator's exit code, read IMMEDIATELY and never through a
# pipe. The three cost columns are the evaluator's own counters, taken from `NIX_SHOW_STATS_PATH`;
# no wall-clock number is read, because a class is not a duration. `digest` is the graph the cell
# actually built — its two sizes, and both ends of both sequences. Only the SIZES are refused on:
# they are what makes a cost figure the cost of the right thing. The sequence is printed and left to
# the suite, which is the oracle for it.
#
# THE BUDGET is a per-doubling exponent of 1.05 on each axis of each arm. `overlays` allocating
# Theta(n^2) list elements to build an n-long vertex list is the defect this guards;
# 1.05 leaves room for the linear term's constants and refuses anything with a super-linear one.
#
# ★ ONLY `list.elements` DISCRIMINATES, and the row must not be misread as three passes. The
# quadratic constructor ALREADY satisfies the budget on `sets.elements` and on `nrLookups` — those
# two are here to catch a REMEDY THAT TRADES list cost for set or lookup cost, not because they can
# see this defect. A two-axis version of this bench omitting `list.elements` certifies the defect
# unchanged.
#
# ★ THE CONTROL ARM MUST PASS TOO, AND THAT IS THE MEASUREMENT. `linear-control` builds the same
# graph value without reaching `lib/graph.nix`. If the instrument breaks, both arms move together
# and the identical-cell refusal below fires; a table carrying only the shipped arm would read
# clean off an evaluation that never happened.
#
# ★ IDENTICAL CELLS ARE A REFUSAL, NOT A CURVE. The first run of this benchmark returned one
# plausible constant in all eight cells — the evaluator's own baseline, because the fixture's
# top-level lambda was never applied. A flat axis inside an arm is an instrument failure and is
# refused by name, never reported as "the metric does not move with n".
#
# ★ USE `nix-instantiate --arg`, NEVER `nix eval --file`. `nix eval --file f.nix --arg n 7` SILENTLY
# DROPS the argument and exits 0 with a lambda, and `NIX_SHOW_STATS` still writes a full table for
# the unapplied expression. The stats file cannot tell you the size you asked for was ignored.
set -u
cd "$(dirname "$0")/../.." || exit 99

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

sizes=${*:-"500 1000 2000 4000"}
arms="overlays linear-control"
axes="list sets lookups"

# The budget as an exact integer comparison, so the refusal never depends on a float tool being
# present: exponent <= 1.05 is ratio <= 2^1.05 = 2.0705, i.e. 10000*c2 <= 20705*c1.
budget_num=20705
budget_den=10000

declare -A cost

fail=0
refuse() {
  echo "REFUSED: $*"
  fail=1
}

field() { # field <flattened-json-file> <sed-expression>
  sed -n "$2" "$1"
}

printf '%-14s %6s %3s %15s %14s %10s  %s\n' arm n rc list.elements sets.elements nrLookups digest
for arm in $arms; do
  for n in $sizes; do
    rm -f "$tmp/stats.json"
    NIX_SHOW_STATS=1 NIX_SHOW_STATS_PATH="$tmp/stats.json" \
      nix-instantiate --eval --strict --argstr arm "$arm" --arg n "$n" \
      ./ci/bench/graph-overlays.nix >"$tmp/out" 2>"$tmp/err"
    rc=$?
    # Flatten first: the stats writer's whitespace is not a promised format.
    tr -d ' \n' <"$tmp/stats.json" >"$tmp/flat" 2>/dev/null || : >"$tmp/flat"
    l=$(field "$tmp/flat" 's/.*"list":{[^}]*"elements":\([0-9]*\).*/\1/p')
    s=$(field "$tmp/flat" 's/.*"sets":{[^}]*"elements":\([0-9]*\).*/\1/p')
    k=$(field "$tmp/flat" 's/.*"nrLookups":\([0-9]*\).*/\1/p')
    d=$(tr -d '\n' <"$tmp/out")
    cost[$arm,$n,list]=${l:-}
    cost[$arm,$n,sets]=${s:-}
    cost[$arm,$n,lookups]=${k:-}
    printf '%-14s %6s %3s %15s %14s %10s  %s\n' \
      "$arm" "$n" "$rc" "${l:-<none>}" "${s:-<none>}" "${k:-<none>}" "${d:-<no value>}"
    [ "$rc" -eq 0 ] || refuse "$arm n=$n exited $rc -- $(head -c 200 "$tmp/err")"
    [ -n "$l" ] && [ -n "$s" ] && [ -n "$k" ] || refuse "$arm n=$n produced no stats table"
    # THE SIZE INVARIANT, AND DELIBERATELY NOT THE ORDER. The fixture's three segments contribute
    # n + (n+1) + 2n vertices and 0 + n + n edges, so a cell that cleared the budget while building
    # a SMALLER graph is caught here — that is the false green a cost oracle is exposed to. Order is
    # NOT checked: the suite is the order oracle, and an O1 that also refused a reordering would
    # collapse the conjunction the two of them make. The digest prints its ends regardless, so a
    # reader sees the sequence even where nothing refuses on it.
    want="nv=$((4 * n + 1)) ne=$((2 * n)) "
    case "$d" in
      *"$want"*) : ;;
      *) refuse "$arm n=$n built the wrong graph: expected ${want}... got ${d:-<no value>}" ;;
    esac
  done
done

echo
printf '%-14s %-8s %s\n' arm axis 'per-doubling exponents (budget 1.05)'
for arm in $arms; do
  for axis in $axes; do
    line=""
    distinct=$(
      for n in $sizes; do echo "${cost[$arm,$n,$axis]:-}"; done | sort -u | wc -l
    )
    [ "$distinct" -gt 1 ] || refuse "$arm $axis is IDENTICAL in every cell -- the instrument, not the curve"
    prev=""
    for n in $sizes; do
      cur=${cost[$arm,$n,$axis]:-}
      [ -n "$cur" ] || continue
      if [ -n "$prev" ]; then
        if [ "$prev" -le 0 ]; then
          refuse "$arm $axis has a zero cell -- no ratio is defined"
        else
          # exact integer form of exponent <= 1.05
          [ $((budget_den * cur)) -le $((budget_num * prev)) ] ||
            refuse "$arm $axis $prev -> $cur exceeds the budget"
        fi
        line="$line $(awk -v a="$prev" -v b="$cur" 'BEGIN { if (a <= 0) print "-"; else printf "%.2f", log(b / a) / log(2) }')"
      fi
      prev=$cur
    done
    printf '%-14s %-8s %s\n' "$arm" "$axis" "${line# }"
  done
done

echo
if [ "$fail" -eq 0 ]; then
  echo "overlays is linear in its segments -- and the live control is linear beside it on the same values"
else
  echo "AT LEAST ONE ARM IS NOT LINEAR, OR THE INSTRUMENT DID NOT MEASURE WHAT IT PRINTED"
fi
exit "$fail"
