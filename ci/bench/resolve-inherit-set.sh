#!/usr/bin/env bash
# Reads the `resolve-inherit-set.nix` arms and REFUSES if `inheritSet` allocates more than the set
# it emits.
#
#   ./ci/bench/resolve-inherit-set.sh [sizes...]  -> arm n rc list.elements nrFunctionCalls digest
#                                                 -> then the per-doubling exponent per arm per axis
#
# WHAT THE COLUMNS MEAN. `rc` is the evaluator's exit code, read IMMEDIATELY and never through a
# pipe. The two cost columns are the evaluator's own counters, taken from `NIX_SHOW_STATS_PATH`; no
# wall-clock number is read, because a class is not a duration. `digest` is the set the cell
# actually built — its length and both ends of the sequence.
#
# THE BUDGET is a per-doubling exponent of 1.05 on `list.elements` ONLY. The dedup keeps 3n of 3n
# distinct contributions, so its OUTPUT is linear in the size swept and its allocation must be too;
# the prior `acc ++ [ x ]` re-copied the kept list at every element and measured 2.00 on this axis.
#
# ★ `nrFunctionCalls` IS PRINTED AND DELIBERATELY NOT BUDGETED, and reading it as an unguarded axis
# is the mistake this paragraph exists to prevent. `eq` is a caller-supplied predicate and there is
# no key to index it by, so the pairwise scan is this constructor's SPECIFIED SEMANTICS — the way
# n(n-1)/2 edges are a clique's. It reads 2.00 before the repair and 2.00 after, and a run in which
# it FELL would mean an arm had stopped comparing what the contract says it compares. The repair is
# entirely on the allocation axis; printing the two together is what stops a reader taking a linear
# `list` row for a linear constructor.
#
# ★ THE SIZE INVARIANT IS CHECKED BEFORE ANY COST FIGURE IS READ. The fixture's three nodes each
# contribute n DISTINCT values, so the deduped length is exactly 3n — an arm that cleared the budget
# by keeping fewer elements is caught here, whatever it cost.
#
# ★ THE DEFECT ARM IS HELD TO THE OPPOSITE ASSERTION. If `fold-defect` ever fits the budget, this
# bench has stopped discriminating and the shipped arm's green off it means nothing, so a run in
# which it passes is REFUSED. Its digest is compared to the other arms' as well, which makes it the
# equivalence proof for the rewrite that replaced it.
#
# ★ USE `nix-instantiate --arg`, NEVER `nix eval --file`. `nix eval --file f.nix --arg n 7` SILENTLY
# DROPS the argument and exits 0 with a lambda, and `NIX_SHOW_STATS` still writes a full table for
# the unapplied expression. The stats file cannot tell you the size you asked for was ignored.
set -u
cd "$(dirname "$0")/../.." || exit 99

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

sizes=${*:-"125 250 500 1000"}
arms="inheritSet linear-control fold-defect"
axes="list calls"

# The budget as an exact integer comparison, so the refusal never depends on a float tool being
# present: exponent <= 1.05 is ratio <= 2^1.05 = 2.0705, i.e. 10000*c2 <= 20705*c1.
budget_num=20705
budget_den=10000

declare -A cost
declare -A digest

fail=0
refuse() {
  echo "REFUSED: $*"
  fail=1
}

field() { # field <flattened-json-file> <sed-expression>
  sed -n "$2" "$1"
}

printf '%-14s %6s %3s %15s %16s  %s\n' arm n rc list.elements nrFunctionCalls digest
for arm in $arms; do
  for n in $sizes; do
    rm -f "$tmp/stats.json"
    NIX_SHOW_STATS=1 NIX_SHOW_STATS_PATH="$tmp/stats.json" \
      nix-instantiate --eval --strict --argstr arm "$arm" --arg n "$n" \
      ./ci/bench/resolve-inherit-set.nix >"$tmp/out" 2>"$tmp/err"
    rc=$?
    # Flatten first: the stats writer's whitespace is not a promised format.
    tr -d ' \n' <"$tmp/stats.json" >"$tmp/flat" 2>/dev/null || : >"$tmp/flat"
    l=$(field "$tmp/flat" 's/.*"list":{[^}]*"elements":\([0-9]*\).*/\1/p')
    c=$(field "$tmp/flat" 's/.*"nrFunctionCalls":\([0-9]*\).*/\1/p')
    d=$(tr -d '\n' <"$tmp/out")
    cost[$arm,$n,list]=${l:-}
    cost[$arm,$n,calls]=${c:-}
    digest[$arm,$n]=$d
    printf '%-14s %6s %3s %15s %16s  %s\n' \
      "$arm" "$n" "$rc" "${l:-<none>}" "${c:-<none>}" "${d:-<no value>}"
    [ "$rc" -eq 0 ] || refuse "$arm n=$n exited $rc -- $(head -c 200 "$tmp/err")"
    [ -n "$l" ] && [ -n "$c" ] || refuse "$arm n=$n produced no stats table"
    want="nd=$((3 * n)) "
    case "$d" in
      *"$want"*) : ;;
      *) refuse "$arm n=$n built the wrong set: expected ${want}... got ${d:-<no value>}" ;;
    esac
    ref=${digest[inheritSet,$n]:-}
    [ -z "$ref" ] || [ "$d" = "$ref" ] ||
      refuse "$arm n=$n disagrees with the shipped arm: $d vs $ref"
  done
done

echo
printf '%-14s %-8s %s\n' arm axis 'per-doubling exponents (list budget 1.05; fold-defect must EXCEED it; calls is reported, not budgeted)'
for arm in $arms; do
  for axis in $axes; do
    line=""
    overruns=0
    ratios=0
    distinct=$(
      for n in $sizes; do echo "${cost[$arm,$n,$axis]:-}"; done | sort -u | wc -l
    )
    if [ "$distinct" -le 1 ]; then
      refuse "$arm $axis is IDENTICAL in every cell -- the instrument, not the curve"
    fi
    prev=""
    for n in $sizes; do
      cur=${cost[$arm,$n,$axis]:-}
      [ -n "$cur" ] || continue
      if [ -n "$prev" ] && [ "$axis" = list ]; then
        if [ "$prev" -le 0 ]; then
          refuse "$arm $axis has a zero cell -- no ratio is defined"
        else
          ratios=$((ratios + 1))
          # exact integer form of exponent <= 1.05
          if [ $((budget_den * cur)) -gt $((budget_num * prev)) ]; then
            overruns=$((overruns + 1))
            if [ "$arm" != "fold-defect" ]; then
              refuse "$arm $axis $prev -> $cur exceeds the budget"
            fi
          fi
        fi
      fi
      line="$line $(awk -v a="$prev" -v b="$cur" 'BEGIN { if (a == "" || a <= 0) print "-"; else printf "%.2f", log(b / a) / log(2) }')"
      prev=$cur
    done
    # The defect arm's OPPOSITE assertion: every doubling of its allocation must overrun the same
    # budget the shipped arm clears. A run in which it fits is a run in which this bench has stopped
    # discriminating, and the shipped arm's green off it would mean nothing.
    if [ "$arm" = "fold-defect" ] && [ "$axis" = list ] && [ "$overruns" -ne "$ratios" ]; then
      refuse "fold-defect list overran on only $overruns of $ratios doublings -- the bench no longer discriminates"
    fi
    printf '%-14s %-8s %s\n' "$arm" "$axis" "${line# }"
  done
done

echo
if [ "$fail" -eq 0 ]; then
  echo "inheritSet allocates its output -- and the prior fold exceeds the same budget in the same run"
else
  echo "AT LEAST ONE ARM IS OUT OF CLASS, OR THE INSTRUMENT DID NOT MEASURE WHAT IT PRINTED"
fi
exit "$fail"
