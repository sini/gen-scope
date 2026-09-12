#!/usr/bin/env bash
# Reads the `graph-clique.nix` arms and REFUSES if `clique` costs more than the clique it emits.
#
#   ./ci/bench/graph-clique.sh [sizes...]   -> arm n rc list.elements sets.elements nrLookups digest
#                                           -> then the per-doubling exponent per arm per axis
#
# WHAT THE COLUMNS MEAN. `rc` is the evaluator's exit code, read IMMEDIATELY and never through a
# pipe. The three cost columns are the evaluator's own counters, taken from `NIX_SHOW_STATS_PATH`;
# no wall-clock number is read, because a class is not a duration. `digest` is the graph the cell
# actually built — its two sizes, and both ends of both sequences.
#
# THE BUDGET is a per-doubling exponent of 2.05, NOT the 1.05 `graph-overlays.sh` holds `overlays`
# to. A clique on n vertices HAS n(n-1)/2 edges, so 2.00 is the output and the budget leaves room
# for the quadratic term's constants. What this refuses is the ACCUMULATOR term on top of it: the
# prior `foldl' connect empty` re-copied the edge list at every step and measured 2.98.
#
# ★ THE SIZES ARE CHECKED BEFORE ANY COST FIGURE IS READ, and that is the whole guard against the
# false green a cost oracle is exposed to. An arm that cleared 2.05 by emitting a SMALLER graph
# would be a regression wearing a repair's number, so `nv` and `ne` are asserted against the closed
# form and a cell that misses them is refused whatever it cost.
#
# ★ THE DEFECT ARM IS HELD TO THE OPPOSITE ASSERTION, and that is what keeps this bench honest. If
# `fold-defect` ever clears the budget, the instrument has stopped discriminating and the shipped
# arm's green means nothing — so a run in which it passes is REFUSED. Its digest is compared to the
# other two arms' as well, which makes it the equivalence proof for the rewrite that replaced it.
#
# ★ IDENTICAL CELLS ARE A REFUSAL, NOT A CURVE. A flat axis inside an arm is an instrument failure
# and is refused by name, never reported as "the metric does not move with n".
#
# ★ USE `nix-instantiate --arg`, NEVER `nix eval --file`. `nix eval --file f.nix --arg n 7` SILENTLY
# DROPS the argument and exits 0 with a lambda, and `NIX_SHOW_STATS` still writes a full table for
# the unapplied expression. The stats file cannot tell you the size you asked for was ignored.
set -u
cd "$(dirname "$0")/../.." || exit 99

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

sizes=${*:-"100 200 400 800"}
arms="clique linear-control fold-defect"
axes="list sets lookups"

# The budget as an exact integer comparison, so the refusal never depends on a float tool being
# present: exponent <= 2.05 is ratio <= 2^2.05 = 4.14106, i.e. 10000*c2 <= 41410*c1.
budget_num=41410
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

printf '%-14s %6s %3s %15s %14s %10s  %s\n' arm n rc list.elements sets.elements nrLookups digest
for arm in $arms; do
  for n in $sizes; do
    rm -f "$tmp/stats.json"
    NIX_SHOW_STATS=1 NIX_SHOW_STATS_PATH="$tmp/stats.json" \
      nix-instantiate --eval --strict --argstr arm "$arm" --arg n "$n" \
      ./ci/bench/graph-clique.nix >"$tmp/out" 2>"$tmp/err"
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
    digest[$arm,$n]=$d
    printf '%-14s %6s %3s %15s %14s %10s  %s\n' \
      "$arm" "$n" "$rc" "${l:-<none>}" "${s:-<none>}" "${k:-<none>}" "${d:-<no value>}"
    [ "$rc" -eq 0 ] || refuse "$arm n=$n exited $rc -- $(head -c 200 "$tmp/err")"
    [ -n "$l" ] && [ -n "$s" ] && [ -n "$k" ] || refuse "$arm n=$n produced no stats table"
    # THE SIZE INVARIANT. A clique on n vertices is n vertices and n(n-1)/2 edges, both closed
    # forms, so a cell that cleared the budget while building a SMALLER graph is caught here.
    want="nv=$n ne=$((n * (n - 1) / 2)) "
    case "$d" in
      *"$want"*) : ;;
      *) refuse "$arm n=$n built the wrong graph: expected ${want}... got ${d:-<no value>}" ;;
    esac
    # THE ARMS MUST AGREE ON THE VALUE, sequence included. The defect arm is the prior
    # implementation, so this comparison is what makes the rewrite an equivalence rather than a
    # reimplementation that happens to be cheaper.
    ref=${digest[clique,$n]:-}
    [ -z "$ref" ] || [ "$d" = "$ref" ] ||
      refuse "$arm n=$n disagrees with the shipped arm: $d vs $ref"
  done
done

echo
printf '%-14s %-8s %s\n' arm axis 'per-doubling exponents (budget 2.05; fold-defect must EXCEED it)'
for arm in $arms; do
  for axis in $axes; do
    line=""
    overruns=0
    ratios=0
    # ON `list` ONLY, and the scoping is a measurement rather than a convenience: `linear-control`
    # allocates a CONSTANT 144 set elements at every size, because the per-edge records do not reach
    # this counter at all. A flat `sets` row is that arm telling the truth; a flat `list` row is the
    # fixture never having been applied. Refusing on the axis that cannot legitimately be flat is
    # what keeps this a check on the instrument instead of a check on the counter's taxonomy.
    distinct=$(
      for n in $sizes; do echo "${cost[$arm,$n,$axis]:-}"; done | sort -u | wc -l
    )
    if [ "$axis" = list ] && [ "$distinct" -le 1 ]; then
      refuse "$arm $axis is IDENTICAL in every cell -- the instrument, not the curve"
    fi
    prev=""
    for n in $sizes; do
      cur=${cost[$arm,$n,$axis]:-}
      [ -n "$cur" ] || continue
      if [ -n "$prev" ]; then
        if [ "$prev" -le 0 ]; then
          refuse "$arm $axis has a zero cell -- no ratio is defined"
        else
          ratios=$((ratios + 1))
          # exact integer form of exponent <= 2.05
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
    if [ "$arm" = "fold-defect" ] && [ "$axis" = "list" ] && [ "$overruns" -ne "$ratios" ]; then
      refuse "fold-defect list overran on only $overruns of $ratios doublings -- the bench no longer discriminates"
    fi
    printf '%-14s %-8s %s\n' "$arm" "$axis" "${line# }"
  done
done

echo
if [ "$fail" -eq 0 ]; then
  echo "clique costs its output -- and the prior fold exceeds the same budget in the same run"
else
  echo "AT LEAST ONE ARM IS OUT OF CLASS, OR THE INSTRUMENT DID NOT MEASURE WHAT IT PRINTED"
fi
exit "$fail"
