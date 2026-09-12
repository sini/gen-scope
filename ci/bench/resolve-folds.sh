#!/usr/bin/env bash
# Reads the `resolve-folds.nix` arms and REFUSES if `collectionAttr` or `inheritAll` allocates more
# than the list it emits.
#
#   ./ci/bench/resolve-folds.sh [sizes...]  -> arm n rc list.elements nrOpUpdateValuesCopied digest
#                                           -> then the per-doubling exponent per arm per axis
#
# WHAT THE COLUMNS MEAN. `rc` is the evaluator's exit code, read IMMEDIATELY and never through a
# pipe. The two cost columns are the evaluator's own counters, taken from `NIX_SHOW_STATS_PATH`; no
# wall-clock number is read, because a class is not a duration. `digest` is the list the cell
# actually gathered — its length and both ends.
#
# THE BUDGET is a per-doubling exponent of 1.05. Both fixtures gather exactly n values, so the
# OUTPUT is linear in the size swept and the allocation must be too.
#
# ★ THE TWO AXES ARE NOT INTERCHANGEABLE AND EACH HAS ITS OWN DEFECT ARM.
#   `list.elements`          — the `++` accumulator, which BOTH constructors had.
#   `nrOpUpdateValuesCopied` — `inheritAll`'s `_visited //` cycle guard, which `collectionAttr`
#                              never had and which `genericClosure` replaced. `collect*` reads a
#                              CONSTANT here and that is the arm telling the truth, not a flat
#                              instrument; only `inherit*` is asserted on this axis.
#
# ★ THE DEFECT ARMS ARE HELD TO THE OPPOSITE ASSERTION. If a `-defect` arm ever fits the budget the
# shipped arm clears, this bench has stopped discriminating and the shipped arm's green off it means
# nothing, so a run in which that happens is REFUSED. `collect-defect` reaches the prior fold
# through the PUBLIC surface (`combine = a: b: a ++ b`), so it is also the standing proof that a
# caller-supplied `combine` is still folded rather than quietly ignored.
#
# ★ DIGESTS ARE COMPARED WITHIN A FAMILY at every size. The defect arms are the prior semantics, so
# that comparison is the equivalence proof for both rewrites.
#
# ★ USE `nix-instantiate --arg`, NEVER `nix eval --file`. `nix eval --file f.nix --arg n 7` SILENTLY
# DROPS the argument and exits 0 with a lambda, and `NIX_SHOW_STATS` still writes a full table for
# the unapplied expression. The stats file cannot tell you the size you asked for was ignored.
set -u
cd "$(dirname "$0")/../.." || exit 99

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

sizes=${*:-"125 250 500 1000"}
arms="collect collect-defect inherit inherit-defect"
axes="list updates"

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

family() { # the shipped arm of this arm's family
  case $1 in
    collect*) echo collect ;;
    inherit*) echo inherit ;;
  esac
}

printf '%-16s %6s %3s %15s %22s  %s\n' arm n rc list.elements nrOpUpdateValuesCopied digest
for arm in $arms; do
  for n in $sizes; do
    rm -f "$tmp/stats.json"
    NIX_SHOW_STATS=1 NIX_SHOW_STATS_PATH="$tmp/stats.json" \
      nix-instantiate --eval --strict --argstr arm "$arm" --arg n "$n" \
      ./ci/bench/resolve-folds.nix >"$tmp/out" 2>"$tmp/err"
    rc=$?
    # Flatten first: the stats writer's whitespace is not a promised format.
    tr -d ' \n' <"$tmp/stats.json" >"$tmp/flat" 2>/dev/null || : >"$tmp/flat"
    l=$(sed -n 's/.*"list":{[^}]*"elements":\([0-9]*\).*/\1/p' "$tmp/flat")
    u=$(sed -n 's/.*"nrOpUpdateValuesCopied":\([0-9]*\).*/\1/p' "$tmp/flat")
    d=$(tr -d '\n' <"$tmp/out")
    cost[$arm,$n,list]=${l:-}
    cost[$arm,$n,updates]=${u:-}
    digest[$arm,$n]=$d
    printf '%-16s %6s %3s %15s %22s  %s\n' \
      "$arm" "$n" "$rc" "${l:-<none>}" "${u:-<none>}" "${d:-<no value>}"
    [ "$rc" -eq 0 ] || refuse "$arm n=$n exited $rc -- $(head -c 200 "$tmp/err")"
    [ -n "$l" ] && [ -n "$u" ] || refuse "$arm n=$n produced no stats table"
    # THE SIZE INVARIANT. Both fixtures contribute exactly one value per node, so the gathered
    # length is n — an arm that cleared the budget by gathering less is caught here, whatever it
    # cost, and it is checked before any cost figure is read.
    case "$d" in
      *"len=$n "*) : ;;
      *) refuse "$arm n=$n gathered the wrong list: expected len=$n got ${d:-<no value>}" ;;
    esac
    ref=${digest[$(family "$arm"),$n]:-}
    [ -z "$ref" ] || [ "$d" = "$ref" ] ||
      refuse "$arm n=$n disagrees with its family's shipped arm: $d vs $ref"
  done
done

echo
printf '%-16s %-8s %s\n' arm axis 'per-doubling exponents (budget 1.05; -defect arms must EXCEED it)'
for arm in $arms; do
  for axis in $axes; do
    line=""
    overruns=0
    ratios=0
    # ON `list` ONLY. `collect*` allocates a CONSTANT number of set elements because it carries no
    # `//` at all, so a flat `updates` row is that arm telling the truth; a flat `list` row is the
    # fixture never having been applied.
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
      if [ -n "$prev" ] && [ "$prev" -gt 0 ]; then
        ratios=$((ratios + 1))
        if [ $((budget_den * cur)) -gt $((budget_num * prev)) ]; then
          overruns=$((overruns + 1))
        fi
      fi
      line="$line $(awk -v a="$prev" -v b="$cur" 'BEGIN { if (a == "" || a+0 <= 0) print "-"; else printf "%.2f", log(b/a)/log(2) }')"
      prev=$cur
    done

    # WHO IS ASSERTED ON WHICH AXIS, stated rather than implied. Both shipped arms are held to the
    # budget on `list`; only `inherit` is held on `updates`, because `collect` has no `//` to hold.
    case "$arm:$axis" in
      collect:list | inherit:list | inherit:updates)
        [ "$overruns" -eq 0 ] || refuse "$arm $axis overran the budget on $overruns of $ratios doublings"
        ;;
      collect-defect:list | inherit-defect:list | inherit-defect:updates)
        [ "$ratios" -gt 0 ] ||
          refuse "$arm $axis produced no usable ratio -- the defect arm cannot be shown to overrun"
        [ "$overruns" -eq "$ratios" ] ||
          refuse "$arm $axis overran on only $overruns of $ratios doublings -- the bench no longer discriminates"
        ;;
    esac
    printf '%-16s %-8s %s\n' "$arm" "$axis" "${line# }"
  done
done

echo
if [ "$fail" -eq 0 ]; then
  echo "both constructors allocate their output -- and both prior forms exceed the same budget in the same run"
else
  echo "AT LEAST ONE ARM IS OUT OF CLASS, OR THE INSTRUMENT DID NOT MEASURE WHAT IT PRINTED"
fi
exit "$fail"
