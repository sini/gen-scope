#!/usr/bin/env bash
# The engine's cost-class sweep, and the ACCEPTANCE DERIVATION read off it.
#
#   ./ci/bench/cost-classes.sh [depth ladder...]   -> one row per cell, then the derived bound
#
# THE DERIVATION FUNCTION, which is a PINNED TERM of the acceptance comparison and is therefore
# implemented once, here, rather than described: the bound is *"the greatest condensation depth at
# which every arm of ci/bench/cost-classes.nix completed with converged=true, over the fixture
# families named beside it"* — quoted from `lib/acceptance.nix`, which is where that string is
# RECORDED and against which `acceptanceSignal` voids a comparison. The families it names are
# `$shapes` below, and the maximum is taken over that one list. It is what has been VERIFIED. It
# is not a budget, nothing refuses at it, and no threshold is picked to make this runnable — the
# judge of whether the curve below is adequate for the fleet the engine is for is a person reading
# it, once.
#
# A cell that does not converge, or that does not return, ENDS the ladder: the bound is the last
# depth every cell cleared, so an incomplete cell cannot be rounded up into one that passed.
#
# Every exit code is read IMMEDIATELY — `$?` after a pipe reads the pipe's last stage and is a
# false green.
set -u
cd "$(dirname "$0")/../.." || exit 99

ladder=${*:-"8 32 128 512 1024 2048"}
shapes="chain cycle blocks blocksWide deepContested layers"
arms="model depth solve"

cell() { # cell <shape> <arm> <d> -> prints the row, returns the evaluator's exit code
  nix-instantiate --eval --strict --json \
    --arg d "$3" --arg w 4 --arg k 2 --argstr shape "$1" --argstr arm "$2" \
    ./ci/bench/cost-classes.nix 2>/dev/null
}

verified=0
printf '%-14s %-6s %6s %9s %8s %6s %s\n' shape arm d wall_ms converged depth row
for d in $ladder; do
  cleared=1
  for shape in $shapes; do
    for arm in $arms; do
      start=$(date +%s%N)
      out=$(cell "$shape" "$arm" "$d")
      rc=$?
      ms=$(((($(date +%s%N) - start)) / 1000000))
      conv=$(printf '%s' "$out" | sed -n 's/.*"converged":\([a-z]*\).*/\1/p')
      dep=$(printf '%s' "$out" | sed -n 's/.*"\(condensationD\|d\)epth":\([0-9]*\).*/\2/p')
      printf '%-14s %-6s %6s %9s %8s %6s %s\n' \
        "$shape" "$arm" "$d" "$ms" "${conv:-ABORT(rc=$rc)}" "${dep:--}" "${out:-<no value>}"
      [ "$rc" -eq 0 ] && [ "$conv" = true ] || cleared=0
    done
  done
  if [ "$cleared" -eq 1 ]; then
    # The maximum is taken over `$shapes` — ONE list, the same one the clearing loop above reads.
    # A second list naming only "the depth-bearing families" stood here, and it was a place the
    # rule could drift from the figure it defines: adding a depth-bearing family to the RECORDED
    # `fixtures` without adding it here would silently under-report the maximum, and the
    # detector's voiding term could not catch it, because the recorded string would be unchanged.
    # The depth-0 families contribute 0 and cannot be the maximum, so iterating all of them costs
    # two extra cells per rung and REMOVES the drift rather than documenting it.
    best=0
    for shape in $shapes; do
      dep=$(cell "$shape" depth "$d" | sed -n 's/.*"depth":\([0-9]*\).*/\1/p')
      [ -n "$dep" ] && [ "$dep" -gt "$best" ] && best=$dep
    done
    verified=$best
    echo "rung d=$d CLEARED — greatest condensation depth at this rung: $best"
  else
    echo "rung d=$d NOT CLEARED — the ladder ends here"
    break
  fi
done

echo
# ★ QUOTED, NOT PARAPHRASED. This is the string `lib/acceptance.nix` records as the comparison's
# pinned DERIVATION FUNCTION term, printed character-for-character so the two can be diffed rather
# than read for agreement. A paraphrase here would read as agreement while the detector's voiding
# term compared something else. "…named beside it" is the `fixtures` list, printed below.
echo "derivation: the greatest condensation depth at which every arm of ci/bench/cost-classes.nix completed with converged=true, over the fixture families named beside it"
echo "fixture families: $shapes"
echo "verified depth: $verified"
