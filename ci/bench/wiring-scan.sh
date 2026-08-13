#!/usr/bin/env bash
# `wiringFor`'s sweep: an EXIT-CODE instrument, because the thing being measured is an abort no
# in-language assertion can observe, and an ORDER the suite's own cell cannot arm.
#
#   ./ci/bench/wiring-scan.sh   -> per-cell readings, then SCAN-FLAT | SCAN-HAS-A-CEILING | INVALID
#
# A GREEN RUN WITH NO FIRING CONTROL IS AN INVALID RUN, never a pass. The claim is that the shipped
# indexed scan RETURNS where the list walk it replaced ABORTS — which says nothing at all unless
# the walk aborted in this same sweep, on this same resolution.
#
# THE CONTROL IS CHECKED FOR FAITHFULNESS BEFORE IT IS TRUSTED. `agree` runs both arms at a size
# both survive and compares the two lists element for element. A control that computed something
# else would abort for reasons that say nothing about the construction under test, so a false
# `agree` invalidates the sweep rather than being reported as a difference.
#
# BOTH SIGNATURES ARE ARMED, because a sweep armed for one reads the other as a green run:
#   default guard   the walk calls itself per entry -> `max-call-depth exceeded`   CALLDEPTH
#   raised guard    the same walk, guard moved out of the way -> `stack overflow`  CSTACK
# Raising the guard does not make the walk flat; it moves the failure to the mechanism with
# nothing in front of it. `max-call-depth exceeded` is matched BEFORE the generic `stack overflow`
# because the generic string also appears in the specific diagnostic.
#
# THE ORDERING ARM IS NOT ABOUT AN ABORT. It reports the fixture's global schedule order beside the
# order a kind-grouped construction would produce. If those agreed, the suite's order cell would be
# green under either construction and would be pinning nothing — so agreement is INVALID here
# rather than a pass.
#
# Every exit code is read IMMEDIATELY — `$?` after a pipe reads the pipe's last stage and is a
# false green.
set -u
cd "$(dirname "$0")/../.." || exit 99

cell() { # cell <arm> <n> [extra nix options...] -> prints the reading, returns the evaluator's rc
  local arm=$1 n=$2
  shift 2
  nix-instantiate "$@" --eval --strict --json \
    --arg n "$n" --argstr arm "$arm" ./ci/bench/wiring-scan.nix 2>&1
}

label() { # label <stderr blob> -> the abort signature
  case "$1" in
  *"max-call-depth exceeded"*) echo CALLDEPTH ;;
  *"stack overflow"*) echo CSTACK ;;
  *) echo OTHER ;;
  esac
}

# Counted PER SIGNATURE, not pooled. A sweep in which only one of the two fired armed one
# mechanism and left the other untested, and pooling would hide exactly that.
calldepth_fired=0
cstack_fired=0
scan_failures=0
invalid=0

echo "── the control is the real construction, checked before it is trusted ──"
out=$(cell agree 500)
rc=$?
printf '%-14s %7s exit=%d %s\n' agree 500 "$rc" "$out"
if [ "$rc" -ne 0 ] || [ "$out" != true ]; then
  echo "   INVALID — the walk and the scan do not compute the same list, so the control is a strawman"
  invalid=$((invalid + 1))
fi

echo
echo "── scan versus walk, DEFAULT guard: the walk's descent depth is its trace length ──"
for n in 8000 9900 10000 20000; do
  for arm in scan walk; do
    out=$(cell "$arm" "$n")
    rc=$?
    if [ "$arm" = scan ]; then
      [ "$rc" -eq 0 ] || scan_failures=$((scan_failures + 1))
      printf '%-14s %7s exit=%d %s\n' "$arm" "$n" "$rc" "${out:-<no value>}"
    elif [ "$rc" -eq 0 ]; then
      printf '%-14s %7s exit=0 green — BELOW its boundary, so this cell arms nothing\n' "$arm" "$n"
    else
      sig=$(label "$out")
      [ "$sig" = CALLDEPTH ] && calldepth_fired=$((calldepth_fired + 1))
      [ "$sig" = CSTACK ] && cstack_fired=$((cstack_fired + 1))
      printf '%-14s %7s exit=%d %s\n' "$arm" "$n" "$rc" "$sig"
    fi
  done
done

echo
echo "── the SAME walk with the guard raised: the failure moves, it does not go away ──"
for n in 20000 60000; do
  for arm in scan walk; do
    out=$(cell "$arm" "$n" --option max-call-depth 1000000)
    rc=$?
    if [ "$arm" = scan ]; then
      [ "$rc" -eq 0 ] || scan_failures=$((scan_failures + 1))
      printf '%-14s %7s exit=%d %s\n' "$arm@1e6" "$n" "$rc" "${out:-<no value>}"
    elif [ "$rc" -eq 0 ]; then
      printf '%-14s %7s exit=0 green — BELOW its boundary, so this cell arms nothing\n' "$arm@1e6" "$n"
    else
      sig=$(label "$out")
      [ "$sig" = CALLDEPTH ] && calldepth_fired=$((calldepth_fired + 1))
      [ "$sig" = CSTACK ] && cstack_fired=$((cstack_fired + 1))
      printf '%-14s %7s exit=%d %s\n' "$arm@1e6" "$n" "$rc" "$sig"
    fi
  done
done

echo
echo "── the scan alone, an order of magnitude past where the walk died ──"
# The size this construction's landing claim quotes. It is run HERE, by the committed instrument,
# rather than stated as a figure someone once measured: a number in a commit body that no script
# reproduces is a number the next reader has to take on trust. The walk is not run at this size —
# it aborted at 60000 above, and re-establishing that costs nothing and proves nothing.
out=$(cell scan 200000 --option max-call-depth 1000000)
rc=$?
[ "$rc" -eq 0 ] || scan_failures=$((scan_failures + 1))
printf '%-14s %7s exit=%d %s\n' "scan@1e6" 200000 "$rc" "${out:-<no value>}"

echo
echo "── uncatchability, and the catcher's own control ──"
out=$(cell walkTry 20000)
rc=$?
if [ "$rc" -eq 0 ]; then
  printf '%-14s %7s exit=0 RETURNED (%s) — tryEval contained it, which would refute the reason this is a sweep\n' \
    walkTry 20000 "$out"
  invalid=$((invalid + 1))
else
  printf '%-14s %7s exit=%d %s — the wrapper did not contain it\n' walkTry 20000 "$rc" "$(label "$out")"
fi
out=$(cell catchControl 1)
rc=$?
printf '%-14s %7s exit=%d %s\n' catchControl 1 "$rc" "$out"
if [ "$rc" -ne 0 ] || [ "$out" != false ]; then
  echo "   INVALID — the catcher does not catch, so an abort reading says nothing"
  invalid=$((invalid + 1))
fi

echo
echo "── the ordering control: what the suite's order cell would fail to distinguish ──"
for arm in globalOrder byKindOrder; do
  out=$(cell "$arm" 1)
  rc=$?
  printf '%-14s %7s exit=%d %s\n' "$arm" - "$rc" "$out"
  [ "$rc" -eq 0 ] || invalid=$((invalid + 1))
done
out=$(cell orderDiffers 1)
rc=$?
printf '%-14s %7s exit=%d %s\n' orderDiffers - "$rc" "$out"
if [ "$rc" -ne 0 ] || [ "$out" != true ]; then
  echo "   INVALID — the two orders agree on this fixture, so the suite's order cell pins nothing"
  invalid=$((invalid + 1))
fi

echo
echo "controls: CALLDEPTH fired: $calldepth_fired   CSTACK fired: $cstack_fired   invalid arms: $invalid   scan failures: $scan_failures"
if [ "$invalid" -ne 0 ] || [ "$calldepth_fired" -eq 0 ] || [ "$cstack_fired" -eq 0 ]; then
  echo "INVALID — a control did not fire or did not hold, so no arm below it is readable"
  exit 2
elif [ "$scan_failures" -ne 0 ]; then
  echo "SCAN-HAS-A-CEILING"
  exit 1
else
  echo "SCAN-FLAT within the range swept, where the walk it replaced aborts under both signatures"
fi
