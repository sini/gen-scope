#!/usr/bin/env bash
# The wiring surface's sweep: an EXIT-CODE instrument, because everything it measures is an abort
# no in-language assertion can observe, plus an ORDER the suite's own cell cannot arm.
#
#   ./ci/bench/wiring-scan.sh   -> per-cell readings, then READ-FLAT | READ-HAS-A-CEILING | INVALID
#
# A GREEN RUN WITH NO FIRING CONTROL IS AN INVALID RUN, never a pass. Two claims are under test and
# neither says anything on its own:
#
#   COST      the shipped field read RETURNS where the list walk it eventually replaced ABORTS —
#             which is empty unless the walk aborted in this same sweep, on this same resolution.
#   REFUSAL   the ill-formed resolutions that used to reach the evaluator through the consumer
#             accessors can no longer be handed to the library at all — which is empty unless those
#             same inputs are seen aborting through the RETIRED constructions in this same sweep,
#             and unless the shipped library is seen to have lost the surface.
#
# THE CONTROLS ARE CHECKED FOR FAITHFULNESS BEFORE THEY ARE TRUSTED. `agree` runs the shipped read
# and both retired constructions at a size all three survive and compares the lists element for
# element. A control that computed something else would abort for reasons that say nothing about
# the construction under test, so a false `agree` invalidates the sweep rather than being reported
# as a difference.
#
# BOTH WALK SIGNATURES ARE ARMED, because a sweep armed for one reads the other as a green run:
#   default guard   the walk calls itself per entry -> `max-call-depth exceeded`   CALLDEPTH
#   raised guard    the same walk, guard moved out of the way -> `stack overflow`  CSTACK
# Raising the guard does not make the walk flat; it moves the failure to the mechanism with
# nothing in front of it. `max-call-depth exceeded` is matched BEFORE the generic `stack overflow`
# because the generic string also appears in the specific diagnostic.
#
# THE READ ARMS ARE NOT ABOUT A COST. The published record is total — a key for every subject a
# claim was about — so a consumer's read decides whether the never-registered subject stays
# distinguishable from the registered-but-unwired one. Of the three ways to write it, the two
# reflexive ones are the two broken ones, and both are run here rather than described.
#
# THE ORDERING ARM IS NOT ABOUT AN ABORT EITHER. It reports the fixture's global schedule order
# beside the order a kind-grouped construction would produce. If those agreed, the suite's order
# cell would be green under either construction and would be pinning nothing — so agreement is
# INVALID here rather than a pass.
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

reason() { # reason <stderr blob> -> the evaluator's own words, one line
  printf '%s' "$1" | grep -oE "error: .*" | head -1
}

# Counted PER SIGNATURE, not pooled. A sweep in which only one of the two walk signatures fired
# armed one mechanism and left the other untested, and pooling would hide exactly that.
calldepth_fired=0
cstack_fired=0
illformed_fired=0
read_failures=0
invalid=0

echo "── the controls are the real constructions, checked before they are trusted ──"
out=$(cell agree 500)
rc=$?
printf '%-22s %7s exit=%d %s\n' agree 500 "$rc" "$out"
if [ "$rc" -ne 0 ] || [ "$out" != true ]; then
  echo "   INVALID — the shipped read and the two retired constructions do not compute the same"
  echo "             list, so the controls are strawmen"
  invalid=$((invalid + 1))
fi

echo
echo "── what ships, against the two constructions it retired: DEFAULT guard ──"
for n in 8000 9900 10000 20000; do
  for arm in read scan walk; do
    out=$(cell "$arm" "$n")
    rc=$?
    if [ "$arm" = read ]; then
      [ "$rc" -eq 0 ] || read_failures=$((read_failures + 1))
      printf '%-22s %7s exit=%d %s\n' "$arm" "$n" "$rc" "${out:-<no value>}"
    elif [ "$rc" -eq 0 ]; then
      printf '%-22s %7s exit=0 green — BELOW its boundary, so this cell arms nothing\n' "$arm" "$n"
    else
      sig=$(label "$out")
      [ "$sig" = CALLDEPTH ] && calldepth_fired=$((calldepth_fired + 1))
      [ "$sig" = CSTACK ] && cstack_fired=$((cstack_fired + 1))
      printf '%-22s %7s exit=%d %s\n' "$arm" "$n" "$rc" "$sig"
    fi
  done
done

echo
echo "── the SAME walk with the guard raised: the failure moves, it does not go away ──"
for n in 20000 60000; do
  for arm in read walk; do
    out=$(cell "$arm" "$n" --option max-call-depth 1000000)
    rc=$?
    if [ "$arm" = read ]; then
      [ "$rc" -eq 0 ] || read_failures=$((read_failures + 1))
      printf '%-22s %7s exit=%d %s\n' "$arm@1e6" "$n" "$rc" "${out:-<no value>}"
    elif [ "$rc" -eq 0 ]; then
      printf '%-22s %7s exit=0 green — BELOW its boundary, so this cell arms nothing\n' "$arm@1e6" "$n"
    else
      sig=$(label "$out")
      [ "$sig" = CALLDEPTH ] && calldepth_fired=$((calldepth_fired + 1))
      [ "$sig" = CSTACK ] && cstack_fired=$((cstack_fired + 1))
      printf '%-22s %7s exit=%d %s\n' "$arm@1e6" "$n" "$rc" "$sig"
    fi
  done
done

echo
echo "── the read alone, an order of magnitude past where the walk died ──"
# The size this construction's landing claim quotes. It is run HERE, by the committed instrument,
# rather than stated as a figure someone once measured: a number in a commit body that no script
# reproduces is a number the next reader has to take on trust. The walk is not run at this size —
# it aborted at 60000 above, and re-establishing that costs nothing and proves nothing.
out=$(cell read 200000 --option max-call-depth 1000000)
rc=$?
[ "$rc" -eq 0 ] || read_failures=$((read_failures + 1))
printf '%-22s %7s exit=%d %s\n' "read@1e6" 200000 "$rc" "${out:-<no value>}"

echo
echo "── uncatchability, and the catcher's own control ──"
out=$(cell walkTry 20000)
rc=$?
if [ "$rc" -eq 0 ]; then
  printf '%-22s %7s exit=0 RETURNED (%s) — tryEval contained it, which would refute the reason this is a sweep\n' \
    walkTry 20000 "$out"
  invalid=$((invalid + 1))
else
  printf '%-22s %7s exit=%d %s — the wrapper did not contain it\n' walkTry 20000 "$rc" "$(label "$out")"
fi
out=$(cell catchControl 1)
rc=$?
printf '%-22s %7s exit=%d %s\n' catchControl 1 "$rc" "$out"
if [ "$rc" -ne 0 ] || [ "$out" != false ]; then
  echo "   INVALID — the catcher does not catch, so an abort reading says nothing"
  invalid=$((invalid + 1))
fi

echo
echo "── the ill-formed resolutions, through the RETIRED constructions: every one an abort ──"
# Each is a way the two published views could disagree, or a malformed value standing in for one.
# They are the negative control for the retirement: the surface is gone, and these are what it did
# with such input while it was there.
for arm in missingKind shortList noByKind noKindField traceNotList noIdHash \
  spliceMissingKind spliceShortList spliceNoIdHash; do
  out=$(cell "$arm" 8)
  rc=$?
  if [ "$rc" -eq 0 ]; then
    printf '%-22s %7s exit=0 RETURNED (%s) — this input was expected to abort\n' "$arm" - "$out"
    invalid=$((invalid + 1))
  else
    illformed_fired=$((illformed_fired + 1))
    printf '%-22s %7s exit=%d %s\n' "$arm" - "$rc" "$(reason "$out")"
  fi
done
out=$(cell handAligned 8)
rc=$?
printf '%-22s %7s exit=%d %s\n' handAligned - "$rc" "$out"
if [ "$rc" -ne 0 ] || [ "$out" != '"returned"' ]; then
  echo "   INVALID — the ALIGNED hand-built resolution did not return, so the nine readings above"
  echo "             are about hand-built input rather than about misalignment"
  invalid=$((invalid + 1))
fi

echo
echo "── and the surface those nine inputs used to reach: gone from the shipped library ──"
# The only arm that can show it. An absence is not something the aborting arms above demonstrate.
out=$(cell surfaceGone 1)
rc=$?
printf '%-22s %7s exit=%d %s\n' surfaceGone - "$rc" "$out"
if [ "$rc" -ne 0 ] || [ "$out" != true ]; then
  echo "   INVALID — the accessors are still exported, so the nine arms above describe a live"
  echo "             surface rather than a retired one"
  invalid=$((invalid + 1))
fi

echo
echo "── the consumer's read: of the three ways to write it, the two reflexive ones are broken ──"
out=$(cell bareReadNeverClaimed 1)
rc=$?
if [ "$rc" -eq 0 ]; then
  printf '%-22s %7s exit=0 RETURNED (%s) — the bare read was expected to abort on a subject no\n' \
    bareRead - "$out"
  echo "                              claim named"
  invalid=$((invalid + 1))
else
  printf '%-22s %7s exit=%d %s\n' bareRead - "$rc" "$(reason "$out")"
fi
erasing_unwired=$(cell erasingReadUnwired 1)
rc=$?
erasing_never=$(cell erasingReadNeverClaimed 1)
rc2=$?
printf '%-22s %7s exit=%d,%d unwired=%s neverClaimed=%s\n' \
  erasingRead - "$rc" "$rc2" "$erasing_unwired" "$erasing_never"
if [ "$rc" -ne 0 ] || [ "$rc2" -ne 0 ] || [ "$erasing_unwired" != "$erasing_never" ]; then
  echo "   INVALID — the erasing read did not erase, so the safe read's cells are reading a"
  echo "             difference no construction could have lost"
  invalid=$((invalid + 1))
fi
safe_unwired=$(cell safeReadUnwired 1)
rc=$?
safe_never=$(cell safeReadNeverClaimed 1)
rc2=$?
printf '%-22s %7s exit=%d,%d unwired=%s neverClaimed=%s\n' \
  safeRead - "$rc" "$rc2" "$safe_unwired" "$safe_never"
if [ "$rc" -ne 0 ] || [ "$rc2" -ne 0 ] || [ "$safe_unwired" = "$safe_never" ]; then
  echo "   INVALID — the safe read answered the same thing for both subjects, so absence does not"
  echo "             mean 'not registered' at the surface a consumer is told to read"
  invalid=$((invalid + 1))
fi

echo
echo "── the ordering control: what the suite's order cell would fail to distinguish ──"
for arm in globalOrder byKindOrder; do
  out=$(cell "$arm" 1)
  rc=$?
  printf '%-22s %7s exit=%d %s\n' "$arm" - "$rc" "$out"
  [ "$rc" -eq 0 ] || invalid=$((invalid + 1))
done
out=$(cell orderDiffers 1)
rc=$?
printf '%-22s %7s exit=%d %s\n' orderDiffers - "$rc" "$out"
if [ "$rc" -ne 0 ] || [ "$out" != true ]; then
  echo "   INVALID — the two orders agree on this fixture, so the suite's order cell pins nothing"
  invalid=$((invalid + 1))
fi

echo
echo "controls: CALLDEPTH fired: $calldepth_fired   CSTACK fired: $cstack_fired   ill-formed aborts: $illformed_fired/9   invalid arms: $invalid   read failures: $read_failures"
if [ "$invalid" -ne 0 ] || [ "$calldepth_fired" -eq 0 ] || [ "$cstack_fired" -eq 0 ] || [ "$illformed_fired" -ne 9 ]; then
  echo "INVALID — a control did not fire or did not hold, so no arm below it is readable"
  exit 2
elif [ "$read_failures" -ne 0 ]; then
  echo "READ-HAS-A-CEILING"
  exit 1
else
  echo "READ-FLAT within the range swept, where the walk it replaced aborts under both signatures,"
  echo "and every ill-formed resolution the retired accessors accepted is now unconstructible"
fi
