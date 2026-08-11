#!/usr/bin/env bash
# The engine's ceiling sweep: an EXIT-CODE instrument, because the thing being measured is an
# abort no in-language assertion can observe.
#
#   ./ci/bench/engine-ceiling.sh   -> per-cell readings, then CEILING-FREE | CEILING-FOUND | INVALID
#
# A GREEN RUN WITH NO FIRING CONTROL IS AN INVALID RUN, never a pass. Every engine claim below
# rides on the abort controls having fired in the same sweep: if they did not, the evaluation
# could not have observed an abort at all and a green engine row says nothing about whether the
# engine would have survived one.
#
# BOTH SIGNATURES ARE ARMED, because an engine armed for one misses the other:
#   unforcedCall      chains through a function application -> `max-call-depth exceeded`
#   unforcedOperator  chains through `+`                    -> `stack overflow`, no guard first
# The labels are read off the diagnostic, and `max-call-depth exceeded` is tested BEFORE the
# generic `stack overflow` because the second string is a prefix of neither but the generic
# message also appears where the specific one does not.
#
# `tryUnforced` is the uncatchability cell: the same construction wrapped in `tryEval`, which
# still dies. `catchControl` in the same sweep shows the catcher itself works, so an abort
# reading is not confused with a broken evaluation.
#
# Every exit code is read IMMEDIATELY — `$?` after a pipe reads the pipe's last stage and is a
# false green.
set -u
cd "$(dirname "$0")/../.." || exit 99

cell() { # cell <arm> <n> -> prints the reading, returns the evaluator's exit code
  nix-instantiate --eval --strict --json \
    --arg n "$2" --argstr arm "$1" ./ci/bench/engine-ceiling.nix 2>&1
}

label() { # label <stderr blob> -> the abort signature
  case "$1" in
  *"max-call-depth exceeded"*) echo CALLDEPTH ;;
  *"stack overflow"*) echo CSTACK ;;
  *) echo OTHER ;;
  esac
}

# Counted PER SIGNATURE, not pooled. A sweep in which only one of the two fired is a sweep that
# armed one mechanism and left the other untested, and pooling the counts would hide exactly
# that. A cell below its own boundary returns and is reported as arming nothing.
calldepth_fired=0
cstack_fired=0
controls_run=0
engine_failures=0

echo "── the forced/unforced comparison: one loop, one accumulator, one round count ──"
for n in 9995 9998 45000 45500 50000; do
  for arm in forced unforcedCall unforcedOperator; do
    out=$(cell "$arm" "$n")
    rc=$?
    if [ "$arm" = forced ]; then
      [ "$rc" -eq 0 ] || engine_failures=$((engine_failures + 1))
      printf '%-18s %6s exit=%d %s\n' "$arm" "$n" "$rc" "${out:-<no value>}"
    else
      controls_run=$((controls_run + 1))
      if [ "$rc" -eq 0 ]; then
        printf '%-18s %6s exit=0 green — BELOW its boundary, so this cell arms nothing\n' "$arm" "$n"
      else
        sig=$(label "$out")
        [ "$sig" = CALLDEPTH ] && calldepth_fired=$((calldepth_fired + 1))
        [ "$sig" = CSTACK ] && cstack_fired=$((cstack_fired + 1))
        printf '%-18s %6s exit=%d %s\n' "$arm" "$n" "$rc" "$sig"
      fi
    fi
  done
done

echo
echo "── uncatchability, and the catcher's own control ──"
out=$(cell tryUnforced 50000)
rc=$?
controls_run=$((controls_run + 1))
[ "$rc" -eq 0 ] || cstack_fired=$((cstack_fired + 1))
printf '%-18s %6s exit=%d %s\n' tryUnforced 50000 "$rc" \
  "$([ "$rc" -eq 0 ] && echo "RETURNED — tryEval contained it, which would refute the claim" || label "$out")"
for arm in okControl catchControl; do
  out=$(cell "$arm" 1)
  rc=$?
  printf '%-18s %6s exit=%d %s\n' "$arm" 1 "$rc" "${out:-<no value>}"
  [ "$rc" -eq 0 ] || engine_failures=$((engine_failures + 1))
done

echo
echo "── the refusals, read where their text is readable ──"
# One of these two is not catchable at all and the other's MESSAGE is not: `tryEval` kills the
# evaluation on an argument-arity error and discards the message on a throw. A refusal that does
# not name the surface and the offending rule is not a named refusal, so the text is matched here
# rather than asserted in prose.
for spec in "refuseUnknownField negs" "refuseConjunctiveOnUnaryArm unary-only"; do
  read -r arm want <<<"$spec"
  out=$(cell "$arm" 1)
  rc=$?
  controls_run=$((controls_run + 1))
  case "$out" in
  *"$want"*) named="NAMED (matched '$want')" ;;
  *) named="UNNAMED — the diagnostic does not carry '$want'" ;;
  esac
  [ "$rc" -eq 0 ] && named="RETURNED — the refusal did not fire"
  printf '%-26s %6s exit=%d %s\n' "$arm" 1 "$rc" "$named"
  case "$named" in
  NAMED*) ;;
  *) engine_failures=$((engine_failures + 1)) ;;
  esac
done

echo
echo "── the engine's own loops, at the sizes that are reachable ──"
for n in 500 2000 8000; do
  for arm in rounds outer; do
    out=$(cell "$arm" "$n")
    rc=$?
    [ "$rc" -eq 0 ] || engine_failures=$((engine_failures + 1))
    printf '%-18s %6s exit=%d %s\n' "$arm" "$n" "$rc" "${out:-<no value>}"
  done
done

echo
echo "── the round loop PAST the call-depth guard, which is what says it is flat ──"
# A loop written as a self-applying lambda spends one evaluator frame per iteration, so its
# descent depth IS its iteration count and it cannot pass `max-call-depth` (10000) at all. A
# GREEN run at 12001 rounds is therefore a positive statement about the encoding rather than
# another row below a boundary — and it is the one reading that distinguishes a flat loop from a
# recursive one that has simply not been pushed far enough yet.
#
# The outer loop is not driven here: its cost is outer rounds × two least-model passes × atoms,
# so reaching 10001 outer rounds needs ~20000 atoms and runs for minutes. It is run separately
# and its reading is recorded in README; this sweep states what it did NOT push rather than
# inferring the outer loop's encoding from the inner one's.
out=$(cell rounds 12000)
rc=$?
[ "$rc" -eq 0 ] || engine_failures=$((engine_failures + 1))
printf '%-18s %6s exit=%d %s\n' rounds 12000 "$rc" "${out:-<no value>}"

echo
echo "controls run: $controls_run   CALLDEPTH fired: $calldepth_fired   CSTACK fired: $cstack_fired   engine failures: $engine_failures"
if [ "$calldepth_fired" -eq 0 ] || [ "$cstack_fired" -eq 0 ]; then
  echo "INVALID — a signature did not fire, so this sweep armed one mechanism and left the other untested"
  exit 2
elif [ "$engine_failures" -ne 0 ]; then
  echo "CEILING-FOUND"
  exit 1
else
  echo "CEILING-FREE within the range swept"
fi
