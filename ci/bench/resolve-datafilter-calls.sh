#!/usr/bin/env bash
# Reads the `resolve-datafilter-calls.nix` arms and REFUSES if a `visible` read applies `dataFilter`
# more than once per visit it reads (den-hoag-gayc C1 spec §2.2 item 4: the value is the datum the
# presence test already forced).
#
#   ./ci/bench/resolve-datafilter-calls.sh   -> arm rc applications want value
#
# ★ THE `groupBy-*` ARMS ARE THE LIVE CONTROL: the strict key reads every witness once, five
# applications. A control that reads anything else means the trace did not reach the count, and the
# run is REFUSED as unmeasured, whatever the `group-*` arms read.
set -u
cd "$(dirname "$0")/../.." || exit 99

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

fail=0
refuse() {
  echo "REFUSED: $*"
  fail=1
}

declare -A want=([group-single]=1 [group-both]=5 [groupBy-single]=5 [groupBy-both]=5)

printf '%-15s %3s %12s %4s  %s\n' arm rc applications want value
for arm in groupBy-single groupBy-both group-single group-both; do
  nix-instantiate --eval --strict --argstr arm "$arm" ./ci/bench/resolve-datafilter-calls.nix \
    >"$tmp/out" 2>"$tmp/err"
  rc=$?
  n=$(grep -c '^trace: DF ' "$tmp/err")
  val=$(tr -d '\n' <"$tmp/out")
  printf '%-15s %3s %12s %4s  %s\n' "$arm" "$rc" "$n" "${want[$arm]}" "${val:-<no value>}"
  [ "$rc" -eq 0 ] || refuse "$arm exited $rc -- $(head -c 300 "$tmp/err")"
  if [ "$n" -ne "${want[$arm]}" ]; then
    case "$arm" in
      groupBy-*) refuse "CONTROL $arm read $n applications, expected ${want[$arm]} -- the instrument, not the selection" ;;
      *) refuse "$arm applied dataFilter $n times, expected ${want[$arm]}" ;;
    esac
  fi
done

echo
if [ "$fail" -eq 0 ]; then
  echo "every visible read applies dataFilter once per visit it reads -- and the strict control reads all five"
else
  echo "AT LEAST ONE ARM RE-APPLIES dataFilter, OR THE INSTRUMENT DID NOT MEASURE WHAT IT PRINTED"
fi
exit "$fail"
