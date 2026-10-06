#!/usr/bin/env bash
# Reads the `resolve-visible-fanout.nix` arms and REFUSES if `visible` under a declared `group` costs
# more per walk-tree visit than its recorded bound, or LESS (a ratchet: lower the bound to the reading
# in the same change, so a won optimization stays won).
#
#   ./ci/bench/resolve-visible-fanout.sh   -> arm d rc nrThunks value, then each arm's marginal
#
# THE READING is the MARGINAL cost, nrThunks(d2) - nrThunks(d1), over the visits the two sizes differ
# by, so the evaluator's start-up and the library's own evaluation cancel. It is compared EXACTLY, as
# integers: thunk counts are deterministic for one evaluator, and an exact bound is what lets a
# planted regression of one thunk per visit read.
#
# EXIT CODES are the hub perf-bench's (den-hoag-r8y89, as built): 0 every arm equals its bound ·
# 1 a regression, or an arm that did not measure · 7 RE-ANCHOR OWED · 8 RATCHET OWED (a reading below
# its bound; lower the bound in the same change) · 9 RE-ANCHOR BLOCKED. 1 outranks 7 and 9, which
# outrank 8.
#
# ★ THE BOUNDS BELONG TO ONE EVALUATOR AND ONE SOURCE, recorded beside them: `anchor` is the
# `nix-instantiate --version` they were read under, and `anchor_source` digests the source they were
# read from (`lib/`, `default.nix`, the root `flake.lock` and the fixture). Only the ENVIRONMENT
# re-anchors (r8y89 P5 (i)): this bench has no reference pin, so that is the evaluator alone. The
# source, member pins included, is the change under test. A different evaluator compares nothing:
#   · 7 when the source equals `anchor_source`: record the printed readings as the bounds, with the
#     new `anchor`;
#   · 9 when the source moved too: re-anchor at the revision whose source is `anchor_source`, then run
#     this tree against those bounds. Re-recording from this tree would absorb its own regression.
# Every change that writes a bound also writes `anchor_source`.
#
# ★ USE `nix-instantiate --arg`, NEVER `nix eval --file` (see `resolve-inherit-set.sh`).
set -u
cd "$(dirname "$0")/../.." || exit 99
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

anchor='nix-instantiate (Nix) 2.34.8'
anchor_source=6c5d6c0265ee9d0a
# arm -> "d1 d2 visits(d2)-visits(d1) bound(thunks over that difference)"
declare -A cell=(
  [fanout]="3 5 1280 150246"
  [neron]="100 400 1500 195300"
  [chain]="400 1600 1200 271200"
)
declare -A want=(
  [fanout,3]=16 [fanout,5]=256
  [neron,100]=1 [neron,400]=1
  [chain,400]=1 [chain,1600]=1
)

ver=$(nix-instantiate --version)
source=$({
  find lib -type f -name '*.nix' | LC_ALL=C sort
  printf '%s\n' default.nix flake.lock ci/bench/resolve-visible-fanout.nix
} | xargs sha256sum | sha256sum | cut -c1-16)
reanchor=0
if [ "$ver" != "$anchor" ]; then
  if [ "$source" = "$anchor_source" ]; then reanchor=7; else reanchor=9; fi
fi

fail=0
printf '%-8s %5s %3s %10s  %s\n' arm d rc nrThunks answers
declare -A cost
for arm in fanout neron chain; do
  read -r d1 d2 dv bound <<<"${cell[$arm]}"
  for d in $d1 $d2; do
    rm -f "$tmp/stats.json"
    NIX_SHOW_STATS=1 NIX_SHOW_STATS_PATH="$tmp/stats.json" \
      nix-instantiate --eval --strict --json --argstr arm "$arm" --arg d "$d" \
      ./ci/bench/resolve-visible-fanout.nix >"$tmp/out" 2>"$tmp/err"
    rc=$?
    t=$(tr -d ' \n' <"$tmp/stats.json" 2>/dev/null | sed -n 's/.*"nrThunks":\([0-9]*\).*/\1/p')
    n=$(tr -cd ',' <"$tmp/out" | wc -c)
    [ -s "$tmp/out" ] && [ "$(cat "$tmp/out")" != "[]" ] && n=$((n + 1)) || n=0
    cost[$arm,$d]=${t:-}
    printf '%-8s %5s %3s %10s  %s\n' "$arm" "$d" "$rc" "${t:-<none>}" "$n"
    if [ "$rc" -ne 0 ] || [ -z "$t" ]; then
      echo "REFUSED: $arm d=$d did not measure (rc $rc) -- $(head -c 300 "$tmp/err")"
      fail=1
    elif [ "$n" != "${want[$arm,$d]}" ]; then
      echo "REFUSED: $arm d=$d answered $n, expected ${want[$arm,$d]}"
      fail=1
    fi
  done
done

echo
if [ "$reanchor" -ne 0 ]; then
  [ "$reanchor" -eq 7 ] && echo "RE-ANCHOR OWED: the bounds were read under '$anchor', this is '$ver'; record these:" ||
    echo "RE-ANCHOR BLOCKED: the bounds were read under '$anchor' from source $anchor_source; this is '$ver' and source $source. Re-anchor at the revision whose source is $anchor_source, then run this tree:"
  for arm in fanout neron chain; do
    read -r d1 d2 dv bound <<<"${cell[$arm]}"
    a=${cost[$arm,$d1]:-}
    b=${cost[$arm,$d2]:-}
    [ -n "$a" ] && [ -n "$b" ] && echo "  $arm $((b - a))"
  done
  echo "  anchor_source $source"
  [ "$fail" -ne 0 ] && exit 1
  exit "$reanchor"
fi
for arm in fanout neron chain; do
  read -r d1 d2 dv bound <<<"${cell[$arm]}"
  a=${cost[$arm,$d1]:-}
  b=${cost[$arm,$d2]:-}
  [ -n "$a" ] && [ -n "$b" ] || continue
  delta=$((b - a))
  per=$(awk -v x="$delta" -v v="$dv" 'BEGIN { printf "%.2f", x / v }')
  if [ "$delta" -gt "$bound" ]; then
    echo "REGRESSION: $arm $delta thunks over $dv visits ($per per visit) > bound $bound"
    fail=1
  elif [ "$delta" -lt "$bound" ]; then
    echo "RATCHET OWED: $arm $delta < bound $bound ($per per visit) -- lower the bound to $delta in this change"
    [ "$fail" -eq 0 ] && fail=8
  else
    echo "$arm $delta thunks over $dv visits ($per per visit) = bound"
  fi
done
exit "$fail"
