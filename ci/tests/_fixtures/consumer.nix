# The consumer side of the cascade's published wiring: the read a caller performs over
# `resolution.wiring.<id>`, and the splice a caller assembles from it. Written once here and
# exercised by two suites, because a discipline written twice agrees only for as long as someone
# keeps the copies in step.
#
# NOT A SUITE. It sits under `_fixtures/` because the tree importer ignores any path containing
# `/_`, so this file is reached only by the suites that import it and never as a flake module.
#
# ★ WHY THIS IS A FIXTURE AND NOT A LIBRARY EXPORT. `resolveClaims` publishes one subject's entries
# in global schedule order, so reaching them is an attribute lookup and there is nothing left for
# an accessor to reconstruct. What a caller does have to get right is the READ, because the record
# is TOTAL: a key sits there for every subject a claim was about, so a missing key means the
# subject was never registered and a present record with `entries = [ ]` means it was registered
# and nothing wired it. Two observations, and the two reflexive ways of reading collapse or abort
# on exactly that difference — which is why both of them are kept below as armed controls rather
# than described in prose.
{ lib }:
rec {
  # The safe read: registration is DECIDED before anything is projected, so the two cases stay two.
  wiringOf =
    resolution: subject:
    let
      id = subject.id_hash;
    in
    if resolution.wiring ? ${id} then
      {
        registered = true;
        inherit (resolution.wiring.${id}) entries;
      }
    else
      { registered = false; };

  # The erasing read, kept beside the safe one AS ITS ARM. A default on the record answers `[ ]` for
  # the registered-but-unwired subject and `[ ]` for the subject no claim ever named, which is the
  # library's own erasure re-created one call outward. A cell claiming the two cases are
  # distinguishable pins nothing unless a construction that fails to distinguish them is live in
  # the same suite.
  erasingWiringOf =
    resolution: subject: (resolution.wiring.${subject.id_hash} or { entries = [ ]; }).entries;

  # One subject's wiring entries spliced into a single record, per top-level key: the values
  # contributed under a key — in the global schedule order the field publishes — handed to
  # `combine`, whose `key: [v]: v` signature is the one a kind's resource fold already has. One
  # vocabulary serves both because both are the same operation: several fragments arriving under
  # one name with a declared rule for reconciling them.
  #
  # `combine` has no default here, and that is the difference retirement makes. Single-writer-per-key
  # was the right refusal for a library surface that had to answer for callers who named no rule;
  # a caller assembling its own splice has already chosen one, and a default would be this fixture
  # choosing on its behalf.
  splice =
    {
      resolution,
      subject,
      combine,
    }:
    let
      w = wiringOf resolution subject;
      vals = map (e: e.wiring) (if w.registered then w.entries else [ ]);
      allKeys = lib.unique (lib.concatMap builtins.attrNames vals);
    in
    builtins.listToAttrs (
      map (
        k: lib.nameValuePair k (combine k (lib.concatMap (v: if v ? ${k} then [ v.${k} ] else [ ]) vals))
      ) allKeys
    );
}
