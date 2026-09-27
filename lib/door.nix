# THE PUBLISHED DOOR OVER A NATIVE FORMAL SET (den-hoag-7gp66 P1, R5).
#
# A native closed formal set refuses an unknown argument, and a native required formal a missing
# one, past `tryEval` (ADR-0025 item 1). `door name impl` is `impl` behind gen-prelude's shared
# checks, which refuse the same violations by name and catchably, naming `gen-scope.<name>` first
# (R6). `impl` keeps its native pattern, and its formals are the ONE statement of the door's fields:
# the required and accepted sets are read off them rather than transcribed beside them.
#
# The class is the pattern's own shape, per the spec's partition (§v1.2):
#   record  (every field required) — `checkRequired`: a missing field is refused and an extra one is
#           ADMITTED, R5's stated price; only the declared fields reach `impl`.
#   options (every field optional) — `checkOptions`: an unknown field is refused, the set is closed.
#   mixed   — `checkOptions` over `checkRequired`, closed over the whole set. Transitional: P2 moves
#           the options off the record.
#
# The fields are read once per door, at the export; a call pays the checks and nothing else. The
# library's own calls reach `impl` directly — a recursion through the door would re-check per node.
{ prelude }:
name: impl:
let
  door = "gen-scope.${name}";
  fields = builtins.functionArgs impl;
  accepted = builtins.attrNames fields;
  required = builtins.filter (f: !fields.${f}) accepted;
in
if required == accepted then
  args: impl (builtins.intersectAttrs fields (prelude.checkRequired door required args))
else if required == [ ] then
  args: impl (prelude.checkOptions door accepted args)
else
  args: impl (prelude.checkOptions door accepted (prelude.checkRequired door required args))
