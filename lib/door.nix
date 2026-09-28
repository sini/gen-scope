# THE PUBLISHED DOORS (den-hoag-7gp66 P2, R7 argument structure / R5 field closure).
#
# Every published step that takes a RECORD is a gen-prelude `door`: its field contract is published
# as data (`__contract`, `__functionArgs`), and a violation is refused by name and catchably at the
# step's own application, naming `gen-scope.<name>` first (R6). A native closed formal refused the
# same violations past `tryEval` (ADR-0025 item 1).
#
# `impl` keeps its native pattern, and its formals stay the ONE statement of the door's fields: each
# constructor below reads the required and optional sets off them rather than transcribing them
# beside the door, so the published contract cannot drift from what the body accepts. The library's
# own calls reach `impl` directly — a recursion through the door would re-check per node.
#
# The three shapes R7 leaves:
#   record    every formal required: ONE open data record (R5). A missing field is refused; an extra
#             field is admitted and never reaches `impl`.
#   options   the defaulted formals become ONE closed options set, FIRST in the call, checked when
#             `f opts` is formed; the required formals follow as positional operands in the order
#             `positional` states (configuration first, subject last). `positional` must be exactly
#             the required formals — a mismatch is refused here, at the export, never at a call.
#   chained   options first, then the required formals as ONE open record (R7 (a)/(b)), guarded
#             against the options step: an option given on the record instead is refused by name
#             (`optionsStep`) rather than silently dropped.
{ prelude }:
let
  inherit (builtins)
    attrNames
    elemAt
    filter
    functionArgs
    intersectAttrs
    length
    lessThan
    sort
    toJSON
    ;
  doorName = name: "gen-scope.${name}";
  optionalOf = f: filter (n: f.${n}) (attrNames f);
  requiredOf = f: filter (n: !f.${n}) (attrNames f);
in
{
  record =
    name: impl:
    let
      f = functionArgs impl;
    in
    prelude.door {
      name = doorName name;
      required = attrNames f;
      open = true;
    } (r: impl (intersectAttrs f r));

  options =
    name: positional: impl:
    let
      f = functionArgs impl;
      d = prelude.door {
        name = doorName name;
        optional = optionalOf f;
      };
      n = length positional;
      a0 = elemAt positional 0;
      a1 = elemAt positional 1;
    in
    if sort lessThan positional != requiredOf f then
      throw "gen-scope door.nix: ${doorName name}'s positional operands ${toJSON positional} are not its required formals ${toJSON (requiredOf f)}"
    else if n == 0 then
      d impl
    else if n == 1 then
      d (o: x: impl (o // { ${a0} = x; }))
    else if n == 2 then
      d (
        o: x: y:
        impl (
          o
          // {
            ${a0} = x;
            ${a1} = y;
          }
        )
      )
    else
      throw "gen-scope door.nix: ${doorName name} takes ${toString n} positional operands; a door past two states its record instead";

  chained =
    name: impl:
    let
      f = functionArgs impl;
      required = requiredOf f;
      requiredSet = removeAttrs f (optionalOf f);
      opts = prelude.door {
        name = doorName name;
        optional = optionalOf f;
      };
      operands = prelude.door {
        name = doorName name;
        inherit required;
        open = true;
        optionsStep = self;
      };
      self = opts (o: operands (r: impl (o // intersectAttrs requiredSet r)));
    in
    self;
}
