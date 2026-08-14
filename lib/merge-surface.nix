# THE REFUSING MERGE — the assembly's fold over the modules, which throws on a name contributed
# twice instead of resolving it by position.
#
# A `//` chain is last-wins and silent: a module free to choose its own export names and an assembly
# free to merge them in a written order are each correct alone, and compose into a shadowed export
# that nothing says out loud. The fold below is the same merge with the duplicate test the chain
# leaves out, so the property holds for every module in the set rather than for the ones whose author
# remembered a cell.
#
# THE PRICE, so it is weighed rather than discovered: one pass over the merged names per library
# evaluation, paid at assembly and never per call.
#
# This file is the assembly's helper and is NOT one of the merged modules — nothing here reaches the
# library's surface.
{ prelude }:
modules:
let
  step =
    acc: moduleName:
    let
      exports = modules.${moduleName};
      duplicated = prelude.filter (name: acc.owner ? ${name}) (prelude.attrNames exports);
      name = prelude.head duplicated;
    in
    if duplicated == [ ] then
      {
        surface = acc.surface // exports;
        owner = acc.owner // prelude.genAttrs (prelude.attrNames exports) (_: moduleName);
      }
    else
      throw "gen-scope: '${name}' is exported by both '${acc.owner.${name}}' and '${moduleName}', and the library's assembly refuses a duplicate export rather than resolving it by position";
in
(prelude.foldl' step {
  surface = { };
  owner = { };
} (prelude.attrNames modules)).surface
