# THE REFUSING MERGE — the fold over the module record, which throws on a name contributed twice
# instead of resolving it by position.
#
# A `//` chain is last-wins and silent: a module free to choose its own export names and an assembly
# free to merge them in a written order are each correct alone, and compose into a shadowed export
# that nothing says out loud. The fold below is the same merge with the duplicate test the chain
# leaves out, so the property holds for every module in the set rather than for the ones whose author
# remembered a cell.
#
# WHERE IT RUNS: in the suite (`ci/tests/merge-surface.nix`), over the record `lib/modules.nix`
# returns, and not at load (den-hoag-9lg69). `lib/default.nix` publishes a literal of
# `inherit (modules.<m>)` clauses, lazy per name, and the suite holds that literal equal to this
# fold's result. Folding at load forced all nineteen modules for every caller, demanded or not, and
# no caller input can reach the refusal: the module name sets read none of the library's formals.
#
# This file is NOT one of the merged modules — nothing here reaches the library's surface.
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
      throw "gen-scope: '${name}' is exported by both '${acc.owner.${name}}' and '${moduleName}', and the library refuses a duplicate export rather than resolving it by position";
in
(prelude.foldl' step {
  surface = { };
  owner = { };
} (prelude.attrNames modules)).surface
