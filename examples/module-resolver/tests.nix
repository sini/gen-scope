# Module resolver tests.
{
  genScope,
  lib,
  result,
}:
let
  # Néron's D < I < P as the one calculus reads it; `transitive` is the WFL `parent* imports*`.
  lookup =
    transitive: dataFilter: id:
    (genScope.resolve {
      wf =
        if transitive then
          genScope.wellFormed {
            alphabet = [
              "parent"
              "imports"
            ];
            expression = "parent* imports*";
          }
        else
          genScope.neron.wf;
      inherit (genScope.neron) order;
      inherit dataFilter;
      mode = "visible";
      groupBy = _: "x";
    } result id).single
      "x";
  # Every resolution, one per acyclic path.
  witnesses =
    dataFilter: id:
    (genScope.resolve {
      inherit (genScope.neron) wf;
      inherit dataFilter;
      mode = "witnesses";
    } result id).answers;
  # More than one DISTINCT declaring node among the resolutions (Neron §2.2).
  ambiguous =
    dataFilter: id: builtins.length (lib.unique (map (a: a.node) (witnesses dataFilter id))) > 1;
in
{
  # --- Resolution: D < I < P specificity (Neron 2015 Fig. 2) -----

  direct-lookup = result.get "Std.IO" "lookup" "print";
  # -> "io.print"

  import-lookup = result.get "App" "lookup" "concat";
  # -> "string.concat"

  parent-inherit = result.get "App.Sub" "lookup" "main";
  # -> "app.main"

  sub-import = result.get "App.Sub" "lookup" "print";
  # -> "io.print"

  # Transitive imports: String imports Math, so App sees pi through chain.
  transitive-import = lookup true (n: n.decls.pi or null) "App";
  # -> 3

  # Non-transitive (default): App cannot see Math's pi.
  non-transitive = lookup false (n: n.decls.pi or null) "App";
  # -> null

  # --- Ambiguity detection (van Antwerpen 2018) -------------------

  not-ambiguous = ambiguous (n: n.decls.concat or null) "Std.String";
  # -> false

  shadow-no-ambiguity = ambiguous (n: n.decls.format or null) "App.Sub";
  # -> false

  # --- Cyclic imports (acyclic resolution paths, NR-Cons) ---------

  cycle-safe-c1 = lookup false (n: n.decls.val or null) "Cycle1";
  # -> "c1"

  cycle-safe-c2 = lookup false (n: n.decls.val or null) "Cycle2";
  # -> "c2"

  cycle-all-reachable = builtins.sort builtins.lessThan (
    map (a: a.value) (witnesses (n: n.decls.val or null) "Cycle1")
  );
  # -> [ "c1" "c2" ]

  # --- Shadowing (Neron 2015 §5, Def. 1) -------------------------

  visible-decls-app-sub =
    let
      decls = result.get "App.Sub" "visibleDecls";
    in
    {
      has-helper = decls ? helper;
      has-main = decls ? main;
      has-print = decls ? print;
      has-format = decls ? format;
    };

  # --- Structural queries -----------------------------------------

  std-submodules = builtins.sort builtins.lessThan (genScope.childrenIds result "Std");
  app-sub-ancestors = genScope.ancestors result "App.Sub";
  module-count = result.get "root" "moduleCount";
  typed-modules = builtins.length (builtins.attrNames (genScope.nodesByType result "module"));
}
