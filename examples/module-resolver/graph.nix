# LM-inspired module system scope graph (Neron 2015 §2.1, §3, §4).
#
# Modules form a scope hierarchy via parent edges (lexical nesting).
# Imports create cross-scope visibility via import edges.
# Declarations are resolved through the scope graph using the
# resolution calculus with specificity D < I < P.
#
# program:
#   module Std {
#     module IO     { def print = "io.print"; def format = "io.format" }
#     module Math   { def sqrt = "math.sqrt"; def pi = 3 }
#     module String { import Math; def concat = "string.concat" }
#   }
#   module App {
#     import Std.String
#     def main = "app.main"
#     module Sub {
#       import Std.IO
#       def helper = "sub.helper"
#     }
#   }
#   module Cycle1 { import Cycle2 }
#   module Cycle2 { import Cycle1 }
{ genScope, lib }:
let
  # Parent edges encode lexical nesting.
  parentGraph = genScope.overlays [
    (genScope.star "root" [
      "Std"
      "App"
      "Cycle1"
      "Cycle2"
    ])
    (genScope.star "Std" [
      "Std.IO"
      "Std.Math"
      "Std.String"
    ])
    (genScope.edge {
      from = "App.Sub";
      to = "App";
    })
  ];

  # Import edges encode module imports.
  importGraph = genScope.overlays [
    (genScope.edge {
      from = "Std.String";
      to = "Std.Math";
    })
    (genScope.edge {
      from = "App";
      to = "Std.String";
    })
    (genScope.edge {
      from = "App.Sub";
      to = "Std.IO";
    })
    # Cyclic: Cycle1 ↔ Cycle2
    (genScope.edge {
      from = "Cycle1";
      to = "Cycle2";
    })
    (genScope.edge {
      from = "Cycle2";
      to = "Cycle1";
    })
  ];

  # A FLAT kind vocabulary: the names this graph's nodes are, with no order between them, so no
  # kind expands into another. Registering them is what gives the kind set a domain — an
  # unregistered spelling is refused rather than silently becoming a kind of its own.
  kinds = genScope.mkKinds (
    map (name: genScope.mkKind { } name) [
      "root"
      "module"
    ]
  );

  roots = genScope.buildRoots {
    inherit parentGraph importGraph;
    decls = {
      root = { };
      Std = { };
      "Std.IO" = {
        print = "io.print";
        format = "io.format";
      };
      "Std.Math" = {
        sqrt = "math.sqrt";
        pi = 3;
      };
      "Std.String" = {
        concat = "string.concat";
      };
      App = {
        main = "app.main";
      };
      "App.Sub" = {
        helper = "sub.helper";
      };
      Cycle1 = {
        val = "c1";
      };
      Cycle2 = {
        val = "c2";
      };
    };
    kinds = kinds;
    types = {
      root = "root";
      Std = "module";
      "Std.IO" = "module";
      "Std.Math" = "module";
      "Std.String" = "module";
      App = "module";
      "App.Sub" = "module";
      Cycle1 = "module";
      Cycle2 = "module";
    };
  };
in
{
  inherit roots;
}
