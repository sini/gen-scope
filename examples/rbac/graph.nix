# RBAC scope graph.
#
# Role hierarchy:
#   viewer -> can: read
#   editor -> inherits viewer, can: read, write
#   admin  -> inherits editor, can: read, write, delete, manage
#   auditor -> inherits viewer, can: read, audit (parallel hierarchy)
#
# Users:
#   alice -> admin
#   bob   -> editor + auditor (multiple roles)
#   carol -> viewer
#   dave  -> editor, but DENIED delete on project-x
#
# Resources:
#   org/
#   +-- project-x/ (high sensitivity)
#   |   +-- doc-1
#   |   +-- doc-2
#   +-- project-y/ (low sensitivity)
#       +-- doc-3
{ genScope, lib }:
let
  # A FLAT kind vocabulary: the names this graph's nodes are, with no order between them, so no
  # kind expands into another. Registering them is what gives the kind set a domain — an
  # unregistered spelling is refused rather than silently becoming a kind of its own.
  kinds = genScope.mkKinds (
    map (name: genScope.mkKind { } name) [
      "role"
      "user"
      "resource"
    ]
  );
in
{
  roots = genScope.buildRoots {
    # Resource hierarchy (parent edges)
    parentGraph = genScope.overlays [
      (genScope.star "org" [
        "project-x"
        "project-y"
      ])
      (genScope.star "project-x" [
        "doc-1"
        "doc-2"
      ])
      (genScope.edge {
        from = "doc-3";
        to = "project-y";
      })
    ];
    edgeGraphs = [
      # R = role inheritance (Neron 2015 §3, Fig. 16)
      {
        label = "R";
        graph = genScope.overlays [
          (genScope.edge {
            from = "editor";
            to = "viewer";
          })
          (genScope.edge {
            from = "admin";
            to = "editor";
          })
          (genScope.edge {
            from = "auditor";
            to = "viewer";
          })
        ];
      }
      # A = role assignment (user -> role)
      {
        label = "A";
        graph = genScope.overlays [
          (genScope.edge {
            from = "alice";
            to = "admin";
          })
          (genScope.edge {
            from = "bob";
            to = "editor";
          })
          (genScope.edge {
            from = "bob";
            to = "auditor";
          })
          (genScope.edge {
            from = "carol";
            to = "viewer";
          })
          (genScope.edge {
            from = "dave";
            to = "editor";
          })
        ];
      }
      # D = deny override (user -> resource)
      {
        label = "D";
        graph = genScope.edge {
          from = "dave";
          to = "project-x";
        };
      }
    ];
    decls = {
      viewer = {
        read = true;
      };
      editor = {
        write = true;
      };
      admin = {
        delete = true;
        manage = true;
      };
      auditor = {
        audit = true;
      };
      alice = {
        email = "alice@corp.com";
      };
      bob = {
        email = "bob@corp.com";
      };
      carol = {
        email = "carol@corp.com";
      };
      dave = {
        email = "dave@corp.com";
        __deny = {
          "project-x" = [
            "delete"
            "manage"
          ];
        };
      };
      org = {
        name = "Acme Corp";
      };
      "project-x" = {
        name = "Project X";
        sensitivity = "high";
      };
      "project-y" = {
        name = "Project Y";
        sensitivity = "low";
      };
      "doc-1" = {
        title = "Design doc";
      };
      "doc-2" = {
        title = "API spec";
      };
      "doc-3" = {
        title = "Roadmap";
      };
    };
    kinds = kinds;
    types = {
      viewer = "role";
      editor = "role";
      admin = "role";
      auditor = "role";
      alice = "user";
      bob = "user";
      carol = "user";
      dave = "user";
      org = "resource";
      "project-x" = "resource";
      "project-y" = "resource";
      "doc-1" = "resource";
      "doc-2" = "resource";
      "doc-3" = "resource";
    };
  };
}
