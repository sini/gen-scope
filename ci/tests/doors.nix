# The closed doors' shared checks (den-hoag-7gp66 P1): each published door takes gen-prelude's
# `checkRequired` / `checkOptions` rather than a native closed formal set, which refused a missing or
# unknown field past `tryEval` (ADR-0025 item 1). Catchability is asserted here, one cell per door;
# each message is pinned in `ci/tests-error.nix` (`doors`), where the admission arms are too.
{ genScope, ... }:
let
  doors = import ./_fixtures/doors.nix;
  refused = e: !(builtins.tryEval e).success;
  cell =
    name: d:
    let
      door = genScope.${name};
    in
    {
      expr = {
        nonSet = refused (door 1);
      }
      // (if d.class == "options" then { } else { missing = refused (door d.withoutMissing); })
      // (if d.class == "record" then { } else { unknown = refused (door d.withUnknown); });
      expected = {
        nonSet = true;
      }
      // (if d.class == "options" then { } else { missing = true; })
      // (if d.class == "record" then { } else { unknown = true; });
    };
in
{
  flake.tests.doors =
    builtins.listToAttrs (
      map (name: {
        name = "test-${name}";
        value = cell name doors.${name};
      }) (builtins.attrNames doors)
    )
    // {
      # The minting entry's emitter record, one position in: every field required, the set closed.
      test-mintStrata-emitter = {
        expr =
          let
            emitter = {
              pass = 0;
              identifier = "a";
              kind = "k";
              relata = { };
              content = { };
              site = "s";
            };
            mint =
              emitters:
              genScope.mintStrata {
                inherit emitters;
                kinds = { };
              };
          in
          {
            valid = builtins.attrNames (mint [ emitter ]).nodes;
            missing = refused (mint [ (builtins.removeAttrs emitter [ "site" ]) ]);
            unknown = refused (mint [ (emitter // { "_${emitter.site}_" = 1; }) ]);
          };
        expected = {
          valid = [ "a" ];
          missing = true;
          unknown = true;
        };
      };
    };
}
