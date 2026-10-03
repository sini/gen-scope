# How many times `dataFilter` is APPLIED per `visible` read — the arms, read by
# `resolve-datafilter-calls.sh`.
#
# WHY THIS CANNOT BE A SUITE CELL. Thunk sharing is unobservable from inside an evaluation: a datum
# applied twice and a datum applied once answer the same value. Each application emits one trace
# line on stderr instead, and the driver counts them.
#
# THE FIXTURE is a parent chain n0 ← n1 ← … ← n4 where EVERY node declares `v`, read from the leaf
# under `parent*` visible.
#
#   arm "group-single"   — `single` under the declared key: the nearest declaration is the answer,
#                          so ONE application, at n4.
#   arm "group-both"     — `answers` and `shadowed` under the declared key: `shadowed` lists every
#                          present candidate, so each of the five visits is applied ONCE.
#   arm "groupBy-single" — THE LIVE CONTROL, the strict key: every witness's presence is read, five
#   arm "groupBy-both"     applications either way. A control reading 0 means the trace never
#                          reached the instrument.
{
  arm ? "group-single",
}:
let
  S = import ../../. { };
  d = 5;
  ids = builtins.genList (i: "n${toString i}") d;
  nodes = builtins.listToAttrs (
    builtins.genList (i: {
      name = "n${toString i}";
      value = {
        id = "n${toString i}";
        type = "n";
        parent = if i == 0 then null else "n${toString (i - 1)}";
        decls.v = "v${toString i}";
      };
    }) d
  );
  ev =
    S.eval
      {
        parseParent = id: nodes.${id}.parent;
      }
      {
        children = _: _: { };
        imports = _: _: [ ];
        marks = _: _: [ ];
      }
      {
        inherit nodes;
        nodeOrder = ids;
      };
  read =
    key:
    S.resolve (
      {
        wf = S.wellFormed {
          alphabet = [ "parent" ];
          expression = "parent*";
        };
        order = S.labelOrder {
          alphabet = [ "parent" ];
          layers = [ [ "parent" ] ];
          endOfPath = -1;
        };
        mode = "visible";
        dataFilter = n: builtins.trace "DF ${n.id}" (n.decls.v or null);
      }
      // key
    ) ev "n4";
  both = r: builtins.deepSeq [ r.answers r.shadowed ] (map (a: a.node) (r.answers ++ r.shadowed));
  arms = {
    group-single = (read { group = "k"; }).single "k";
    group-both = both (read {
      group = "k";
    });
    groupBy-single = (read { groupBy = _: "k"; }).single "k";
    groupBy-both = both (read {
      groupBy = _: "k";
    });
  };
in
arms.${arm}
