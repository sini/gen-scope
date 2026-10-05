# A one-hop edge read is LINEAR in the edges it reads and in the calls made — the arms, read by
# `resolve-one-hop.sh`.
#
# WHY THIS CANNOT BE A SUITE CELL. Each one-hop read is a resolution `wf = l` (den-hoag-4or0a U2),
# and the suite pins its DENOTATION (the B cells of `ci/tests/walks-through-resolve.nix`). A dedup
# that rebuilt its list per target answers the same set and reads green there; only a sweep over
# sizes sees its class.
#
#   arm "fan-<read>"   — one read from `s`, whose `include` and `imports` edges fan out to n targets.
#   arm "every-<read>" — the read at EVERY scope of a parent chain c0 ← … ← c(n-1), each with one
#                        `include` and one `imports` edge to the sink `t`: a per-call cost that grew
#                        with the graph shows only here, as calls × size.
#   arm "*-raw"        — THE LIVE CONTROL: the same edges read as the authored attribute
#                        (`self.get id "edges-include"`), no resolution. An instrument failure moves it
#                        with the reads, so a control over budget refuses the run as unmeasured.
#
# Every arm answers the number of targets read, n, which the script checks before any cost figure.
{
  arm ? "fan-followEdge",
  n ? 1000,
}:
let
  S = import ../../. { };
  node = id: parent: {
    inherit id parent;
    type = "n";
    decls = { };
  };
  scope =
    nodes: attrs:
    S.eval { parseParent = id: nodes.${id}.parent; }
      (
        {
          children = _: _: { };
          marks = _: _: [ ];
        }
        // attrs
      )
      {
        inherit nodes;
        nodeOrder = builtins.attrNames nodes;
      };

  ts = builtins.genList (i: "t${toString i}") n;
  fan =
    scope
      (builtins.listToAttrs (
        map (id: {
          name = id;
          value = node id null;
        }) ([ "s" ] ++ ts)
      ))
      {
        imports = _: id: if id == "s" then ts else [ ];
        edges-include = _: id: if id == "s" then ts else [ ];
      };

  cs = builtins.genList (i: "c${toString i}") n;
  chain =
    scope
      (
        builtins.listToAttrs (
          builtins.genList (i: {
            name = "c${toString i}";
            value = node "c${toString i}" (if i == 0 then null else "c${toString (i - 1)}");
          }) n
        )
        // {
          t = node "t" null;
        }
      )
      {
        imports = _: id: if id == "t" then [ ] else [ "t" ];
        edges-include = _: id: if id == "t" then [ ] else [ "t" ];
      };
  every = read: builtins.foldl' (a: c: a + builtins.length (read chain c)) 0 cs;

  ids = _: id: [ id ];
  arms = {
    fan-followEdge = builtins.length (S.followEdge "include" fan "s");
    fan-imports = builtins.length (S.collectionAttr { } "imports" ids fan "s");
    fan-raw = builtins.length (fan.get "s" "edges-include");
    every-followEdge = every (S.followEdge "include");
    every-collectImports = every (S.collectImports ids);
    every-raw = every (self: id: self.get id "edges-include");
  };
in
arms.${arm}
