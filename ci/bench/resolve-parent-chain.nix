# A `parent`-letter resolution is LINEAR in the chain it walks — the arms, read by
# `resolve-parent-chain.sh`.
#
# WHY THIS CANNOT BE A SUITE CELL. The oracle is a complexity class, observable only across a sweep
# of depths. The suite pins D9's DENOTATION (refusal row 16, the N3 and D9 cells of
# `ci/tests/calculus.nix`, the `inherit'` parity cell), and it read green over the per-read form,
# whose cost was O(depth²): a chain walk per `parent` read.
#
# THE FIXTURE is a parent chain n0 ← n1 ← … ← n(d-1) read from the leaf, where only the root
# declares `v`, so every arm walks the whole chain and answers `n0` / `"hit"`.
#
#   arm "parent-<mode>" — `parent*` under mode <mode>: the letter D9 guards.
#   arm "inherit"       — `inherit'`, which is `parent*` visible `single`.
#   arm "neron"         — `neron` visible `single` (`parent* imports?`).
#   arm "up-<mode>"     — THE LIVE CONTROL: the same chain as the edge letter `up` (`edges-up`), where
#                         D9 never runs. It differs from `parent-<mode>` in exactly the letter's
#                         read, so an instrument failure moves both, and a control over budget
#                         refuses the run as unmeasured rather than passing it.
{
  arm ? "parent-visible",
  d ? 100,
}:
let
  S = import ../../. { };
  ids = builtins.genList (i: "n${toString i}") d;
  nodes = builtins.listToAttrs (
    builtins.genList (i: {
      name = "n${toString i}";
      value = {
        id = "n${toString i}";
        type = "n";
        parent = if i == 0 then null else "n${toString (i - 1)}";
        decls = if i == 0 then { v = "hit"; } else { };
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
        edges-up =
          _: id:
          let
            p = nodes.${id}.parent;
          in
          if p == null then [ ] else [ p ];
      }
      {
        inherit nodes;
        nodeOrder = ids;
      };
  v = n: n.decls.v or null;
  leaf = "n${toString (d - 1)}";
  letterArm =
    letter: mode:
    let
      wf = S.wellFormed {
        alphabet = [ letter ];
        expression = "${letter}*";
      };
      order = S.labelOrder {
        alphabet = [ letter ];
        layers = [ [ letter ] ];
        endOfPath = -1;
      };
    in
    map (a: a.node)
      (S.resolve (
        {
          inherit wf mode;
          dataFilter = v;
        }
        // (
          if mode == "visible" then
            {
              inherit order;
              groupBy = _: "k";
            }
          else
            { }
        )
      ) ev leaf).answers;
  arms = {
    "inherit" = S."inherit'" { } v ev leaf;
    neron =
      (S.resolve (
        S.neron
        // {
          mode = "visible";
          dataFilter = v;
          groupBy = _: "k";
        }
      ) ev leaf).single
        "k";
  }
  // builtins.listToAttrs (
    builtins.concatMap
      (mode: [
        {
          name = "parent-${mode}";
          value = letterArm "parent" mode;
        }
        {
          name = "up-${mode}";
          value = letterArm "up" mode;
        }
      ])
      [
        "reachable"
        "witnesses"
        "visible"
      ]
  );
in
arms.${arm}
