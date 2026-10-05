# THE REACH CENSUS (premise §7.1 P14, "one query vocabulary"; den-hoag-25dd7, owner arm (a)
# 2026-10-05): every relation this substrate CARRIES is reached by a ONE-LETTER resolution, and by
# no caller predicate.
#
# THE DOMAIN is the lift, not a list written here. `buildRoots` carries exactly `edgeGraphs ∪ {P, I}`
# — `P` as the node record's `.parent`, every other label under `decls.__edges` — and refuses a
# reserved or duplicate label at its door (`lib/build-nodes.nix`). So the census does not enumerate
# labels: it offers the lift a set of candidate spellings, keeps every one the lift ADMITS, lifts
# them together, and reads the carried set back off the lifted record. A spelling the lift starts
# admitting joins the census without an edit here, and one it carries but the calculus walks by
# nothing reds the census by name.
#
# THE LETTER. `P` is walked by the calculus's `parent`, `I` by `imports`, and every other label `l`
# by `l` itself, read from `edges-l` (`calculus.nix` `targetsAt`). The evaluation binds each carried
# label at that name from the lifted record, which is the binding a consumer of the lift writes.
#
# The second clause FOLLOWS over this domain: a carried label reached by a one-letter `resolve`
# (`followEdge`, whose `dataFilter` admits every node) is not reachable ONLY through a resolver.
# What no predicate over the lift sees is a relation living in caller code the substrate does not
# carry; that is the reviewed convention, and `lib/traversal-names.nix` names it.
#
# Beside it: `calculus.test-N5-reserved-letters-refused-at-the-lift`, the door that keeps the
# calculus's own letters out of the domain.
{ lib, genScope, ... }:
let
  S = genScope;
  answers = e: (builtins.tryEval (builtins.deepSeq e true)).success;

  # Ordinary spellings, path-expression syntax a letter must not be parsed as, and every name
  # either side reserves. Each label gets its own target, so a misrouted read answers wrongly.
  candidates = [
    "peer"
    "two words"
    "x*"
    "(y|z)"
    "P"
    "I"
    "imports"
    "parent"
    "_"
    "$"
  ];

  liftWith =
    labels:
    S.buildRoots {
      parentGraph = S.edge {
        from = "b";
        to = "a";
      };
      importGraph = S.edge {
        from = "a";
        to = "d";
      };
      edgeGraphs = lib.imap0 (i: label: {
        inherit label;
        graph = S.edge {
          from = "a";
          to = "t${toString i}";
        };
      }) labels;
    };

  admitted = builtins.filter (l: answers (liftWith [ l ]).nodes) candidates;
  roots = liftWith admitted;

  # The carried set, read off the lifted record: `P` rides `.parent`, the rest `decls.__edges`.
  carried = [ "P" ] ++ builtins.attrNames roots.nodes.a.decls.__edges;
  letterOf =
    c:
    {
      P = "parent";
      I = "imports";
    }
    .${c} or c;
  lifted =
    c: id:
    let
      n = roots.nodes.${id};
    in
    if c == "P" then lib.optional (n.parent != null) n.parent else lib.unique n.decls.__edges.${c};

  ev =
    S.eval
      {
        parseParent = id: (roots.nodes.${id} or { parent = null; }).parent;
      }
      (
        {
          children = _: _: { };
          marks = _: _: [ ];
          imports = _: id: roots.nodes.${id}.decls.__edges.I;
        }
        // lib.listToAttrs (
          map (c: lib.nameValuePair "edges-${c}" (_: id: roots.nodes.${id}.decls.__edges.${c})) (
            lib.subtractLists [ "P" "I" ] carried
          )
        )
      )
      roots;

  # A carried label is unreached at a node when its one-letter read refuses or answers other than
  # the lifted edges.
  unreached = builtins.filter (
    c:
    builtins.any (
      id:
      let
        r = builtins.tryEval (
          builtins.deepSeq (S.followEdge (letterOf c) ev id) (S.followEdge (letterOf c) ev id)
        );
      in
      !r.success || r.value != lifted c id
    ) roots.nodeOrder
  ) carried;
in
{
  flake.tests.reach-census = {
    test-the-lift-carries-exactly-edgeGraphs-and-P-and-I = {
      expr = lib.sort lib.lessThan carried;
      expected = lib.sort lib.lessThan (
        lib.unique (
          admitted
          ++ [
            "P"
            "I"
          ]
        )
      );
    };

    test-every-carried-label-is-reached-by-one-letter = {
      expr = unreached;
      expected = [ ];
    };

    # The census is not vacuous: it read relations of all three routes at a node that has edges.
    test-the-census-reads-every-route = {
      expr = map (c: S.followEdge (letterOf c) ev (if c == "P" then "b" else "a")) [
        "P"
        "I"
        "peer"
      ];
      expected = [
        [ "a" ]
        [ "d" ]
        [ "t0" ]
      ];
    };
  };
}
