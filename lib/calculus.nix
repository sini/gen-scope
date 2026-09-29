# THE ONE RESOLUTION CALCULUS — van Antwerpen, Poulsen, Rouvoet & Visser 2018 ("Scopes as Types"),
# Fig. 1, run over an EVALUATED scope (den-hoag-gayc; ADR-0008, ADR-0024 carrier (L, E, <, r) + k).
#
#   resolve { wf; dataFilter; mode ? "reachable"; order ?; groupBy ?; bound ?; } self from
#
# `wf` is WFL (label well-formedness, a regular expression over the alphabet L, stepped by
# Brzozowski derivatives — `regex.nix`); `dataFilter` is the relation's lookup composed with WFD,
# `node → datum | null`, required and never defaulted (ADR-0024 ruling 3); `order` is `<l` over
# L̂ = L ∪ {$}; `groupBy` is the competition key k, the `d′ ≤d d` conjunct of (NR-Vis).
#
# TWO CYCLE LAWS, ONE PER MODE (den-hoag-gayc Q4 = S):
#   · `reachable` is THE WALK LAW — a `genericClosure` over ⟨node, derivative-state⟩, so a revisit in
#     a new state is a new item and the closure is the quotient of the walk by that pair. Exact on any
#     graph, cyclic included, and linear in |nodes| × |states|.
#   · `witnesses` and `visible` are THE ACYCLIC-PATH LAW, (NR-Cons): a path never re-enters a scope
#     it has already visited, the start included, so each answer carries its path and a diamond
#     answers twice. Enumeration is priced by the number of such paths.
#
# THE LETTERS READ THE SCOPE, NEVER A DECLARED EDGE LIST. At each reached ⟨node, state⟩ the walk reads
# the edge attribute of every letter whose derivative from `state` is not ∅: `imports` reads the
# import relation (`traversal-names.nix`), `parent` reads the node record's `.parent`, and every
# other letter `l` reads `edges-l` (`structural.edgePrefix`). All three routes are structural, so a
# warm evaluation recomputes every one. A letter whose attribute is undeclared is refused by name at
# that read (`eval.nix`), never read as no edges.
#
# THE BOUNDARY MARKS ARE READ IN EVERY RESOLUTION (ADR-0026; den-hoag-gayc N1 (α), O8 (i)). At the
# source of every edge the walk considers it reads `marks` (`structural.markAttribute`) and admits an
# edge labelled `l` iff every mark in `marks src ++ bound src` admits `l`. `bound` is the query's
# narrowing: it only removes edges, and the floor is never reachable from here. A scope that declares
# no `marks` is refused by name at the first read; `_: _: [ ]` is the declaration of none.
#
# The parameter constructors (`wellFormed`, `labelOrder`) and the WFL syntax (`wfl`) are published;
# the derivative engine (`deriv`, `nullable`, `stateKey`, `parse`) is not.
{ prelude, key }:
let
  inherit (key)
    attrKey
    badResult
    callableAt
    identifier
    renderId
    ;
  regex = import ./regex.nix { inherit prelude; };
  structural = import ./structural.nix { inherit prelude; };
  relations = import ./traversal-names.nix;
  # Containment rides the node record's `.parent` field (`structural.nix`, "containment needs no
  # term"), so the calculus names its letter here and reads no attribute for it.
  parentLetter = "parent";

  emptyKey = regex.stateKey regex.empty;
  inherit (builtins)
    concatMap
    elem
    filter
    head
    isAttrs
    isBool
    isList
    isString
    length
    toJSON
    typeOf
    ;
  refuse = site: msg: throw "gen-scope.${site}: ${msg}";
  quote = xs: toJSON xs;

  # ── L — the alphabet's letter law (gen-view `lettersLaw`, carried) ─────────────────────────────
  # A letter is a string; `$` is the extended label marking the end of a path and `_` the parse
  # grammar's any-label wildcard, so neither can name an edge; a letter is listed once.
  lettersLaw =
    site: xs:
    let
      nonString = filter (l: !(isString l)) xs;
      reserved = filter (l: l == "$" || l == "_") xs;
      dup = filter (l: length (filter (m: m == l) xs) > 1) xs;
    in
    if !(isList xs) then
      refuse site "alphabet is a ${typeOf xs}, not a list of letters"
    else if xs == [ ] then
      refuse site "alphabet is empty; an alphabet with no letters admits no path"
    else if nonString != [ ] then
      refuse site "alphabet carries a ${typeOf (head nonString)} where a letter (a string) belongs"
    else if reserved != [ ] then
      refuse site "alphabet carries the reserved letter '${head reserved}' — `_` is the any-label wildcard of the path-expression grammar and `$` the extended label marking the end of a path (van Antwerpen 2018 Fig. 1); neither can also name an edge"
    else if dup != [ ] then
      refuse site "alphabet lists the letter '${head dup}' more than once"
    else
      xs;

  # The literals a term names, once each: a closure keyed by the canonical key visits each distinct
  # subterm once, where a fold over the TREE is exponential in `(…)+` nesting (gen-view, carried).
  literalsOf =
    r:
    let
      children =
        n:
        if n.t == "star" then
          [ n.r ]
        else if n.t == "seq" then
          [
            n.hd
            n.tl
          ]
        else if n.t == "alt" then
          n.rs
        else
          [ ];
      reached = builtins.genericClosure {
        startSet = [
          {
            key = regex.stateKey r;
            n = r;
          }
        ];
        operator =
          x:
          map (c: {
            key = regex.stateKey c;
            n = c;
          }) (children x.n);
      };
    in
    map (x: x.n.l) (filter (x: x.n.t == "lit") reached);

  # ── E — label well-formedness ──────────────────────────────────────────────────────────────────
  # `expression` is a string, parsed under `maxLength` (the parser's recursion cap, a parameter:
  # den-hoag-2dx7j), or a term the WFL constructors built. Every literal is checked against the
  # alphabet, so a name outside L is refused rather than silently matching nothing.
  wellFormed =
    prelude.door
      {
        name = "gen-scope.wellFormed";
        required = [
          "alphabet"
          "expression"
        ];
        optional = [ "maxLength" ];
      }
      (
        a:
        let
          alphabet = lettersLaw "wellFormed" a.alphabet;
          e = a.expression;
          term =
            if isString e then
              regex.parseWith (if a ? maxLength then { inherit (a) maxLength; } else { }) e
            else if isAttrs e then
              builtins.seq (regex.stateKey e) e
            else
              refuse "wellFormed" "expression is a ${typeOf e}, not a path expression (a string, or a term built by the `wfl` constructors)";
          foreign = filter (l: !(elem l alphabet)) (literalsOf term);
        in
        builtins.seq alphabet (
          if foreign != [ ] then
            refuse "wellFormed" "the expression names '${head (builtins.sort builtins.lessThan foreign)}', which is not a letter of the alphabet (${quote alphabet}); a path expression ranges over L and a name outside it would match nothing and say nothing"
          else
            {
              __element = "wellFormed";
              inherit alphabet term;
              expression = e;
            }
        )
      );

  # ── < — the label order (gen-view `labelOrder` + `orderLaw`, moved) ────────────────────────────
  # `layers` is a list of ranks, most specific first; two letters of one rank are incomparable, which
  # is how a strict PARTIAL order is declared. `endOfPath` is `$`'s rank. The ranking is total over
  # L̂: an unranked letter is refused by name, never given a default rank.
  orderLaw =
    alphabet: layers: endOfPath:
    let
      flat = builtins.concatLists layers;
      nonString = filter (l: !(isString l)) flat;
      dup = filter (l: length (filter (m: m == l) flat) > 1) flat;
      missing = filter (l: !(elem l flat)) alphabet;
      foreign = filter (l: !(elem l alphabet)) flat;
      ranks = builtins.foldl' (
        acc: i:
        acc
        // builtins.listToAttrs (
          map (l: {
            name = l;
            value = i;
          }) (builtins.elemAt layers i)
        )
      ) { } (builtins.genList (i: i) (length layers));
      rankOf =
        l:
        if l == "$" then
          endOfPath
        else if isString l && ranks ? ${l} then
          ranks.${l}
        else
          refuse "labelOrder" "${
            if isString l then "'${l}'" else "a ${typeOf l}"
          } is not a label of L̂ (${quote alphabet}, or `$`)";
    in
    if !(isList layers) || builtins.any (l: !(isList l)) layers then
      refuse "labelOrder" "layers must be a list of lists — each inner list is one rank, and two letters sharing a rank are incomparable, which is how a strict PARTIAL order is declared"
    else if !(builtins.isInt endOfPath) then
      refuse "labelOrder" "endOfPath must be an int; it is the rank of the extended label `$` and decides whether stopping outranks continuing"
    else if nonString != [ ] then
      refuse "labelOrder" "layers rank a ${typeOf (head nonString)} where a letter (a string) belongs"
    else if dup != [ ] then
      refuse "labelOrder" "layers rank the letter '${head dup}' more than once"
    else if foreign != [ ] then
      refuse "labelOrder" "layers rank '${head (builtins.sort builtins.lessThan foreign)}', which is not a letter of the alphabet (${quote alphabet})"
    else if missing != [ ] then
      refuse "labelOrder" "letter '${head missing}' is not ranked; the label order is total over the alphabet, and an unranked letter would otherwise take a default rank nobody declared"
    else
      rankOf;

  labelOrder =
    prelude.door
      {
        name = "gen-scope.labelOrder";
        required = [
          "alphabet"
          "layers"
          "endOfPath"
        ];
      }
      (
        a:
        let
          alphabet = lettersLaw "labelOrder" a.alphabet;
          rankOf = orderLaw alphabet a.layers a.endOfPath;
        in
        builtins.seq rankOf {
          __element = "labelOrder";
          inherit alphabet rankOf;
          inherit (a) layers endOfPath;
          # Fig. 1's Visibility Order, rule by rule: recursion is licensed by label EQUALITY only;
          # where the labels differ this is the last position read, and the two paths are ordered
          # only if `<l` orders those two labels (van Antwerpen 2018 114:6, "the prefix order only
          # orders paths that have a common prefix").
          pathPrecedes =
            pa: pb:
            let
              la = length pa;
              lb = length pb;
              labelAt = p: i: (builtins.elemAt p i).label;
              go =
                i:
                if i >= la && i >= lb then
                  false
                else if i >= la then
                  rankOf "$" < rankOf (labelAt pb i)
                else if i >= lb then
                  rankOf (labelAt pa i) < rankOf "$"
                else if labelAt pa i == labelAt pb i then
                  go (i + 1)
                else
                  rankOf (labelAt pa i) < rankOf (labelAt pb i);
            in
            go 0;
        }
      );

  # ── Néron et al. 2015's resolution as a preset: D < I < P, i.e. `$ < imports < parent` ─────────
  neron = {
    wf = wellFormed {
      alphabet = [
        parentLetter
        relations.imports
      ];
      expression = "${parentLetter}* ${relations.imports}?";
    };
    order = labelOrder {
      alphabet = [
        parentLetter
        relations.imports
      ];
      layers = [
        [ relations.imports ]
        [ parentLetter ]
      ];
      endOfPath = -1;
    };
  };

  modes = [
    "reachable"
    "witnesses"
    "visible"
  ];

  # ── THE WALK ───────────────────────────────────────────────────────────────────────────────────
  run =
    o: mode: self: from:
    let
      alphabet = o.wf.alphabet;
      st0 = o.wf.term;
      dataFilter = callableAt "resolve" "dataFilter" "a datum or null" o.dataFilter;
      dataAt = id: dataFilter (self.node id);
      bound =
        if o ? bound then
          callableAt "resolve" "bound" "a list of marks { name; admits; }" o.bound
        else
          null;

      # A mark is read for `admits` wherever an edge is classified; its `name` only by `withheld`.
      markAt =
        id: what: m:
        if !(isAttrs m) || !(m ? admits) then
          refuse "resolve" "the ${what} of node ${renderId id} carry ${
            if isAttrs m then "a mark with no admits" else "a ${typeOf m}"
          }, not a mark { name; admits; }"
        else
          m
          // {
            admits = callableAt "resolve" "a mark's admits (${what} of node ${renderId id})" "a bool" m.admits;
          };
      marksOf =
        id: what: ms:
        if isList ms then
          map (markAt id what) ms
        else
          refuse "resolve" "the ${what} of node ${renderId id} is a ${typeOf ms}, not a list of marks { name; admits; }";
      marksAt =
        id:
        marksOf id "`${structural.markAttribute}`" (self.get id structural.markAttribute)
        ++ (if bound == null then [ ] else marksOf id "`bound`" (bound id));
      admitsLetter =
        id: l: m:
        let
          r = m.admits l;
        in
        if isBool r then
          r
        else
          badResult "resolve" "a mark's admits" "at node ${renderId id} on the label ${toJSON l}" "a bool" r;
      nameOf =
        id: m:
        m.name
          or (refuse "resolve" "node ${renderId id} carries a mark with no name; `withheld` reports a mark by its name");

      edgeList =
        id: l: v:
        if isList v then
          map (
            t:
            if isString t then
              t
            else
              refuse "resolve" "node ${renderId id}, letter '${l}': an edge target is a ${typeOf t}, not a node id (a string)"
          ) v
        else
          refuse "resolve" "node ${renderId id}, letter '${l}': the edge attribute is a ${typeOf v}, not a list of node ids";

      # D9: a parent cycle is refused only when it is made of parent edges alone. The chain from `id`
      # is walked once per parent read; a finite chain ends at a root, so a chain whose every member
      # has a parent has closed on itself.
      # ponytail: O(depth) per parent read, O(depth²) per resolution; memoize the chain if deep
      # containment trees make it measurable.
      parentOf =
        id:
        let
          p = (self.node id).parent;
          chain = builtins.genericClosure {
            startSet = [ { key = id; } ];
            operator =
              x:
              let
                q = (self.node x.key).parent;
              in
              if q == null then [ ] else [ { key = q; } ];
          };
        in
        if p == null then
          [ ]
        else if builtins.all (x: (self.node x.key).parent != null) chain then
          refuse "resolve" "node ${renderId id} is on a parent cycle: containment is a tree, and a parent chain that returns to itself is malformed data, not a scope to walk"
        else
          [ p ];

      targetsAt =
        id: l:
        if l == parentLetter then
          parentOf id
        else if l == relations.imports then
          edgeList id l (self.get id relations.imports)
        else
          edgeList id l (self.get id (structural.edgePrefix + l));

      # One ⟨node, state⟩ expansion: the live letters in the alphabet's order, the edges within a
      # letter in the attribute's order, each admitted or withheld by the marks at the source.
      expand =
        id: st:
        let
          live = filter (x: x.k != emptyKey) (
            map (
              l:
              let
                d = regex.deriv l st;
              in
              {
                inherit l d;
                k = regex.stateKey d;
              }
            ) alphabet
          );
          marks = marksAt id;
          perLetter = map (
            x:
            let
              blockers = filter (m: !(admitsLetter id x.l m)) marks;
              ts = targetsAt id x.l;
            in
            if blockers == [ ] then
              {
                admitted = map (t: {
                  label = x.l;
                  target = t;
                  st = x.d;
                  inherit (x) k;
                }) ts;
                withheld = [ ];
              }
            else
              {
                admitted = [ ];
                withheld = map (t: {
                  label = x.l;
                  target = t;
                  marks = map (nameOf id) blockers;
                }) ts;
              }
          ) live;
        in
        if live == [ ] then
          {
            admitted = [ ];
            withheld = [ ];
          }
        else
          {
            admitted = concatMap (p: p.admitted) perLetter;
            withheld = concatMap (p: p.withheld) perLetter;
          };

      k0 = regex.stateKey st0;
      keyOf =
        n: k:
        toJSON [
          n
          k
        ];

      # THE WALK LAW: the closure over ⟨node, state⟩ (gen-graph `queryAll`, carried).
      closure = builtins.genericClosure {
        startSet = [
          {
            key = keyOf from k0;
            node = from;
            st = st0;
            x = expand from st0;
          }
        ];
        operator =
          item:
          map (e: {
            key = keyOf e.target e.k;
            node = e.target;
            inherit (e) st;
            x = expand e.target e.st;
          }) item.x.admitted;
      };

      # THE ACYCLIC-PATH LAW: DFS with per-path seen scopes, the start included (gen-graph
      # `queryPaths`, carried). Every visit is kept, answer or not, so `withheld` reads the same
      # expansions the walk stepped.
      go =
        visited: path: id: st: k:
        let
          x = expand id st;
        in
        [
          {
            node = id;
            inherit
              st
              k
              path
              x
              ;
          }
        ]
        ++ concatMap (
          e:
          let
            tk = attrKey "resolve" e.target;
          in
          if visited ? ${tk} then
            [ ]
          else
            go (visited // { ${tk} = true; }) (
              path
              ++ [
                {
                  inherit (e) label;
                  from = id;
                  to = e.target;
                }
              ]
            ) e.target e.st e.k
        ) x.admitted;

      visits =
        if mode == "reachable" then closure else go { ${attrKey "resolve" from} = true; } [ ] from st0 k0;

      withheldBy = builtins.groupBy (w: attrKey "resolve" w.from) (
        concatMap (v: map (w: w // { from = v.node; }) v.x.withheld) visits
      );
      # Each withheld edge once, in first-classified order: one visit per ⟨node, state⟩ or per path
      # may classify it again (`listToAttrs` keeps the first index of a name).
      withheld =
        id:
        let
          ws = withheldBy.${attrKey "resolve" id} or [ ];
          at = builtins.elemAt ws;
          firstIdx = builtins.listToAttrs (
            builtins.genList (i: {
              name = toJSON [
                (at i).label
                (at i).target
              ];
              value = i;
            }) (length ws)
          );
        in
        map (
          i:
          let
            w = at i;
          in
          {
            inherit (w) label target marks;
          }
        ) (builtins.sort builtins.lessThan (builtins.attrValues firstIdx));

      reachableAnswers =
        let
          nodes = builtins.attrValues (
            builtins.listToAttrs (
              map (i: {
                name = attrKey "resolve" i.node;
                value = i.node;
              }) (filter (i: regex.nullable i.st) closure)
            )
          );
        in
        concatMap (
          n:
          let
            v = dataAt n;
          in
          if v == null then
            [ ]
          else
            [
              {
                node = n;
                value = v;
              }
            ]
        ) nodes;

      witnessAnswers = concatMap (
        v:
        if regex.nullable v.st then
          let
            d = dataAt v.node;
          in
          if d == null then
            [ ]
          else
            [
              {
                inherit (v) node path;
                value = d;
                state = v.k;
              }
            ]
        else
          [ ]
      ) visits;

      # (NR-Vis): the witnesses grouped by k, each group's minimal set under `<p`, computed as a
      # prefix minimum over label words (gen-view `relation.nix` step 6, carried): a member survives
      # iff at every node of its word ŵ = w·$ its symbol takes the minimum rank among the symbols
      # the group's members take there.
      visibleParts =
        let
          groupBy = callableAt "resolve" "groupBy" "a string, the answer's competition key" o.groupBy;
          inherit (o.order) rankOf;
          tagged = map (
            a:
            let
              g = groupBy a;
            in
            if isString g then
              {
                inherit (a) node value path;
                group = g;
              }
            else
              badResult "resolve" "groupBy" "on the answer at ${renderId a.node}"
                "a string, the answer's competition key"
                g
          ) witnessAnswers;
          groups = builtins.groupBy (a: attrKey "resolve" a.group) tagged;
          split =
            members:
            let
              branchesOf =
                c:
                let
                  s = map (step: step.label) c.path ++ [ "$" ];
                in
                builtins.genList (i: {
                  node = toJSON (builtins.genList (j: builtins.elemAt s j) i);
                  rank = rankOf (builtins.elemAt s i);
                }) (length s);
              minRank = builtins.mapAttrs (
                _: bs: builtins.foldl' (m: b: if b.rank < m then b.rank else m) (head bs).rank bs
              ) (builtins.groupBy (b: b.node) (concatMap branchesOf members));
              survives = c: builtins.all (b: b.rank == minRank.${b.node}) (branchesOf c);
            in
            {
              visible = filter survives members;
              shadowed = filter (c: !(survives c)) members;
            };
        in
        builtins.mapAttrs (_: split) groups;
      groupNames = builtins.attrNames visibleParts;

      single =
        group:
        let
          part = visibleParts.${attrKey "resolve" group} or null;
          origins = prelude.unique (map (a: a.node) part.visible);
        in
        if part == null then
          null
        else if length origins > 1 then
          refuse "resolve" "group ${toJSON group} has more than one visible declaration, from ${toJSON origins}. That is an AMBIGUITY in the sense of Neron et al. 2015 (Fig. 3 rule (V); §2.2 Duplicate Declarations) — two declaration occurrences for one read. `single` answers with one declaration or REFUSES; read the group's `answers` to see every one"
        else
          (head part.visible).value;
    in
    builtins.seq (identifier "resolve" from) (
      builtins.seq dataFilter (
        {
          inherit mode withheld;
          answers =
            if mode == "reachable" then
              reachableAnswers
            else if mode == "witnesses" then
              witnessAnswers
            else
              concatMap (g: visibleParts.${g}.visible) groupNames;
        }
        // prelude.optionalAttrs (mode == "visible") {
          shadowed = concatMap (g: visibleParts.${g}.shadowed) groupNames;
          inherit single;
        }
      )
    );

  resolve =
    prelude.door
      {
        name = "gen-scope.resolve";
        required = [
          "wf"
          "dataFilter"
        ];
        optional = [
          "mode"
          "order"
          "groupBy"
          "bound"
        ];
      }
      (
        o:
        let
          mode = o.mode or "reachable";
        in
        if !(elem mode modes) then
          refuse "resolve" "unknown mode ${toJSON mode} (one of ${quote modes})"
        else if mode == "visible" && (o.groupBy or null) == null then
          refuse "resolve" "groupBy is required and is never defaulted (den-hoag-l7af / ADR-0024 ruling 3); a caller wanting the per-node reading states `groupBy = ans: ans.node;` explicitly"
        else if mode == "visible" && !(o ? order) then
          refuse "resolve" "mode \"visible\" requires `order`, a `labelOrder` value (<l over the alphabet, with `$`'s rank)"
        else if mode != "visible" && o ? order then
          refuse "resolve" "`order` is read only by mode \"visible\", and the mode is ${toJSON mode}"
        else if mode != "visible" && o ? groupBy then
          refuse "resolve" "`groupBy` is read only by mode \"visible\", and the mode is ${toJSON mode}"
        else if (o.wf.__element or null) != "wellFormed" then
          refuse "resolve" "wf is not a `wellFormed` value (build it with `wellFormed { alphabet; expression; }`)"
        else if mode == "visible" && (o.order.__element or null) != "labelOrder" then
          refuse "resolve" "order is not a `labelOrder` value (build it with `labelOrder { alphabet; layers; endOfPath; }`)"
        else
          run o mode
      );
in
{
  inherit
    resolve
    wellFormed
    labelOrder
    neron
    ;
  # The WFL syntax, published under one name: the algebraic-graph constructors already publish
  # `star`, and the refusing merge (`merge-surface.nix`) admits one owner per name.
  wfl = {
    inherit (regex)
      lit
      seq
      alt
      star
      opt
      plus
      any
      ;
  };
}
