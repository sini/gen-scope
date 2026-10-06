# THE ONE RESOLUTION CALCULUS — van Antwerpen, Poulsen, Rouvoet & Visser 2018 ("Scopes as Types"),
# Fig. 1, run over an EVALUATED scope (den-hoag-gayc; ADR-0008, ADR-0024 carrier (L, E, <, r) + k).
#
#   resolve { wf; dataFilter; mode ? "reachable"; order ?; group ? | groupBy ?; bound ?; direction ? "outbound"; } self from
#
# `wf` is WFL (label well-formedness, a regular expression over the alphabet L, stepped by
# Brzozowski derivatives — `regex.nix`); `dataFilter` is the relation's lookup composed with WFD,
# `node → datum | null`, required and never defaulted (ADR-0024 ruling 3); `order` is `<l` over
# L̂ = L ∪ {$}, total over `wf`'s alphabet. The competition key k, the `d′ ≤d d` conjunct of (NR-Vis),
# is stated as exactly one of `group`, a declared constant read before any datum, under which
# resolution stays LAZY in data it shadows, and `groupBy`, a function of the answer, which reads data
# and so forces every candidate it groups (den-hoag-gayc C1).
#
# TWO CYCLE LAWS, ONE PER MODE (den-hoag-gayc Q4 = S):
#   · `reachable` is THE WALK LAW — a `genericClosure` over ⟨node, derivative-state⟩, so a revisit in
#     a new state is a new item and the closure is the quotient of the walk by that pair. Exact on any
#     graph, cyclic included, and linear in |nodes| × |states|.
#   · `witnesses` and `visible` are THE ACYCLIC-PATH LAW, (NR-Cons): a path never re-enters a scope
#     it has already visited, the start included, so each answer carries its path and a diamond
#     answers twice. Enumeration is priced by the number of such paths.
#
# ORDER. `reachable` answers in FIRST-REACH order: breadth-first over ⟨node, state⟩, each node once,
# at its first nullable visit. At each ⟨node, state⟩ the letters are taken in `wf`'s alphabet order
# and a letter's edges in the attribute's declared order (outbound) or `allNodeIds` order (inbound),
# so the order derives from declared inputs. It is not the codepoint order of the answer set, which
# would discard the walk that built it (the undeclared-order defect, `resolve.nix` `collect`). It
# rests on `builtins.genericClosure` processing its worklist first-in first-out and keeping the first
# item of each key, which Nix implements and does not document. `witnesses` answers in depth-first
# pre-order, one answer per path. `calculus.test-ORDER-reachable-is-first-reach` pins the three
# apart on a fixture where first-reach, pre-order and codepoint order all differ.
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
# THE CONVERSE (ADR-0024; Mokhov 2017 §5.2). `direction = "inbound"` is the same query over the
# converse of each letter's edges: from `id` the letter `imports` steps to every node that imports
# `id`, enumerated in `self.allNodeIds` order, and `edges-l` likewise. The marks are applied to the
# AUTHORED graph before the converse is taken, so the edge s —l→ id is admitted or withheld by the
# marks of `s`, its authored source, and `withheld s` reports it as it was authored. Inbound,
# `parent` steps to every node whose `.parent` is `id` (the scopes it contains): the converse of a
# partial function is a relation, not a containment, and D9 still walks each read node's parent chain.
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
            name = attrKey "labelOrder" l;
            value = i;
          }) (builtins.elemAt layers i)
        )
      ) { } (builtins.genList (i: i) (length layers));
      rankOf =
        l:
        if l == "$" then
          endOfPath
        else if isString l && ranks ? ${attrKey "labelOrder" l} then
          ranks.${attrKey "labelOrder" l}
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
          # Fig. 1's Visibility Order, rule by rule, over two paths `[ { label; from; to; } ]` from
          # one origin. Rules 2–4 share one head scope `s`, and rule 1 recurses into paths that each
          # begin at the scope the shared `l`-edge reaches, so recursion is licensed by an equal
          # STEP, the same label to the same scope; an equal label into different scopes leaves the
          # pair unordered. Where the labels differ this is the last position read, and the pair is
          # ordered only if `<l` orders them. The prose at 114:6 states the head-scope half: "s1·l1·s2
          # ≮p s'1·l'1·s'2·l'2·s'3 when s1 ≠ s'1 or l1 ≠ l'1" (van Antwerpen 2018).
          # Two non-empty paths from different origins are refused: rules 2–4 never fire across
          # two heads. An empty path carries no origin, so that pair is the caller's precondition.
          pathPrecedes =
            pa: pb:
            let
              la = length pa;
              lb = length pb;
              stepAt =
                p: i:
                let
                  st = builtins.elemAt p i;
                in
                if isAttrs st && st ? label then
                  st
                else
                  refuse "labelOrder" "pathPrecedes: step ${toString i} is a ${typeOf st} without `label`; a step is `{ label; from; to; }`";
              labelAt = p: i: (stepAt p i).label;
              field =
                n: p: i:
                let
                  st = stepAt p i;
                in
                if st ? ${n} then
                  st.${n}
                else
                  refuse "labelOrder" "pathPrecedes: step ${toString i} has no `${n}`; a step is `{ label; from; to; }`, and the order reads the ${
                    if n == "to" then "target scope at an equal label" else "origin of a non-empty path"
                  }";
              go =
                i:
                if i >= la && i >= lb then
                  false
                else if i >= la then
                  rankOf "$" < rankOf (labelAt pb i)
                else if i >= lb then
                  rankOf (labelAt pa i) < rankOf "$"
                else if labelAt pa i == labelAt pb i then
                  field "to" pa i == field "to" pb i && go (i + 1)
                else
                  rankOf (labelAt pa i) < rankOf (labelAt pb i);
            in
            if la > 0 && lb > 0 && field "from" pa 0 != field "from" pb 0 then
              refuse "labelOrder" "pathPrecedes: the two paths start at different scopes (${renderId (field "from" pa 0)}, ${renderId (field "from" pb 0)}); Fig. 1 orders two paths from one origin only"
            else
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
  directions = [
    "outbound"
    "inbound"
  ];

  # ── THE WALK ───────────────────────────────────────────────────────────────────────────────────
  run =
    o: mode: direction: self: from:
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

      # The `parent` read is the node record's field; D9's cycle verdict is `parentCheck`'s, below.
      parentOf =
        id:
        let
          p = (self.node id).parent;
        in
        if p == null then [ ] else [ p ];

      targetsAt =
        id: l:
        if l == parentLetter then
          parentOf id
        else if l == relations.imports then
          edgeList id l (self.get id relations.imports)
        else
          edgeList id l (self.get id (structural.edgePrefix + attrKey "resolve" l));

      inbound = direction == "inbound";
      # The converse, per letter, built once per resolution and only for a letter the walk reads:
      # target → its authored sources in `allNodeIds` order, each source once. A node does not
      # know its importers locally, so an inbound read forces the full node set (Tier 2, like
      # `collect`).
      #
      # ORDER — the sources are enumerated in MATERIALIZATION order (`self.allNodeIds`: root
      # order, then pre-order through children; see eval.nix). The duality is what fixes the
      # choice. The outbound walk's order is its traversal order, taken from each node's DECLARED
      # edge list; a converse whose order came instead from the codepoint key order of the node
      # set would not be the dual of a traversal-ordered read, and the converse carries no
      # declared list of its own to walk. The rule is this library's own, claimed from no paper:
      # the citation the retired `queryReverse` once carried ("Hedin & Magnusson 2003, inter-type
      # declarations"; "Sloane 2010 §7 collection attributes") named nothing in either primary —
      # `inter-type` occurs 0 times in Hedin & Magnusson (live controls, same run: `aspect` 80,
      # `attribute` 93), and Sloane §7 is Conclusion and Future Work.
      #
      # Where the tree settles no order, the tie-break is `allNodeIds`' and is declared there:
      # SIBLING ties break on `attrNames` (bytewise codepoint), ROOTS follow `scope.nodeOrder`, the
      # declared vertex order. The answer is neither sorted nor deduplicated: a node on two
      # acyclic reverse paths answers twice, as a diamond does outbound.
      converse = builtins.listToAttrs (
        map (l: {
          name = attrKey "resolve" l;
          value = builtins.groupBy (e: attrKey "resolve" e.to) (
            concatMap (
              s:
              map (t: {
                to = t;
                src = s;
              }) (prelude.unique (targetsAt s l))
            ) self.allNodeIds
          );
        }) alphabet
      );
      sourcesOf = id: l: map (e: e.src) (converse.${attrKey "resolve" l}.${attrKey "resolve" id} or [ ]);

      # One ⟨node, state⟩ expansion: the live letters in the alphabet's order, the edges within a
      # letter in the attribute's (outbound) or `allNodeIds`' (inbound) order, each admitted or
      # withheld by the marks at its AUTHORED source. `steps` are `{ to; target; }`: where the walk
      # goes, and the authored edge's target.
      classify =
        src: x: steps:
        let
          blockers = filter (m: !(admitsLetter src x.l m)) (marksAt src);
        in
        {
          label = x.l;
          blocked = blockers != [ ];
        }
        // (
          if blockers == [ ] then
            {
              admitted = map (s: {
                label = x.l;
                target = s.to;
                st = x.d;
                inherit (x) k;
              }) steps;
              withheld = [ ];
            }
          else
            {
              admitted = [ ];
              withheld = map (s: {
                from = src;
                label = x.l;
                inherit (s) target;
                marks = map (nameOf src) blockers;
              }) steps;
            }
        );
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
          perLetter = concatMap (
            x:
            if inbound then
              map (
                s:
                classify s x [
                  {
                    to = s;
                    target = id;
                  }
                ]
              ) (sourcesOf id x.l)
            else
              [
                (classify id x (
                  map (t: {
                    to = t;
                    target = t;
                  }) (targetsAt id x.l)
                ))
              ]
          ) live;
          # The `parent` classifications at this node: at most one outbound, one per converse source
          # inbound. The node's parent edge is admitted when any of them is (D9 then walks its chain).
          parentRead = filter (p: p.label == parentLetter) perLetter;
        in
        if live == [ ] then
          {
            admitted = [ ];
            withheld = [ ];
            readsParent = false;
            admitsParent = false;
          }
        else
          {
            admitted = concatMap (p: p.admitted) perLetter;
            withheld = concatMap (p: p.withheld) perLetter;
            readsParent = parentRead != [ ];
            admitsParent = builtins.any (p: !p.blocked) parentRead;
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
      # expansions the walk stepped. The walk is a TREE: each visit holds `kids`, its admitted child
      # visits, and `via`, the letter it was reached by, which is what `visible`'s staged selection
      # descends; `visits` is its pre-order flattening. `d` is the visit's datum, a thunk applied at
      # most once however many readers (presence, `value`, `shadowed`) reach it. `ix` is the visit's
      # kid-index word, so pre-order is the lexicographic order of `ix` and a reader that needs walk
      # order sorts the visits it holds instead of flattening the tree (which reads every edge).
      #
      # `visited` maps each scope on the path to its depth.
      go =
        visited: depth: path: ix: via: id: st: k:
        let
          x = expand id st;
        in
        {
          node = id;
          d = dataAt id;
          inherit
            st
            k
            path
            ix
            x
            via
            ;
          kids =
            let
              fresh = filter (e: !(visited ? ${attrKey "resolve" e.target})) x.admitted;
            in
            builtins.genList (
              i:
              let
                e = builtins.elemAt fresh i;
              in
              go (visited // { ${attrKey "resolve" e.target} = depth + 1; }) (depth + 1) (
                path
                ++ [
                  {
                    inherit (e) label;
                    from = id;
                    to = e.target;
                  }
                ]
              ) (ix ++ [ i ]) e.label e.target e.st e.k
            ) (length fresh);
        };
      flatten = t: [ t ] ++ concatMap flatten t.kids;
      tree = go { ${attrKey "resolve" from} = 0; } 0 [ ] [ ] null from st0 k0;

      visits = if mode == "reachable" then closure else flatten tree;

      # D9: a parent cycle is refused only when it is made of parent edges alone. The verdict is
      # decided ONCE per resolution, over the union of the parent chains of every node the walk read
      # `parent` at: one closure up those chains, one down from the roots they reach, and a node is
      # well-formed iff it was reached from a root. Linear in the union, where a chain walk per
      # `parent` read made a `parent*` resolution O(depth²) (`ci/bench/resolve-parent-chain.sh`).
      # The walk itself terminates on a cycle either way (the closure's key, NR-Cons's seen set), so
      # the refusal is applied where a read would have met it: an admitted `parent` edge for every
      # answer, a withheld one too for `withheld`, which reads it. Under `group` the selection reads
      # only the classes it examines, and decides D9 over the `parent` fields those classes read
      # instead (`lazyParts`' `parentReadChecked`).
      up = builtins.genericClosure {
        startSet = map (v: {
          key = v.node;
          parent = (self.node v.node).parent;
        }) (filter (v: v.x.readsParent) visits);
        operator =
          x:
          if x.parent == null then
            [ ]
          else
            [
              {
                key = x.parent;
                parent = (self.node x.parent).parent;
              }
            ];
      };
      below = builtins.groupBy (x: attrKey "resolve" x.parent) (filter (x: x.parent != null) up);
      rooted = builtins.listToAttrs (
        map
          (x: {
            name = attrKey "resolve" x.key;
            value = true;
          })
          (
            builtins.genericClosure {
              startSet = filter (x: x.parent == null) up;
              operator = x: below.${attrKey "resolve" x.key} or [ ];
            }
          )
      );
      parentCheck =
        reads:
        let
          cyclic = filter (v: reads v.x && !(rooted ? ${attrKey "resolve" v.node})) visits;
        in
        if cyclic == [ ] then
          true
        else
          refuse "resolve" "node ${renderId (head cyclic).node} is on a parent cycle: containment is a tree, and a parent chain that returns to itself is malformed data, not a scope to walk";
      admittedChecked = builtins.seq (parentCheck (x: x.admitsParent));
      withheldChecked = builtins.seq (parentCheck (x: x.readsParent));

      withheldBy = builtins.groupBy (w: attrKey "resolve" w.from) (concatMap (v: v.x.withheld) visits);
      # Each withheld edge once, in first-classified order: one visit per ⟨node, state⟩ or per path
      # may classify it again (`listToAttrs` keeps the first index of a name).
      withheld =
        id:
        let
          ws = withheldBy.${attrKey "resolve" id} or [ ];
          at = builtins.elemAt ws;
          firstIdx = builtins.listToAttrs (
            builtins.genList (i: {
              name = attrKey "resolve" (toJSON [
                (at i).label
                (at i).target
              ]);
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

      # FIRST-REACH ORDER: each node once, at its first nullable visit in `closure` order (the
      # header's ORDER paragraph). Not `attrValues` of the keyed set, whose codepoint order discards
      # the walk that built it (the undeclared-order defect, `resolve.nix` `collect`). The dedup is a
      # second `genericClosure` with no operator: its worklist is the nullable visits in order, and it
      # keeps the first item of each key, so it rests on the same FIFO worklist as `closure`. The key
      # is the id itself: every id here is a string (`identifier` and `edgeList` refuse the rest), the
      # closure compares strings by their text, and the first occurrence keeps its context.
      reachableAnswers =
        let
          nodes = map (i: i.key) (
            builtins.genericClosure {
              startSet = map (i: { key = i.node; }) (filter (i: regex.nullable i.st) closure);
              operator = _: [ ];
            }
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
          if v.d == null then
            [ ]
          else
            [
              {
                inherit (v) node path;
                value = v.d;
                state = v.k;
              }
            ]
        else
          [ ]
      ) visits;

      # (NR-Vis) UNDER A DECLARED KEY, `group` (den-hoag-gayc C1, owner-ruled 2026-09-30): resolution
      # stays lazy in data it shadows. Every candidate (a nullable visit) is in group `group` before
      # any datum is read, and presence is tested in shadowing order, rank class by rank class down
      # the trie of step prefixes: at a trie node the symbols (`$` for its nullable visits, then its
      # kids, each ranked by the letter it was reached by) are taken one rank at a time, lowest
      # first, and the first rank class with a present stop or a non-empty child selection is the
      # answer. A higher class is never visited, so a candidate under a lower-ranked present one is
      # never forced.
      #
      # EXACT, by the trie argument (not by citation): `labelOrder` declares integer ranks, so `<l`
      # is a strict weak order and `<p` its lexicographic extension with `$` at `endOfPath`. A
      # member survives the strict prefix minimum (`strictParts`) iff at every trie node of its
      # step word its symbol has the minimum rank among the symbols PRESENT members take there; a
      # kid with no present member below it selects `[ ]` and so cannot win a rank, which makes the
      # first non-empty rank class exactly that minimum. Néron 2015 §5's staged shadowing operator is
      # this, applied once per trie node; Néron's own algorithm does not cover a general WF and
      # `<` (its §2.5 variants), so the citation names the operator, not the proof.
      #
      # A trie node is a STEP prefix, label and target scope together, never a label word: Fig. 1's
      # rules share one head scope, so two kids by one label into different scopes are two nodes,
      # equal in rank and never compared again. The walk tree is that trie (one tree node per
      # acyclic path from the origin), so each visit is examined once and no candidate list is
      # re-grouped (the re-grouping trie is quadratic in a chain and refused by
      # `ci/bench/resolve-parent-chain.sh`).
      lazyParts =
        let
          inherit (o.order) rankOf;
          present = c: c.d != null;
          # D9 under `group`, decided over what the selection READ: a class is examined by reading its
          # members' edges, so the relation node → `parent` over every examined member whose `parent`
          # edge is admitted is exactly the `parent` fields read, and nothing new is forced. The verdict
          # is refuse iff that relation has a cycle — a property of what was read, not of the path shape
          # or the rank order it was read in. The relation is a function, so a node is acyclic iff its
          # chain leaves the relation: one closure down from those exits, as `parentCheck` does over
          # whole chains. A cycle above a shadowing declaration is never read, so never refused.
          parentReadChecked =
            examined:
            let
              entries = filter (e: e.parent != null) (
                map (t: {
                  key = t.node;
                  parent = (self.node t.node).parent;
                }) (filter (t: t.x.admitsParent) examined)
              );
              read = builtins.listToAttrs (
                map (e: {
                  name = attrKey "resolve" e.key;
                  value = e;
                }) entries
              );
              below = builtins.groupBy (e: attrKey "resolve" e.parent) entries;
              exits = builtins.genericClosure {
                startSet = filter (e: !(read ? ${attrKey "resolve" e.parent})) entries;
                operator = e: below.${attrKey "resolve" e.key} or [ ];
              };
              acyclic = builtins.listToAttrs (
                map (e: {
                  name = attrKey "resolve" e.key;
                  value = true;
                }) exits
              );
              cyclic = filter (e: !(acyclic ? ${attrKey "resolve" e.key})) entries;
              # Up from a cyclic node, the chain stays in the relation; the last scope before a repeat
              # has the repeated one, which is on the cycle, as its parent.
              chain = builtins.genericClosure {
                startSet = [ (head cyclic) ];
                operator = e: [ read.${attrKey "resolve" e.parent} ];
              };
            in
            if cyclic == [ ] then
              true
            else
              refuse "resolve" "node ${
                renderId (builtins.elemAt chain (length chain - 1)).parent
              } is on a parent cycle: containment is a tree, and a parent chain that returns to itself is malformed data, not a scope to walk";
          # The staged selection as a loop, not a recursion: `genericClosure` steps an explicit stack of
          # trie nodes, so its stack depth is constant in the walk's depth (`pick`'s recursion
          # aborted at a parent chain of 1,700). A frame is one trie node: `ranks` still to try, `cur` the
          # symbols of the rank being tried, `acc` that rank's selection so far. A node is examined
          # (its members' edges read) when its frame is pushed, and a frame returns `acc` to its parent
          # at the first non-empty rank or `[ ]` when its ranks run out (Néron §5's staged shadowing,
          # one trie node per frame). Every state field is forced per step (ADR-0022).
          symRank = s: rankOf (if s == "$" then s else s.via);
          frameOf =
            cls:
            let
              stops = filter (t: regex.nullable t.st) cls;
              # A symbol is `$` or one kid: Fig. 1's rules share one head scope, so a kid is its own
              # trie node and two kids by one label into different scopes are never compared.
              syms = (if stops != [ ] then [ "$" ] else [ ]) ++ concatMap (t: t.kids) cls;
            in
            {
              inherit cls stops syms;
              ranks = builtins.sort builtins.lessThan (prelude.unique (map symRank syms));
              cur = [ ];
              acc = [ ];
            };
          # LEAF-STOP: a kid with no kids is a trie leaf, whose frame would select only its own stop. The
          # run of leaves at the head of a symbol list is decided in one step and none is pushed. It is
          # read in kid order, each leaf's edges then its datum, as the leaves' own frames would read
          # them, so the first read to fail is the one the frames would have met first.
          leafRun =
            xs:
            let
              # The run's length; a negative count is a stopped one, so no symbol past the run is read.
              n = builtins.foldl' (
                r: t:
                if r < 0 then
                  r
                else if t != "$" && t.kids == [ ] then
                  builtins.seq (regex.nullable t.st && present t) (r + 1)
                else
                  -r - 1
              ) 0 xs;
              k = if n < 0 then -n - 1 else n;
              whole = k == length xs;
              leaves = if whole then xs else builtins.genList (builtins.elemAt xs) k;
            in
            {
              inherit leaves;
              rest = if whole then [ ] else builtins.genList (i: builtins.elemAt xs (i + k)) (length xs - k);
              sel = filter (t: regex.nullable t.st && present t) leaves;
            };
          step =
            stack:
            let
              f = stack.f;
              ret =
                xs:
                if stack.up == null then
                  { done = xs; }
                else
                  {
                    stack = {
                      f = stack.up.f // {
                        acc = stack.up.f.acc ++ xs;
                      };
                      inherit (stack.up) up;
                    };
                  };
            in
            if f.cur != [ ] then
              let
                s = head f.cur;
                f' = f // {
                  cur = builtins.tail f.cur;
                };
              in
              if s == "$" then
                {
                  stack = {
                    f = f' // {
                      acc = f.acc ++ filter present f.stops;
                    };
                    inherit (stack) up;
                  };
                }
              else if s.kids == [ ] then
                let
                  r = leafRun f.cur;
                in
                {
                  stack = {
                    f = f // {
                      cur = r.rest;
                      acc = f.acc ++ r.sel;
                    };
                    inherit (stack) up;
                  };
                  examined = r.leaves;
                }
              else
                let
                  g = frameOf [ s ];
                in
                {
                  stack = {
                    f = g;
                    up = {
                      f = f';
                      inherit (stack) up;
                    };
                  };
                  examined = g.cls;
                }
            else if f.acc != [ ] || f.ranks == [ ] then
              ret f.acc
            else
              let
                cls = filter (s: symRank s == head f.ranks) f.syms;
              in
              # A class of one symbol is entered as on main, so a chain pays nothing; a wider class
              # decides its leading run of leaves on entry.
              if builtins.tail cls == [ ] then
                {
                  stack = {
                    f = f // {
                      cur = cls;
                      ranks = builtins.tail f.ranks;
                    };
                    inherit (stack) up;
                  };
                }
              else
                let
                  r = leafRun cls;
                in
                {
                  stack = {
                    f = f // {
                      cur = r.rest;
                      ranks = builtins.tail f.ranks;
                      acc = f.acc ++ r.sel;
                    };
                    inherit (stack) up;
                  };
                  examined = r.leaves;
                };
          forced =
            st:
            if st ? done then
              builtins.seq st.done st
            else
              builtins.seq st.stack.f.acc (builtins.seq st.stack.f.cur (builtins.seq st.stack.f.ranks st));
          pick =
            cls:
            let
              steps = builtins.genericClosure {
                startSet = [
                  {
                    key = 0;
                    st = forced {
                      stack = {
                        f = frameOf cls;
                        up = null;
                      };
                      examined = cls;
                    };
                  }
                ];
                operator =
                  item:
                  if item.st ? done then
                    [ ]
                  else
                    let
                      st = forced (step item.st.stack);
                    in
                    [
                      {
                        key = builtins.seq st (item.key + 1);
                        inherit st;
                      }
                    ];
              };
            in
            builtins.seq (parentReadChecked (concatMap (s: s.st.examined or [ ]) steps))
              (builtins.elemAt steps (length steps - 1)).st.done;
          # The selection in walk order, as `answers` is everywhere else: sorted by `ix`, so no visit
          # the selection did not examine is read (ADR-0008 item 1; den-hoag-gayc U1 rework).
          picked = pick [ tree ];
          chosen = if length picked < 2 then picked else builtins.sort (a: b: a.ix < b.ix) picked;
          chosenKeys = builtins.listToAttrs (
            map (c: {
              name = toJSON c.ix;
              value = true;
            }) chosen
          );
          isChosen = v: chosenKeys ? ${toJSON v.ix};
          nullableVisits = filter (v: regex.nullable v.st) visits;
          answer = c: {
            inherit (c) node path;
            value = c.d;
            inherit (o) group;
          };
        in
        # A group with no present candidate is no group, as under `groupBy` (`single` answers null).
        if chosen == [ ] then
          { }
        else
          {
            ${attrKey "resolve" o.group} = {
              visible = map answer chosen;
              # Strict by definition: it lists shadowed DECLARATIONS, so presence is its content.
              shadowed = map answer (filter (v: !(isChosen v) && present v) nullableVisits);
            };
          };

      # (NR-Vis) UNDER A DATA-READING KEY, `groupBy`: the witnesses grouped by k, each group's
      # minimal set under `<p`, computed as a prefix minimum over step words (gen-view
      # `relation.nix` step 6, carried): a member's word ŵ = w·$ spells each step as its label and
      # target scope, and it survives iff at every node of ŵ its symbol's label takes the minimum
      # rank among the symbols the group's members take there. The key is
      # a function of the datum (vA2018 Fig. 1, `≤d ⊆ D × D`), so membership is unknowable without
      # it, and every witness's presence and key are forced: the strict form.
      strictParts =
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
          # A trie node is named by an id interned one level at a time, `<level>:<first member index>`,
          # never by its word: a word key cost every member |word|² (178 of 211 MB at a 1,600-deep
          # `parent` chain), an interned one |word|.
          split =
            members:
            let
              # A trie node is a STEP prefix — label and target scope — never a label word: Fig. 1's
              # rules share one head scope, so two members meeting one label into different scopes
              # part there and are never compared again.
              words = map (
                c:
                map (step: [
                  step.label
                  step.to
                ]) c.path
                ++ [ [ "$" ] ]
              ) members;
              deepest = builtins.foldl' (m: w: if length w > m then length w else m) 0 words;
              # One `genericClosure` item per level (a loop, so no level list is re-copied), each
              # level's `alive` forced before the next is keyed (ADR-0022).
              levelAt =
                i: alive:
                let
                  here = map (
                    a:
                    let
                      sym = builtins.elemAt (builtins.elemAt words a.m) i;
                    in
                    {
                      inherit (a) m;
                      node = a.key;
                      rank = rankOf (head sym);
                      combo = attrKey "resolve" "${a.key} ${toJSON sym}";
                    }
                  ) (filter (a: length (builtins.elemAt words a.m) > i) alive);
                  ids = builtins.listToAttrs (
                    builtins.genList (j: {
                      name = (builtins.elemAt here j).combo;
                      value = "${toString i}:${toString j}";
                    }) (length here)
                  );
                  next = map (b: {
                    inherit (b) m;
                    key = ids.${b.combo};
                  }) here;
                in
                {
                  key = builtins.deepSeq next i;
                  inherit here next;
                };
              levels = builtins.genericClosure {
                startSet = [
                  (levelAt 0 (
                    builtins.genList (m: {
                      inherit m;
                      key = "r";
                    }) (length members)
                  ))
                ];
                operator = x: if x.key + 1 >= deepest then [ ] else [ (levelAt (x.key + 1) x.next) ];
              };
              branches = concatMap (x: x.here) levels;
              minRank = builtins.mapAttrs (
                _: bs: builtins.foldl' (m: b: if b.rank < m then b.rank else m) (head bs).rank bs
              ) (builtins.groupBy (b: b.node) branches);
              beaten = builtins.listToAttrs (
                map (b: {
                  name = toString b.m;
                  value = true;
                }) (filter (b: b.rank != minRank.${b.node}) branches)
              );
              tagged = builtins.genList (m: {
                c = builtins.elemAt members m;
                survives = !(beaten ? ${toString m});
              }) (length members);
            in
            {
              visible = map (x: x.c) (filter (x: x.survives) tagged);
              shadowed = map (x: x.c) (filter (x: !x.survives) tagged);
            };
        in
        builtins.mapAttrs (_: split) groups;
      visibleParts = if o ? group then lazyParts else strictParts;
      # Under `group` the selection decides D9 itself, over the classes it examines; a whole-walk
      # verdict would read the edges of every scope it shadows.
      selectionChecked = if o ? group then (x: x) else admittedChecked;
      groupNames = builtins.attrNames visibleParts;

      single =
        group:
        let
          part = visibleParts.${attrKey "resolve" group} or null;
          origins = prelude.unique (map (a: a.node) part.visible);
        in
        # G4: under a declared key every candidate is in `group`, so another name could only read as
        # "no declaration" — a typo answering null.
        if o ? group && group != o.group then
          refuse "resolve" "`single` is asked for group ${toJSON group}, but this resolution declares `group = ${toJSON o.group}`: every candidate is in that one group, so any other name would answer null as if nothing were declared"
        else if part == null then
          null
        else if length origins > 1 then
          refuse "resolve" "group ${toJSON group} has more than one visible declaration, from ${toJSON origins}. That is an AMBIGUITY in the sense of Neron et al. 2015 (Fig. 3 rule (V); §2.2 Duplicate Declarations) — two declaration occurrences for one read. `single` answers with one declaration or REFUSES; read the group's `answers` to see every one"
        else
          (head part.visible).value;
    in
    # `marksAt from` is forced with the door's other operands, so a scope that declares no `marks`
    # is refused in every direction and mode, whether or not the walk considers any edge (row 19).
    builtins.seq (identifier "resolve" from) (
      builtins.seq dataFilter (
        builtins.seq (marksAt from) (
          {
            inherit mode;
            withheld = id: withheldChecked (withheld id);
            answers =
              if mode == "reachable" then
                admittedChecked reachableAnswers
              else if mode == "witnesses" then
                admittedChecked witnessAnswers
              else
                selectionChecked (concatMap (g: visibleParts.${g}.visible) groupNames);
          }
          // prelude.optionalAttrs (mode == "visible") {
            # `shadowed` reads every candidate whatever the key, so it takes the whole-walk verdict.
            shadowed = admittedChecked (concatMap (g: visibleParts.${g}.shadowed) groupNames);
            single = group: selectionChecked (single group);
          }
        )
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
          "group"
          "bound"
          "direction"
        ];
      }
      (
        o:
        let
          mode = o.mode or "reachable";
          direction = o.direction or "outbound";
        in
        if !(elem mode modes) then
          refuse "resolve" "unknown mode ${toJSON mode} (one of ${quote modes})"
        # G1 reads presence (`?`): `group` beside `groupBy = null` is still two keys stated.
        else if o ? group && o ? groupBy then
          refuse "resolve" "`group` and `groupBy` are both given; state exactly one competition key: `group`, a declared constant read before any datum (lazy in shadowed data), or `groupBy`, a function of the answer (strict: it forces every candidate it groups)"
        else if mode == "visible" && (o.groupBy or null) == null && !(o ? group) then
          refuse "resolve" "mode \"visible\" requires a competition key, and it is never defaulted (den-hoag-l7af / ADR-0024 ruling 3): state `group = \"k\";` (a declared constant, lazy in shadowed data) or `groupBy = ans: …;` (a function of the answer, strict); a caller wanting the per-node reading states `groupBy = ans: ans.node;` explicitly"
        else if o ? group && !(isString o.group) then
          refuse "resolve" "group is a ${typeOf o.group}, not a string; `group` is the competition key as a declared constant (a key computed from the answer is `groupBy`)"
        else if mode == "visible" && !(o ? order) then
          refuse "resolve" "mode \"visible\" requires `order`, a `labelOrder` value (<l over the alphabet, with `$`'s rank)"
        else if mode != "visible" && o ? order then
          refuse "resolve" "`order` is read only by mode \"visible\", and the mode is ${toJSON mode}"
        else if mode != "visible" && o ? groupBy then
          refuse "resolve" "`groupBy` is read only by mode \"visible\", and the mode is ${toJSON mode}"
        else if mode != "visible" && o ? group then
          refuse "resolve" "`group` is read only by mode \"visible\", and the mode is ${toJSON mode}"
        else if (o.wf.__element or null) != "wellFormed" then
          refuse "resolve" "wf is not a `wellFormed` value (build it with `wellFormed { alphabet; expression; }`)"
        else if mode == "visible" && (o.order.__element or null) != "labelOrder" then
          refuse "resolve" "order is not a `labelOrder` value (build it with `labelOrder { alphabet; layers; endOfPath; }`)"
        # G5: `labelOrder`'s own law (total over L̂) applied at the door that pairs the two values. A
        # letter the walk can step and `order` cannot rank would otherwise be refused only when some
        # datum happened to sit behind it, and the two keys would disagree on when.
        else if mode == "visible" && builtins.any (l: !(elem l o.order.alphabet)) o.wf.alphabet then
          refuse "resolve" "`order` does not rank '${
            head (filter (l: !(elem l o.order.alphabet)) o.wf.alphabet)
          }', a letter of `wf`'s alphabet (${quote o.wf.alphabet}); mode \"visible\" ranks every letter the walk can step, so the label order must be total over the walk's alphabet"
        else if !(elem direction directions) then
          refuse "resolve" "unknown direction ${toJSON direction} (one of ${quote directions})"
        else
          run o mode direction
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
