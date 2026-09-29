# Label-regex kernel for graph queries: Brzozowski (1964) derivatives kept in a
# normal form, so that `stateKey` is a canonical seen-set key.
#
# THE FINITENESS THEOREM IS BRZOZOWSKI'S. Thm 5.2 — "every regular expression
# has only a finite number of dissimilar derivatives" — is what bounds the
# state set, where the similarity of Def 5.2 is the ACI identities of
# ALTERNATION ONLY: R+R=R, P+Q=Q+P, (P+Q)+R=P+(Q+R). That bound is not free for
# an arbitrary expression, it is a bound MODULO those identities, and
# Brzozowski's own proof (Appendix II) names the load-bearing one: "it is the
# identity R + R = R which allows us to terminate the process." So the
# normalization has to be performed, and `alt` performs exactly those three —
# flatten, sort, dedup.
#
# OWENS, REPPY & TURON (2009) SUPPLY THE ENLARGED RULE SET, NOT THE THEOREM.
# Their Def 4.1 is a strict superset of Brzozowski's similarity — sequence
# flattened with unit/zero absorption, star collapsed — together with the
# smart-constructor strategy this file follows, normalizing on the way in
# rather than canonicalizing after the fact. The flattening is right-nested:
# ORT apply `(r · s) · t ≈ r · (s · t)` "as a reduction from left to right"
# (§4.1), so a sequence is a cons whose head is never a sequence, and every
# suffix of one is itself a term. ORT credit the finiteness result
# to Brzozowski themselves (§3.3, §4.1) and state no termination theorem for
# the enlarged set. That composite is folklore, and safely so: every added
# identity is semantics-preserving and size-decreasing, so it can only merge
# states that ACI alone would have kept apart, while Brzozowski's bound already
# holds "even if only similarity ... is recognized". ORT §4.2's character-set
# merge (`alt` of `any` with a literal) is NOT implemented — that is a
# minimality rule, never a termination one.
#
# Labels are the edge-kind names of a labeled graph (Néron et al. 2015); a
# query's path constraint is a word in this alphabet; the parse alphabet is
# [A-Za-z0-9_-]+.
{ prelude }:
let
  # ── the canonical key is a Merkle digest ─────────────────────────────────
  # Every node a constructor builds carries `k`, the sha256 of its tag and its children's `k`.
  # `plus r` holds one `r` twice, and Nix shares that value, so its `k` thunk is forced once
  # however many parents reach it: a key costs one hash per node of the DAG, never a rendering
  # of the tree the DAG unfolds to (5·2^k − 2 characters for k nested `(…)+`, den-hoag-2dx7j).
  # The preimage is injective — one tag character, then a label or 64-hex child keys of fixed
  # width — so two normal forms share a key only by a sha256 collision, and a label carrying
  # `* | . ( )` no longer collides with a composite as the old rendering did.
  #
  # The key exists only on a term the constructors built: normal form is their invariant
  # (Owens, Reppy & Turon's strategy, above), so a hand-built attrset was never canonically
  # keyed, and it is refused by name rather than keyed.
  #
  # Each composite is built with its key already forced (`builtins.seq k { … }`). The constructors
  # force every child before building on it, so on a term already built (e.g. by `builtins.foldl'`)
  # a child's key is a value by then, and reading any node's key walks nothing: such a term keys in
  # constant stack at any depth. Before this, forcing a root's key walked the whole term and met the
  # evaluator's call-depth ceiling near 2,500 levels (den-hoag-regex-statekey-ceiling-4ok8y). A term
  # accumulated LAZILY through the constructors is constructed on its first read, and the recursion
  # of that construction is the caller's: measured at 1,110 levels, with or without this.
  notATerm = "gen-scope.regex: this value was not built by the regex constructors (eps, empty, any, lit, seq, alt, star, opt, plus, deriv, parse), so it has no canonical key";

  # ── constructors normalize on the way in ─────────────────────────────────
  eps = {
    t = "eps";
    k = builtins.hashString "sha256" "e";
    nu = true;
    h = 0;
    sz = 1;
  };
  empty = {
    t = "empty";
    k = builtins.hashString "sha256" "0";
    nu = false;
    h = 0;
    sz = 1;
  };
  any = {
    t = "any";
    k = builtins.hashString "sha256" "_";
    nu = false;
    h = 0;
    sz = 1;
  };
  lit = l: {
    t = "lit";
    inherit l;
    k = builtins.hashString "sha256" ("'" + l);
    nu = false;
    h = 0;
    sz = 1;
  };

  isT = t: r: r.t == t;
  nuOf = r: r.nu or (throw notATerm);
  hOf = r: r.h or (throw notATerm);
  # 1 + the tallest child; children are values by the time a parent is built
  # the constructors have already refused a child with no `k`, so every child carries `nu` and `h`
  above =
    rs:
    let
      hs = builtins.sort builtins.lessThan (builtins.catAttrs "h" rs);
    in
    1 + builtins.elemAt hs (builtins.length hs - 1);

  # the node count of the tree this term unfolds to, saturating past derivDirectSize: an upper
  # bound on what one direct derivative walks, which reads a star's body, an alt's branches and a
  # seq's head, and its tail past a nullable head
  sat = n: if n > derivDirectSize then derivDirectSize + 1 else n;
  szOf = rs: sat (1 + builtins.foldl' builtins.add 0 (builtins.catAttrs "sz" rs));

  # canonical key; alt is sorted by this, making it a true canonical form
  stateKey = r: r.k or (throw notATerm);

  # A seq is a right-nested cons: `hd` is never a seq, and `tl` is the rest, itself a seq or a
  # single term. Every suffix of a sequence is therefore a node, built and keyed once, so a
  # derivative's continuation is a reference rather than a copy of the remaining elements.
  hsOf = t: if t.t == "seq" then t.h else 1 + hOf t;
  cons =
    x: t:
    let
      k = builtins.hashString "sha256" ("." + (x.k or (throw notATerm)) + (t.k or (throw notATerm)));
      nu = x.nu && t.nu;
      h =
        let
          a = 1 + x.h;
          b = hsOf t;
        in
        if a < b then b else a;
      sz = sat (x.sz + (if t.t == "seq" then t.sz else 1 + t.sz));
      node = {
        t = "seq";
        hd = x;
        tl = t;
        # the flat element list, as a seq has always published it; read lazily, never by this file
        rs = spine node;
        inherit
          k
          nu
          h
          sz
          ;
      };
    in
    builtins.seq k (builtins.seq nu (builtins.seq h (builtins.seq sz node)));
  # a seq's elements in order, walked without recursion
  spine =
    s:
    map (x: if isT "seq" x.n then x.n.hd else x.n) (
      builtins.genericClosure {
        startSet = [
          {
            key = 0;
            n = s;
          }
        ];
        operator =
          x:
          if isT "seq" x.n then
            [
              {
                key = x.key + 1;
                n = x.n.tl;
              }
            ]
          else
            [ ];
      }
    );
  reverse =
    xs:
    let
      n = builtins.length xs;
    in
    builtins.genList (i: builtins.elemAt xs (n - 1 - i)) n;
  # `x` in front of `t`: the one step every seq construction is made of
  prepend =
    x: t:
    if x.t == "empty" || t.t == "empty" then
      empty
    else if x.t == "eps" then
      t
    else if t.t == "eps" then
      x
    else if x.t == "seq" then
      builtins.foldl' (a: y: cons y a) t (reverse (spine x))
    else
      cons x t;
  # built right to left with foldl', so a sequence of any width builds in constant stack; the last
  # element's spine is reused whole, and an earlier seq element contributes its own spine
  seq = rs: builtins.foldl' (acc: x: prepend x acc) eps (reverse rs);

  alt =
    rs:
    let
      flat = builtins.concatMap (r: if isT "alt" r then r.rs else [ r ]) rs;
      noEmpty = builtins.filter (r: !(isT "empty" r)) flat;
      # dedup + sort by canonical key (ACI: assoc by flatten, comm by sort, idem by dedup)
      byKey = builtins.listToAttrs (
        map (r: {
          name = stateKey r;
          value = r;
        }) noEmpty
      );
      keys = builtins.sort builtins.lessThan (builtins.attrNames byKey);
      canon = map (k: byKey.${k}) keys;
    in
    if canon == [ ] then
      empty
    else if builtins.length canon == 1 then
      builtins.head canon
    else
      let
        k = builtins.hashString "sha256" ("|" + builtins.concatStringsSep "" keys);
        nu = builtins.elem true (builtins.catAttrs "nu" canon);
        h = above canon;
        sz = szOf canon;
      in
      builtins.seq k (
        builtins.seq nu (
          builtins.seq h (
            builtins.seq sz {
              t = "alt";
              rs = canon;
              inherit
                k
                nu
                h
                sz
                ;
            }
          )
        )
      );

  star =
    r:
    if isT "star" r then
      r
    else if isT "eps" r || isT "empty" r then
      eps
    else
      let
        k = builtins.hashString "sha256" ("*" + r.k or (throw notATerm));
        h = 1 + hOf r;
        sz = sat (1 + r.sz);
      in
      builtins.seq k (
        builtins.seq h (
          builtins.seq sz {
            t = "star";
            nu = true;
            inherit
              r
              k
              h
              sz
              ;
          }
        )
      );

  opt =
    r:
    alt [
      eps
      r
    ];
  plus =
    r:
    seq [
      r
      (star r)
    ];

  nullable = nuOf;

  # The terms one derivative step walks rather than derives: from the root, an alt's branches and a
  # seq's tail past a nullable head, each distinct term once (by key). This is the derivative's
  # sum unrolled across alts and nullable tails: Brzozowski 1964 (3.7) D(PQ) = (D P)Q + δ(P) D Q at
  # each cons, and (3.8) D(P + Q) = D P + D Q at each alt, with R + R = R applied to the walk
  # itself, so a suffix reached from many places is walked once. One step on a seq of width m is
  # therefore O(m), where deriving each summand's suffix separately re-walked it, Θ(m³) per step on
  # the alt of suffixes the first step leaves (den-hoag-6bh04).
  lfReach =
    r:
    map (x: x.r) (
      builtins.genericClosure {
        startSet = [
          {
            key = r.k;
            inherit r;
          }
        ];
        operator =
          x:
          map
            (c: {
              key = c.k;
              r = c;
            })
            (
              if x.r.t == "alt" then
                x.r.rs
              else if x.r.t == "seq" && x.r.hd.nu then
                [ x.r.tl ]
              else
                [ ]
            );
      }
    );
  # a step walks only where a nullable seq head is in reach: a seq led by one, or an alt holding one
  nullHead = x: x.t == "seq" && x.hd.nu;
  walks = r: nullHead r || (r.t == "alt" && builtins.any nullHead r.rs);
  # the subterms one derivative step derives through `self`
  derivChildren =
    r:
    if r.t == "star" then
      [ r.r ]
    else if walks r then
      builtins.concatMap (
        x:
        if x.t == "seq" then
          [ x.hd ]
        else if x.t == "alt" then
          [ ]
        else
          [ x ]
      ) (lfReach r)
    else if r.t == "seq" then
      [ r.hd ]
    else if r.t == "alt" then
      r.rs
    else
      [ ];

  # One Brzozowski step, with `self` deriving the children: one summand per walked term, and one alt.
  derivStep =
    self: l: r:
    if r.t == "eps" || r.t == "empty" then
      empty
    else if r.t == "any" then
      eps
    else if r.t == "lit" then
      (if r.l == l then eps else empty)
    else if r.t == "star" then
      prepend (self r.r) r
    else if !(walks r) then
      (if r.t == "seq" then prepend (self r.hd) r.tl else alt (map self r.rs))
    else
      alt (
        builtins.concatMap (
          x:
          if x.t == "seq" then
            [
              (prepend (self x.hd) x.tl)
            ]
          else if x.t == "alt" then
            [ ]
          else
            [ (self x) ]
        ) (lfReach r)
      );

  derivDirect =
    l:
    let
      go = derivStep go l;
    in
    go;

  # ── the derivative, warmed past a height ─────────────────────────────────
  # Brzozowski's derivative (1964 Thm 3.1) and ν (Def 3.2; Owens, Reppy & Turon 2009 §3.1) are
  # structural recursions, and their result does not depend on the order they are evaluated in.
  # `nullable` is carried: every node is built with `nu` already a value, so reading it walks
  # nothing. `deriv` is one step (`derivStep`) tied two ways: directly, which is the plain
  # recursion, and warmed, where the subterms the step reads are enumerated by `genericClosure`
  # and their memo cells are forced in ascending `h`, so every cell finds its children already
  # evaluated (the `coneRank` construction in order.nix). The warmed arm needs a constant 19-29
  # frames, so a term of any height derives in bounded stack. Before this, `deriv` aborted at 417
  # nested levels and `nullable` at 2,500 (den-hoag-smn53).
  #
  # `deriv`'s arm is chosen by cost. Both switches are cost switches, not bounds: always warming is
  # ceiling-free too, and costs ×2.0 calls on `query`'s own walks. The direct arm is a tree walk, so
  # on a term whose subterms are shared it derives each one once per path to it: `plus r` holds r
  # twice, and nested `(…?)+` doubles the walk at every level. `sz`, carried like `h`, counts the
  # nodes the term unfolds to, saturating past `derivDirectSize`; past it the warmed arm steps each
  # distinct subterm once (its memo is keyed on `k`, ORT 2009 §4.1's finite map with RE keys). A
  # derivative therefore takes at most max(derivDirectSize, distinct subterms) steps (den-hoag-naalo),
  # and a step walks each suffix of a seq once (`lfReach`). Figures are nix; det agrees to +1 call.
  #
  # `derivDirectHeight` = 64 is set by the stack; sharing is `derivDirectSize`'s leg, not its own:
  # - stack: the direct arm needs ~12 frames per unit of height, 773 at h = 64 (lix 772), against
  #   the default `max-call-depth` of 10,000; the warmed arm needs 29;
  # - sharing: a height bounds only what `parse` can share (`plus`'s two copies). One derivative of
  #   `(`×k `a*` `)+`×k takes 79.7 M calls at k = 20 under T = 64 without `sz`, and does not return
  #   at k = 32; with `sz` it takes 24,554 and 75,676. A caller of the constructors shares w ways per
  #   level, which no height bounds: a 64-way fan of height 9 takes 16.6 M calls under T = 16, and
  #   23,823 with `sz`;
  # - workloads: `query`'s patterns and their derivatives reach h ≤ 3, so T ≥ 4 is indifferent.
  # T = 16 with `sz` would remove the direct excess below the size cap (a DAG of height 21 and sz
  # 1,017: 19,882 calls, 2,435 under T = 16) at +39% calls on every unshared term of height 17-64.
  # T = 64 keeps the excess, a constant, over the percentage.
  #
  # `derivDirectSize` = 1024 is set from three legs:
  # - DAG: below it the direct walk takes at most `derivDirectSize` steps, and the bound is tight:
  #   that DAG of sz 1,017 takes 1,017 steps over 30 distinct subterms;
  # - wide: an unshared alternation just past it pays the warmed arm, ×3.0 derivative calls (lix
  #   ×4.3-4.7). Only the constructors build one: 1,000 characters of `parse` hold ≤ ~500 branches;
  # - workloads: realistic patterns sit far below it; carrying `sz` costs +0.5-2.4% calls and
  #   +2.7-5.0% thunks on `query`'s walks and `parse`.
  # Lowering it trades the DAG excess for the wide penalty.
  derivWarmed =
    l: r:
    let
      nodes = builtins.genericClosure {
        startSet = [
          {
            key = stateKey r;
            inherit r;
          }
        ];
        operator =
          x:
          map (c: {
            key = stateKey c;
            r = c;
          }) (derivChildren x.r);
      };
      memo = builtins.listToAttrs (
        map (x: {
          name = x.key;
          value = derivStep (c: memo.${c.k}) l x.r;
        }) nodes
      );
      warmed = builtins.foldl' (acc: x: builtins.seq memo.${x.key} acc) true (
        builtins.sort (a: b: a.r.h < b.r.h) nodes
      );
    in
    builtins.seq warmed memo.${r.k};

  derivDirectHeight = 64;
  derivDirectSize = 1024;
  deriv =
    l: r:
    if (r.h or (throw notATerm)) <= derivDirectHeight && r.sz <= derivDirectSize then
      derivDirect l r
    else
      derivWarmed l r;

  # ── string sugar ──────────────────────────────────────────────────────────
  # grammar:  expr := seqE ("|" seqE)*        (alternation binds loosest)
  #           seqE := post+                    (juxtaposition = sequence)
  #           post := atom ("*" | "?" | "+")?
  #           atom := LABEL | "_" | "(" expr ")"
  # LABEL chars: [A-Za-z0-9_-] — but a lone "_" is the any-label wildcard.
  # Character-level tokenizer + recursive-descent over the token list; index
  # threaded, no regex builtins (builtins.match over user strings backtracks and
  # can stack-overflow — see REFERENCE.md).
  # ADR-0032 (a named refusal where a real ceiling exists): the parser's recursion is bounded
  # by the pattern's length, knowable before the first frame. Nested groups bind: `(`×k a `)`×k
  # returns at k = 623 (1,247 characters) and aborts at 624, and 200 caller frames move that
  # boundary by 13 levels. The default leaves ~1,900 caller frames of headroom. LOWER it to match
  # the stack a caller is itself nested in; raising it past the measured boundary is out of
  # contract and meets the uncatchable abort this cap exists to replace.
  parseMaxLength = 1000;

  # A pure OPTIONS door (P2, `prelude.door`): closed — an unknown option is refused by name,
  # catchably, when the options are applied, before the pattern is.
  parseWith = prelude.door {
    name = "gen-scope.regex.parseWith";
    optional = [ "maxLength" ];
  } (o: parseWithMax (o.maxLength or parseMaxLength));
  parseWithMax =
    maxLength: s:
    let
      err =
        m:
        throw "gen-scope.regex.parse: ${m} (in ${
          builtins.toJSON (if n > 60 then builtins.substring 0 60 s + "…" else s)
        })";
      n = builtins.stringLength s;
      isLabelChar =
        c:
        (c >= "a" && c <= "z") || (c >= "A" && c <= "Z") || (c >= "0" && c <= "9") || c == "_" || c == "-";
      # tokenize → [ { t = "label"|"("|")"|"|"|"*"|"?"|"+"; v? } ]
      tokenize =
        i:
        if i >= n then
          [ ]
        else
          let
            c = builtins.substring i 1 s;
          in
          if c == " " || c == "\t" || c == "\n" then
            tokenize (i + 1)
          else if c == "(" || c == ")" || c == "|" || c == "*" || c == "?" || c == "+" then
            [ { t = c; } ] ++ tokenize (i + 1)
          else if isLabelChar c then
            let
              takeEnd = j: if j < n && isLabelChar (builtins.substring j 1 s) then takeEnd (j + 1) else j;
              e = takeEnd i;
            in
            [
              {
                t = "label";
                v = builtins.substring i (e - i) s;
              }
            ]
            ++ tokenize e
          else
            err "unexpected character '${c}'";
      toks = tokenize 0;
      len = builtins.length toks;
      at = i: builtins.elemAt toks i;

      # each parser: i → { re; i; }
      pAtom =
        i:
        if i >= len then
          err "unexpected end of input"
        else
          let
            tok = at i;
          in
          if tok.t == "label" then
            {
              re = if tok.v == "_" then any else lit tok.v;
              i = i + 1;
            }
          else if tok.t == "(" then
            let
              inner = pExpr (i + 1);
            in
            if inner.i < len && (at inner.i).t == ")" then
              {
                re = inner.re;
                i = inner.i + 1;
              }
            else
              err "unbalanced parenthesis"
          else
            err "unexpected token '${tok.t}'";
      pPost =
        i:
        let
          a = pAtom i;
          tok = if a.i < len then (at a.i).t else "";
        in
        if tok == "*" then
          {
            re = star a.re;
            i = a.i + 1;
          }
        else if tok == "?" then
          {
            re = opt a.re;
            i = a.i + 1;
          }
        else if tok == "+" then
          {
            re = plus a.re;
            i = a.i + 1;
          }
        else
          a;
      startsAtom = i: i < len && ((at i).t == "label" || (at i).t == "(");
      pSeq =
        i:
        let
          go =
            acc: j:
            if startsAtom j then
              let
                p = pPost j;
              in
              go (acc ++ [ p.re ]) p.i
            else
              {
                re = seq acc;
                i = j;
              };
        in
        if startsAtom i then go [ ] i else err "expected a label or '('";
      pExpr =
        i:
        let
          first = pSeq i;
          go =
            acc: j:
            if j < len && (at j).t == "|" then
              let
                nxt = pSeq (j + 1);
              in
              go (acc ++ [ nxt.re ]) nxt.i
            else
              {
                re = alt acc;
                i = j;
              };
        in
        go [ first.re ] first.i;
      result =
        if toks == [ ] then
          {
            re = eps;
            i = 0;
          }
        else
          pExpr 0;
    in
    if n > maxLength then
      err "pattern length ${toString n} exceeds the stated cap of ${toString maxLength} characters; past it the parser's recursion meets the evaluator's call-depth ceiling, an abort tryEval cannot catch (lower the cap with parseWith { maxLength; } when calling from deep in a stack)"
    else if result.i == len then
      result.re
    else
      err "trailing tokens";

  parse = parseWith { };
in
{
  inherit
    eps
    empty
    any
    lit
    seq
    alt
    star
    opt
    plus
    nullable
    deriv
    stateKey
    parse
    parseWith
    ;
}
