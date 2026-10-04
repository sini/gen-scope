{ genPreludeLib, ... }:
let
  # The suite for `lib/regex.nix`, the engine the calculus reads.
  regex = import ../../lib/regex.nix { prelude = genPreludeLib; };
  r = regex;
  # acceptance oracle: fold derivatives over a word, check nullability
  accepts = re: word: r.nullable (builtins.foldl' (st: l: r.deriv l st) re word);
  rep = n: c: builtins.concatStringsSep "" (builtins.genList (_: c) n);
  nested = k: (rep k "(") + "a" + (rep k ")");
  # `(`×k a `)+`×k, 3k+1 characters; `plus` holds its argument twice at every level
  plusNest = k: (rep k "(") + "a" + (rep k ")+");
  # `(`×k a? `)+`×k: over a nullable argument the derivative reads both of plus's copies
  optPlusNest = k: (rep k "(") + "a?" + (rep k ")+");
  # x(k) = x(k-1)* a | x(k-1)* b, each level holding the one below twice, with d_a x(k) written
  # out by the constructors alone: D(k) = D(k-1) x(k-1)* a | eps | D(k-1) x(k-1)* b
  dag =
    n:
    builtins.foldl'
      (
        p: _:
        let
          x = r.alt [
            (r.seq [
              (r.star p.x)
              (r.lit "a")
            ])
            (r.seq [
              (r.star p.x)
              (r.lit "b")
            ])
          ];
          d = r.alt [
            (r.seq [
              p.d
              (r.star p.x)
              (r.lit "a")
            ])
            r.eps
            (r.seq [
              p.d
              (r.star p.x)
              (r.lit "b")
            ])
          ];
        in
        builtins.seq x (builtins.seq d { inherit x d; })
      )
      {
        x = r.lit "a";
        d = r.eps;
      }
      (builtins.genList (i: i) n);
  # `n` levels of `seq [ (lit "a") (star acc) ]`, built through the constructors alone
  chain =
    n:
    builtins.foldl' (
      acc: _:
      r.seq [
        (r.lit "a")
        (r.star acc)
      ]
    ) (r.lit "a") (builtins.genList (i: i) n);
  # a key's width, whichever authority computes the digest
  keyWidth = builtins.stringLength (r.stateKey (r.lit "a"));
  # n levels built bottom-up by the constructors: `head` nests where `deriv` descends, `altseq`
  # where `nullable` does, and `wide` is one seq of n nullable elements
  build = step: n: builtins.foldl' (acc: _: step acc) (r.lit "a") (builtins.genList (i: i) n);
  head = build (
    acc:
    r.seq [
      (r.star acc)
      (r.lit "a")
    ]
  );
  altseq = build (
    acc:
    r.alt [
      (r.lit "b")
      (r.seq [
        acc
        (r.lit "a")
      ])
    ]
  );
  wide = n: r.seq (builtins.genList (_: r.star (r.lit "a")) n);
  optSeq = n: r.seq (builtins.genList (_: r.opt (r.lit "a")) n);
  lits = n: r.seq (builtins.genList (i: r.lit "l${toString i}") n);
  literalsOf =
    x:
    let
      children =
        n:
        if n.t == "star" then
          [ n.r ]
        else if n.t == "seq" || n.t == "alt" then
          n.rs
        else
          [ ];
      reached = builtins.genericClosure {
        startSet = [
          {
            key = r.stateKey x;
            n = x;
          }
        ];
        operator =
          y:
          map (c: {
            key = r.stateKey c;
            n = c;
          }) (children y.n);
      };
    in
    map (y: y.n.l) (builtins.filter (y: y.n.t == "lit") reached);
  # d_a (head n), written out by the constructors alone: d_a h(n) = (d_a h(n-1)) h(n-1)* a | eps
  headDeriv =
    n:
    (builtins.foldl'
      (
        p: _:
        let
          h = r.seq [
            (r.star p.h)
            (r.lit "a")
          ];
          d = r.alt [
            (r.seq [
              p.d
              (r.star p.h)
              (r.lit "a")
            ])
            r.eps
          ];
        in
        # both fields forced per step, or reading `d` unwinds an n-deep thunk chain
        builtins.seq h (builtins.seq d { inherit h d; })
      )
      {
        h = r.lit "a";
        d = r.eps;
      }
      (builtins.genList (i: i) n)
    ).d;
in
{
  flake.tests.regex = {
    test-lit-accepts-itself = {
      expr = accepts (r.lit "a") [ "a" ];
      expected = true;
    };
    test-lit-rejects-other = {
      expr = accepts (r.lit "a") [ "b" ];
      expected = false;
    };
    test-eps-accepts-empty = {
      expr = accepts r.eps [ ];
      expected = true;
    };
    test-empty-rejects-empty = {
      expr = accepts r.empty [ ];
      expected = false;
    };
    test-seq-order = {
      expr =
        accepts
          (r.seq [
            (r.lit "a")
            (r.lit "b")
          ])
          [
            "a"
            "b"
          ];
      expected = true;
    };
    test-seq-wrong-order = {
      expr =
        accepts
          (r.seq [
            (r.lit "a")
            (r.lit "b")
          ])
          [
            "b"
            "a"
          ];
      expected = false;
    };
    test-star-empty = {
      expr = accepts (r.star (r.lit "a")) [ ];
      expected = true;
    };
    test-star-many = {
      expr = accepts (r.star (r.lit "a")) [
        "a"
        "a"
        "a"
      ];
      expected = true;
    };
    test-star-then-lit = {
      expr =
        accepts
          (r.seq [
            (r.star (r.lit "c"))
            (r.lit "n")
          ])
          [
            "c"
            "c"
            "n"
          ];
      expected = true;
    };
    test-opt-present = {
      expr =
        accepts
          (r.seq [
            (r.lit "a")
            (r.opt (r.lit "b"))
          ])
          [
            "a"
            "b"
          ];
      expected = true;
    };
    test-opt-absent = {
      expr = accepts (r.seq [
        (r.lit "a")
        (r.opt (r.lit "b"))
      ]) [ "a" ];
      expected = true;
    };
    test-plus-zero-rejected = {
      expr = accepts (r.plus (r.lit "a")) [ ];
      expected = false;
    };
    test-alt-either = {
      expr = accepts (r.alt [
        (r.lit "a")
        (r.lit "b")
      ]) [ "b" ];
      expected = true;
    };
    test-any-single = {
      expr = accepts r.any [ "whatever" ];
      expected = true;
    };
    test-star-any-universal = {
      expr = accepts (r.star r.any) [
        "x"
        "y"
        "z"
      ];
      expected = true;
    };

    # ACI canonicalization (Brzozowski Thm 5.2: finitely many derivatives modulo
    # the ACI identities of alternation, which are his Def 5.2 similarity)
    test-alt-commutes = {
      expr =
        r.stateKey (
          r.alt [
            (r.lit "a")
            (r.lit "b")
          ]
        ) == r.stateKey (
          r.alt [
            (r.lit "b")
            (r.lit "a")
          ]
        );
      expected = true;
    };
    test-alt-idempotent = {
      expr =
        r.stateKey (
          r.alt [
            (r.lit "a")
            (r.lit "a")
          ]
        ) == r.stateKey (r.lit "a");
      expected = true;
    };
    test-star-star-collapses = {
      expr = r.stateKey (r.star (r.star (r.lit "a"))) == r.stateKey (r.star (r.lit "a"));
      expected = true;
    };
    test-seq-empty-absorbs = {
      expr =
        r.stateKey (
          r.seq [
            (r.lit "a")
            r.empty
          ]
        ) == r.stateKey r.empty;
      expected = true;
    };
    test-seq-eps-drops = {
      expr =
        r.stateKey (
          r.seq [
            r.eps
            (r.lit "a")
          ]
        ) == r.stateKey (r.lit "a");
      expected = true;
    };
    test-alt-associates = {
      expr =
        r.stateKey (
          r.alt [
            (r.alt [
              (r.lit "a")
              (r.lit "b")
            ])
            (r.lit "c")
          ]
        ) == r.stateKey (
          r.alt [
            (r.lit "a")
            (r.alt [
              (r.lit "b")
              (r.lit "c")
            ])
          ]
        );
      expected = true;
    };
    # pins the seq's canonical form: a seq element is spliced into the right-nested cons
    test-seq-associates = {
      expr =
        r.stateKey (
          r.seq [
            (r.seq [
              (r.lit "a")
              (r.lit "b")
            ])
            (r.lit "c")
          ]
        ) == r.stateKey (
          r.seq [
            (r.lit "a")
            (r.seq [
              (r.lit "b")
              (r.lit "c")
            ])
          ]
        );
      expected = true;
    };

    # finiteness: derivative closure of a star-alt reaches a fixed keyset (bounded)
    test-derivative-space-finite = {
      expr =
        let
          re0 = r.seq [
            (r.star (
              r.alt [
                (r.lit "c")
                (r.lit "i")
              ]
            ))
            (r.opt (r.lit "n"))
          ];
          labels = [
            "c"
            "i"
            "n"
          ];
          step =
            states:
            let
              next = builtins.foldl' (
                acc: st: builtins.foldl' (a: l: a // { ${r.stateKey (r.deriv l st)} = r.deriv l st; }) acc labels
              ) states (builtins.attrValues states);
            in
            if builtins.attrNames next == builtins.attrNames states then states else step next;
          all = step { ${r.stateKey re0} = re0; };
        in
        builtins.length (builtins.attrNames all) < 12;
      expected = true;
    };

    # string sugar — parse must agree with the constructor AST (canonical keys equal)
    test-parse-spec-example = {
      expr =
        r.stateKey (r.parse "contains* nest?") == r.stateKey (
          r.seq [
            (r.star (r.lit "contains"))
            (r.opt (r.lit "nest"))
          ]
        );
      expected = true;
    };
    test-parse-alt-loosest = {
      expr =
        r.stateKey (r.parse "a | b c") == r.stateKey (
          r.alt [
            (r.lit "a")
            (r.seq [
              (r.lit "b")
              (r.lit "c")
            ])
          ]
        );
      expected = true;
    };
    test-parse-parens = {
      expr =
        r.stateKey (r.parse "(a | b) c") == r.stateKey (
          r.seq [
            (r.alt [
              (r.lit "a")
              (r.lit "b")
            ])
            (r.lit "c")
          ]
        );
      expected = true;
    };
    test-parse-any = {
      expr = r.stateKey (r.parse "_") == r.stateKey r.any;
      expected = true;
    };
    test-parse-empty-is-eps = {
      expr = r.stateKey (r.parse "") == r.stateKey r.eps;
      expected = true;
    };
    test-parse-plus = {
      expr = accepts (r.parse "hop+") [
        "hop"
        "hop"
      ];
      expected = true;
    };
    test-parse-unbalanced-throws = {
      expr = (builtins.tryEval (r.stateKey (r.parse "(a"))).success;
      expected = false;
    };
    test-parse-leading-postfix-throws = {
      expr = (builtins.tryEval (r.stateKey (r.parse "*a"))).success;
      expected = false;
    };
    test-parse-double-postfix-throws = {
      expr = (builtins.tryEval (r.stateKey (r.parse "a**"))).success;
      expected = false;
    };
    test-parse-dangling-alt-throws = {
      expr = (builtins.tryEval (r.stateKey (r.parse "a |"))).success;
      expected = false;
    };

    # ── the length cap, armed both sides of it ──
    test-parse-length-cap-refuses-by-name = {
      expr = (builtins.tryEval (r.stateKey (r.parse (rep 1001 "a")))).success;
      expected = false;
    };
    test-control-parse-at-the-cap-still-parses = {
      expr = r.stateKey (r.parse (rep 1000 "a")) == r.stateKey (r.lit (rep 1000 "a"));
      expected = true;
    };

    # ── nothing inside the accept band aborts ──
    # 91 characters, 30 levels of `(…)+`: the rendered key was 5·2^30 − 2 characters and `alt`
    # interned it as an attribute name, an uncatchable `Size of symbol exceeds 4GiB` abort.
    test-parse-plus-family-keys-in-bounded-space = {
      expr = builtins.stringLength (r.stateKey (r.parse (plusNest 30)));
      expected = keyWidth;
    };
    # 624 nested groups are one level past the parser's call-depth boundary (623 returns).
    test-parse-deep-nesting-refuses-before-the-uncatchable-abort = {
      expr = (builtins.tryEval (r.stateKey (r.parse (nested 624)))).success;
      expected = false;
    };

    # ── the cap is a parameter a nested caller can lower ──
    test-parse-maxLength-is-a-parameter = {
      expr = (builtins.tryEval (r.stateKey (r.parseWith { maxLength = 500; } (rep 600 "a")))).success;
      expected = false;
    };

    # ── the key is injective on constructed terms, and exists only on them ──
    test-a-label-carrying-metacharacters-keys-apart-from-a-composite = {
      expr = r.stateKey (r.lit "a*") == r.stateKey (r.star (r.lit "a"));
      expected = false;
    };
    test-a-hand-built-term-is-refused-by-name = {
      expr =
        (builtins.tryEval (
          r.stateKey (
            r.star {
              t = "lit";
              l = "a";
            }
          )
        )).success;
      expected = false;
    };

    # ── a constructor-built term keys at any depth (den-hoag-regex-statekey-ceiling-4ok8y) ──
    # `chain n` nests n levels through the constructors, no parse, folded strictly. Each node's
    # key is forced when the node is built, so reading the root's key walks nothing: before
    # that, forcing it walked the chain and met the call-depth ceiling (near 2,500 levels under
    # a sha256 key, 3,333 under Lix; near 450 under a minted key), an abort tryEval cannot catch.
    test-a-constructor-chain-past-the-old-ceiling-keys = {
      expr = builtins.stringLength (r.stateKey (chain 5000)) == keyWidth;
      expected = true;
    };
    test-control-a-constructor-chain-below-the-old-ceiling-keys = {
      expr = builtins.stringLength (r.stateKey (chain 300)) == keyWidth;
      expected = true;
    };
    test-the-deep-chain-key-is-a-function-of-its-depth = {
      expr = r.stateKey (chain 5000) == r.stateKey (chain 4999);
      expected = false;
    };

    # ── deriv and nullable hold no depth ceiling on a constructor-built term ──
    test-deriv-of-a-deep-head-nesting-past-the-old-ceiling = {
      expr = r.stateKey (r.deriv "a" (head 5000)) == r.stateKey (headDeriv 5000);
      expected = true;
    };
    test-control-deriv-of-a-head-nesting-below-the-old-ceiling = {
      expr = r.stateKey (r.deriv "a" (head 300)) == r.stateKey (headDeriv 300);
      expected = true;
    };
    test-deriv-of-a-deep-head-nesting-rejects-an-absent-label = {
      expr = r.nullable (r.deriv "b" (head 5000));
      expected = false;
    };
    test-deriv-of-a-wide-nullable-seq-past-the-old-ceiling = {
      expr = [
        (r.nullable (r.deriv "a" (wide 2000)))
        (r.nullable (r.deriv "b" (wide 2000)))
      ];
      expected = [
        true
        false
      ];
    };
    test-nullable-of-a-deep-term-past-the-old-ceiling = {
      expr = [
        (r.nullable (altseq 5000))
        (r.nullable (r.deriv "b" (altseq 5000)))
      ];
      expected = [
        false
        true
      ];
    };
    # d_b (x* b c) = c, the unrolled seq sum stopping at its first non-nullable element: the
    # first term takes the direct arm (h 2), the second the warmed arm (h 82)
    test-deriv-of-a-seq-past-its-nullable-prefix = {
      expr = [
        (
          r.stateKey (
            r.deriv "b" (
              r.seq [
                (r.star (r.lit "a"))
                (r.lit "b")
                (r.lit "c")
              ]
            )
          ) == r.stateKey (r.lit "c")
        )
        (
          r.stateKey (
            r.deriv "b" (
              r.seq [
                (r.star (head 40))
                (r.lit "b")
                (r.lit "c")
              ]
            )
          ) == r.stateKey (r.lit "c")
        )
      ];
      expected = [
        true
        true
      ];
    };

    # ── deriv derives each shared subterm once ──
    test-deriv-of-a-shared-dag-matches-its-written-out-derivative = {
      expr = r.stateKey (r.deriv "a" (dag 12).x) == r.stateKey (dag 12).d;
      expected = true;
    };
    test-deriv-of-a-nested-plus-over-an-optional-derives-each-subterm-once = {
      expr = [
        (accepts (r.parse (optPlusNest 30)) [
          "a"
          "a"
        ])
        (accepts (r.parse (optPlusNest 30)) [ "c" ])
      ];
      expected = [
        true
        false
      ];
    };

    # ── a seq is a right-nested cons, and one step walks each suffix once ──
    # d_a (a?)^5 = (a?)^4 | (a?)^3 | (a?)^2 | a? | eps, written out by the constructors alone
    test-deriv-of-a-wide-optional-seq-matches-its-written-out-derivative = {
      expr = r.stateKey (r.deriv "a" (optSeq 5)) == r.stateKey (r.alt (builtins.genList optSeq 5));
      expected = true;
    };
    # a seq still publishes its elements flat as `rs`, which gen-view's `literalsOf` reads. The
    # reader below is a copy of gen-view `lib/carrier.nix` `literalsOf` at gen-view 7929a52; if
    # gen-view's changes, this cell keeps testing the copy.
    test-a-seq-publishes-its-elements-flat = {
      expr = [
        (builtins.length (lits 5000).rs)
        (builtins.length (literalsOf (lits 5000)))
      ];
      expected = [
        5000
        5000
      ];
    };
    test-a-seq-suffix-is-a-node = {
      expr =
        (r.seq [
          (r.lit "a")
          (r.lit "b")
          (r.lit "c")
        ]).tl.k or null == (r.seq [
          (r.lit "b")
          (r.lit "c")
        ]).k;
      expected = true;
    };
  };
}
