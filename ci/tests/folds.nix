# The fold vocabulary: what each fold is defined over, what it refuses when it is handed something
# else, and WHEN an aggregate is allowed to run at all.
#
# ★ THE REFUSAL CELLS HERE PIN REACHABILITY, NOT MESSAGES. `tryEval` reports that a refusal fired
# and discards what it said, so no cell in this file can tell one refusal from another. What each
# refusal SAYS is asserted in `../tests-error.nix`, where `expectedError` can read the text.
#
# ★★ AND THE REFUSAL CELLS HERE CANNOT SEE THE FAILURE THEY REPLACED. The preconditions replaced
# evaluator failures — `toJSON` on a value containing a function, `attrNames` on a function — and
# `tryEval` holds neither, so a cell asserting the OLD behaviour would end the runner rather than
# report it. That measurement is `../bench/folds-guard.sh`, which reads exit codes and runs the
# unguarded constructions as live controls beside the guarded ones. Two cells below reach the part
# of the old behaviour that IS observable from inside a suite — the input on which the unguarded
# comparison used to RETURN — and the split is stated so this file is not read as more than it is.
#
# ★★ WHAT THESE CELLS ASSERT IS THE PRECONDITION, AND NOT THAT SUCH FRAGMENTS ARE UNWRITABLE. A
# resolver may still return a function-bearing fragment; what changed is that a fold defined over
# comparable values now says so by name instead of ending the evaluation. Making such a fragment
# INEXPRESSIBLE is a different construction — plain-data conformance of what a resolver may hand
# back — and it is a change to the cascade's contract that is not made here. A cell reading as
# "function-valued fragments cannot exist" would be claiming that construction's property for a
# check an author can still omit.
#
# ── WHEN AN AGGREGATE MAY RUN ──
# The second suite is about the cascade rather than the vocabulary: a fold answers about the fact
# set it is handed, so what makes its answer mean anything is that the set was CLOSED when it ran.
# THEORY: Apt, Blair & Walker (1988), "Towards a Theory of Declarative Knowledge", in Minker (ed.),
# pp. 89–148 — the standard model is built stratum by stratum, `M_i = T_{P_i}↑ω(M_{i-1})` (printed
# p. 108), each stratum reaching its own fixed point before the next begins; that completeness, and
# not a restriction on what a stratum may read, is what aggregation demands of stratification
# (strictly-lower indexing is their rule for the NEGATIVE case, §"Stratified Programs", Definition 3,
# printed p. 96, and this cascade has no negation in it).
#
# The cells measure the difference that guarantee makes: the same fold, the same fixture, folded
# over the closed fact set and over the prefix of it that existed before the higher stratum
# contributed. If those two agreed, the guarantee would be buying nothing and the cells would be
# reporting a property no construction could violate.
{
  genScope,
  genPreludeLib,
  ...
}:
let
  inherit (genScope)
    mkKind
    mkKinds
    mkClaim
    resolveClaims
    folds
    ;

  didThrow = e: !(builtins.tryEval (builtins.deepSeq e null)).success;
  succeeds = e: (builtins.tryEval (builtins.deepSeq e null)).success;

  # The fold vocabulary takes contributor edges `[ { site; value; } ]`. These cells write their
  # fragments as a bare list and site them `s0`, `s1`, … in list order, so every pinned refusal
  # names the contributor by its position in the cell's own list.
  sited =
    vs:
    builtins.genList (i: {
      site = "s${toString i}";
      value = builtins.elemAt vs i;
    }) (builtins.length vs);

  # ── THE COMPARISON WITHOUT ITS PRECONDITION ──
  # Built here to be measured and never used: `same`'s comparison arm alone, which is the only part
  # of the unguarded construction the cells below reach. Its other arm — the mismatch diagnostic —
  # ends the evaluation on these inputs and is measured by the exit-code sweep instead.
  unguardedSame =
    key: vs:
    if builtins.all (v: v == builtins.head vs) vs then
      builtins.head vs
    else
      throw "unguarded.same: conflicting values for key '${key}'";

  # Two fragments carrying functions, as DISTINCT values: nothing is shared between two literals.
  fnA = {
    gen = _: "a";
  };
  fnB = {
    gen = _: "b";
  };
  # ONE fragment, listed twice — the same value slot on both sides of the comparison, which is the
  # only way `==` reports agreement between function-bearing values.
  shared =
    let
      v = {
        gen = _: "a";
      };
    in
    [
      v
      v
    ];
  # ── THE SCAN'S STOPPING RULE, AS THREE PAIRS THAT VARY BOTH OF ITS TERMS ──
  # The evaluator's shortcut is a CONJUNCTION — the derivation marker AND an `outPath` — so a
  # fixture set that holds either term fixed cannot observe the other, and would report a stopping
  # rule that admits fragments the comparison decides by their interiors. All three pairs below are
  # DISTINCT values carrying DIFFERENT functions inside, so nothing here can be explained by one
  # value slot being compared with itself:
  #
  #   drvA/drvA2      marker + path  ⇒ the evaluator agrees by path; the scan must NOT descend
  #   markerOnly1/2   marker, no path ⇒ compared field by field, and `toJSON` aborts on them
  #   bareA/bareA2    path, no marker ⇒ compared field by field
  #
  # The last two are the fragments the scan must ENTER, and each is a shape a stop written on one
  # term alone would have skipped.
  drvA = {
    type = "derivation";
    outPath = "/nix/store/aaaa";
    passthru = _: "one";
  };
  drvA2 = {
    type = "derivation";
    outPath = "/nix/store/aaaa";
    passthru = _: "two";
  };
  drvB = {
    type = "derivation";
    outPath = "/nix/store/bbbb";
    passthru = _: "three";
  };
  bareA = {
    outPath = "/nix/store/aaaa";
    passthru = _: "one";
  };
  bareA2 = {
    outPath = "/nix/store/aaaa";
    passthru = _: "two";
  };
  markerOnly1 = {
    type = "derivation";
    passthru = _: "one";
  };
  markerOnly2 = {
    type = "derivation";
    passthru = _: "two";
  };
  # A marker and an `outPath` that is not a STRING. Both readers need the path's VALUE: the
  # comparison compares the values, and the rendering coerces them. A function there is compared by
  # pointer and cannot be rendered at all.
  fnPath1 = {
    type = "derivation";
    outPath = _: "one";
    passthru = _: "one";
  };
  fnPath2 = {
    type = "derivation";
    outPath = _: "two";
    passthru = _: "two";
  };
  # ★ NO FUNCTION ANYWHERE IN THESE. A path compares perfectly well and cannot be REPORTED, so it is
  # refused on its own ground — and a fixture carrying a function beside the path would be refused
  # for the function instead, passing whatever the path term did. That is the shape these replaced.
  litPath1 = {
    type = "derivation";
    outPath = /x;
  };
  litPath2 = {
    type = "derivation";
    outPath = /y;
  };
  # The same hazard at a position no `outPath` rule reaches: no marker, no store path, no function.
  pathElsewhere1 = {
    a = /x;
  };
  pathElsewhere2 = {
    a = /y;
  };
  # The control for both: identical shape, the path replaced by a string. What is refused above is
  # the value's TYPE and not the shape it sits in.
  stringElsewhere1 = {
    a = "/x";
  };
  stringElsewhere2 = {
    a = "/x";
  };

  # Every fold in the vocabulary, in one list, so a key-type cell reports WHICH member regressed
  # rather than that something did.
  everyFold = [
    folds.same
    folds.one
    folds.list
    folds.mergeAttrs
    (folds.byKey { a = folds.same; })
  ];

  # ── THE TWO-STRATUM FIXTURE ──
  # `leaf` (depth 0) aggregates its fragments per group; `top` (depth 1) resolves earlier and emits
  # a claim INTO one of those groups. So the leaf stratum's fact set is not complete until the top
  # stratum has finished, and a fold that ran before it would be folding a prefix.
  aggKinds =
    {
      fold,
      group ? "g",
      tag ? "from-emission",
    }:
    mkKinds [
      (mkKind {
        dedupKey = c: c.group;
        foldFragments = fold;
        resolve = c: _: { resources.${c.group} = c.tag; };
      } "leaf")
      (mkKind {
        below = [ "leaf" ];
        resolve = c: _: {
          claims = [
            (mkClaim {
              kind = "leaf";
              inherit (c) subject;
              inherit group tag;
            })
          ];
        };
      } "top")
    ];

  subjA = {
    id_hash = "id-a";
    name = "a-subject";
  };
  subjB = {
    id_hash = "id-b";
    name = "b-subject";
  };

  leafRoot = mkClaim {
    kind = "leaf";
    subject = subjA;
    group = "g";
    tag = "from-intake";
  };
  topRoot = mkClaim {
    kind = "top";
    subject = subjB;
  };

  # The run as the cascade schedules it: the fold sees the leaf stratum's fact set CLOSED.
  closed =
    spec:
    resolveClaims { } (aggKinds spec) [
      leafRoot
      topRoot
    ];
  # The same fold over the same registry, folding the fact set as it stood BEFORE the higher
  # stratum contributed. Nothing about the fold changes — only when it is allowed to answer.
  early = spec: resolveClaims { } (aggKinds spec) [ leafRoot ];

  listSpec = {
    fold = folds.list;
  };
  # A variant whose emission lands in a DIFFERENT group: the later stratum still runs, still emits,
  # and contributes nothing to the group under test. Without this row the disagreement below reads
  # as "these two runs differ", which they would whatever the fold did.
  disjointSpec = {
    fold = folds.list;
    group = "h";
  };
  # The sharp form: under `same`, the prefix does not merely give a different answer — it gives a
  # confident one, and the conflict exists only once the fact set is complete.
  sameSpec = {
    fold = folds.same;
    tag = "from-emission";
  };

  # ── CONTRIBUTOR EDGES (den-hoag-bluqd) ──
  # A checker in gen-types' contract (`verify : value -> null | string`), written by shape: the
  # vocabulary reads `verify` and nothing else, and gen-scope takes no gen-types input.
  intChecker = {
    verify =
      v:
      if builtins.isInt v then
        null
      else
        "expected type 'int' but value ${builtins.toJSON v} is of type '${builtins.typeOf v}'";
  };
  # One dedup group of two `port` claims through the cascade, folded by `fold`.
  portRun =
    fold: ports:
    resolveClaims { }
      (mkKinds [
        (mkKind {
          dedupKey = _: "g";
          foldFragments = fold;
          resolve = c: _: { resources.port = c.port; };
        } "endpoint")
      ])
      (
        builtins.genList (
          i:
          mkClaim {
            kind = "endpoint";
            subject = {
              id_hash = "id-${toString i}";
              name = "s${toString i}";
            };
            port = builtins.elemAt ports i;
          }
        ) (builtins.length ports)
      );
in
{
  flake.tests.folds = {
    # ── THE MODULE IS A VALUE ALGEBRA, AND ITS ARGUMENT LIST IS THE EVIDENCE ──
    test-module-takes-the-prelude-and-nothing-else = {
      expr = builtins.attrNames (builtins.functionArgs (import ../../lib/folds.nix));
      expected = [ "prelude" ];
    };
    # The same predicate over a module that takes more, in the same run: without it, an empty or
    # constant answer would satisfy the cell above.
    #
    # ★ THE CASCADE NAMES THIS VOCABULARY NOWHERE: its only formal is the prelude. A kind's resource
    # fold arrives as a FIELD on the kind, so the algebra reaches a run as the author's data rather
    # than as an import, and a consumer assembling its own splice chooses the rule itself. The arm
    # is therefore the minting module, which takes more and does not take THIS.
    test-the-minting-module-takes-more = {
      expr = builtins.attrNames (builtins.functionArgs (import ../../lib/mint.nix));
      expected = [
        "graph"
        "hashIdentity"
        "prelude"
        "stratify"
      ];
    };

    # ── `same`: THE COMPARISON'S PRECONDITION ──
    test-same-refuses-a-function-bearing-fragment = {
      expr = didThrow (
        folds.same "k" (sited [
          fnA
          fnB
        ])
      );
      expected = true;
    };
    # The input the unguarded comparison ANSWERED, and the answer was the caller's value sharing
    # rather than anything about the fragments.
    test-same-refuses-one-value-slot-listed-twice = {
      expr = didThrow (folds.same "k" (sited shared));
      expected = true;
    };
    # LIVE CONTROL for the cell above, same run: without the precondition this input returns.
    test-the-unguarded-comparison-returns-on-the-pointer-accident = {
      expr = succeeds (unguardedSame "k" shared);
      expected = true;
    };
    test-the-unguarded-comparison-answers-with-the-shared-fragment = {
      expr = builtins.typeOf (unguardedSame "k" shared);
      expected = "set";
    };

    # ── AND IT REFUSES NOTHING ELSE ──
    test-same-returns-on-agreeing-plain-fragments = {
      expr = folds.same "k" (sited [
        { a = 1; }
        { a = 1; }
      ]);
      expected = {
        a = 1;
      };
    };
    # The conflict arm stays reachable behind the precondition: the guard dominates the diagnostic
    # for fragments it refuses, and leaves it in place for the fragments it admits.
    test-same-still-refuses-a-plain-conflict = {
      expr = didThrow (
        folds.same "k" (sited [
          1
          2
        ])
      );
      expected = true;
    };
    # ── WHERE THE SCAN STOPS, ON TWO DISTINCT VALUES RATHER THAN ONE COMPARED WITH ITSELF ──
    # Green only if BOTH halves hold: the scan did not descend into a marked derivation (or the
    # function inside would be refused), and the comparison agreed on two values whose interiors
    # differ (which only the evaluator's `outPath` rule can produce). A singleton fragment could
    # report neither — it agrees with itself by pointer identity whatever the rule is.
    test-two-derivations-with-one-store-path-agree = {
      expr =
        (folds.same "k" (sited [
          drvA
          drvA2
        ])).outPath;
      expected = "/nix/store/aaaa";
    };
    # ★ THE SAME PAIR WITHOUT THE MARKER IS REFUSED, because the evaluator's shortcut is narrower
    # than its rendering: an unmarked carrier is compared field by field, functions included. That
    # this cell and the one above disagree IS the stopping rule. Which refusal fires is asserted in
    # `../tests-error.nix` — a fold that let this pair through would ALSO throw here, reporting a
    # conflict between two fragments that render identically, so `didThrow` cannot tell them apart.
    test-a-store-path-without-the-derivation-marker-is-refused = {
      expr = didThrow (
        folds.same "k" (sited [
          bareA
          bareA2
        ])
      );
      expected = true;
    };
    # ★ THE MARKER WITHOUT A PATH IS THE OTHER HALF OF THE CONJUNCTION, and this cell is the one
    # that fails LOUDEST when the stop is written on one term: a stop testing the marker alone
    # skips these, hands them to a comparison their functions decide, and then to a `toJSON` that
    # ABORTS — so this cell does not go red, it takes the runner's cell down with it (radioactive). That is
    # the same uncatchable failure the fold's whole precondition exists to remove.
    test-a-derivation-marker-without-a-store-path-is-refused = {
      expr = didThrow (
        folds.same "k" (sited [
          markerOnly1
          markerOnly2
        ])
      );
      expected = true;
    };
    # ★ THE THIRD TERM: A PATH THAT IS NOT A STRING. Both readers want the path's VALUE, so a marker
    # and a present `outPath` are not enough — a function there is compared by pointer and cannot be
    # rendered. Skipping these is the abort again, so the scan enters them and refuses by name.
    test-a-store-path-that-is-not-a-string-is-refused = {
      expr = didThrow (
        folds.same "k" (sited [
          fnPath1
          fnPath2
        ])
      );
      expected = true;
    };
    # ── AND THE OTHER HALF OF THE PROPERTY: WHAT IS ADMITTED MUST BE REPORTABLE ──
    # A path passes the comparison and defeats the message. These fragments contain NO function, so
    # nothing but the path's own type can be refusing them.
    test-a-path-valued-store-path-is-refused = {
      expr = didThrow (
        folds.same "k" (sited [
          litPath1
          litPath2
        ])
      );
      expected = true;
    };
    # ★ AND AT A POSITION NO `outPath` RULE REACHES. No marker, no store path, no function: a rule
    # written about `outPath` would admit this pair and abort inside the conflict message.
    test-a-path-anywhere-in-a-fragment-is-refused = {
      expr = didThrow (
        folds.same "k" (sited [
          pathElsewhere1
          pathElsewhere2
        ])
      );
      expected = true;
    };
    # ★ THE COST, PINNED RATHER THAN DISCOVERED. Refusal is at admission, so it does not wait to see
    # whether the fragments agree — these two are the SAME path and are refused anyway. The fold
    # could have returned this, and the reason it does not is written at the construction: what it
    # cannot report, it does not accept.
    test-agreeing-path-fragments-are-refused-too = {
      expr = didThrow (
        folds.same "k" (sited [
          pathElsewhere1
          pathElsewhere1
        ])
      );
      expected = true;
    };
    # POSITIVE CONTROL for all three: the same shape with a STRING is folded, not refused. Without
    # it the rows above are equally satisfied by a fold that refuses this fragment shape outright.
    test-the-same-shape-with-a-string-is-folded = {
      expr = folds.same "k" (sited [
        stringElsewhere1
        stringElsewhere2
      ]);
      expected = {
        a = "/x";
      };
    };
    # Two marked derivations with DIFFERENT paths still conflict: where the scan stops decides what
    # is compared, not whether anything is.
    test-two-derivations-with-different-store-paths-conflict = {
      expr = didThrow (
        folds.same "k" (sited [
          drvA
          drvB
        ])
      );
      expected = true;
    };

    # ── THE KEY IS AN ARGUMENT THE VOCABULARY DECIDES, AT EVERY MEMBER ──
    test-every-fold-refuses-a-non-string-key = {
      expr = builtins.map (f: didThrow (f 42 (sited [ { a = 1; } ]))) everyFold;
      expected = [
        true
        true
        true
        true
        true
      ];
    };
    # CONTROL, same run, same folds, same fragments: with a string key every one of them returns.
    # Without it the row above is satisfied by a vocabulary that refuses this fragment list outright.
    test-every-fold-accepts-a-string-key = {
      expr = builtins.map (f: succeeds (f "k" (sited [ { a = 1; } ]))) everyFold;
      expected = [
        true
        true
        true
        true
        true
      ];
    };
    # The key is decided before the fragments are, so it is refused where the fragments would have
    # folded cleanly, where they would have conflicted, and where there are none at all.
    test-a-non-string-key-is-refused-where-the-fragments-would-conflict = {
      expr = didThrow (
        folds.same 42 (sited [
          1
          2
        ])
      );
      expected = true;
    };
    test-a-non-string-key-is-refused-on-an-empty-fragment-list = {
      expr = didThrow (folds.same 42 (sited [ ]));
      expected = true;
    };

    # ── THE FRAGMENT-SHAPE PRECONDITIONS ──
    test-mergeattrs-refuses-a-fragment-that-is-not-an-attribute-set = {
      expr = didThrow (
        folds.mergeAttrs "k" (sited [
          { a = 1; }
          (_: "not a fragment")
        ])
      );
      expected = true;
    };
    test-mergeattrs-returns-on-attribute-set-fragments = {
      expr = folds.mergeAttrs "k" (sited [
        { a = 1; }
        { b = 2; }
      ]);
      expected = {
        a = 1;
        b = 2;
      };
    };
    test-bykey-refuses-a-fragment-that-is-not-an-attribute-set = {
      expr = didThrow (folds.byKey { gen = folds.same; } "k" (sited [ (_: "not a fragment") ]));
      expected = true;
    };
    test-bykey-returns-on-attribute-set-fragments = {
      expr = folds.byKey { gen = folds.same; } "k" (sited [
        { gen = "hex"; }
        { gen = "hex"; }
      ]);
      expected = {
        gen = "hex";
      };
    };

    # ── CONTRIBUTOR EDGES: WHAT A FOLD IS HANDED (den-hoag-bluqd) ──
    # Every refusal's TEXT, the sited one, is pinned in `../tests-error.nix` `folds-refusals`.
    test-typed-is-in-the-vocabulary = {
      expr = folds ? typed;
      expected = true;
    };
    # A passing typed fold IS the fold it wraps, over the same edges.
    test-a-passing-typed-fold-equals-the-untyped-fold = {
      expr =
        let
          es = sited [
            22
            23
          ];
        in
        [
          (folds.typed intChecker folds.list "port" es)
          (folds.list "port" es)
        ];
      expected = [
        [
          22
          23
        ]
        [
          22
          23
        ]
      ];
    };
    # Two equal values from two contributors agree: the comparison is of the values, never of the
    # records that carry them.
    test-agreeing-values-from-different-sites-agree = {
      expr = folds.same "k" [
        {
          site = "a";
          value = 1;
        }
        {
          site = "b";
          value = 1;
        }
      ];
      expected = 1;
    };
    # The cascade hands a kind's fold the contributor edges, sited by claim path, in schedule order.
    test-the-cascade-sites-each-fragment-by-its-claim = {
      expr =
        (portRun (_: es: map (e: e.site) es) [
          22
          23
        ]).resources.endpoint.port;
      expected = [
        "claim at path [0]"
        "claim at path [1]"
      ];
    };
    # ★ AND THE RECORD IS THE VOCABULARY'S `{ site; value; }`, nothing of the run's own bookkeeping:
    # a fold reading another field would work here and abort at a wiring splice, which hands the
    # same record (`cascade-helpers`, `test-a-splice-combine-is-handed-site-and-value-only`).
    test-a-kind-fold-is-handed-site-and-value-only = {
      expr =
        (portRun (_: es: map builtins.attrNames es) [
          22
          23
        ]).resources.endpoint.port;
      expected = [
        [
          "site"
          "value"
        ]
        [
          "site"
          "value"
        ]
      ];
    };
    # The control the typed refusal (`folds-refusals`, `test-typed-at-the-cascade-names-the-claim`)
    # is read against, same fixture: untyped, the ill-typed fragment folds at rc 0.
    test-control-the-untyped-cascade-folds-the-ill-typed-fragment = {
      expr =
        (portRun folds.list [
          22
          "22"
        ]).resources.endpoint.port;
      expected = [
        22
        "22"
      ];
    };
    # ★ THE ENUMERATED RESIDUE AT THE DOOR (`lib/folds.nix`, the head): a bare-value list whose values
    # spell an edge is read as edges. Pinned so the residue stays a decision; any other bare value is
    # refused by name (`folds-refusals`, `test-a-bare-value-is-refused-at-the-door`).
    test-residue-bare-values-that-spell-an-edge-are-read-as-edges = {
      expr = folds.list "c" [
        {
          site = "x";
          value = 1;
        }
      ];
      expected = [ 1 ];
    };
  };

  # ── `set` AND `mergeAttrsDeep` (den-hoag-izo7a) ──
  # The two `==`-collapsing folds. Each collapse is a quotient (den-hoag-kunjm): the kept value
  # carries its twins' store contexts, so the context cells count the paths the kept value carries,
  # against `unique`'s own count on the same twins as the control. Every refusal's TEXT is pinned in
  # `../tests-error.nix` `folds-refusals`; the cells here pin that each is reached.
  flake.tests.folds-quotient =
    let
      # Two strings `==`-equal ("x") carrying different store contexts.
      ca = "${builtins.substring 0 0 (toString (builtins.toFile "izo7a-ctx-a" "a"))}x";
      cb = "${builtins.substring 0 0 (toString (builtins.toFile "izo7a-ctx-b" "b"))}x";
      ctxN = s: builtins.length (builtins.attrNames (builtins.getContext s));
      deep = vs: folds.mergeAttrsDeep "k" (sited vs);
      fleet = [
        {
          nixosConfigurations.h1 = "sys1";
          deploy.nodes.h1.hostname = "a";
          colmena.h1 = "c1";
        }
        {
          nixosConfigurations.h2 = "sys2";
          deploy.nodes.h2.hostname = "b";
          colmena.h2 = "c2";
        }
        { deploy.nodes.h1.hostname = "a"; }
      ];
      at = builtins.elemAt fleet;
      reversed = [
        (at 2)
        (at 1)
        (at 0)
      ];
      mkIf = condition: content: {
        _type = "if";
        inherit condition content;
      };
    in
    {
      test-set-is-in-the-vocabulary = {
        expr = folds ? set && folds ? mergeAttrsDeep;
        expected = true;
      };
      test-set-keeps-first-occurrences-in-pinned-order = {
        expr = folds.set "k" (sited [
          "b"
          "a"
          "b"
          "c"
          "a"
        ]);
        expected = [
          "b"
          "a"
          "c"
        ];
      };
      test-set-dedups-non-strings-in-the-same-order = {
        expr = folds.set "k" (sited [
          1
          "a"
          { x = 1; }
          1
          "a"
          { x = 1; }
          [ 2 ]
        ]);
        expected = [
          1
          "a"
          { x = 1; }
          [ 2 ]
        ];
      };
      test-set-of-a-singleton-is-the-singleton = {
        expr = folds.set "k" (sited [ "a" ]);
        expected = [ "a" ];
      };
      test-set-is-idempotent = {
        expr =
          let
            vs = [
              "b"
              1
              "a"
              1
              { y = 2; }
              "b"
            ];
          in
          folds.set "k" (sited (folds.set "k" (sited vs) ++ vs)) == folds.set "k" (sited vs);
        expected = true;
      };
      test-set-carries-both-twins-contexts = {
        expr = map ctxN (
          folds.set "k" (sited [
            ca
            cb
          ])
        );
        expected = [ 2 ];
      };
      # The control: `unique` on the same twins keeps one context, so the count above is the fold's.
      test-control-unique-keeps-one-context = {
        expr = map ctxN (
          genPreludeLib.unique [
            ca
            cb
          ]
        );
        expected = [ 1 ];
      };
      test-mergeAttrs-refuses-the-fleet = {
        expr = didThrow (folds.mergeAttrs "k" (sited fleet));
        expected = true;
      };
      test-mergeAttrsDeep-joins-the-fleet = {
        expr = deep fleet;
        expected = {
          colmena = {
            h1 = "c1";
            h2 = "c2";
          };
          deploy.nodes = {
            h1.hostname = "a";
            h2.hostname = "b";
          };
          nixosConfigurations = {
            h1 = "sys1";
            h2 = "sys2";
          };
        };
      };
      test-mergeAttrsDeep-leaves-a-one-sided-subtree-unforced = {
        expr = builtins.attrNames (deep [
          { a.x = throw "never forced"; }
          { b = 1; }
        ]);
        expected = [
          "a"
          "b"
        ];
      };
      test-mergeAttrsDeep-leaf-carries-both-twins-contexts = {
        expr =
          ctxN
            (deep [
              { a = ca; }
              { a = cb; }
            ]).a;
        expected = 2;
      };
      test-mergeAttrsDeep-is-bracketing-and-order-invariant = {
        expr =
          deep [
            (deep [
              (at 0)
              (at 1)
            ])
            (at 2)
          ] == deep fleet
          && deep reversed == deep fleet;
        expected = true;
      };
      # A `_type`-tagged set is a LEAF (den-hoag-izo7a OQ-2): two equal ones collapse as leaves, and
      # one beside an untagged namespace sharing a field name is refused, never read as a namespace.
      test-mergeAttrsDeep-collapses-equal-tagged-leaves = {
        expr = deep [
          { a = mkIf true { x = 1; }; }
          { a = mkIf true { x = 1; }; }
        ];
        expected = {
          a = mkIf true { x = 1; };
        };
      };
      test-mergeAttrsDeep-refuses-a-tagged-leaf-beside-a-namespace = {
        expr = didThrow (deep [
          { a = mkIf true { x = 1; }; }
          { a.content.y = 2; }
        ]);
        expected = true;
      };
      test-mergeAttrsDeep-refuses-two-unequal-tagged-leaves = {
        expr = didThrow (deep [
          { a = mkIf true { x = 1; }; }
          { a = mkIf false { y = 2; }; }
        ]);
        expected = true;
      };
      test-refusals-are-reached = {
        expr = map didThrow [
          (folds.set 1 (sited [ ]))
          (folds.set "k" (sited [ { f = _: 1; } ]))
          (folds.set "k" (sited [ { p = ./folds.nix; } ]))
          (folds.set "k" (sited [
            [ (builtins.unsafeDiscardStringContext ca) ]
            [ ca ]
          ]))
          (folds.mergeAttrsDeep 1 (sited [ ]))
          (deep [
            { }
            1
          ])
          (deep [
            { deploy.nodes.h1.hostname = "a"; }
            { deploy.nodes.h1.hostname = "b"; }
          ])
          (deep [
            { a = _: 1; }
            { a = _: 1; }
          ])
          (deep [
            { a.x = 1; }
            { a = 2; }
          ])
          (deep [
            { a = [ (builtins.unsafeDiscardStringContext ca) ]; }
            { a = [ ca ]; }
          ])
        ];
        expected = [
          true
          true
          true
          true
          true
          true
          true
          true
          true
          true
        ];
      };
    };

  # ── STRATUM-LOCAL AGGREGATION: THE FOLD RUNS ON A CLOSED FACT SET ──
  flake.tests.stratum-aggregation = {
    # The fold's contributors span BOTH strata: the intake claim and the one the higher stratum
    # emitted, in schedule order.
    test-fold-sees-the-later-emission = {
      expr = (closed listSpec).resources.leaf.g;
      expected = [
        "from-intake"
        "from-emission"
      ];
    };
    # And the second contributor really is a child of the higher stratum's claim — a path of
    # `[1 0]` is an emission of the claim at intake index 1, not something present at intake.
    test-the-second-contributor-is-an-emission = {
      expr = (closed listSpec).trace.resources.leaf.g.claims;
      expected = [
        [ 0 ]
        [
          1
          0
        ]
      ];
    };

    # ── THE EARLY-FOLD VARIANT, AND IT MUST DISAGREE ──
    test-the-early-fold-answers-about-the-prefix = {
      expr = (early listSpec).resources.leaf.g;
      expected = [ "from-intake" ];
    };
    test-the-early-fold-disagrees-with-the-complete-fact-set = {
      expr = (early listSpec).resources.leaf.g != (closed listSpec).resources.leaf.g;
      expected = true;
    };
    # The other direction, so the disagreement is attributable to the emission and not to the
    # variant: when the later stratum contributes to a different group, the two agree.
    test-the-early-fold-agrees-when-the-later-stratum-contributes-elsewhere = {
      expr = (early disjointSpec).resources.leaf.g == (closed disjointSpec).resources.leaf.g;
      expected = true;
    };

    # ── AND THE PREFIX ANSWER IS NOT MERELY DIFFERENT ──
    # Under `same`, folding the prefix RETURNS: one fragment, no disagreement to find. The conflict
    # is a fact about the complete set, and only the complete set can report it.
    test-the-early-fold-returns-where-the-complete-set-refuses = {
      expr = succeeds (early sameSpec).resources.leaf.g;
      expected = true;
    };
    test-the-complete-fact-set-refuses-the-conflict = {
      expr = didThrow (closed sameSpec).resources.leaf.g;
      expected = true;
    };
  };
}
