# THE DOORS (den-hoag-7gp66 P2 — `prelude.door`) — every published step taking a record catches its
# own violations.
#
# A native closed formal (`{ dataFilter, … }:`) aborts UNCATCHABLY on an unknown or a missing
# argument — not even `builtins.tryEval` sees it, which is ADR-0025 item 1's named defect. Every
# record step in `../doors.nix` is a `prelude.door`, so the same violations are NAMED and CATCHABLE.
# Each cell `seq`s the STEP applied to its argument and nothing else (no later argument, no field
# read), so a refusal is observed where the step is applied. Covered, per row:
#   - an OPTIONS step admits `{ }`, and refuses an unknown option and a non-attrset (G1/G4)
#   - a RECORD step admits its good record, refuses a missing field (D2) and a non-attrset, and
#     admits a field no step names (G2, R5's stated price; G10-ctl on the guarded rows)
#   - a record behind an options step refuses each of that step's own names (`optionsStep`, G10)
#   - every step publishes its row as its contract, read as data and through the functor-aware
#     reader (D3)
#   - a non-default option reaches the partially applied door and changes the answer (G3)
#
# `success == false` pins catchability, not the message; WHICH refusal fired, and that it names the
# door (R6), is pinned byte-for-byte in `ci/tests-error.nix`'s `door-checks` group.
{
  lib,
  genScope,
  genGraph,
  genPreludeLib,
  ...
}:
let
  S = genScope;
  F = import ../doors.nix { inherit genScope genGraph; };

  applied = step: r: (builtins.tryEval (builtins.seq (step r) true)).success;
  unknown = {
    unknownField = 1;
  };
  each = f: builtins.mapAttrs (_: f);
  flag = v: names: lib.genAttrs names (_: v);
  guarded = lib.filterAttrs (_: r: r ? guardedBy) F.records;

  # Every options door on the published surface, read off its `__contract` rather than a hand list,
  # so a new one is seen whether or not a row was written for it.
  # A retirement tombstone (`buildNodes`) is a published throw, so the walk takes the names that
  # evaluate.
  isDoor = v: builtins.isAttrs v && v ? __contract && v ? __functor;
  surface = builtins.filter (n: (builtins.tryEval (builtins.typeOf S.${n})).success) (
    builtins.attrNames S
  );
  surfaceOptionDoors = builtins.filter (
    n: isDoor S.${n} && !S.${n}.__contract.open && S.${n}.__contract.required == [ ]
  ) surface;
  surfaceRecordDoors = builtins.filter (n: isDoor S.${n} && S.${n}.__contract.open) surface;

  # G3: each row is the door's projection under a non-default option (`on`), under `{ }` (`off`),
  # and the direct full call under the same option (`full`). `agrees` is `on == full`; `differs` is
  # `on != off`. A door whose partial application is the call itself (no operand after the options)
  # still discriminates on `differs`, which is what an ignored option fails.
  inherit (F) ev attributes roots;
  val = n: n.decls.val or null;
  ids = n: [ n.id ];
  g3 = {
    buildRoots =
      let
        f = o: builtins.attrNames (S.buildRoots o).nodes;
      in
      {
        on = f { parentGraph = S.vertex "x"; };
        off = f { };
        full = builtins.attrNames (S.buildRoots { parentGraph = S.vertex "x"; }).nodes;
      };
    circular =
      let
        f =
          o:
          S.circular o (
            _: _: _:
            0
          );
      in
      {
        on = (f { carrier = "c"; }).carrier;
        off = (f { }).carrier;
        full =
          (S.circular { carrier = "c"; } (
            _: _: _:
            0
          )).carrier;
      };
    collect =
      let
        f = o: S.collect o (_: id: [ id ]);
        b = {
          filter = n: n.id == "b";
        };
      in
      {
        on = f b ev;
        off = f { } ev;
        full = S.collect b (_: id: [ id ]) ev;
      };
    collectionAttr =
      let
        f = o: S.collectionAttr o "imports" (_: id: id);
        c = {
          combine = _: _: [ "combined" ];
        };
      in
      {
        on = f c ev "a";
        off = f { } ev "a";
        full = S.collectionAttr c "imports" (_: id: id) ev "a";
      };
    eval =
      let
        f = o: S.eval o attributes;
        p = {
          provenance = [ "p" ];
        };
      in
      {
        on = (f p roots).provenance;
        off = (f { } roots).provenance;
        full = (S.eval p attributes roots).provenance;
      };
    evalWarm =
      let
        f = o: S.evalWarm o;
        p = {
          provenance = [ "p" ];
        };
      in
      {
        on = (f p F.warmRecord).provenance;
        off = (f { } F.warmRecord).provenance;
        full = (S.evalWarm p F.warmRecord).provenance;
      };
    foldEquations =
      let
        f = o: S.foldEquations o;
        s = {
          settings.s = 1;
        };
      in
      {
        on = (f s F.foldRecord).settings;
        off = (f { } F.foldRecord).settings;
        full = (S.foldEquations s F.foldRecord).settings;
      };
    inheritAll =
      let
        f = o: S.inheritAll o ids;
        c = {
          combine = _: acc: acc;
        };
      in
      {
        on = f c ev "a";
        off = f { } ev "a";
        full = S.inheritAll c ids ev "a";
      };
    inheritSet =
      let
        f = o: S.inheritSet o ids;
        e = {
          eq = _: _: true;
        };
      in
      {
        on = f e ev "a";
        off = f { } ev "a";
        full = S.inheritSet e ids ev "a";
      };
    mkKind =
      let
        f = o: S.mkKind o;
        b = {
          below = [ "x" ];
        };
      in
      {
        on = (f b "k").below;
        off = (f { } "k").below;
        full = (S.mkKind b "k").below;
      };
    mkRule =
      let
        f = o: S.mkRule o;
        p = {
          pos = [ "b" ];
        };
      in
      {
        on = (f p "a").pos;
        off = (f { } "a").pos;
        full = (S.mkRule p "a").pos;
      };
    queryReverse =
      let
        f = o: S.queryReverse o (n: n.id);
        t = {
          transitive = true;
        };
      in
      {
        on = f t ev "c";
        off = f { } ev "c";
        full = S.queryReverse t (n: n.id) ev "c";
      };
    # The calculus is not an options door (its `wf` and `dataFilter` are required), so it has no row
    # in the table; its non-default option is `mode = "visible"` with `neron.order`, which answers
    # the D < I < P selection the retired selector made: from `a` the import `b` shadows the parent
    # `root`, where the default `reachable` walk answers both.
    resolve =
      let
        f =
          o:
          (S.resolve (
            {
              inherit (S.neron) wf;
              dataFilter = val;
            }
            // o
          ) ev "a").answers;
        v = {
          mode = "visible";
          inherit (S.neron) order;
          groupBy = _: "val";
        };
      in
      {
        on = f v;
        off = f { };
        full =
          (S.resolve (
            S.neron
            // {
              mode = "visible";
              dataFilter = val;
              groupBy = _: "val";
            }
          ) ev "a").answers;
      };
    subtypeOf =
      let
        f = o: S.subtypeOf o;
        e = {
          eq =
            _: _: _:
            false;
        };
      in
      {
        on = f e ev "b" "c";
        off = f { } ev "b" "c";
        full = S.subtypeOf e ev "b" "c";
      };
  };
  # The options doors with no G3 row, each with its reason; G4 alone stands for them.
  #   evalDebug      its one option, `parseParent`, answers a node the scope does not register, and
  #                  the debug evaluator refuses materialization, so no projection of a registered
  #                  scope's result reads it.
  #   inherit'       it has no option: its walk is the calculus's (`parent*`, mode "visible"), and
  #                  the recursion state it once took as `_visited` retired with the recursion.
  #   resolveClaims  its one option, `ctx`, reaches only a kind's `resolve`, whose result record is
  #                  closed and carries no field a caller could set to it.
  noG3 = [
    "evalDebug"
    "inherit'"
    "resolveClaims"
  ];
in
{
  flake.tests.door-checks = {
    # ★ LIVE CONTROLS FOR THE WHOLE SUITE: `tryEval` catches an ordinary throw, and a non-throwing
    # value answers. Without these, a broken `applied` reading one constant satisfies half the cells.
    test-control-tryeval-catches-an-ordinary-throw = {
      expr = applied (_: throw "control probe, not this suite's subject") null;
      expected = false;
    };
    test-control-tryeval-answers-a-non-throwing-value = {
      expr = applied (x: x) 1;
      expected = true;
    };

    # The table is the surface: every door the surface publishes has a row, and every row is a door
    # the surface publishes. A door dropped from the table would drop its cells silently. The
    # guarded record rows are step two of a surface options door, so the surface does not list them.
    test-the-table-is-the-surface = {
      expr = {
        options = builtins.attrNames F.options;
        records = builtins.attrNames (builtins.removeAttrs F.records (builtins.attrNames guarded));
      };
      expected = {
        options = surfaceOptionDoors;
        records = surfaceRecordDoors;
      };
    };

    test-the-empty-options-are-admitted-at-every-options-step = {
      expr = builtins.mapAttrs (n: _: applied S.${n} { }) F.options;
      expected = each (_: true) F.options;
    };
    # G1/G4: refused when the options are applied, before any operand or record.
    test-an-unknown-option-is-refused-catchably-at-every-options-step = {
      expr = builtins.mapAttrs (n: _: applied S.${n} unknown) F.options;
      expected = each (_: false) F.options;
    };
    test-a-non-attrset-options-argument-is-refused-catchably = {
      expr = builtins.mapAttrs (n: _: applied S.${n} 1) F.options;
      expected = each (_: false) F.options;
    };
    # D3: the contract is published as data, and the functor-aware reader reads the same map.
    test-every-options-step-publishes-the-row-as-its-contract = {
      expr = builtins.mapAttrs (n: _: {
        inherit (S.${n}.__contract) optional required open;
        functionArgs = genPreludeLib.functionArgs S.${n};
      }) F.options;
      expected = each (d: {
        inherit (d) optional;
        required = [ ];
        open = false;
        functionArgs = flag true d.optional;
      }) F.options;
    };

    test-the-good-record-is-admitted-at-every-record-step = {
      expr = each (d: applied d.step d.good) F.records;
      expected = each (_: true) F.records;
    };
    # D2
    test-a-missing-field-is-refused-catchably = {
      expr = each (d: applied d.step (builtins.removeAttrs d.good [ d.drop ])) F.records;
      expected = each (_: false) F.records;
    };
    test-a-non-attrset-record-is-refused-catchably = {
      expr = each (d: applied d.step 1) F.records;
      expected = each (_: false) F.records;
    };
    # G2 / R5, and G10-ctl on the guarded rows: a field no step names is admitted.
    test-an-extra-field-is-admitted-at-every-record-step = {
      expr = each (d: applied d.step (d.good // unknown)) F.records;
      expected = each (_: true) F.records;
    };
    # G10: each of the options step's own names (from that step's `__contract`), given on the record
    # instead, is refused. The answer is the names ADMITTED.
    test-every-option-is-refused-at-every-guarded-record-step = {
      expr = each (
        d:
        builtins.filter (o: applied d.step (d.good // { ${o} = null; })) (
          S.${d.guardedBy}.__contract.optional
        )
      ) guarded;
      expected = each (_: [ ]) guarded;
    };
    # Every options door on the surface is classified: a chained one has a guarded record row, and
    # the rest are named as not chained. `surfaceOptionDoors` is the enumerator; the table cell above
    # pins it equal to the table's rows, so a walk that found nothing reds there.
    test-every-options-door-on-the-surface-is-classified = {
      expr = builtins.filter (n: !(guarded ? ${n}) && !(builtins.elem n F.notChained)) surfaceOptionDoors;
      expected = [ ];
    };
    test-every-record-step-publishes-the-row-as-its-contract = {
      expr = each (d: {
        inherit (d.step.__contract) required open;
        functionArgs = genPreludeLib.functionArgs d.step;
      }) F.records;
      expected = each (d: {
        inherit (d) required;
        open = true;
        functionArgs = flag false d.required;
      }) F.records;
    };

    # G3: a non-default option reaches the partially applied door (agrees with the full call) and
    # changes the answer (differs from `{ }`).
    test-a-non-default-option-reaches-the-partial-application = {
      expr = each (r: {
        agrees = r.on == r.full;
        differs = r.on != r.off;
      }) g3;
      expected = each (_: {
        agrees = true;
        differs = true;
      }) g3;
    };
    # Every options door has a G3 row or is named without one, and not both.
    test-every-options-door-has-a-g3-row-or-a-stated-reason = {
      expr = {
        uncovered = builtins.filter (n: !(g3 ? ${n}) && !(builtins.elem n noG3)) (
          builtins.attrNames F.options
        );
        both = builtins.filter (n: g3 ? ${n}) noG3;
      };
      expected = {
        uncovered = [ ];
        both = [ ];
      };
    };

    # The minting entry's emitter record, reached through the positional entry: every field
    # required, the set closed.
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
          mint = S.mintStrata { };
        in
        {
          valid = builtins.attrNames (mint [ emitter ]).nodes;
          missing = !(builtins.tryEval (mint [ (builtins.removeAttrs emitter [ "site" ]) ])).success;
          unknown = !(builtins.tryEval (mint [ (emitter // { "_${emitter.site}_" = 1; }) ])).success;
        };
      expected = {
        valid = [ "a" ];
        missing = true;
        unknown = true;
      };
    };
  };
}
