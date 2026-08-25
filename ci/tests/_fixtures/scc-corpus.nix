# THE SHARED-ROUND FIXTURE CORPUS — the tracked model of record's forty programs, ported onto the
# REAL evaluator.
#
# NOT A SUITE. It sits under `_fixtures/` because the tree importer ignores any path containing
# `/_`, so this file is reached only by the suites that import it and never as a flake module.
#
# PROVENANCE. Each fixture is a port of the correspondingly named program in the migration spec's
# tracked executable model (den-ag-design `specs/2026-08-22-gen-scc-admission-model/m49/fixtures.py`,
# forty fixtures), and the expected verdicts asserted over them in `tests/scc-round.nix` and
# `tests-error.nix` are that model's HAND-DERIVED expectations (`r28/HAND-DERIVED-r28.md`, the
# default column) — derived before any cell here ran, not read off this implementation. The
# blind-spot family (UNDEMERR and its two controls) is deliberately included: the pre-round-28
# tracked suite was measured blind to the demand-cone/undemanded-forcing class, and porting the
# corpus without those cells would re-import the blind spot. The LATEREAD family is the ONE
# exception to the port provenance — not among the forty — and says so where it stands.
#
# ENCODING. The model's programs declare every attribute circular on one node `n`; a member read
# `a.get("n.x")` and a quotient read `a.getq("n.x")` both port to `self.get "n" "x"` — the real
# evaluator dispatches on the declaration's own `quotient` term, which is the construction the
# model's split accessor was standing in for. Carriers port term for term; the two-element order
# is EXACTLY {0 < 1} (not `<=` on the integers, whose height would be unbounded and make the
# declared height a lie rather than the truth under test).
{ genScope }:
let
  # Carrier vocabulary, mirroring the model's `num` / `q` / `TWO` / the subset order.
  num = bottom: height: {
    inherit bottom height;
    leq = a: b: a <= b;
    quotient = false;
  };
  qnum = bottom: height: {
    inherit bottom height;
    leq = a: b: a <= b;
    quotient = true;
  };
  two = height: {
    bottom = 0;
    inherit height;
    leq = x: y: (x == 0 && (y == 0 || y == 1)) || (x == 1 && y == 1);
    quotient = false;
  };
  sub = x: y: builtins.all (e: builtins.elem e y) x;
  subCarrier = height: {
    bottom = [ ];
    inherit height;
    leq = sub;
    quotient = false;
  };
  inherit (genScope) circular;

  # One node, every attribute a circular declaration, the demand at the named target.
  scope = genScope.buildRoots {
    parentGraph = genScope.vertex "n";
    importGraph = genScope.empty;
    decls.n = { };
    types = { };
  };
  run =
    attrs: target:
    (genScope.eval {
      inherit scope;
      attributes = {
        children = _self: _id: { };
        imports = _self: _id: [ ];
      }
      // attrs;
    }).get
      "n"
      target;

  # The shared driver `n.c`: caps at 4 over a height-4 chain.
  drv = circular { carrier = num 0 4; } (
    self: _id: _prev:
    let
      c = self.get "n" "c";
    in
    if c >= 4 then 4 else c + 1
  );

  # ── UNEVALXC family — the hybrid-only declaration's VALUE axis, and its member twin ──
  unevalxc =
    zr: udir:
    {
      c = drv;
      m = circular { carrier = num 0 3; } (
        self: _id: _prev:
        if self.get "n" "c" <= 2 then (self.get "n" "q") + (self.get "n" "zr") else 2
      );
      q = circular { carrier = qnum 0 4; } (
        self: _id: _prev:
        {
          "0" = 0;
          "1" = 4;
          "2" = 6;
        }
        .${toString (self.get "n" "c")} or 0
      );
      zr = circular { carrier = qnum 0 4; } (
        self: _id: _prev:
        if self.get "n" "c" >= 3 then zr else 0
      );
    }
    // (
      if udir == null then
        { }
      else
        {
          uq = circular { carrier = qnum 0 8; } (
            self: _id: _prev:
            let
              c = self.get "n" "c";
            in
            if udir == "desc" then
              (if c <= 1 then 8 else 5)
            else if udir == "asc" then
              (if c <= 1 then 5 else 8)
            else
              5
          );
          u = circular { carrier = num 0 2; } (
            self: _id: _prev:
            self.get "n" "uq"
          );
        }
    );

  # ── LAZYI / H5 / H10B — the demand-shift and clamp families ──
  lazyi = {
    c = drv;
    m = circular { carrier = num 0 4; } (
      self: _id: _prev:
      self.get "n" "mq"
    );
    m2 = circular { carrier = num 0 4; } (
      self: _id: _prev:
      if self.get "n" "lq" == 1 then self.get "n" "m" else 3
    );
    lq = circular { carrier = qnum 0 4; } (
      self: _id: _prev:
      if self.get "n" "c" >= 4 then 1 else 0
    );
    mq = circular { carrier = qnum 0 4; } (
      self: _id: _prev:
      if self.get "n" "c" == 2 then 4 else 2
    );
  };

  q5decl = circular { carrier = qnum 0 8; } (
    self: _id: _prev:
    let
      c = self.get "n" "c";
    in
    if c <= 1 then
      0
    else if c == 2 then
      8
    else
      5
  );

  h5 = {
    c = drv;
    m = circular { carrier = num 0 4; } (
      self: _id: _prev:
      self.get "n" "q5"
    );
    m2 = circular { carrier = num 0 4; } (
      self: _id: _prev:
      self.get "n" "m"
    );
    q5 = q5decl;
  };

  h10b = {
    c = drv;
    m = circular { carrier = num 0 4; } (
      self: _id: _prev:
      self.get "n" "q5"
    );
    m2 = circular { carrier = num 0 4; } (
      self: _id: _prev:
      if self.get "n" "m" < 6 then 9 else self.get "n" "m"
    );
    q5 = circular { carrier = qnum 0 8; } (
      self: _id: _prev:
      let
        c = self.get "n" "c";
      in
      if c <= 1 then
        0
      else if c == 2 then
        8
      else
        0
    );
  };

  # H2 — A24's specimen: an antitone quotient behind a member, answered not refused.
  h2 = {
    c = drv;
    m = circular { carrier = num 0 8; } (
      self: _id: _prev:
      self.get "n" "qa"
    );
    qa = q5decl;
  };

  # ── H8b / H8c — the height row: a genuine chain of three against a declared height of one ──
  h8Step =
    self: _id: _prev:
    let
      m = self.get "n" "m";
    in
    if m + 2 >= 6 then 6 else m + 2;
  h8b = {
    c = drv;
    m = circular { carrier = num 0 1; } h8Step;
    qh = circular { carrier = qnum 0 4; } (
      _self: _id: _prev:
      1
    );
  };
  h8c = {
    c = drv;
    m = circular { carrier = num 0 1; } h8Step;
  };

  # ── UNSHOW / NONREFL / FLIP — the clamp fallback's neutrality axis ──
  unshow = mode: {
    c = drv;
    w = circular { carrier = subCarrier 4; } (
      self: _id: _prev:
      self.get "n" "wq"
    );
    m = circular { carrier = num 0 4; } (
      self: _id: _prev:
      let
        w = self.get "n" "w";
      in
      if self.get "n" "c" > 2 then
        2
      else if w == [ ] then
        7
      else if w == [ "a" ] then
        9
      else
        2
    );
    wq =
      circular
        {
          carrier = (qnum 0 4) // {
            bottom = [ ];
          };
        }
        (
          self: _id: _prev:
          let
            c = self.get "n" "c";
            hi =
              if mode == "inc" then
                [ "b" ]
              else
                [
                  "a"
                  "b"
                ];
          in
          if c <= 0 then
            [ ]
          else if c <= 1 then
            [ "a" ]
          else
            hi
        );
  };

  nonrefl = {
    c = drv;
    m = circular { carrier = num 0 4; } (
      self: _id: _prev:
      self.get "n" "q5"
    );
    m2 =
      circular
        {
          carrier = {
            bottom = 0;
            leq = a: b: a < b;
            height = 4;
            quotient = false;
          };
        }
        (
          self: _id: _prev:
          self.get "n" "m"
        );
    q5 = q5decl;
  };

  flip = ordered: {
    c = drv;
    w = circular { carrier = subCarrier 4; } (
      self: _id: _prev:
      self.get "n" "wq"
    );
    m = circular { carrier = num 0 4; } (
      self: _id: _prev:
      if self.get "n" "c" > 2 then
        self.get "n" "mq"
      else
        self.get "n" "mq2" + (if self.get "n" "w" == [ "b" ] then 9 else 0)
    );
    wq =
      circular
        {
          carrier = (qnum 0 4) // {
            bottom = [ ];
          };
        }
        (
          self: _id: _prev:
          let
            c = self.get "n" "c";
          in
          if ordered then
            (if c <= 1 then [ ] else [ "b" ])
          else if c <= 0 then
            [ ]
          else if c <= 1 then
            [ "a" ]
          else
            [ "b" ]
        );
    mq = circular { carrier = qnum 0 4; } (
      self: _id: _prev:
      if self.get "n" "c" <= 2 then 9 else 2
    );
    mq2 = circular { carrier = qnum 0 4; } (
      self: _id: _prev:
      if self.get "n" "c" <= 2 then 5 else 0
    );
  };

  # ── TWIN family — the presence and order axes of an unread declaration ──
  twinBase = {
    b = circular { carrier = num 0 1; } (
      self: _id: _prev:
      let
        b = self.get "n" "b";
      in
      if b >= 1 then 1 else b + 1
    );
    t = circular { carrier = num 0 8; } (
      self: _id: _prev:
      if self.get "n" "b" == 0 then 8 else 5
    );
  };
  twin = twinBase;
  twinP = twinBase // {
    zq = circular { carrier = qnum 0 4; } (
      _self: _id: _prev:
      5
    );
  };
  twin2 = twinBase // {
    zq = circular { carrier = qnum 0 4; } (
      self: _id: _prev:
      if self.get "n" "b" == 0 then 8 else 5
    );
  };

  ctlValue = {
    v = circular { carrier = num 0 2; } (
      _self: _id: _prev:
      7
    );
  };
  ctlRefusal = {
    c = drv;
    m = circular { carrier = num 0 4; } (
      self: _id: _prev:
      if self.get "n" "c" <= 2 then 9 else 2
    );
  };

  # LIAR — a coarse `leq` declared `quotient = false`: the bound seat is the residue's detector.
  liar = {
    k =
      circular
        {
          carrier = {
            bottom = 1;
            leq = _x: _y: true;
            height = 2;
            quotient = false;
          };
        }
        (
          self: _id: _prev:
          if self.get "n" "k" == 1 then 2 else 1
        );
    b = circular { carrier = num 0 2; } (
      self: _id: _prev:
      let
        b = self.get "n" "b";
      in
      if b + 1 >= 2 then 2 else b + 1
    );
  };

  # CLAMPLAZY — an unread descending pair beside UNEVALXC: the clamp is entrywise.
  clamplazy = unevalxc 9 null // {
    xq = circular { carrier = qnum 0 4; } (
      self: _id: _prev:
      if self.get "n" "c" <= 1 then 8 else 5
    );
    x = circular { carrier = num 0 2; } (
      self: _id: _prev:
      self.get "n" "xq"
    );
  };

  # QSPLIT — one accessor serving two values for one member, by route.
  qsplit = {
    c = drv;
    u = circular { carrier = num 0 2; } (
      self: _id: _prev:
      let
        u = self.get "n" "u";
      in
      if u + 1 >= 2 then 2 else u + 1
    );
    m = circular { carrier = num 0 6; } (
      self: _id: _prev:
      if self.get "n" "c" >= 4 then 2 else (self.get "n" "u") * 10 + self.get "n" "qu"
    );
    qu = circular { carrier = qnum 0 4; } (
      self: _id: _prev:
      self.get "n" "u"
    );
  };

  # ── HOSC family — the height cap counts a RUN, not a tally ──
  zRamp = circular { carrier = num 0 2; } (
    self: _id: _prev:
    let
      z = self.get "n" "z";
    in
    if z + 1 >= 2 then 2 else z + 1
  );
  hoscWith = mheight: oscStep: {
    z = zRamp;
    m = circular { carrier = two mheight; } (
      self: _id: _prev:
      self.get "n" "osc"
    );
    osc = circular { carrier = qnum 0 4; } oscStep;
  };
  hosc = hoscWith 1 (
    self: _id: _prev:
    if self.get "n" "z" >= 2 then 1 else 1 - self.get "n" "m"
  );
  hoscH2 = hoscWith 2 (
    self: _id: _prev:
    if self.get "n" "z" >= 2 then 1 else 1 - self.get "n" "m"
  );
  hoscNoosc = hoscWith 1 (
    self: _id: _prev:
    if self.get "n" "z" >= 2 then 1 else 0
  );
  hoscOnedesc = hoscWith 1 (
    self: _id: _prev:
    if self.get "n" "z" >= 2 then 0 else 1 - self.get "n" "m"
  );

  # BOUNDPLATEAU — the attempted silent arm: over-declared height, caught at the bound.
  boundplateau = {
    z = zRamp;
    m = circular { carrier = two 6; } (
      self: _id: _prev:
      self.get "n" "osc"
    );
    a = circular { carrier = two 6; } (
      self: _id: _prev:
      self.get "n" "m"
    );
    osc = circular { carrier = qnum 0 4; } (
      self: _id: _prev:
      if self.get "n" "z" >= 8 then 1 else 1 - self.get "n" "m"
    );
  };

  # ── TRIPLE — closure join + height cap + clamp, all three live in one program ──
  tripleWith = mheight: {
    c = drv;
    uq = circular { carrier = qnum 0 4; } (
      self: _id: _prev:
      if self.get "n" "c" <= 1 then 8 else 5
    );
    u = circular { carrier = num 0 1; } (
      self: _id: _prev:
      self.get "n" "uq"
    );
    m = circular { carrier = num 0 mheight; } h8Step;
    k = circular { carrier = num 0 4; } (
      self: _id: _prev:
      self.get "n" "q" + (if self.get "n" "u" >= 0 then 0 else 1) + 0 * self.get "n" "m"
    );
    q = circular { carrier = qnum 0 4; } (
      self: _id: _prev:
      self.get "n" "r"
    );
    r = circular { carrier = qnum 0 4; } (
      self: _id: _prev:
      self.get "n" "q"
    );
  };
  triple = tripleWith 1;
  tripleHonest = tripleWith 3;
  tripleNoq =
    builtins.removeAttrs (tripleWith 1) [
      "q"
      "r"
    ]
    // {
      k = circular { carrier = num 0 4; } (
        self: _id: _prev:
        (if self.get "n" "u" >= 0 then 0 else 1) + 0 * self.get "n" "m"
      );
    };

  # ── THE BOUND FAMILY (round 27) ──
  boundfam = h: zh: oscAlways: {
    z = circular { carrier = num 0 zh; } (
      self: _id: _prev:
      let
        z = self.get "n" "z";
        inc = if self.get "n" "osc" == 1 then 1 else 0;
      in
      if z + inc >= h then h else z + inc
    );
    m = circular { carrier = two 1; } (
      self: _id: _prev:
      self.get "n" "osc"
    );
    osc = circular { carrier = qnum 0 4; } (
      self: _id: _prev:
      if oscAlways || self.get "n" "z" >= h then 1 else 1 - self.get "n" "m"
    );
  };
  boundT =
    h: fam:
    fam
    // {
      t = circular { carrier = two 1; } (
        self: _id: _prev:
        if self.get "n" "z" >= h then 1 else 0
      );
    };
  boundshort = boundfam 3 3 false;
  boundquiet = boundT 4 (boundfam 4 4 false);
  boundquietNoosc = boundT 4 (boundfam 4 4 true);
  boundquietFath = boundT 4 (boundfam 4 8 false);

  # WIDEFLAT — a self-driven non-ascending walk on a wide flat carrier, no quotient anywhere.
  wideflat = {
    w =
      circular
        {
          carrier = {
            bottom = 0;
            leq = x: y: x == y || x == 0 || y == 9;
            height = 2;
            quotient = false;
          };
        }
        (
          self: _id: _prev:
          {
            "0" = 1;
            "1" = 2;
            "2" = 3;
            "3" = 4;
            "4" = 9;
            "9" = 9;
          }
          .${toString (self.get "n" "w")}
        );
  };

  # ── THE BLIND-SPOT FAMILY (round 28, C26-1) ──
  # UNDEMERR must LIVE under the cone-scoped settlement and its erroring member must NEVER be
  # forced — the cell is self-witnessing, because forcing `n.e` is an unnamable division-by-zero
  # death. UNDEMOK keys on the ERROR; DEMERR keys on UNDEMANDEDNESS.
  undem = err: demanded: {
    t = circular { carrier = num 0 2; } (
      self: _id: _prev:
      let
        t = self.get "n" "t";
        v = if t + 1 >= 2 then 2 else t + 1;
      in
      if demanded then v + 0 * self.get "n" "e" else v
    );
    e = circular { carrier = num 0 2; } (
      _self: _id: _prev:
      if err then 1 / 0 else 1
    );
  };
  undemerr = undem true false;
  undemok = undem false false;
  demerr = undem true true;

  # ── THE LATEREAD FAMILY — the LAZYI × UNDEMERR crossing the forty lack ──
  # Not among the model's forty programs: these are the exec gate's differential probes, kept
  # because no ported fixture crosses a DEMAND-GAPPED member with an UNDEMANDED EARLY LEVEL that
  # errors. The model of record answers 3 on every arm (its force-gated height counter never
  # reads an unforced pair); a counter computed over a demanded member's WHOLE raw column dies on
  # `b`'s level-1 entry (LATEREAD) and transitively runs the never-demanded `c`'s step
  # (LATEREAD2) — the undemanded-forcing class the bound's cone rule excludes, reintroduced at
  # the height seat. Expectations hand-derived before any cell ran: `a` self-ascends 0→1→2→3 and
  # reads `b` only from level 4 on, `b` mirrors `a`'s settled 3, nothing moves at the bound.
  lateReadTarget = circular { carrier = num 0 5; } (
    self: _id: _prev:
    let
      av = self.get "n" "a";
    in
    if av < 3 then
      av + 1
    else
      let
        bv = self.get "n" "b";
      in
      if bv > av then bv else av
  );
  lateread = {
    a = lateReadTarget;
    b = circular { carrier = num 0 5; } (
      self: _id: _prev:
      let
        av = self.get "n" "a";
      in
      if av == 0 then 1 / 0 else av
    );
  };
  latereadCtl = {
    a = lateReadTarget;
    b = circular { carrier = num 0 5; } (
      self: _id: _prev:
      let
        av = self.get "n" "a";
      in
      if av == 0 then 0 else av
    );
  };
  lateread2 = {
    a = lateReadTarget;
    b = circular { carrier = num 0 5; } (
      self: _id: _prev:
      let
        av = self.get "n" "a";
      in
      if av < 2 then self.get "n" "c" else av
    );
    c = circular { carrier = num 0 5; } (
      _self: _id: _prev:
      1 / 0
    );
  };

  # ── A11a — the saturating ratchet: the composed bound is Σhᵢ + 1, never max(hᵢ) + 1 ──
  # Two members over subsets of {1,2,3}, each of declared height 3, ascending in ALTERNATION:
  # six strictly ascending levels saturate Σhᵢ = 6 and the seventh observes the fixed point.
  # Under max(hᵢ) + 1 = 4 the round would stop two ascents short of the least fixed point.
  ratchetStep =
    other: gate: self: _id: _prev:
    let
      mine = self.get "n" (if other == "b" then "a" else "b");
      theirs = self.get "n" other;
      n = builtins.length mine;
    in
    if n < 3 && gate n (builtins.length theirs) then mine ++ [ (n + 1) ] else mine;
  ratchet = {
    a = circular { carrier = subCarrier 3; } (ratchetStep "b" (m: t: m <= t));
    b = circular { carrier = subCarrier 3; } (ratchetStep "a" (m: t: m < t));
  };
  # Every fixture as { attrs; out; }, keyed by the model's own names.
  fixtures = {
    "UNEVALXC-ZR9" = {
      attrs = unevalxc 9 null;
      out = "m";
    };
    "UNEVALXC-ZR0" = {
      attrs = unevalxc 0 null;
      out = "m";
    };
    UDESC = {
      attrs = unevalxc 9 "desc";
      out = "m";
    };
    UASC = {
      attrs = unevalxc 9 "asc";
      out = "m";
    };
    UFLAT = {
      attrs = unevalxc 9 "flat";
      out = "m";
    };
    LAZYI = {
      attrs = lazyi;
      out = "m2";
    };
    H5 = {
      attrs = h5;
      out = "m2";
    };
    H10B = {
      attrs = h10b;
      out = "m2";
    };
    H2 = {
      attrs = h2;
      out = "m";
    };
    H8B = {
      attrs = h8b;
      out = "m";
    };
    H8C = {
      attrs = h8c;
      out = "m";
    };
    UNSHOWINC = {
      attrs = unshow "inc";
      out = "m";
    };
    UNSHOWORD = {
      attrs = unshow "ord";
      out = "m";
    };
    NONREFL = {
      attrs = nonrefl;
      out = "m2";
    };
    FLIP = {
      attrs = flip false;
      out = "m";
    };
    FLIPORD = {
      attrs = flip true;
      out = "m";
    };
    TWIN = {
      attrs = twin;
      out = "t";
    };
    TWINP = {
      attrs = twinP;
      out = "t";
    };
    TWIN2 = {
      attrs = twin2;
      out = "t";
    };
    LIAR = {
      attrs = liar;
      out = "k";
    };
    CTLVALUE = {
      attrs = ctlValue;
      out = "v";
    };
    CTLREFUSAL = {
      attrs = ctlRefusal;
      out = "m";
    };
    CLAMPLAZY = {
      attrs = clamplazy;
      out = "m";
    };
    QSPLIT = {
      attrs = qsplit;
      out = "m";
    };
    HOSC = {
      attrs = hosc;
      out = "m";
    };
    HOSC-H2 = {
      attrs = hoscH2;
      out = "m";
    };
    HOSC-NOOSC = {
      attrs = hoscNoosc;
      out = "m";
    };
    HOSC-ONEDESC = {
      attrs = hoscOnedesc;
      out = "m";
    };
    BOUNDPLATEAU = {
      attrs = boundplateau;
      out = "a";
    };
    TRIPLE = {
      attrs = triple;
      out = "k";
    };
    TRIPLE-HONEST = {
      attrs = tripleHonest;
      out = "k";
    };
    TRIPLE-NOQ = {
      attrs = tripleNoq;
      out = "k";
    };
    BOUNDSHORT = {
      attrs = boundshort;
      out = "z";
    };
    BOUNDQUIET = {
      attrs = boundquiet;
      out = "t";
    };
    BOUNDQUIET-NOOSC = {
      attrs = boundquietNoosc;
      out = "t";
    };
    BOUNDQUIET-FATH = {
      attrs = boundquietFath;
      out = "t";
    };
    WIDEFLAT = {
      attrs = wideflat;
      out = "w";
    };
    UNDEMERR = {
      attrs = undemerr;
      out = "t";
    };
    UNDEMOK = {
      attrs = undemok;
      out = "t";
    };
    DEMERR = {
      attrs = demerr;
      out = "t";
    };
    LATEREAD = {
      attrs = lateread;
      out = "a";
    };
    "LATEREAD-CTL" = {
      attrs = latereadCtl;
      out = "a";
    };
    LATEREAD2 = {
      attrs = lateread2;
      out = "a";
    };
  };
in
{
  inherit run fixtures;

  # The demanded value of each fixture, by name — the one expression both suites assert over.
  results = builtins.mapAttrs (_: f: run f.attrs f.out) fixtures;

  # A11a's ratchet, exposed for the composed-bound cell.
  ratchetA = run ratchet "a";
  ratchetB = run ratchet "b";

  # The LIFETIME RULE's two sides, on a two-node tree: a member's step reaching a child record's
  # co-located `_eval` cache inside an open round meets the named refusal; the same demand through
  # `self.get` is unaffected and answers.
  lifetime =
    let
      scope2 = genScope.buildRoots {
        parentGraph = genScope.overlays [ (genScope.edge "c" "p") ];
        importGraph = genScope.empty;
        decls = {
          p = { };
          c = { };
        };
        types = { };
      };
      evalWith =
        step:
        (genScope.eval {
          scope = scope2;
          attributes = {
            children = self: id: if id == "p" then { c = self.node "c"; } else { };
            imports = _self: _id: [ ];
            plain = _self: _id: 3;
            circ = genScope.circular {
              carrier = {
                bottom = 0;
                leq = x: y: x <= y;
                height = 3;
                quotient = false;
              };
            } step;
          };
        }).get
          "p"
          "circ";
    in
    {
      cacheRead = evalWith (
        self: _id: _prev:
        (self.get "p" "children").c._eval.plain
      );
      getRead = evalWith (
        self: _id: _prev:
        self.get "c" "plain"
      );
    };
}
