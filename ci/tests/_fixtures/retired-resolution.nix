# THE RETIRED RESOLUTION SURFACES, FROZEN AS THE REFERENCE THE CALCULUS IS READ AGAINST.
#
# gen-scope `query`, `queryAll`, `ambiguous` and `inherit'` as they stood at `gayc-u1b` (c8785fb,
# `lib/resolve.nix`), copied without their doors and with the `_seen` citation corrected (den-hoag-gayc
# U1c; it read "rule X", the seen-IMPORTS rule, for a set of scope ids). They are no
# longer the library's: the library publishes tombstones under these names and resolves through
# `resolve`. This copy is what "today" means in `tests/calculus.nix`'s grid cells, so each intended
# answer change is counted against the construction it replaces rather than asserted from memory.
{ prelude }:
let
  relations = import ../../../lib/traversal-names.nix;
  # Resolve with specificity ordering D < I < P (Neron Fig. 2). `query`'s own selector, and no longer
  # published: the surface name `resolve` is the calculus (`calculus.nix`), and this ordering is
  # `neron.order` there, read by mode "visible".
  resolve =
    {
      local ? null,
      imported ? null,
      inherited ? null,
      localShadowsImport ? true,
      importShadowsParent ? true,
    }:
    if local != null && localShadowsImport then
      local
    else if imported != null && importShadowsParent then
      imported
    else if local != null then
      local
    else if imported != null then
      imported
    else
      inherited;

  # Generalized query combinator (van Antwerpen §2.1).
  # Import edges come from self.get id relations.imports (computed attribute).
  # _seen holds scope ids: it is the SEEN-SCOPES set (Neron Fig. 19's S, van Antwerpen 2016 rule (T)'s S).
  # The answer is a SINGLE declaration. An import set contributed by more than one DISTINCT node is
  # an ambiguity (Neron §2.2, Duplicate Declarations) and refuses by name rather than being folded
  # together or chosen from by traversal order. Refusing is this library's single-answer contract,
  # not Neron's rule — the calculus deliberately identifies ambiguous resolutions rather than
  # requiring their absence (§2.2), and `queryAll` is that identify-all reading (Fig. 3 rule R).
  query =
    {
      dataFilter,
      localShadowsImport ? true,
      importShadowsParent ? true,
      transitiveImports ? false,
      _seen ? { },
    }:
    self: id:
    let
      node = self.node id;
      local = dataFilter node;
      importIds = self.get id relations.imports;
      unseenImports = builtins.filter (iid: !(_seen ? ${iid})) importIds;
      collectFromImport =
        seen: importId:
        let
          v = dataFilter (self.node importId);
          # Each candidate travels with the id of the node whose `dataFilter` produced it. Neron's
          # judgements conclude at a declaration OCCURRENCE (Fig. 3, `x^D_j`) and occurrence identity
          # is positional — §2.2, "all occurrences b_i denote the same name b at different positions"
          # — so the contributing node is the identity the predicate below is over. The recursion
          # needs no help: each recursive call knows its own `importId`, so a transitively-reached
          # candidate is attributed to the node that DECLARED it, never to the direct import it was
          # reached through.
          direct = prelude.optional (v != null) {
            node = importId;
            value = v;
          };
          transitive =
            if transitiveImports then
              let
                nextImports = self.get importId relations.imports;
                nextUnseen = builtins.filter (iid: !(seen ? ${iid})) nextImports;
                nextSeen = seen // {
                  ${importId} = true;
                };
              in
              prelude.concatMap (collectFromImport nextSeen) nextUnseen
            else
              [ ];
        in
        direct ++ transitive;
      imported =
        let
          contributions = prelude.concatMap (collectFromImport (_seen // { ${id} = true; })) unseenImports;
          contributors = prelude.unique (map (c: c.node) contributions);
        in
        # AMBIGUITY IS MORE THAN ONE DISTINCT DECLARATION OCCURRENCE, NOT MORE THAN ONE DERIVATION.
        # A node reached along several import routes — a repeated edge, a diamond — is ONE
        # declaration reached several ways, and the seen-imports machinery exists to make those
        # routes terminate (Neron §2.4) rather than to multiply the answer. Two distinct declaring
        # nodes are §2.2's Duplicate Declarations, and those refuse.
        #
        # Distinctness is deliberately NOT value equality. Comparing candidate values would force
        # them deeply, where the emptiness test below already forces each to WHNF and no further;
        # the ids cost nothing, being `importIds` the filters above have forced already. Value
        # equality would also refuse two nodes carrying the same function, which Nix compares as
        # unequal without erroring.
        if contributions == [ ] then
          null
        else if builtins.length contributors > 1 then
          throw "gen-scope: node '${id}' imports more than one declaration of the queried datum, from ${builtins.toJSON contributors}. That is an AMBIGUITY in the sense of Neron et al. 2015 (Fig. 3 rule (V); §2.2 Duplicate Declarations) — two declaration occurrences for one read. This query answers with a single declaration or REFUSES; it does not choose among them, and it does not fold them together. Declare the datum on '${id}' itself (a local declaration shadows imports at the default `localShadowsImport = true`), drop one of the competing imports, or read the whole set with `queryAll`, which identifies ALL the resolutions without shadowing (Neron rule R, and §2.2's own reading) and leaves the choice at the call site."
        else
          # One distinct contributor means every candidate carries the same value — `dataFilter` is a
          # pure function of the node — so this head is a projection out of a singleton equivalence
          # class, not a tie-break among rivals.
          (builtins.head contributions).value;
      inherited =
        if node.parent != null then
          query {
            inherit
              dataFilter
              localShadowsImport
              importShadowsParent
              transitiveImports
              ;
            _seen =
              _seen
              // builtins.listToAttrs (
                map (iid: {
                  name = iid;
                  value = true;
                }) importIds
              );
          } self node.parent
        else
          null;
    in
    resolve {
      inherit
        local
        imported
        inherited
        localShadowsImport
        importShadowsParent
        ;
    };

  # Return all reachable results without shadowing (Neron §2.3, rule R).
  queryAll =
    {
      dataFilter,
      transitiveImports ? false,
      _seen ? { },
    }:
    self: id:
    let
      node = self.node id;
      local = dataFilter node;
      importIds = self.get id relations.imports;
      unseenImports = builtins.filter (iid: !(_seen ? ${iid})) importIds;
      collectFromImportAll =
        seen: importId:
        let
          v = dataFilter (self.node importId);
          direct = prelude.optional (v != null) v;
          transitive =
            if transitiveImports then
              let
                nextImports = self.get importId relations.imports;
                nextUnseen = builtins.filter (iid: !(seen ? ${iid})) nextImports;
                nextSeen = seen // {
                  ${importId} = true;
                };
              in
              prelude.concatMap (collectFromImportAll nextSeen) nextUnseen
            else
              [ ];
        in
        direct ++ transitive;
      importResults = prelude.concatMap (collectFromImportAll (_seen // { ${id} = true; })) unseenImports;
      parentResults =
        if node.parent != null then
          queryAll {
            inherit dataFilter transitiveImports;
            _seen =
              _seen
              // builtins.listToAttrs (
                map (iid: {
                  name = iid;
                  value = true;
                }) importIds
              );
          } self node.parent
        else
          [ ];
    in
    (prelude.optional (local != null) local) ++ importResults ++ parentResults;

  # Ambiguity detection (van Antwerpen §2.3).
  # `queryAll`'s fields, named: the door built over it reads its contract off these formals.
  ambiguous =
    {
      dataFilter,
      transitiveImports ? false,
      _seen ? { },
    }@args:
    self: id: builtins.length (queryAll args self id) > 1;

  # Inherited attribute: walks parent chain until resolve returns non-null.
  # _visited prevents cycles on malformed parent relations.
  inherit' =
    {
      resolve,
      _visited ? { },
    }:
    self: id:
    let
      node = self.node id;
      result = resolve node;
    in
    if _visited ? ${id} then
      throw "gen-scope: parent cycle detected at '${id}'"
    else if result != null then
      result
    else if node.parent == null then
      null
    else
      inherit' {
        inherit resolve;
        _visited = _visited // {
          ${id} = true;
        };
      } self node.parent;
in
{
  inherit
    query
    queryAll
    ambiguous
    inherit'
    ;
}
