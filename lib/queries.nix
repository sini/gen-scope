# Structural queries as thin wrappers over self.node and self._childRecords (on an armed body's
# reader, over self.node and self._childOrder).
#
# parent is structural (on the node). children, descendants, siblings and the
# descendant tests read the child direction through the accessor's composed
# child-record read (`self._childRecords`), which is `children` with the spawn
# channel's half — a spawned node is a node (one graph, one node notion), so a
# query surface reading the declared half alone answers about a different node
# set than the evaluator materializes.
{ prelude, key }:
let
  # A node id may carry store-path string context, which an attribute name cannot: the visited sets
  # below are keyed by the id's text (den-hoag-di165), and the answers keep the id as written.
  toKey = key.attrKey "queries";

  # Every query reaches `self.node` or `self.get`, which refuse a non-string id by name. The three
  # below also hold a name they only COMPARE, and a comparison answers `false` about a record rather
  # than refusing it, so each refuses that argument itself, ahead of the walk.
  string = import ./string-argument.nix;

  parent = self: id: (self.node id).parent;

  # An armed body's reader carries no `_childRecords` (a named refusal): a body reads a node's
  # children through the guarded names, `_childOrder` and `node`, so each child is a declared read.
  # The unarmed reader answers through `_childRecords`, unchanged.
  armed = self: !(builtins.tryEval self._childRecords).success;

  children =
    self: id:
    if armed self then
      builtins.listToAttrs (
        map (cid: {
          name = toKey cid;
          value = self.node cid;
        }) (self._childOrder id)
      )
    else
      self._childRecords id;

  childrenIds = self: id: self._childOrder id;

  ancestors =
    self: id:
    let
      go =
        visited: nid:
        let
          p = (self.node nid).parent;
        in
        if p == null then
          [ ]
        else if visited ? ${toKey p} then
          [ ]
        else
          [ p ] ++ go (visited // { ${toKey p} = true; }) p;
    in
    go { ${toKey id} = true; } id;

  siblings =
    self: id:
    let
      p = (self.node id).parent;
    in
    if p == null then [ ] else builtins.filter (cid: cid != id) (self._childOrder p);

  descendants =
    self: id:
    let
      go =
        visited: nid:
        let
          cids = self._childOrder nid;
        in
        prelude.concatMap (
          cid: if visited ? ${cid} then [ ] else [ cid ] ++ go (visited // { ${cid} = true; }) cid
        ) cids;
    in
    go { ${toKey id} = true; } id;

  # Early-return walk: O(depth) best case instead of always building full list.
  isAncestor =
    self: ancestorId: id:
    builtins.seq (string "isAncestor" "a node identifier" ancestorId) (
      let
        go =
          visited: nid:
          let
            p = (self.node nid).parent;
          in
          if p == null then
            false
          else if p == ancestorId then
            true
          else if visited ? ${toKey p} then
            false
          else
            go (visited // { ${toKey p} = true; }) p;
      in
      go { ${toKey id} = true; } id
    );

  # DFS with early termination: avoids building full descendant list.
  isDescendant =
    self: descendantId: id:
    builtins.seq (string "isDescendant" "a node identifier" descendantId) (
      let
        go =
          visited: nid:
          let
            cids = self._childOrder nid;
          in
          builtins.any (
            cid:
            if visited ? ${cid} then
              false
            else if cid == descendantId then
              true
            else
              go (visited // { ${cid} = true; }) cid
          ) cids;
      in
      go { ${toKey id} = true; } id
    );

  # Delegates to eval's nodesOfType (selective walk) instead of forcing allNodes.
  # Armed, the walk is the enumeration `allNodeIds` read through `node`, so every node it ranges
  # over is a declared read; unarmed, `nodesOfType`'s selective walk, unchanged.
  nodesByType =
    self: type:
    if armed self then
      let
        ty = string "nodesByType" "a kind name" type;
      in
      builtins.listToAttrs (
        prelude.concatMap (
          nid:
          let
            n = self.node nid;
          in
          prelude.optional (n.type == ty) {
            name = toKey nid;
            value = n;
          }
        ) self.allNodeIds
      )
    else
      self.nodesOfType (string "nodesByType" "a kind name" type);
in
{
  inherit
    parent
    children
    childrenIds
    ancestors
    siblings
    descendants
    isAncestor
    isDescendant
    nodesByType
    ;
}
