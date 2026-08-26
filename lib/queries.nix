# Structural queries as thin wrappers over self.node and self._childRecords.
#
# parent is structural (on the node). children, descendants, siblings and the
# descendant tests read the child direction through the accessor's composed
# child-record read (`self._childRecords`), which is `children` with the spawn
# channel's half — a spawned node is a node (one graph, one node notion), so a
# query surface reading the declared half alone answers about a different node
# set than the evaluator materializes.
{ prelude }:
let
  parent = self: id: (self.node id).parent;

  children = self: id: self._childRecords id;

  childrenIds = self: id: builtins.attrNames (self._childRecords id);

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
        else if visited ? ${p} then
          [ ]
        else
          [ p ] ++ go (visited // { ${p} = true; }) p;
    in
    go { ${id} = true; } id;

  siblings =
    self: id:
    let
      p = (self.node id).parent;
    in
    if p == null then
      [ ]
    else
      builtins.filter (cid: cid != id) (builtins.attrNames (self._childRecords p));

  descendants =
    self: id:
    let
      go =
        visited: nid:
        let
          cids = builtins.attrNames (self._childRecords nid);
        in
        prelude.concatMap (
          cid: if visited ? ${cid} then [ ] else [ cid ] ++ go (visited // { ${cid} = true; }) cid
        ) cids;
    in
    go { ${id} = true; } id;

  # Early-return walk: O(depth) best case instead of always building full list.
  isAncestor =
    self: ancestorId: id:
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
        else if visited ? ${p} then
          false
        else
          go (visited // { ${p} = true; }) p;
    in
    go { ${id} = true; } id;

  # DFS with early termination: avoids building full descendant list.
  isDescendant =
    self: descendantId: id:
    let
      go =
        visited: nid:
        let
          cids = builtins.attrNames (self._childRecords nid);
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
    go { ${id} = true; } id;

  # Delegates to eval's nodesOfType (selective walk) instead of forcing allNodes.
  nodesByType = self: type: self.nodesOfType type;
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
