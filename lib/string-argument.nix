# A NAME ARGUMENT THAT IS NOT A STRING, REFUSED BY THE DOOR THAT RECEIVED IT (den-hoag-bkdkg).
#
# Every node is keyed by its identifier and every kind by its name, so a door handed anything else —
# typically the node VALUE where its identifier goes — used to abort past `tryEval` on an attribute
# lookup, naming nothing the caller wrote, or answer `false`/`[ ]` about a name no node can carry.
# `parseParent` already refused by name; this is that refusal for the doors that route a name
# somewhere. It names the TYPE and never the value, because rendering a value that is not a string
# is the very coercion abort it replaces, and it returns the string so a door can pass it on.
#
# ★ ONE BINDING, SEVERAL DOORS: the evaluators' accessors, the structural queries and the minting
# entry all take it, and the queries reach the accessors' guards by composition rather than carrying
# their own. The module takes no argument, like `callable.nix` beside it.
who: noun: v:
if builtins.isString v then
  v
else
  throw "gen-scope.${who}: got ${builtins.typeOf v}, expected ${noun} (a string)"
