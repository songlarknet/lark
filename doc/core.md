# core language

```
exp ::=
  | x | v
  | prim(exp,...)
  | exp -> exp
  | pre(exp)

sort ::= ...
prop ::= require | guarantee | property | sorry | generated;

node ::=
 node when exp reset exp (pure|nondet) {
  var (v : sort,...);
  subnode (v,...) := nodeRef;
  v := exp;...
  prop string: exp;...
 }

nodeRef ::=
  node | name[v := exp,...]
```

transforms for model checking:
1. contract instantiation: guarantees become sorries at use-sites; requires become properties at use-sites and sorries in body.
   later, refinement types?
   arithmetic overflow/underflow - could these be implemented as contracts on prims?
2. flattening: pull out nested subnodes, replace activation of each node with conjunction of all parents
3. common subnode elimination: find pure nodes with same activation and arguments, substitute
4. slicing: look at dependencies of set of properties
5. bmc, k-ind and feasibility

transforms for compilation:
for V0, should be relatively straightforward to generate the worst-possible-C-code as-is from the initial core. then:
1. re-fold definitions to reduce code duplication.

```
node... =flatten> node...
```



judgment `node... | exp  INVARIANT`, `exp UNSAT`
```
----------------------- T
node... | True INVARIANT

      not p UNSAT
----------------------- unsat
node... | p   INVARIANT


node... | (e /\ h') INVARIANT
---------------------------- inv-gen
node... | e         INVARIANT

```




judgment `exp anf`, `exp val`
```
-----   -----
x val   v val

e val
-----
e anf

    e_i val
-----------------
prim(e,...) anf

e val    e' val
---------------
    e -> e'

   e val
----------
pre(e) anf
```


