# Lack: a Scala EDSL for Lustre

bare minimum to be useful:
* model checking with BMC and K-induction
* compilation to C - bare minimum with code duplication
* well-formedness checks: causality
later:
* invariant generation
* plumb generated invariants to generated C code - any way to use CBMC for translation validation?
* compilation to java?
* automata
* better compilation without code duplication

## design / features for minimum viable product

### arithmetic: machine integers
all integer types have explicit bitwidths. proof obligations are generated for arithmetic overflow and underflow.

### polymorphism
we get polymorphism "for free" by using Scala as the meta language.

```
  def abs[T: SortRepr: Num](x: Stream[T])(using builder: Builder): Stream[T] =
    cond(
      when(x >= int(0)) {  x },
      otherwise         { -x }
    )
```

### structs
gotta have structs

### pure / deterministic language fragment
one issue with Kind2 is that it's not clear that two invocations of the same node with the same argument produce equal outputs. they might be different if the node is imported and has a non-deterministic contract. this non-determinism causes problems when you have a contract with a guarantee `f(x)` and then try to prove `f(x)` at the use-site of the contract. to prove this property, Kind2 needs to prove that `f(x) == f(x)`, which isn't always easy.

with a pure/deterministic fragment we can do a common subexpression elimination over all of the instantiated nodes and rewrite the two instances of `f` to the same instance. this should make it trivial to show that `f(x)` implies `f(x)`. this equivalence requires both instances to have the same activation context (when, reset).

### invariants
#### reaching into subnodes' local variables to state invariants
one issue with Kind2 is that you can't always state the required invariants in the source language because the variables are not in scope.

one semi-solution is to, by convention, make local variables publicly-accessible in nodes, eg:
```
  class LastN(n: Integer, e: Stream[Bool], application: NodeApplication) extends Node(application):
    val count     = local[UInt8]
    val out       = output[Bool]
    count := ...
    out   := count >= n
```
a node that instantiates `val lastn = LastN(...)` can refer to `lastn.count` in its invariants. later we might want a check that only properties and invariants can refer to guts of subnodes, while contracts and real executable code cannot.

it might not always be possible to refer to subnodes by index or name - might want some helper functions to find them by index or something, eg to find the first subnode of type `LastN` could do `subnodes.ofType[LastN](0).local[UInt8]("count") <= n`

## features for later

### arithmetic
#### subranges
subranges have a carrier type which defines the machine integer representation. performing arithmetic on values of subrange type reverts to the representation type and need to be explicitly cast back.
#### modulo arithmetic
Mod8, Mod16,... Mod64 types for unsigned overflow-safe arithmetic.
#### floats
float support? subranges for floats?

### contracts
require/guarantee contracts

### sum types
maybe later

### automata
I think we could desugar automata down to the core language without having to change it much. I'm not sure how good the counterexample printing would be though.

### clocks
can clock constraints be encoded as properties? that would be nice.


### refinement types, of some sort?
a const stream such as `n : Const[UInt8]` could be encoded by emitting a precondition when it occurs in arguments to a node:
```
requires { true -> n === pre(n) }
```
and when constructing a value of type `Const[UInt8]`, it should emit a guarantee or a property.

maybe subranges are similar.
