# Lack: a Scala EDSL for Lustre

This document describes the short-term and mid-term roadmap for lack.
For the first milestone I want to pare it down to the bare minimum to be "useful".
The high-level goal is to have a model checker and compiler toolchain that's scalable, debuggable, executable, and sound.

## Milestones
### M1: bare minimum
Bare minimum features to be useful:
* ~~surface language, maybe with syntax for simple automata;~~
* ~~model checking with BMC and K-induction;~~
* ~~basic counterexamples;~~
* ~~typechecking, causality checking, etc;~~
* ~~compilation to C - simplest possible generation ok;~~
* ~~decent property testing of interpreter, SMT semantics, and C semantics.~~

### M2: scale
Just these features might be OK, but with just plain old K-induction there's some risk that we could run into programs we can specify but can't prove.
To make it "more scalable" I want these features, but I think they can wait until the second milestone:
* contracts allows replacing complex implementations with simpler specs;
* path compression makes K-induction stronger;
* common subexpression elimination so that hopefully `x ==> x` is always trivial to prove;
* sneaky invariants let the user specify invariants that refer to nested private state inside subnodes.

### M3: sound
After we know that we can prove interesting things, we want to make sure anything we prove is actually true of the compiled code.
This is not the case with machine integers which can overflow.
To make it "more sound" I want these features in milestone three:
* ~~integer bounds checks;~~
* float bounds and NaN checks.

### M4: better compilation
At some point we probably want to generate nicer C code, and maybe also generate Scala code.
Milestone four, maybe:
* better compilation to C ~~(modular, support separate compilation)~~ *(modular compilation is done, but need to remove duplicates from node graph)*;
* compilation to Scala or Java.

### M5: better debugging
Debuggable:
* better counterexamples;
* determine safe/invalid/unknown for each property. At the moment it just prints invalid/unknown if any properties are bad.

## design / features

### arithmetic: machine integers
All integer types have explicit bitwidths.
In the long term, proof obligations are generated for arithmetic overflow and underflow.

### arithmetic: floating point
I don't know how good the SMT solver support for floating-point numbers is.
I don't expect it to be as good as the support for reals.
Would it be useful to have two types of floating points / reals with different logical representations?
We'd have `Real32` which has the logical representation of a real, and `Float32` which uses machine float logic.
Both would be represented by a 32-bit floating point value at runtime.

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
We will want structs eventually, but I don't think they are required for the first few milestones.
To start with, we can probably just use Scala meta-level structs to package them up.
One day we can add real struct support, which I assume would mainly be useful for interop with other C code.

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
