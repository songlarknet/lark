# Why?

Why another reactive language / model checker / compiler?


## Similar projects

### Kind2

Kind2 is a model checker.
It supports Lustre input programs as well as a lower-level transition system description.

The prover is pretty mature and supports k-induction and fancy invariant generation techniques.


+ mature, stable
+ active development
+ friendly, helpful developers
- contracts can be unreliable, especially when using temporal logic inside guarantees
- can't express invariants referring to internal state of subnodes
- automata too slow; now removed
- no direct compilation to C
- no polymorphism
- bounded arithmetic not baked:
  - uint32 type does not support subtraction
  - arithmetic with subranges, intermediate calculations not checked for under/overflow
? Rust backend - stability unknown
? using low-level transition system format may resolve some of these issues (eg invariants referring to internal states)

### Copilot (Galois project)

Copilot is a Haskell embedded DSL.
It has a similar goal but the input language is a bit different.

Uses an SMT solver to check user-specified safety properties.
Proof backends are simple K-induction or call out to Kind2.
The checker semantics doesn't match the compiled code - pure integer and real arithmetic with no boundedness checks.

+ metaprogramming, presumably supports faux-polymorphic definitions
+ prover uses Kind2's transition-system backend
+ compiles to C
+ trigger mechanism looks like nice C integration
- prover doesn't check bounded arithmetic
- no contracts or abstraction for "proving in the large"
- code duplication in both transition system and generated C code; the Scala embedding can address this by keeping more structure.
- no counterexamples
- no automata; not sure how clean it would be to add them
- generated code loses local variable names; in Scala can resolve this with an implicit macro to get location and name information
? supports local quantification in properties, eg for-all integers; however not clear whether this is useful in practice as Kind2 and SMT solvers don't have great support

### CoCoSim
https://github.com/NASA-SW-VnV/CoCoSim

I don't know much about Simulink.
Does it have a textual input language?

### SCADE

Commercial proprietary tool.

We found it difficult to get concrete information about what features SCADE supports.
We had a few conversations with them and they couldn't give us details about what the model checker supports or how it works.
The pricing was also unclear.
Implementation is Windows-only.

The whole language seemed a bit bifurcated because you had the graphical language, which supports some features, and the textual language, which supported other features (eg clocks).
The graphical language looked useful for electrical engineers but it didn't seem to be designed for software engineers.

The generated code looked pretty nice.

### SpinalHDL
https://spinalhdl.github.io/SpinalDoc-RTD/master/index.html

Spinal is a Scala EDSL for describing hardware designs.
It is conceptually very similar except that the programs look more like Verilog than Lustre, which means that they have a sort of low-level imperative feel rather than an applicative / functional feel.
It generates Verilog rather than C.

It also supports some model checking via Symbi-yosys, which can do bounded model checking as well as k-inductive proofs.
I'm not sure whether it supports fancy stuff like path compression.
It doesn't have modular verification features like contracts.

You could probably write some high-level controllers in this if you wanted to.

### Chisel
https://www.chisel-lang.org/

Chisel solves the same problem as Spinal, slightly differently.
Spinal was originally a re-implementation of Chisel with stronger types.

Chisel uses a compiler plugin to generate some definitions.
It also uses some macros.
The implementations of these may be useful as references: https://github.com/chipsalliance/chisel3/blob/master/plugin/src/main/scala/chisel3/internal/plugin/BundleComponent.scala and https://github.com/chipsalliance/chisel3/tree/master/macros/src/main/scala/chisel3/internal.