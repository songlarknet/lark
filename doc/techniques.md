
This document contains rough notes on a bunch of model checking techniques.

# Overview

High-level papers that give a broad overview of multiple techniques.

## An insight into SMT-based model checking techniques for … dataflow; Jonathan Laurent 2014
Talk based on the Copilot work.
Pretty helpful.

* https://github.com/GaloisInc/copilot-1/blob/master/copilot-theorem/doc/talk.pdf

## Verifying safety properties of Lustre programs: an SMT-based approach (George Hagen PhD thesis, 2008)
* http://clc.cs.uiowa.edu/Kind/Papers/Hag-PHD-08.pdf

George Hagen's PhD thesis that describes the original Kind implementation.

Good introduction, uses different encoding of Lustre programs into SMT logic than more recent Kind2.
Streams are treated as functions from time (nat) to the value at that time.
Kind2 uses a transition system with initial predicate and transition relation.

They evaluated a bunch of fairly simple techniques to see how they helped with proving properties:
* Simple dependency-graph-based slicing showed to be useful.
* A more dynamic "cone of influence", a smarter sort of slicing, was less useful.
* If-then-else elimination (partial evaluation of ifs with known predicate values) was not too helpful.
* Inlining simple variable definitions (x = y) was always helpful; more aggressive inlining could reduce the effectiveness of abstraction.
* Skipping steps: instead of trying 1-induction, 2-induction, 3-induction, etc… try skipping some for the step (invariant maintenance) case: 3, 5, 7 etc…. Don't want to skip for base case because then you might not get the shortest counterexample. Unclear benefit, but sometimes improved performance.

Two techniques had big improvements: path compression and structural abstraction.

Combination of path compression and structural abstraction is subtle: when you slice a subset of the node to create the abstraction, a path that has no cycles in the original version might have cycles in the sliced version because you're discarding part of the state.
The simplest solution seems to be to only use the original / concrete version for checking compression termination.
I didn't understand the explanation of the more sophisticated solution, maybe the paper will help.

How to choose which to refine based on the unsatisfiable core?
Many heuristics to try.
Dependency graph of program variables, try different search strategies, eg breadth-first and depth-first.
They found that only introducing one variable definition per iteration introduced too much overhead.
_Path refinement_ seems to be the best.
It tries to find a path between the variable in the unsatisfiable core and an input variable, and refines all of those variables at once.

## Scaling up the formal verification of Lustre programs with SMT-based techniques (George Hagen, Cesare Tinelli, 2008)
* https://homepage.cs.uiowa.edu/~tinelli/papers/HagTin-FMCAD-08.pdf

For path compression, only need to look at the variables in calls to pre (`pre(v)`) which are the _state variables_.

Doesn't explain the subtlety in combining path compression and structural abstraction.

## JKind

* Gacek, Backes, Whalen, Wagner, Ghassabani. The JKind model checker. 2017. https://sci-hub.se/https://link.springer.com/chapter/10.1007/978-3-319-96142-2_3

Tool paper with a few cool tricks: inductive validity cores, counterexample smoothing, and remembering invariants across runs.

Inductive validity cores: find roughly-minimal subset of program equations required for a property to hold.
Apparently useful for certification.
They use some heuristics to avoid brute-force search for the minimal core.

Counterexample smoothing - simplifying counterexamples.
The idea is to minimize the number of changes to input variables so that the examples are "smoother".
Re-formulates the bounded model checking problem as a MaxSat problem with soft assertions that the values of input variables should not change.
Fair bit slower ("increased runtime 40%") but might be worthwhile.

The _advice engine_ holds state across different executions to produce invariants.
JKind saves the sliced, flattened transition system, as well as the invariants used to prove it.
In the next run they can load the old invariants and use them if they are still valid and well-typed.
The advice engine checks the loaded invariants itself before giving them to the other engines.

Choice quote:

> Unfortunately, the algorithms used in the commercial tool support are undocumented and performance comparisons are prohibited by the tool licenses, so it is not possible to compare performance on this aspect.

I didn't know that licences could stop you from doing benchmarks.

# Bounded model checking
For a transition system with initial predicate `I` and transition relation `T`, bounded model checking just checks the first k reachable states satisfy some property `\phi`:
```
I(s0) /\ T(s0, s1) /\ T(s1, s2) /\ ... /\ T(s{k-1}, sk)
=> \phi(s0) /\ \phi(s1) /\ ... /\ \phi(sk)
```

This can provide good counterexamples but doesn't say anything about longer executions.

# K-induction

K-induction is sound but not complete.

## Path compression
For a counterexample of length k, we already know that there doesn't exist a shorter counterexample (of length `< k`).
When searching for counterexamples, we can filter out repeated states (cycles) or multiple initial states.
Define compression predicate:
```
C_k[x_0, ..., x_k] := (/\_{i /= j} x_i /= x_j) /\ (/\_{i > 0} ~I[x_i])
```

Then the k-inductive maintenance becomes:
```
  /\_{i=0}^{k-1} P[x_i] /\
  /\_{i=0}^{k-1} T[x_i, x_{i+1}] /\
                 C_k[x_0, ..., x_k]
|=
  P[x_k]
```

For completeness, you can check whether you've covered all possible compressed paths by asking "is there a non-compressed path of length k?":
```
I[x_0] /\ T[x_0, x_1] /\ ... /\ T[x_{k-1}, x_k] |= ~C_k[x_0, ..., x_{k-1}]
```
If this entailment holds (solver returns unsat), then there are no "interesting" paths of length >k.
That means that bounded model checking up to k-1 has exhaustively covered the search space.

Sound and complete for finite-state transition systems.
How important is this completeness in practice, for realistically-sized programs?
For a program like `lastn(4, e)` it should figure out that you only really need paths of length 4 to cover the whole state space.

Version in George Hagen PhD thesis doesn't include no-reinitialize `~I[x_i]` in definition of C_k.
Introducing the no-reinitialize check seems like it should reduce the maximum length.

This doesn't seem like it would be very useful in practice once the input contains anything larger than a few booleans.
For example:
```
node sum_pairs(i: int8) returns (j: int8)
var p: int8;
let
 p = 0 -> pre i;
 j = p + i;
tel

property
  lastn(2, i >= 0) => sum_pairs(i) >= 0
```

K-induction with k=2 should solve this (`pre i >= 0 /\ i >= 0 => pre i + i >= 0`).
The exhaustivity/non-compression check above would require a k of ~2^8 to visit all states, but it feels like there should be a stronger exhaustivity check that somehow abstracts away the input values.
Maybe if we restrict the values that the input integer variables can take.
For example for checking whether three steps can be compressed to two, we allocate two real integer values for i, and restrict i at each time step to be one of those.
```
fresh_0, fresh_1 : int8;
For x_n = (i_n, p_n, j_n);
I[x_0] /\ T[x_0, x_1] /\ T[x_1, x_2] /\ T[x_2, x_3] /\
  i_0 \in {fresh_0, fresh_1} /\
  i_1 \in {fresh_0, fresh_1} /\
  i_2 \in {fresh_0, fresh_1}
  |= ~C_k[x_0, ..., x_2]
```

No - no good, obviously wrong if k=1. taking `i - pre i` - will always be 0 when i = pre i.
Abstract interpretation?

What if we split the whole int8 range into two chunks `{ [-128, 0), [0, 128) }`:
```
type bi8 = enum { LT0, GE0 };

LT0 + LT0 = LT0
LT0 + GE0 = ?
GE0 + LT0 = ?
GE0 + GE0 = GE0

LT0 >= 0  = false
GE0 >= 0  = true

node sum_pairs(i: bi8) returns (j: bi8)
var p: bi8;
let
 p = GE0 -> pre i;
 j = p + i;
tel

property
  lastn(2, i >= 0) => sum_pairs(i) >= 0
```

This sounds like a sort of data abstraction.
Would this sort of abstraction also be useful for generalizing counterexamples?

* https://homepage.cs.uiowa.edu/~tinelli/talks/NFM-12.pdf

### Simulation-compression
* Bounded model checking and induction: from refutation to verification. Leonardo de Moura, Harald Rueß, Maria Sorea. 2003.
https://link.springer.com/content/pdf/10.1007/978-3-540-45069-6_2.pdf

Given a direct simulation `<=_d` and a reverse simulation `<=_r`, which describe a sort of abstract equivalence between states, you can define a more general path compression that requires that pairs of states are not similar according to the simulation relations.

Direct simulation captures the notion of "equal distance to a bad state".
If two states are related, then they can both reach a bad state in the same number of steps.
For a direct simulation with respect to property `\phi`, there is a functor `F_d`:
```
F_d(R)(s1, s2) = if ~\phi(s1) then ~\phi(s2)
                 else \forall s1'. T(s1, s1') =>
                      \exists s2'. T(s2, s2') /\ R(s1', s2')
```

R is a direct simulation if `R \subseteq F_d(R)`.

Reverse simulations are roughly "equal distance from an initial state":
```
F_d(R)(s1, s2) = if I(s1) then I(s2)
                 else \forall s1'. T(s1', s1) =>
                      \exists s2'. T(s2', s2) /\ R(s1', s2')
```

Then you define a compressed path predicate as:
```
\pi_(R)(s0, ..., sn) =
  T(s0, s1) /\ T(s1, s2) /\ ... /\ T(s{n-1}, sn) /\
  /\_{0 <= i < j <= n} ~(si R sj)
```
Where R is the conjunction of the direct and reverse simulation relations.

Path compression with equality is complete for finite state systems but might require a high k-inductive k; path compression with simulation sometimes makes the compressed paths shorter, reducing the required k.
Some simulation relations can also compress some infinite state systems.

Path compression with simulation cannot compress all systems.
For the infinite state system `I = (x = 0)` and `T = (x' = x + 2)`, with the property `x /= 3` there is no bounded k that works with ordinary path compression.
I cannot find a direct simulation relation R that satisfies `R <= F_d(R)`.
Is there one?
My gut feeling is no: there is only one bad state, so there's no way to group them together with just the simulation relation.
We need a stronger property (`x % 2 == 0`).

# Structural abstraction

Removing clauses to get an abstraction / approximation.
Once you find a counterexample, ask the SMT solver whether it applies to the real program.
If it does, then it's a real counterexample.
If the counterexample doesn't apply to the original program, then you can get the 'unsatisfiable core' from the SMT solver, and use it to guide heuristics for adding clauses back in.

# Slicing
Split a problem with multiple properties into multiple smaller problems.
Slicing seems pretty easy - though would the SMT solver be able to do this on its own with a dependency analysis?

How does slicing interact with path compression?

# Invariant generation

## IC3 / property-directed reachability

IC3 is an invariant generation technique.
The property-directed reachability (PDR) paper calls the _implementation_ IC3 while it calls the general proof method property-directed reachability.
The PDR paper is not written by the original IC3 authors though; I don't know whether the original authors agree with that distinction.

The papers by the original authors are pretty dense.
There are at least three papers that are kind of meant to be read together.

* Formal definition: A. R. Bradley. SAT-based model checking without unrolling. 2011 https://www.researchgate.net/profile/Aaron-Bradley-3/publication/221550929_SAT-Based_Model_Checking_without_Unrolling/links/00b7d5399cfcc23d5e000000/SAT-Based-Model-Checking-without-Unrolling.pdf
* Understanding paper: Aaron Bradley 2012 Understanding IC3: http://theory.stanford.edu/~arbrad/papers/Understanding_IC3.pdf
* Example paper: F. Somenzi and A. R. Bradley. IC3: Where monolithic and incremental meet. 2011 https://www.cs.utexas.edu/users/hunt/FMCAD/FMCAD11/papers/inv3.pdf

But the property-directed reachability paper seems easier to read:

* Een, Mishchenko, Brayton. Efficient implementation of property directed reachability. 2011. http://www.een.se/niklas/eff_impl_pdr.pdf

Given a system and desired property `(T, I, P)` we want to find an inductive invariant `\phi` that implies `P`.
The main data structure is a trace of frame formulas R_0 to R_N, where each frame R_i overapproximate the set of reachable states i steps from an initial state.
The trace satisfies the properties:

```
-- First frame describes initial state
1. R_0 = I
-- Each frame after the first is the conjunction of a set of clauses (where each clause is a disjunction of literals):
2. clauses(R_i) : {Clause} for i > 0
-- Each frame is subsumed by those after it
3a. R_i => R_{i+1}
-- Which can be syntactically proved looking at the sets of clauses (rather than semantically)
3b. clauses(R_{i+1}) \subseteq clauses(R_i) for i > 0.
-- If we take a step from frame i, then frame i+1 holds at the new state
4. R_i /\ T => R_{i+1}'
-- First N-1 steps satisfy P (though RN may or may not imply P)
5. R_i => P for 0 <= i < N
```

The beginning of the main loop searches for assignments such that `R_N /\ ~P`.
Initially, N=0, and so the above is equivalent to `I /\ ~P`.
An assignment is a valid 0-step counterexample.

You need a way to generalize assignments to predicates - this generalization seems easier for SAT formula than SMT formula.
The equality / predicate abstraction seems like it could be useful for generating more general predicates.


Judgment form `P, I, T; F... |=c F...`

Initial value of F_0, F_1 is initial state and goal property as long as it holds for at least one step:
```
I |= P    I /\ T |= P'
---------------------- (init)
   P, I, T; |=c I, P
```

No need to loop further when consecutive frames in H are the same, as this means we've found an inductive hypothesis:
```
      \forall i. G_i /= G_{i+1}
P, I, T; F |=c G       P, I, T; G |=c H
----------------------------------------- (iterate)
           P, I, T; F |=c H
```

Propagation step: last frame (F_k) maintains the invariant, so move on to major iteration k+1
```
F_k, T |= P'        -- invariant maintained
G = F; P            -- append P
H_0 = G_0           -- don't propagate to zeroth frame
H_{i+1} = G_{i+1} /\ { c | c \in H_i, (H_i, T |= c) }
                    -- propagate any constraints from earlier frames
----------------------------------------- (propagate)
P, I, T; F |=c H
```

The above can be split into two, first appending:
```
F_k, T |= P'        -- invariant maintained
----------------------------------------- (append)
P, I, T; F |=c F, P
```

Then propagating:
```
H_0 = G_0           -- don't propagate to zeroth frame
H_{i+1} = G_{i+1} /\ { c | c \in H_i, (H_i, T |= c) }
                    -- propagate any constraints from earlier frames
----------------------------------------- (propagate)
P, I, T; G |=c H
```


Extension:
```
                    F_i, T, c |= c'
-----------------------------------------------------------(extend)
P, I, T; F |=c F_0 /\ c, ... F_{i+1} /\ c, F_{i+2}, ... F_k
```

Invariants of frame form:
1. I => F_0
2. F_i => F_{i+1}
  aka clauses(F_{i+1}) \subseteq clauses(F_i)
3. F_i => P
4. F_i /\ T => F_{i+1}

## Template-based

* Kahsai, Ge, Tinelli. Instantiation-based invariant discovery. 2011. https://homepage.cs.uiowa.edu/~tinelli/papers/KahGT-NFM-11.pdf

Here the template is a binary relation `R[_, _]` that describes a partial ordering, such as boolean implication, numerical ordering, set inclusion.
For the transition system S, they have a cheap way to generate the conjunction of all possible relations, `/\{ R[s,t] | s,t : U }`.
Rather than eagerly constructing this conjunction, you want a better representation so that you can simplify using the partial-ordering.
A better representation lets you avoid instantiating the relation for redundant cases, eg `x <= 1 /\ x <= 2 /\ x <= 3 /\ ...` only needs to specify `x <= 1`.

The idea is to find the invariant subset of the conjunction of all relations.
They start with all relations as `C := /\{ R[s, t] | ... }` and use the solver to filter out those that can be falsified in 1 step from an initial state.
Then they filter out those that can be falsified in 2 steps from an initial state.
This process repeats for more steps until you reach a number of steps that no more are filtered out.
(Though adding more steps could still filter out more clauses.)

Then they try to do a k-inductive step (where k is the number of base steps taken above).
They filter out the clauses that the solver finds counterexamples for, repeating until there are no more counterexamples.
The remaining clauses are invariant, but they can include trivial ones.

Finally, they remove the trivial relations by filtering out those that are directly implied by a single step of the transition relation with no inductive hypothesis.

The rest of the paper describes the fancy encoding they use to avoid the n-squared number of constraints.

* Kahsai, Garoche, Tinelli, Whalen. Incremental verification with mode variable invariants in state machines. 2012. https://homepage.cs.uiowa.edu/~tinelli/papers/KahEtAl-NFM-12.pdf

Extends the above with an analysis to determine which variables are mode variables.
Mode variables are variables that determine the current state in a state machine.
The paper introduces two main techniques:

1. inferring mode variables from system description so they can be used for invariant generation. My initial thought is that with control of the programming language, we could side-step this by adding explicit mode variable annotations.
2. communicating status of properties to the user as soon as the status is known. Properties are also used to prove other properties as soon as it is known that they are invariant.

Describes a concurrent implementation with the bounded model checking (k-inductive base), k-inductive step and invariant generation executing in parallel.
The concurrent communication looks reasonable, though it adds a lot of non-determinism.
I don't know how much non-determinism the SMT solver uses, but maybe it would be more deterministic to verify each node modularly and parallelise over the nodes instead of having the concurrent implementation.
Maybe just having a `-j1` mode to disable concurrency would be useful for CI.

## Abstract interpretation
* Garoche, Kahsai, Tinelli. Incremental Invariant Generation using Logic-based Automatic Abstract Transformers. 2013. https://homepage.cs.uiowa.edu/~tinelli/papers/GarKT-NFM-13.pdf

This paper describes two main techniques:

1. using an SMT solver's counterexamples to compute the abstract-interpretation fixed point predicate describing reachable states; and
2. using the abstract-interpretation description of reachable states to suggest invariants.

For a concrete domain `D` and an abstract domain `A` with join, meet, concretization and abstraction functions, construct an initial abstract value `a : A` that describes the initial state of the system `a = abstract(I)`.
Then you can iterate a procedure of asserting that if you take a step from a state `x` described by abstraction `a`, then the result state `x'` is also described by abstraction `a`.
That is, find an assignment such that `x : concrete(a), T[x, x'] |= ~(x' : concrete(a))`.
If the solver finds an assignment, then you can update `a` to join the two abstraction: `a \join abstract(x')`.
If the assertion is unsatisfiable, then `a` is already the fixed point.

The above process can start suggesting possible invariants even before it reaches the fixed point.
Assuming that the formula produced by `x : concrete(a)` is a conjunction of clauses, you can take a subset of those clauses and try to prove them (k-)inductively.

Looks pretty reasonable.

## Equality abstraction

* Goel. From Finite to Infinite: Scalable Automatic Verification of Hardware Designs and Distributed Protocols. 2021. PhD thesis. https://deepblue.lib.umich.edu/bitstream/handle/2027.42/171355/amangoel_1.pdf?sequence=1
* Goel, Sakallah. Model Checking of Verilog RTL using IC3 with Syntax-guided Abstraction. 2019. https://aman-goel.github.io/publications/goel2019model_preprint.pdf

Hardware verification.
The thesis introduces a few techniques, but the most relevant is _equality abstraction_, which extends IC3.
The idea is to look at the system's initial predicate, transition relation and property to prove, and collect all of the subterms.
The abstract representation is the set of equivalence classes of all of the subterms.
So, for example, the abstract representation could know that `u + v` and `v + 1` are in the same equivalence class, but doesn't care so much about the concrete values of u and v.
The high-level idea of taking interesting subterms and treating them abstractly sounds nice, but I'm still pretty hazy on the details.
It's not clear to me which part of the implementation performs it either https://github.com/aman-goel/avr.
It might be necessary to work through the previous predicate abstraction papers first to really understand what's going on here.

In the paper, they refer to this technique as syntax-guided abstraction, while the thesis referres to it as equality abstraction.
The name equality abstraction was chosen to place emphasis on the concept of equivalence classes.

* Lee, Sakallah. Unbounded scalable verification based on approximate property-directed reachability and datapath abstraction. 2014. https://link.springer.com/content/pdf/10.1007/978-3-319-08867-9_56.pdf

The basic idea is to treat datatypes such as words abstractly, translating concrete operations like `x + y` to abstract operations using uninterpreted function applications such as `ADD(\hat{x}, \hat{y})`.
Then when you run IC3 on this abstracted version, it will generate a spurious counterexample because it doesn't know about the semantics of `ADD`.
You use this counterexample to generate new lemmas about the real addition operation and apply them to `ADD`.
You repeat this process until the IC3 no longer finds any counterexamples.

I'm still confused about the details though.
I don't think there's enough detail here to reconstruct the algorithm.
I can't find the implementation of this first version of Averroes either.

## ICE

* Garg, Löding, Madhusudan, Neider. ICE: a robust framework for learning invariants. 2014. https://link.springer.com/chapter/10.1007/978-3-319-08867-9_5
* Garg, Neider, Madhusudan, Roth. Learning invariants using decision trees and implication counterexamples. 2016. https://dl.acm.org/doi/pdf/10.1145/2914770.2837664

ICE is a black-box "learning-based" invariant generation technique.
The technique uses two processes: the learner which cannot see the program or the property being verified but can suggest candidate invariants, and the teacher which can see the program and check the learner's candidates.
After checking a candidate, the teacher gives feedback to the learner which are concrete states that the invariant should handle differently.
The feedback characterises states as either examples, which should be accepted by the invariant but aren't; counterexamples, which should not satisfy the invariant; or _implications_, which are counterexamples-to-induction.
The key of ICE is treating the counterexamples-to-induction differently; previous learning-based techniques made an arbitrary choice of whether to treat counterexamples-to-induction as positive examples or negative counterexamples.

The claim is that the black-box learning-based approach is able to find better, simpler invariants.

## Interpolation

A Craig interpolant is some predicate that "sits in between" two other predicates.
If you have `A => B`, then there is some formula \psi such that `A => \psi` and `\psi => B`.
Many logical theories have procedures to generate interpolants; some SMT solvers can generate them.

For model checking, if you are trying to inductively prove some property `\phi` and you find a counterexample-to-induction `s`, then you could strengthen your property to be `\phi /\ ~s`.
This strengthening isn't very useful if there are lots of states.
Interpolation can help generalise the counterexample by finding an interpolant `\psi` between `s => ~\phi` such that `s => \psi` and `\psi => ~\phi`.
Then you can strengthen the property to `\phi /\ ~\psi`.

* Reynolds, Tinelli, Hadarean. Certified interpolant generation for EUF. 2011 https://homepage.cs.uiowa.edu/~tinelli/papers/ReyTH-SMT-11.pdf

Paper describes a method to generate interpolants for quantifier-free formulae over uninterpreted functions.
Not directly relevant to model checking, didn't read too closely.

# Liveness properties

* Wei, Li. NKind: a model checker for liveness property verification on Lustre programs. 2022. http://ksiresearch.org/seke/seke22paper/paper089.pdf

Checks liveness properties that are eventually true.
Counterexamples are interesting: as a counterexample is an infinite trace, they represent counterexamples as traces with loops.

The paper doesn't really motivate why you'd want liveness properties.
Most real-time reactive systems really want bounded liveness, which is a safety property.

# Composition

Larraz, Tinelli. Realizability checking of contracts with Kind2. 2022, draft. https://arxiv.org/pdf/2205.09082.pdf

Given an imported node with a contract, does there exist a node that actually satisfies the contract?

Uses quantifier elimination to encode realizability check.


# Bigger picture
## Tool qualification and certification

* Wagner, Mebsout, Tinelli, Cofer, Slind. Qualification of a model checker for avionics software verification. 2018. https://homepage.cs.uiowa.edu/~tinelli/papers/WagEltAl-NFM-17.pdf

DO-178C and formal methods supplement DO-333.

Qualification is required for tools that eliminate or reduce any of the DO-178C processes and the output of the tool is not verified (eg not manually checked).

They describe a proof checker called Check-It that takes a certificate and checks it.
Kind2 generates two certificates:

1. PC: a proof certificate that provides evidence that the safety properties are invariant; and
2. FEC: a front-end certificate that provides evidence that the SMT embedding of the input program agrees with an independent tool.

They use CVC4 to generate the detailed proof certificates.

## Requirements

* Giannakopoulou, Pressburger, Mavridou, Rhein, Schumann, Shi. Formal requirements elicitation with Fret. 2020. https://ntrs.nasa.gov/api/citations/20200001989/downloads/20200001989.pdf

Tool for describing requirements in a English-like language with clear semantics.
Generates interactive simulator for some states from the requirements.

# Other stuff

Remaining techniques to read about.

## Lemma tightening
What does this mean?

## One-state vs two-state invariant generation
Kind2 talks about doing invariant generation for one-state vs two-state.
One-state means generating invariants that only look at the current state, eg `state0.x <= state0.y`.
Two-state means generating invariants that look at two consecutive states, eg `state0.x <= state1.x`.