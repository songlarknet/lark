# Lack

Lack wants to be a Scala EDSL for writing real-time reactive control systems.
The programmer can specify _safety properties_ that all executions of the system should satisfy, and these properties are verified via model checking.
The system can then be compiled to executable C code.

The language is very similar to a cut-down version of Lustre.
The idea is that having Scala as the meta-language will make it easy to write larger programs, without needing too many fancy language support.
Features like polymorphism or templates come for free, and generating lookup tables programmatically should be straightforward.

## Roadmap

What is the bare minimum feature set that is required to be useful?

Required features for V0:
* simple types: fixed-width integer types, booleans;
* model checking: K-induction and path compression;
* compilation to C: simplest-possible "monolithic" compilation.

In the air:
* contracts and modular verification;
* compound types: structs;
* overflow checks for arithmetic.

It's not clear whether simple k-induction will scale to "useful-sized" programs, so we might need contracts to begin with.
Structs would be convenient, especially for calling the generated C code, but I don't think they're necessary for adding structure to the source program; meta-level structs should suffice.
Overflow checks would be good, but int operations in Kind2 don't have them anyway so they could probably wait.

Later:
* automata;
* better compilation (modular rather than monolithic);
* pure stream transformers: so node applications with same arguments are definitionally equal.

## Other systems

There are many systems trying to do similar things.
None of them quite solve the same problems that Lack aims to solve.

## Licence

Non-commercial / evaluation licence, with secondary commercial licence?
Similar to CompCert:
https://raw.githubusercontent.com/AbsInt/CompCert/master/LICENSE
