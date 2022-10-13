# Stuff to do eventually

## Mistakes

### Bounded arithmetic
#### Sort.ArbitraryInteger vs Sort.BoundedInteger, bounded prims
#### Boxing/unboxing integers is confusing and opposite, makes generating expressions more complicated than necessary.

Probably each numeric prim should probably take a Num type specifying what precision it works on.

#### Overflow checks occur for operations inside false conditionals
See lack.examples.bug.IntegerOverflow.

An expression like `if x > 0 then x - 1 else 0` is obviously safe, but if you put streaming operators inside the conditions it gets a bit subtle.

### SMT.Translate
* SMT.Translate should use node.Node instead of node.Builder
* SMT.System should use term.Exp with a separate Exp->SMTLib step


### Core language: merge => match
Change the "merge" construct in nodes to match on small types.
This will make it easier to bake the clocks later and simplify some of the codegen.

## Missing features

### Expressions missing source location
Source location should be available everywhere.

### Core language: local variables in nested contexts
Maybe nested contexts should be able to declare local variables. Might simplify some checks.

### `Const[T]` and top-level constants

Currently all top-level constants get substituted into the program.
Core langauge should allow top-level definitions and source langauge could refer to them as `Const[T] extends Stream[T]`.

### Sneaky invariants:
Add a check that a node only refers to explicit outputs of its subnodes.
I want two "sneaky modes" that let you dig into the guts.
One just disables the output-only check for that reference, the other allows a DOM-style tree search for references.

Suppose the following invariant fails the outputs check because you're touching a non-output variable:
```
val lastn = LastN(5, e)

check() {
  lastn.count <= 5
}
```

Then you would instead say:
```
check() {
  sneaky(lastn.count) <= 5
}
```

Or with the DOM-style reference:
```
check() {
  sneaky.node("LastN").variable[UInt32]("count") <= 5
}
```
