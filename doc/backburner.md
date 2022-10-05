# Stuff to do eventually

## Core language: merge => match
Change the "merge" construct in nodes to match on small types.
This will make it easier to bake the clocks later and simplify some of the codegen.

## Core language: local variables in nested contexts
Maybe nested contexts should be able to declare local variables. Might simplify some checks.

## Sneaky invariants:
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
