# Input program
```
node f(e: int):
  subnode g(e):
    subnode lastn(10, e):
      count     = if e then pre_count + 1 else 0
      pre_count = 0 -> pre count
      out       = count >= 10

    ok = nondet
    guarantee lastn.out implies ok

  subnode lastn(20, e):
    count     = if e then pre_count + 1 else 0
    pre_count = 0 -> pre count
    out       = count >= 20

  ok = g.ok
  property lastn.out implies ok
```

## Bindings:
```
g.e = e
g.lastn.e = g.e
g.lastn.count = if e then g.lastn.pre_count + 1 else 0
g.lastn.pre_count = 0 -> pre g.lastn.count
g.lastn.out = g.lastn.count >= 10

g.guarantee = g.lastn.out implies g.ok

lastn.e = e
lastn.count = if e then lastn.pre_count + 1 else 0
lastn.pre_count = 0 -> pre lastn.count

ok   = g.ok
prop = lastn.out implies ok
```

## Equivalence graph
Start with the simple equivalence graph:
```
e = g.e = g.lastn.e = lastn.e
ok = g.ok

g.lastn.count = if e then g.lastn.pre_count + 1 else 0
g.lastn.pre_count = 0 -> pre g.lastn.count
g.lastn.out = g.lastn.count >= 10

g.guarantee = g.lastn.out implies ok

lastn.count = if e then lastn.pre_count + 1 else 0
lastn.pre_count = 0 -> pre lastn.count

prop = lastn.out implies ok
```

It's not clear that g.lastn.count = lastn.count. The structure is the same but
the variables are different, and the mutual recursion means that we can't just
substitute one for the other. We really want a way to specify them that doesn't
involve names at all, so we define recursive mu binders with de bruijn indices.
The term `µ. 0 -> pre µ0` is short for `let x = 0 -> pre x in x`.
```
e ::= µ. e | µ0 | µ1 | µ2...
```

We need to take the named representation and rewrite it to use recursive terms.
One problem is that there are many different ways to convert the named recursion
to recursive terms. For the count above, we could write it as:
```
count = µ. if e then (0 -> pre µ0) + 1 else 0
count = if e then (µ. (0 -> pre (if e then µ0 else 0)) + 1) else 0
count = if e then ((µ. 0 -> pre (if e then µ0 + 1 else 0)) + 1) else 0
count = if e then ((0 -> (µ. pre (if e then (0 -> µ0) + 1 else 0))) + 1) else 0
```

We want to take advantage of the fact that these are all equivalent, but if we
added them all to the equivalence graph, we'd get bogged down in all the
different ways to write it.
We could look at the list of bindings related to `lastn.count`, which is just
`lastn.count` and `lastn.pre_count`, and just choose one of those to decide
where to insert the µ, but it's not very satisfying. The names and the bindings
don't really have any semantic meaning to latch on to. (???)

Idea: use `pre` to select where to introduce recursion. All causal cycles must
include at least one `pre`.
The choice here seems a bit like selecting a loop breaker in optimising mutually
recursive functions (worker/wrapper?).
If a recursive binding has multiple pres, we can just probably insert them
everywhere.
```
 rules for introducing and removing recursion (pre=>µ):
  pre e = µ. pre e[pre e := µ0]   if (pre e) in fv(e)
```
For any equivalence class with representation `pre e`, if `e` refers back to the
class (directly or indirectly), then introduce a recursive binder (😺).

We need to define substitution on equivalence classes. This goes deep inside
bindings, recursively applying the substitution to all members of the
equivalence class. Equivalence substitution is a meta-operation.
Substitution has the form `class[class := term]` or `class[class := class]`:
```
for equivalence class k, k', term e,
  k[k  := e] = canonical(e)
  k[k' := e] = k if k' not in fv(k)
  k[k' := e] =
   merge(
    for (f(k0, ..., kn)) in k.nodes:
      f(k0[k' := e], ..., kn[k' := e]))
```
(does this terminate?)
(we also need to lift the substitutand when substituting into µ binders, eg `(µ. µ0 + x)[x := µ0]` simplifies to `(µ. µ0 + µ1)`)

Applying the pre=>µ rewrite gives the following (intermediate equations are intermediate steps in the substitution, but are not added as rewrites):
```
pre g.lastn.count
  = µ. pre g.lastn.count[pre g.lastn.count := µ0]
  = µ. pre (if e then g.lastn.pre_count[pre g.lastn.count := µ0] + 1 else 0)
  = µ. pre (if e then (0 -> µ0) + 1 else 0)

pre lastn.count
  = µ. pre lastn.count[pre lastn.count := µ0]
  = µ. pre (if e then (0 -> µ0) + 1 else 0)
```

With these extra equivalences, we have the following equivalence classes:

```
e  = g.e = g.lastn.e = lastn.e
ok = g.ok

g.lastn.count = lastn.count = if e then g.lastn.pre_count + 1 else 0
g.lastn.pre_count = lastn.pre_count = 0 -> pre_lastn_count
pre_lastn_count = pre g.lastn.count = µ. pre (if e then (0 -> µ0) + 1 else 0)
g.lastn.out = g.lastn.count >= 10
lastn.out   = g.lastn.count >= 20

g.guarantee = g.lastn.out implies ok

prop = lastn.out implies ok
```

From these equivalences alone it's pretty clear that if we assume `(g.lastn.out = g.lastn.count >= 10) implies ok`, then we can show `(lastn.out = g.lastn.count >= 20) implies ok`.
But for programs with clocks it's not always clear how to express them as equivalence graphs.
(Is this true? Maybe it's not so bad.)
Rather than proving the property directly on the equivalence graph, we just use the equivalence graph for generating invariants.
That way, if the equivalence graph is missing some bindings (like nodes with complex clocks) then we'll get a smaller set of invariants, but we can still prove properties about the whole program.

So we can extract some invariants from this:
```
invariant g.lastn.count     = lastn.count
invariant g.lastn.pre_count = lastn.pre_count
```

These aren't both strictly necessary - we only need one.
How do we find the minimum set of invariants?

An alternative would be to modify the transition-system translation to directly use the equivalence classes, but that would make these equivalence classes part of the trusted base.
If we just use these to generate invariants, then we can then prove them separately without trusting this analysis.

Greedy invariant extraction:
```
initialise e-graph G0 with base expressions from the program
apply base rewrites to G0 such as trivial mathematical identities
copy G0 into a new e-graph G
insert µ bindings to G: pre e = pre (µ. e[pre e := µ0])
apply rewrites to G such as pre distributivity, etc, up to saturation
for each equivalence class c in G:
  for nodes n,m in c:
    if G0.class(n) != G0.class(m) then:
      record invariant n = m
      merge n, m in G0
      rebuild congruence relation in G0
```

This process will record only the invariants that are not direct consequences of previous invariants and the mathematical identities that we expect the SMT solver to already know about.
However, this will include invariants about µ-recursive bindings, which the SMT translation doesn't know about.
We should filter out nodes that include µ-bindings as well as favouring simple invariants like `g.lastn.count = lastn.count` which only refer to terms that are already part of the program.

## Equivalence relation

The rewrite `pre (x + 1) = (pre x) + 1` is morally right but is not strictly true for the non-deterministic encoding of uninitialised `pre` expressions.
For expressions with only guarded pres it is always true.
For `pre` expressions where the sub-expression is guarded, they are equal after the first step, but not necessarily on the first step.
We can rewrite it to ignore the first step as:
```
true -> pre (x + 1) = (pre x) + 1
```

We need to be careful about the definition of the equivalence relation, because element-wise equality in the language doesn't satisfy `undefined = undefined`.
(The practical reason we don't have this is that the SMT encoding encodes undefined as non-deterministic values.)
So we define the equivalence relation as something like:
```
x =_e y := forall i. (undefined x(i) /\ undefined y(i)) \/ x(i) = y(i)
```

Now, if we know that `pre (x + 1) =_e (pre x) + 1`, and we also know that `pre (x + 1)` is defined everywhere after the first step, then together these properties imply that any values after the first step are equal (in the in-language element-wise equality): `true -> pre (x + 1) = (pre x) + 1`.

If we know that certain streams are well-defined everywhere, then we don't need the `true -> _` prefix.
But it's sound to have the prefix even for well-defined streams because `x = y` implies `true -> x = y`.
Intuitively, it doesn't seem like it should make the invariants weaker in practice, or harder to prove, because it should be obviously true in the initial step anyway.

## Interaction with pre-sinking and arrow-floating
Given the input term:
```
pre_count = 0 -> pre (if e then pre_count + 1 else 0)
```

We can push pre inwards or float arrow outwards.
Pushing pre inwards:
```
pre_count = 0 -> if (pre e) then pre(pre_count + 1) else 0
          = 0 -> if (pre e) then pre(pre_count) + 1 else 0
```
Floating arrow outwards:
```
pre_count = 0 -> pre (if e then (0 -> pre (if e then pre_count + 1 else 0)) + 1 else 0)
          = 0 -> pre (if e then 1 -> (pre (if e then pre_count + 1 else 0) + 1) else 0)
          = 0 -> pre ((if e then 1 else 0) -> (if e then pre (if e then pre_count + 1 else 0) else 0))
```
Or do a bit of both:
```
pre_count = 0 -> if (pre e) then pre(1 -> (pre (if e then pre_count + 1 else 0))) else 0
```

Altogether we have 6 unique terms which we could µ-insert, but only 3 are in "pre-arrow" `pre(e -> e')` form.
Let's just µ-insert those three.
```
pre_count
          = 0 -> if (pre e) then pre(pre_count) + 1 else 0
          = 0 -> if (pre e) then pre (µ. pre_count[pre(pre_cound) := µ0]) + 1 else 0
          = 0 -> if (pre e) then pre (µ. (0 -> if (pre e) then (pre µ0) + 1 else 0)) + 1 else 0

          = 0 -> pre ((if e then 1 else 0) -> (if e then pre (if e then pre_count + 1 else 0) else 0))
          = 0 -> pre (µ. (if e then 1 else 0) -> (if e then pre (if e then (0 -> pre µ0) + 1 else 0) else 0))

          = 0 -> if (pre e) then pre(1 -> (pre (if e then pre_count + 1 else 0))) else 0
          = 0 -> if (pre e) then pre(µ. 1 -> (pre (if e then (0 -> if (pre e) then pre µ0 else 0) + 1 else 0))) else 0
```

This creates a number of µ-recursive copies which is linear in the height of the recursive binding.
Is there any way around this?
For now, just perform µ-insertion at all pres before performing pre-sinking.

## References

* Synthesising mathematical identities with e-graphs. Briggs, Panchekha. EGRAPHS 2022
https://arxiv.org/pdf/2206.07086.pdf

Applies rewrites to an e-graph to find rewrites. Then uses a second e-graph with some definitions hidden on purpose to filter out the boring equalities that are true of all possible functions.
Uses ILP to find minimal set of rewrites.