# Talk at Synchron22: invariant extraction with e-graphs

Hi, I'm Amos Robinson.
I'm from Sydney, Australia.

I'm going to talk about extracting invariants from Lustre programs using equivalence graphs.
The invariants are the nectar, and the chickadee is the equivalence graph.

## Usage of synchronous languages at an autonomous vehicle startup

I previously worked at an autonomous vehicle startup, which Kai has talked about before.

### Happy days
* Implemented controllers, drivers, state machines in Lustre
* Proved some reassuring properties about programs
* Executed them in the car
* They worked first time (more or less)

### Went with open-source
We decided to use a mostly open-source toolchain:

* Kind2
* Heptagon
* …and a small internal tool to go from Kind2 to Heptagon

### Experience with Kind2

Kind2 is generally great:
* solid for small programs
* actively developed
* helpful, friendly developers

but as our programs got bigger…
* became hard to predict whether a property will be provable
* modifications became difficult and could require serious restructuring
* spurious failures in CI make us look flaky

## When you can't prove what you want

We can't always prove what we want, even if it's true.

There was one particular class of properties that we had issues with.
Suppose we have a controller that checks if an input signal coming from the outside world is "good".
There are a bunch of criteria for what constitutes a good signal, but one criterion is that the delta
has to be below some threshold for the last ten samples or something.

We'll use the `lastn` node, which takes a predicate and some integer `n`, and returns true if the predicate has been true for the last `n` ticks.
```
node lastn(const n: int; pred: bool)
returns (out: bool)
let
  count = if pred then (0 -> pre count) + 1 else 0;
  out   = count >= n;
tel
```

The `lastn` node has some internal state for its counter, and it returns a stream of booleans.


We'll use `lastn` to implement `signal_valid`, which checks if the signal is good.
Here is a small part of the contract, with the implementation hidden:

```
function delta_valid(input1: int, input2: int)
returns (ok: bool)
let
  ok = abs(input1 - input2) <= DELTA_MAX
tel

node signal_valid(input: int)
returns (ok: bool)
(*@contract
  guarantee
    not lastn(10, delta_valid(input, 0 -> pre input)) =>
    not ok;
  ...
*)
```

The contract says that the signal is not OK if the last 10 inputs are not OK.

Let's suppose that we use `signal_valid` in the main node to determine whether the system is engaged or not:

```
function delta_valid(input1: int, input2: int)
returns (ok: bool)
let
  ok = abs(input1 - input2) <= DELTA_MAX
tel

node signal_valid(input: int)
returns (ok: bool)
(*@contract
  guarantee
    not lastn(10, delta_valid(input, 0 -> pre input)) =>
    not ok;
  ...
*)
type SAMPLE       = { adc: int; ... }
const SAMPLE_ZERO = { adc  = 0; ... }

node main(sample: SAMPLE)
returns (engaged: bool; ...)
(*@contract
  guarantee
    not lastn(10, delta_valid(sample.adc, (SAMPLE_ZERO -> pre sample).adc)) =>
    not engaged;
*)
let
  engaged = signal_valid(sample.adc);
  ...
tel
```

We've really just restated the guarantee from `signal_valid` at a higher level, so it's conceptually a pretty simple property.


### Pen-and-paper proof
How about we try to prove the property in `main` on paper.
In our proof, we're going to assume that the `input_vaild` subnode's contract has been proven separately.
Let's start by unfolding the contract and substituting the arguments into it:

```
assume
  signal_valid.guarantee[input := sample.adc, ok := engaged]:
    not lastn(10, delta_valid(sample.adc, 0 -> pre sample.adc)) =>
    not engaged;

  engaged = signal_valid(sample.adc);
```

We also know something about the value of `SAMPLE_ZERO`, so we'll write that down in our proof context too.

```
assume
  signal_valid.guarantee[input := sample.adc, ok := engaged]:
    not lastn(10, delta_valid(sample.adc, 0 -> pre sample.adc)) =>
    not engaged;

  engaged = signal_valid(sample.adc);

  SAMPLE_ZERO = { adc = 0; ... };
```

So these form our hypotheses.
Next, let's write down our proof goal.
We'll separate the hypotheses and the goal with a line to give a "natural deduction" feel.
The exact proof system doesn't matter too much, I just want to get an intuition for how we might prove it.

```
assume
  signal_valid.guarantee[input := sample.adc, ok := engaged]:
    not lastn(10, delta_valid(sample.adc, 0 -> pre sample.adc)) =>
    not engaged;

  engaged = signal_valid(sample.adc);

  SAMPLE_ZERO = { adc = 0; ... };
---------------------------------------------------------------------
show main.guarantee:
  not lastn(10, delta_valid(sample.adc, (SAMPLE_ZERO -> pre sample).adc)) =>
  not engaged;
```

We can almost use the assumption as-is, except that the second argument to `delta_valid` doesn't quite match.
They both talk about the previous sample, but one extracts the `.adc` field inside the delay, and the other extracts the field outside of the delay.
We'll have to do some book-keeping to get it to match, but because Lustre is an applicative / pure language, equational reasoning is pretty straightforward.

```
assume
  signal_valid.guarantee[input := sample.adc, ok := engaged]:
    not lastn(10, delta_valid(sample.adc, 0 -> pre sample.adc)) =>
    not engaged;

  engaged = signal_valid(sample.adc);

  SAMPLE_ZERO = { adc = 0; ... };
---------------------------------------------------------------------
show main.guarantee:
  not lastn(10, delta_valid(sample.adc, (SAMPLE_ZERO -> pre sample).adc)) =>
  not engaged;


rewrite prim_distributes_arrow: forall stream e e', pure function f.
  f (e -> e') = (f e) -> (f e')
```

To massage the goal to look like the assumption, we want to somehow push the field access down deeper into the expression.
Let's try rewriting with the fact that primitive applications distribute over arrow.

```
assume
  signal_valid.guarantee[input := sample.adc, ok := engaged]:
    not lastn(10, delta_valid(sample.adc, 0 -> pre sample.adc)) =>
    not engaged;

  engaged = signal_valid(sample.adc);

  SAMPLE_ZERO = { adc = 0; ... };
---------------------------------------------------------------------
show main.guarantee:
  not lastn(10, delta_valid(sample.adc, SAMPLE_ZERO.adc -> (pre sample).adc)) =>
  not engaged;


rewrite prim_distributes_arrow: forall stream e e', pure function f.
  f (e -> e') = (f e) -> (f e')
with f := _.adc, e := SAMPLE_ZERO, e' := pre sample:
  (SAMPLE_ZERO -> pre sample).adc = SAMPLE_ZERO.adc -> (pre sample).adc
```

So we've pushed the field accesses inside the arrow.

```
assume
  signal_valid.guarantee[input := sample.adc, ok := engaged]:
    not lastn(10, delta_valid(sample.adc, 0 -> pre sample.adc)) =>
    not engaged;

  engaged = signal_valid(sample.adc);

  SAMPLE_ZERO = { adc = 0; ... };
---------------------------------------------------------------------
show main.guarantee:
  not lastn(10, delta_valid(sample.adc, SAMPLE_ZERO.adc -> (pre sample).adc)) =>
  not engaged;


rewrite prim_distributes_pre: forall stream e, pure function f.
  f (pre e) = pre (f e)
```

We can continue pushing the field access down into the `pre` because primitives also distribute over pre, just as they do for arrow.
Let's apply the rewrite.

```
assume
  signal_valid.guarantee[input := sample.adc, ok := engaged]:
    not lastn(10, delta_valid(sample.adc, 0 -> pre sample.adc)) =>
    not engaged;

  engaged = signal_valid(sample.adc);

  SAMPLE_ZERO = { adc = 0; ... };
---------------------------------------------------------------------
show main.guarantee:
  not lastn(10, delta_valid(sample.adc, SAMPLE_ZERO.adc -> pre sample.adc)) =>
  not engaged;


rewrite prim_distributes_pre: forall stream e, pure function f.
  f (pre e) = pre (f e)
with f := _.adc, e := sample
  (pre sample).adc = pre sample.adc
```

Finally, we just need to simplify the `SAMPLE_ZERO.adc` to replace it with `0`.

```
assume
  signal_valid.guarantee[input := sample.adc, ok := engaged]:
    not lastn(10, delta_valid(sample.adc, 0 -> pre sample.adc)) =>
    not engaged;

  engaged = signal_valid(sample.adc);

  SAMPLE_ZERO = { adc = 0; ... };
---------------------------------------------------------------------
show main.guarantee:
  not lastn(10, delta_valid(sample.adc, 0 -> pre sample.adc)) =>
  not engaged;

unfold SAMPLE_ZERO, constant propagation
```

Our goal directly matches the thing we know about the `signal_valid`, so we can just use the assumption.

```
assume
  signal_valid.guarantee[input := sample.adc, ok := engaged]:
    not lastn(10, delta_valid(sample.adc, 0 -> pre sample.adc)) =>
    not engaged;

  engaged = signal_valid(sample.adc);

  SAMPLE_ZERO = { adc = 0; ... };
---------------------------------------------------------------------
show main.guarantee:
  not lastn(10, delta_valid(sample.adc, 0 -> pre sample.adc)) =>
  not engaged;

assumption signal_valid.guarantee
```

### Kind2 proof
Unfortunately, the job's a bit harder for Kind2.
While it was easy to prove on our nice high-level applicative semantics, Kind2 does all of its proofs on a labelled transition system semantics, which is a bit closer to an imperative semantics.

Transition systems have a state type, which defines the internal state of the system, as well as an initial predicate that defines the starting state, and a step relation that defines how the system progresses over time.

<!-- Here is the transition system for the `lastn` node:

```
node lastn(const n: int; pred: bool)
returns (out: bool)
let
  count = if pred then (0 -> pre count) + 1 else 0;
  out   = count >= n;
tel

==>

lts lastn:
  type state = { pre_count: int; init: bool; }

  init(s: state): bool =
    s.init == true

  step(s: state, n: int, pred: bool): (state * bool) =
    let
      pre_count    = if s.init then 0 else s.pre_count
      count        = if pred then pre_count + 1 else 0
      out          = count >= n
    in
      ({ init = false; pre_count = count }, out)
``` -->

The first part of our pen-and-paper proof was proving that the two arguments in both calls to `delta_valid` were equivalent, so let's focus on that small part of the transition system first:

```
node delta_valid_sample(sample: SAMPLE)
returns (delta_main: bool, delta_signal: bool)
let
  delta_main   = delta_valid(sample.adc, (SAMPLE_ZERO -> pre sample).adc);
  delta_signal = delta_valid(sample.adc, 0 -> pre sample.adc);
tel

==>

lts delta_valid_sample:
  type state = { init:         bool;
                 delay_main:   SAMPLE;
                 delay_signal: int; };

  init(s: state): bool =
    s.init == true;

  step(s: state, sample: SAMPLE): (state * bool * bool) =
    let
      delay_main                        = if s.init then SAMPLE_ZERO else s.delay_main
      delta_main                        = delta_valid(sample.adc, delay_main.adc)

      delay_signal                      = if s.init then 0 else s.delay_signal
      delta_signal                      = delta_valid(sample.adc, delay_signal)

    in
      ({ init           = false;
         delay_main     = sample;
         delay_signal   = sample.adc },
         delta_main, delta_signal)
```

Although our Lustre program is deterministic and pure, the init predicate is non-deterministic: it identifies a set of states instead of a single state.

The real transition system that Kind2 uses would have a relation for `step` rather than a function, because it can be non-deterministic too, but for this example it's a bit cleaner to only look at deterministic step functions.

The translation itself is fairly straightforward: it really just rearranges things and teases them apart.
Whereas in the source program we can talk about a stream as a single expression, such as `0 -> pre sample.adc`, in the transition system this gets split into a bunch of different places.

<!-- slides: highlight one expression in lustre, and highlight parts of that expression in the transition system -->

So, while we were able to perform local reasoning before to learn that the two deltas are equivalent, it's less obvious on the transition system.
In this case it becomes clear if we unroll the step relation twice, which is basically what k-induction does.

```
node delta_valid_last2(delta_ok: bool)
returns (last_main: bool, last_signal: bool)
let
  last_main   = lastn(10, delta_ok);
  last_signal = lastn(10, delta_ok);

tel

==>

lts delta_valid_last2:
  type state = { last_main:   lastn.state;
                 last_signal: lastn.state; };

  init(s: state): bool =
    lastn.init(s.last_main) and lastn.init(s.last_signal);

  step(s: state, delta_ok: bool): (state * bool * bool) =
    let
      (state_last_main',   last_main)   = lastn.step(s.last_main,   10, delta_ok)
      (state_last_signal', last_signal) = lastn.step(s.last_signal, 10, delta_ok)
    in
      ({ init        = false;
         last_main   = state_last_main';
         last_signal = state_last_signal' }, last_main, last_signal)
```

Here we have two invocations of `lastn` with identical arguments translated to a transition system.
It's obvious here that the two calls take the same arguments, other than the state, but it's not obvious whether the states are the same or not.
Just like the init predicate we saw earlier, `lastn`'s init predicate describes a set of states, rather than one specific state.
The non-determinism and the state mean that we can't just perform a local rewrite with equational reasoning to show that the two `lastn` invocations return the same result.

Instead, we need to prove it inductively, which requires a stronger induction hypothesis.
(We could also prove it by performing k-induction with k=10, but that requires unfolding the step relation ten times, which results in a fairly large problem.)

```
node delta_valid_last2(delta_ok: bool)
returns (last_main: bool, last_signal: bool)
let
  last_main   = lastn(10, delta_ok);
  last_signal = lastn(10, delta_ok);
  --%PROPERY ??? = ???;
tel

==>

lts delta_valid_last2:
  type state = { last_main:   lastn.state;
                 last_signal: lastn.state; };

  init(s: state): bool =
    lastn.init(s.last_main) and lastn.init(s.last_signal);

  step(s: state, delta_ok: bool): (state * bool * bool) =
    let
      (state_last_main',   last_main)   = lastn.step(s.last_main,   10, delta_ok)
      (state_last_signal', last_signal) = lastn.step(s.last_signal, 10, delta_ok)
    in
      ({ init        = false;
         last_main   = state_last_main';
         last_signal = state_last_signal' }, last_main, last_signal)
      --%PROPERTY state_last_main' == state_last_signal'
```

It's fairly easy to state the invariant we need on the transition system: the two states must be equal.
If we use this property as our induction hypothesis, then the two output booleans will be equivalent by congruence.
But here's the rub: we can't state that property in the original Lustre program.
We can't refer to the internal state of the lastn invocations because there's no way to refer to a specific invocation, and there's also no way to look into its internal state.

Kind2 resolves this by doing automatic invariant generation.
It runs a few invariant generation algorithms -- IC3 and template-based invariants instantiation -- concurrently with the main proof work.

Unfortunately, it's difficult to predict whether the invariant generation will find the right invariant.
IC3 uses counterexamples from the SMT solver to generate candidate invariants, which isn't necessarily deterministic.
Template-based invariant instantiation has to look through a large search space of possible candidates too, and the order in which the space is searched isn't clear from the source program.

Altogether, it can be hard to know whether Kind2 will be able to prove a problem.
Small, seemingly-local changes can affect the provability of far-away properties.
Even just rerunning the proofs on the same computer can be unpredictable.

This unpredictability can be doubly frustrating: not only is the property obvious on the source language semantics, but we also know exactly the extra invariant we need to make the induction go through.
We just can't write it down.

### Two problems:
The problems we face are:

* invariants that are obvious on the "applicative" semantics aren't obvious on the transition system; and
* we can't tell Kind2 about the invariants we know

## What we can prove

Property space diagram:
* trivial properties: the SMT solver is good at these things and can always prove them. eg `x + y = y + x`
* k-inductive properties: we can (almost) always prove these for low k, but becomes harder as k gets bigger
* IC3 and template-based invariant generation: we can usually prove these, but it gets a bit blurry as our program gets bigger

We'd like to add a new class to our property space.
The new class describes "applicative properties":

* applicative properties: properties that are clear from the high-level semantics, but maybe not from LTS

The goal is that, ideally, this will be a relatively well-defined set, and we will be able to reliably generate the invariants in that set.

### Invariant extraction with e-graphs

The high-level idea is to use the equational rewrites to generate our invariants.
Basically:
* convert node to e-graph, including instantiating any subnodes
* apply the applicative rewrites
* extract interesting invariants from the e-graph

### Concrete

So let's try to apply this to our `lastn` problem.

First, we normalise the program.
It's important that all of the state variables like `pre`s have names so that we can refer to them, so we pull them up to top-level bindings.
Subnode invocations are also brought up to top-level bindings.
```
node signal_valid(input: int)
(*@contract guarantee not last.out => not ok; *)
  ok            : bool;
  pre_input       = pre input;
  del_input       = 0 -> pre_input;
  subnode last    = lastn(10, delta_valid(input, del_input))

node main(sample: SAMPLE)
(*@contract guarantee not last.out => not engaged; *)
  pre_sample      = pre sample;
  del_sample      = SAMPLE_ZERO -> pre_sample;
  subnode valid   = signal_valid(sample.adc);
  subnode last    = lastn(10, delta_valid(sample.adc, del_sample.adc))
  engaged         = valid.ok;
```

An equivalence graph is essentially a set of equality constraints, and Lustre nodes are essentially a set of equality constraints too, so it's not too hard to translate unclocked nodes to an equivalence graph.
We really just need to instantiate each subnode by copying its equality constraints and substituting the actual arguments in.
We'll worry about nodes with interesting clocks later.
```
-- subnode valid = signal_valid(sample.adc)
-- guarantee not valid.last.out => not valid.ok;
  valid.pre_input = pre sample.adc;
  valid.del_input = 0 -> valid.pre_input;
  valid.last.out  = lastn(10, valid_delta(sample.adc, valid.del_input));

-- node main(sample)
-- guarantee not last.out => not engaged;
  pre_sample      = pre sample;
  del_sample      = SAMPLE_ZERO -> pre_sample;
  last.out        = lastn(10, delta_valid(sample.adc, del_sample.adc));
  engaged         = valid.ok;
```

We've left `lastn` and `delta_valid` uninstantiated for now as uninterpreted functions, but we'll deal with them in a bit.
We can now apply the same rewrites that we did in our proof, except because we're operating on an equivalence graph, we only add equivalence information, we never destructively update the graph.

We can apply some cool rewrites now.
How about: `forall e e'. (e -> e').adc = (e.adc -> e'.adc)`
```
-- subnode valid = signal_valid(sample.adc)
-- guarantee not valid.last.out => not valid.ok;
  valid.pre_input = pre sample.adc;
  valid.del_input = 0 -> valid.pre_input;
  valid.last.out  = lastn(10, valid_delta(sample.adc, valid.del_input));

-- node main(sample)
-- guarantee not last.out => not engaged;
  pre_sample      = pre sample;
  del_sample      = SAMPLE_ZERO -> pre_sample;


  last.out        = lastn(10, delta_valid(sample.adc, del_sample.adc));
  engaged         = valid.ok;

---------------------------------------------------------------------

rewrite prim_distributes_arrow: forall stream e e', pure function f.
  f (e -> e') = (f e) -> (f e')
```

rewrites to…

```
-- subnode valid = signal_valid(sample.adc)
-- guarantee not valid.last.out => not valid.ok;
  valid.pre_input = pre sample.adc;
  valid.del_input = 0 -> valid.pre_input;
  valid.last.out  = lastn(10, valid_delta(sample.adc, valid.del_input));

-- node main(sample)
-- guarantee not last.out => not engaged;
  pre_sample      = pre sample;
  del_sample      = SAMPLE_ZERO -> pre_sample;
  del_sample_adc  = del_sample.adc;
  del_sample_adc  = SAMPLE_ZERO.adc -> pre_sample.adc;
  last.out        = lastn(10, delta_valid(sample.adc, del_sample_adc));
  engaged         = valid.ok;

---------------------------------------------------------------------

rewrite prim_distributes_arrow: forall stream e e', pure function f.
  f (e -> e') = (f e) -> (f e')
with f := _.adc, e := SAMPLE_ZERO, e' := pre sample:
  (SAMPLE_ZERO -> pre sample).adc = SAMPLE_ZERO.adc -> (pre sample).adc
```

and the next rewrite…


```
-- subnode valid = signal_valid(sample.adc)
-- guarantee not valid.last.out => not valid.ok;
  valid.pre_input = pre sample.adc;
  valid.del_input = 0 -> valid.pre_input;
  valid.last.out  = lastn(10, valid_delta(sample.adc, valid.del_input));

-- node main(sample)
-- guarantee not last.out => not engaged;
  pre_sample      = pre sample;


  del_sample      = SAMPLE_ZERO -> pre_sample;
  del_sample_adc  = del_sample.adc;
  del_sample_adc  = SAMPLE_ZERO.adc -> pre_sample.adc;
  last.out        = lastn(10, delta_valid(sample.adc, del_sample_adc));
  engaged         = valid.ok;

---------------------------------------------------------------------

rewrite prim_distributes_pre: forall stream e, pure function f.
  f (pre e) = pre (f e)
```

becomes…

```
-- subnode valid = signal_valid(sample.adc)
-- guarantee not valid.last.out => not valid.ok;
  valid.pre_input = pre sample.adc;
  valid.del_input = 0 -> valid.pre_input;
  valid.last.out  = lastn(10, valid_delta(sample.adc, valid.del_input));

-- node main(sample)
-- guarantee not last.out => not engaged;
  pre_sample      = pre sample;
  pre_sample_adc  = pre sample.adc;
  pre_sample_adc  = (pre sample).adc;
  del_sample      = SAMPLE_ZERO -> pre_sample;
  del_sample_adc  = del_sample.adc;
  del_sample_adc  = SAMPLE_ZERO.adc -> pre_sample_adc;
  last.out        = lastn(10, delta_valid(sample.adc, del_sample_adc));
  engaged         = valid.ok;

---------------------------------------------------------------------

rewrite prim_distributes_pre: forall stream e, pure function f.
  f (pre e) = pre (f e)
with f := _.adc, e := sample
  (pre sample).adc = pre sample.adc
```

with a bit of constant folding, congruence and substitution, we can rewrite it to something like:

```
-- subnode valid = signal_valid(sample.adc)
-- guarantee not valid.last.out => not valid.ok;
  valid.pre_input = pre_sample_adc;
  valid.del_input = del_sample_adc;
  valid.last.out  = lastn(10, valid_delta(sample.adc, del_sample_adc));

-- node main(sample)
-- guarantee not last.out => not engaged;
  pre_sample      = pre sample;
  pre_sample_adc  = pre sample.adc;
  pre_sample_adc  = (pre sample).adc;
  del_sample      = SAMPLE_ZERO -> pre_sample;
  del_sample_adc  = del_sample.adc;
  del_sample_adc  = SAMPLE_ZERO.adc -> pre_sample_adc;
  del_sample_adc  = 0 -> pre_sample_adc;
  last.out        = lastn(10, delta_valid(sample.adc, del_sample_adc));
  engaged         = valid.ok;
```

which makes it pretty clear that the two `lastn` calls are equivalent.
So we know that `last.out = valid.last.out`, which is basically what we wanted to prove.
If we trusted all of our equivalence graph machinery and rewrites, we could just take this equality as an axiom and prove the rest of the system assuming that it's true.
But one of the great advantages of invariant generation techniques is that we don't have to trust them: they offer invariant candidates that we can independently check.
This equality isn't strong enough for the invariant we need, though, because it doesn't tell us that the two counts are equal.
We could add some smarts to the invariant extraction to know that if two invocations are congruent, then the internal state is also the same, but this is kind of unsatisfying because the set of properties that we can prove is not closed under inlining - we might lose knowledge by inlining a function.

### Diving into lastn

Instead, we'll unfold the definition of `lastn` and see what opportunities that exposes.
The definition of `lastn`, in normalised Lustre, is:

```
node lastn(const n: int; pred: bool)
  pre_count     = pre count;
  arr_count     = 0 -> pre_count;
  count         = if pred then arr_count + 1 else 0;
  out           = count >= n;
```

We can extract the equivalence graph from this as well by instantiating this twice, once inside main, and once inside signal_valid.
Let's focus on just this part of the equivalence graph:
```
-- subnode last = lastn(10, delta_valid(...))
  last.pre_count       = pre last.count;
  last.arr_count       = 0 -> last.pre_count;
  last.count           = if delta_valid(...)
                         then last.arr_count + 1
                         else 0;
  last.out             = last.count >= 10;

-- subnode valid.last  = lastn(10, delta_valid(...))
  valid.last.pre_count = pre valid.last.count;
  valid.last.arr_count = 0 -> valid.last.pre_count;
  valid.last.count     = if delta_valid(...)
                         then valid.last.arr_count + 1
                         else 0;
  valid.last.out       = valid.last.count >= 10;
```

We want to prove that `last.count = valid.last.count`, but it's not immediately clear from these equations.
They have the same structure, but they refer to different variables which aren't obviously equivalent either.
The variable names are getting in the way.
We want some "normalised" form where the names in the recursion don't affect equivalence.
```
  last.pre_count       = pre last.count;
  last.arr_count       = 0 -> last.pre_count;
  last.count           = if delta_valid(...)
                         then last.arr_count + 1
                         else 0;

==(rewrite recursive binding)=>

  last.count           = µ.
                         if delta_valid(...)
                         then (0 -> pre µ0) + 1
                         else 0;
```

Here, the mu binder form `µ. e` represents a recursive expression, where the de Bruijn mu variable `µ0` refers to the recursive value of the closest µ binder.

Once we do this "µ-normalisation" to both count variables, it becomes clear that they're equal, and we get some nice equalities:

```
-- subnode last = lastn(10, delta_valid(...))
  last.pre_count       = valid.last.pre_count
                       = pre last.count;
  last.arr_count       = valid.last.arr_count
                       = 0 -> last.pre_count;
  last.count           = valid.last.count
                       = if delta_valid(...)
                         then last.arr_count + 1
                         else 0;
                       = if delta_valid(...)
                         then valid.last.arr_count + 1
                         else 0;
                       = µ.
                         if delta_valid(...)
                         then (0 -> pre µ0) + 1
                         else 0;
  last.out             = valid.last.out
                       = last.count >= 10;
```

One neat side-effect of adding the µ-binders is that it works for invocations of `lastn` with different values of `n`.
So we can easily prove `lastn(20, e) => lastn(10, e)`.

> Describe invariant extraction on this example: there are lots of equalities but we don't want all of them.

### Extracting invariants
Idea:
* boring graph and interesting graph
* do boring rewrites (commutative, associative, constant folding) to both graphs
* do interesting rewrites (streaming ops, µ) to interesting graph
* find small terms that are equivalent only in interesting graph
* add to boring graph, do more rewrites

### Relationship to k-induction

It's not clear what the relationship to k-induction is, but I think they're complementary techniques.
Intuitively, some of the equalities we learn feel like what we learn from unfolding the step relation.
When we learnt that the two deltas were valid by rewriting the arrow and pre, it's a bit like learning from the 2-inductive step relation.
When we learnt that the two `lastn`s are equal, it's a bit like learning from the 10-inductive step relation.

But there are some cases where it's stronger than k-induction alone, like with `SoFar`:

```
node SoFar(pred: bool)
returns (out: bool)
let
  out = pred and (true -> pre out);
tel

---------------------------------------------------------------------
assume
  SoFar(X) => P

show
  SoFar(X) => P
```

This looks trivial, but k-induction alone can't get it because we have no invariant that the two instances of SoFar have the same state.

However, equivalence extraction isn't strictly stronger than k-induction, because there are almost certainly properties about inequalities that we won't pick up.

```
node countmod4()
returns (mod4: int)
let
  mod4 = 0 -> if pre mod4 = 3 then 0 else pre mod4 + 1;
  --%PROPERTY mod4 <= 8;
tel
```

Equivalence extraction is also more modular than k-induction.
We can perform equivalence extraction on subnodes and learn invariants that we then make use of in the parent nodes.
If the parent node were too large to run equivalence extraction to saturation, we can still use the properties we learnt about the subnodes.
In comparison, k-induction is kind of all-or-nothing.
When proving a particular node, there's a single k parameter that affects the whole transition system, including subnodes.
We can't unfold the `lastn` nodes ten times, while only unfolding the others fewer times.
This modularity might make equivalence extraction useful even in cases where k-induction would get all of the invariants eventually.

### Cool stuff

User-specified rewrite rules

```
SoFar(a and b) = SoFar(a) and SoFar(b):
  (µ. a and b and (true -> pre µ0)) =
    (µ. a and (true -> pre µ0)) and (µ. b and (true -> pre µ0))
```

```
LastN(n, a and b) =
  = LastN(n, a) and LastN(n, b):
  (µ. if a and b then (0 -> pre µ0) + 1 else (0 -> pre µ0)) =
    min((µ. if a then (0 -> pre µ0) + 1 else (0 -> pre µ0)),
        (µ. if b then (0 -> pre µ0) + 1 else (0 -> pre µ0)))
```

### Future work

Currently implemented in a small model checker, "Songlark", which is a Scala EDSL on top of a Lustre-style core.

#### Better clock support
Clock support is very simple right now.
Each clock is given its own e-graph with just the bindings that are defined on that clock.

#### Integration with other invariant generation
Could template-based invgen use the e-graph as a starting point?
Could we use the invariants invgen finds to rewrite more?

#### Other relations
Coloured e-graphs can represent relations other than equivalence relations.
Could we use them to infer implication and less-than invariants?
