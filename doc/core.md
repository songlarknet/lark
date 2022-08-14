# core language

Lack: a minimal core language for model-checked realtime control systems.

The goal is to support only very basic clock operations that are useful for composing systems together without any clock checking.
Lack Core supports conditional activation ("when") and modular reset ("reset every") for subcomputations but there is no static check that streams with subclocks are only used in correct contexts.

Lack Core also has deliberately relaxed scoping rules to make it easier to specify invariants that refer to internal variables.
Each subnode invocation has an instance identifier, and you can access local variables declared inside subnodes by qualifying variables with the instance identifier.
Variables inside nested subnodes can also be referred to this way.
Each streaming context also defines a special variable that refers to the "initialised flag", which is true initially and whenever the context is reset, and becomes false when the stream is next evaluated.
Its value is equivalent to (true -> false), but it is exposed so that invariants can refer to the flag directly.

In the future I aim to support more sophisticated clocks by providing a higher-level layer that translates to this minimal core language.
In this higher layer, clock consistency might be checked by generating proof obligations if they can't be shown syntactically.

## Grammar

```
-- All bound variable occurrences use qualified identifiers.
-- Variable names that start with ^ are expected to be internally-generated.
qualid ::= x | qualid.x

-- Expressions are split into groups...
exp ::=
  -- Pure expressions
  | qualid | value
  | prim(exp,...)

  -- Flow, streaming expressions
  | exp -> exp
  | pre(exp)

  -- Non-deterministic expressions
  | undefined_{sort}

-- Sorts or value types. These sorts represent the elements that a stream might contain.
sort ::= Bool | UInt8 | ...

-- Recursive namespaces declaring the type of each variable.
-- These can be a regular sort or can also represent a nested namespace of values inside a subnode
namespace ::= {x : (sort | namespace),...}

-- Properties or judgments. Things we either want to be true or already know to be true.
prop ::= require | guarantee | check | sorry | generated(prop) ;

-- Nodes define a streaming function that takes some arguments.
-- Nodes declare the types of variables and the subnodes and declare the properties
-- that are expected to hold.
-- The main definitions are nested inside contexts.
node ::=
 qualid(x : sort,...) = node {
  var {x : sort,...};
  subnode { x : node };

  prop string: exp;...

  x = @init;
  context;...

 }

context ::=
  -- Local variable definitions
  | x = exp
  -- Subnode invocations; results are referred to by qualified identifiers prefixed with `x.`
  | subnode x(exp,...)
  -- Nested activation context; stream computations in the subcontext are only
  -- activated when `e` is true. The `x` variable refers to the initialisation flag `true -> false`.
  -- The variables with definitions in the subcontext have well-defined values when `e` is true,
  -- but might be undefined otherwise.
  | when(e) { x = @init; context;... }
  -- Nested reset context; stream computations in the subcontext are reset whenever `e` is true.
  -- The `x` variable refers to the initialisation flag `true -> false`.
  | reset(e) { x = @init; context;... }
```

## Examples

A simple counter:
```
counter(e: Bool) = node {
 var     { result : UInt8; ^init : Bool; };
 subnode { };

 ^init  = @init;
 result = (if e then 1 else 0)
        + (0 -> pre result);
}

```

An instantiation of `λe. LastN(4, e)`.
The 4 is a constant (non-streaming) integer, so we specify it as a meta-level integer.
Maybe in the future we would want a way to pass constants too so that callers of the generated code can instantiate them.

```
lastn4(e: Bool) = node {
 var { result: Bool; count : UInt8; ^init : Bool; };
 subnode {};

 ^init = @init;
 count =
  if e then ((0 -> pre count) + 1)
       else 0;

 result = count >= 4;
}
```

An instantiation of `λi. LastN(4, 0 <= i) and LastN(4, i < 10)`

```
inbounds(i: Int) = node {
 var { result: Bool; ^init: Bool; };
 subnode { ge0: lastn4; lt10: lastn4; };

 ^init = @init;

 subnode ge0(i >= 0);
 subnode lt10(i < 10);
 result = ge0.result and lt10.result;
}
```

An example with conditional activation.
The node receives asynchronous messages and checks that the last four received messages are all valid.
If there is no new message, it holds the previous value.
In Lustre we might write:

```
type payload = { valid: bool; ... };

node status_consistently_good(msg_ck: bool; msg_payload: payload when msg_ck)
let
 hold = false -> pre result;
 result = merge(
  when     msg_ck -> LastN(4, msg_payload.valid)
  when not msg_ck -> hold when not msg_ck
 );
tel
```

In Lack Core:

```
status_consistently_good(msg_ck: Bool; msg_payload: Payload) = node {
 var { result: Bool; hold: Bool; ^init: Bool; ^init?1: Bool; ^init?2: Bool; };
 subnode { lastn4_valid: lastn4; };

 ^init = @init;

 when(msg_ck) {
  ^init?1 = @init;

  subnode lastn4_valid(msg_payload.valid)
 }

 hold = false -> pre result;

 result =
  if msg_ck then lastn4_valid.result else hold;
}
```

The input msg_payload has no clock associated with it to describe when it is available.
There is no clock check that msg_payload or the result `lastn4_valid.result` are only used when msg_ck is true.
If `lastn4_valid.result` were used when msg_ck is false, the result would be undefined.

For this first prototype we'll get around that by restricting the source language a bit...
In the future we probably want a stronger system that generates proof obligations for well-clockedness.

## Semantics

### Denotational semantics

The denotational semantics maps nodes to a transition system, which is represented as a state type, a row type, a predicate describing the initial states, and a step (transition) relation.
The state type describes a record containing the internal state such as initialise flags and previous values, and can contain nested records to store the state of subnodes.
The row type describes a record containing all of the program-visible variables, including node inputs and the computed outputs.
The initialisation predicate takes a state and returns a boolean indicating whether the state is a valid reset state.
(It is a predicate rather than a function to allow the states to be initialised with undefined values.)
The step relation takes the starting state, the row record, and the result state.
Functionally, the starting state is an input and the result state is an output, while the row can be a combination of input values and computed values.

```
system ::= system {
  state: namespace;
  row:   namespace;

  init: state -> bool;
  step: state -> row -> state' -> bool;
}

[| . |] : node -> system
```

You can combine two systems together with parallel composition by taking the union of the states and the rows.
The init predicate and the step relation are joined by conjunction.
The two row types will usually refer to the same variables, so any overlaps are ok.
The states are allowed to refer to the same states too: different parts of the same node will refer to the same initialised flag.
There should be a monoid:
```
sy <> sy' = system {
  sy.state <> sy'.state;
  st.row <> sy'.row;

  init = λs. sy.init s /\ sy'.init s
  step = λs r s'. sy.step s r s' /\ sy'.step s r s'
}
```


For the semantics of expressions, we also define "expression systems" whose step relation also takes the result value.
```
e-system ::= system with {
  step: state -> row -> state' -> value -> bool;
}
```

Parallel composition for these just bundles up the results into a pair:
```
sy <> sy' = e-system {
  sy.state <> sy'.state;
  st.row <> sy'.row;

  init = λs. sy.init s /\ sy'.init s
  step = λs r s' (v0, v1).
    sy.step s r s' v0 /\ sy'.step s r s' v1
}
```

The denotation of expressions depends on the context so that it can refer to the initialised variable.
So we encode the denotation `[| c |- e |]` meaning "expression e under context c".
```
init-context ::= { @init: variable }

[| . |- . |] : init-context -> exp -> e-system

-- Values are easy:
for v <- value
[| c |- v |] = {
  state = {};
  row   = {};
  init  = const true;
  step  = λs r s' v'. v' = v
}

-- Look up variables in the row:
for q <- qualid
[| c |- q |] = {
  state = { };
  row   = { q };
  init  = const true;
  step  = λs r s' v. v = r[q]
}

-- To apply a primitive, compose all of the expressions, tuple them up, and apply
[| c |- f(e0, e1, ..., ei) |] =
  let t = [|c |- e0|] <> [|c |- e1|] <> ... <> [|c |- ei|]
  in {
    state = t.state;
    row   = t.row;
    init  = t.init;
    step  = λs r s' v.
      let x0, x1, ..., xi = fresh
      in t.step s r s' (x0, x1, ..., xi)
      /\ v = f(x0, x1, ..., xi)
  }

-- Streaming operations: arrow runs both and selects based on the context @init flag
[| c |- e0 -> e1 |] =
  let t = [|c |- e0|] <> [|c |- e1|]
  in {
    state = t.state;
    row   = t.row;
    init  = t.init;
    step  = λs r s' v.
      let (x0, x1) = fresh
      in t.step s r s' (x0, x1)
      /\ v = (if s[c.@init] then x0 else x1)
  }

-- Streaming operations: pre introduces some state
[| c |- pre e |] =
  let t = [|c |- e|]
  and x = fresh
  in {
    state = t.state U { x : e.type };
    row   = t.row;
    -- Don't care what value x has - uninitialized is undefined
    init  = t.init;
    step  = λs r s' v.
      t.step s r s' s'[x]
      /\ v = s[x]
  }

-- Undefined has no restrictions at all
[| c |- undefined |] =
  let t = [|c |- e|]
  and x = fresh
  in {
    state = t.state U { x : e.type };
    row   = t.row;
    -- Don't care what value x has - uninitialized is undefined
    init  = t.init;
    step  = λs r s' v.
      t.step s r s' s'[x]
      /\ v = s[x]
  }
```

XXX: this is close to the semantics we want for SMT solving, but is there a simpler semantics for exposition?
XXX: if step type is `state -> row -> state' -> (bool, value)` then might reduce some fresh variable bindings in plumbing

```
[| c |- c |] init-context -> context -> system

[| c |- x = e |] =
 let t = [|c |- exp|]
 in t with {
  row = t.row U {x};
  step = λs r s'. t.step s r s' row[x] }

[| c |- subnode x(e0,...,ei) |] =
 let n = subnodes[x]
 and t = [|c |- e0|] <> ... <> [|c |- ei|]
 in t with {
  state = t.state U {x : n.state};
  row   = t.row   U {x : n.row}
  init  = λs. t.init s /\ n.init s[x]
  step  = λs r s'.
    let a0,...ai = r[x][a] | a <- n.args
    t.step s r s' (a0,...ai) /\ n.step s[x] r[x] s'[x] }

[| c |- when(k) { x = @init; cc } |] =
 let tk = [| c |- k |]
 and tc = [| x |- cc |]
 in tk <> {
  state = { x : bool } <> tc.state;
  row   = tc.row;
  init  = λs. s[x] /\ tc.init s
  step  = λs r s'.
    let vk = fresh
    in tk.step s r s' vk
    /\ if vk
       then (tc.step s r s' /\ ~s'[x])
       else (s[i] = s'[i] for i in tc.state)
 }

[| c |- reset(k) { x = @init; cc } |] =
 let tk = [| c |- k |]
 and tc = [| x |- cc |]
 in tk <> {
  state = { x : bool } <> tc.state;
  row   = tc.row;
  init  = λs. s[x] /\ tc.init s
  step  = λs r s'.
    let vk = fresh
    and sr = fresh
    in tk.step s r s' vk
    /\ tc.step sr r s'
    /\ ~s'[x]
    /\ if vk
       then (sr[x] /\ tc.init sr)
       else (sr[i] = s[i] for i in tc.state)
 }
```

### Scheduled semantics

Scheduled semantics that requires program to be in correct order.
```
```

## Extensions

* Pure functions:
Probably want a way to represent pure functions rather than nodes.
This would involve removing the `@init` flag, disallowing nested contexts, and only allowing pure function subnodes.

# Shelve

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



