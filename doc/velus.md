# Generating Vélus

examples https://github.com/amosr/velus/blob/popl20-artifact/examples/stopwatch_reset.lus

## Quibbles and oddities

* Integer literals are typed: 1 is int32, `1u` is uint32, and `1ull` is uint64, but how to do int8 and int16? Character literals `'\001'` can be used for uint8.
* Restart applies to nodes only, not arbitrary expressions or blocks


## Clock semantics

In this program has three clocked bindings, a and b are equivalent.
```
node clocks(k: bool)
returns (a, b, c : bool when k)
let
  a = true -> false;
  b = (true when k) -> (false when k);
  c = (true -> false) when k;
tel
```
