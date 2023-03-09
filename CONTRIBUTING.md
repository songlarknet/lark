# Contributing
The Songlark toolchain is free open-source software; contributions are welcome.


## Practical requirements

There are some practical requirements that contributions should adhere to.
The main coding guidelines are that "real" code should compile cleanly without
warnings, but it's fine to be a bit looser in test code.

The `lark.meta` package is all "meta" code that runs at program compilation
time. It doesn't have to run on real hardware or with any sort of realtime
constraints. It should make liberal use of assertions: failing assertions are
better than silent mistakes. From the user's perspective, crashes during code
generation could be interpreted as a compile-time error if the error message is
adequate.

Performance is not yet an issue in the model checker or compiler itself, so in
general prefer slower "obviously correct" implementations over convoluted ones.
If something has the wrong asymptotic complexity, though, make sure to comment
it with a `PERF` tag so that it's easy to spot when we do run into issues.

The runtime-system in `src/rts` is real code that runs on the hardware. Any
allocations must be carefully considered, and timing must be predictable. We're
really more interested in the worst-case execution time rather than the minimum
or average execution time. Aim for predictable mediocrity rather than good with
outliers.

For large changes, it's good to discuss the proposed changes beforehand. One
place to have such discussions is to open a Github issue describing the issue
or feature.
