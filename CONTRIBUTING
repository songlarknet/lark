# Contributing
The Songlark toolchain is not free open-source software. It is dual-licensed
under a restricted non-commercial licence as well as a commercial licence. That
said, contributions are welcome, especially from commercial partners who would
otherwise need to maintain an internal fork of the toolchain.

There are a few legal issues related to copyright to consider before we can
accept contributions. This document describes the process around receiving
contributions to the Songlark toolchain itself and the base libraries. Programs
and libraries written in the Lark modelling language generally have looser
restrictions, as they are considered to be separate works.

The main underlying legal issue is that we wish to retain the authority to
re-distribute Songlark under another licence. In the future, it may be feasible
to move to a standard free open-source licence. It would be unfortunate if
community contributions prevented us from being able to release it under a more
permissive licence.

## Legal requirements

Contributors must grant an unrestricted perpetual licence of their
contributions to Songlark Automata, unless otherwise specified in
a separate contract.

The licence granted by the contributor ensures that Songlark Automata retains
its authority to re-license the Songlark Toolchain as it sees fit.

The licence granted by the contributor also includes unrestricted royalty-free
use and re-licensing of any patents owned by the contributor or copyright
holder that directly relate to the contribution.

Depending on the nature of your commercial licence agreement with Songlark
Automata, you will not necessarily retain the licence to use all derived
products that contain your contribution. (For example, if a licensee previously
held an Annual Support Licence which the licensee does not renew, then the
licensee will retain their perpetual licence for the current version at the
time of expiry, but the licensee will not be granted a licence for any later
updates, even if these updates contain the licensee's contributions.)

Contributors must have the legal authority to grant such a licence. In
practice, this means that their contributions must be their own work. If the
contributor does not hold copyright, then the copyright holder must give the
contributor explicit permission to offer this contribution and grant the
licence.

Clarification of the terms used above:
* the Songlark Toolchain refers to all software, documentation and other
  artefacts in this repository;
* Songlark Automata refers to the entity which oversees development of the
  Songlark Toolchain;
* contributions refer to any changes that are submitted for inclusion in the
  Songlark Toolchain repository;
* an Annual Support Licence is a perpetual licence that includes one year of
  updates and a specific number of support hours; on expiration of the contract
  the latest version retains its perpetual licence with no further updates.

For any further clarification of the above, please contact
contributing@songlark.net.

## Practical requirements

Aside from the above legal requirements, there are some practical requirements.
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
it with a `PERF` tag so that it's easy to spot when we run into issues.

The runtime-system in `src/rts` is real code that runs on the hardware. Any
allocations must be carefully considered, and timing must be predictable. We're
really more interested in the worst-case execution time rather than the minimum
or average execution time. Aim for predictable mediocrity rather than good with
outliers.

For large changes, it's good to discuss the proposed changes beforehand. One
place to have such discussions is to open a Github issue describing the issue
or feature.
