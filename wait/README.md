# Waiting after the Beeping Busy Beaver cutoff

`BBB_wait(n,m)` is the least number of **additional transitions** needed
after the state-based cutoff `B = BBB(n,m)` to determine which states will
ever be visited again. The symbol count defaults to two.

The observation window includes configuration `B`, which is already available
after simulating `B` transitions. Thus a wait of `w` observes indices
`B, B+1, ..., B+w`. This uses the repository's BBB score convention:
the last visit at index `s` has score `s+1`.

| Domain | BBB cutoff | Exact BBB_wait | Last index to observe | Waiting witness (target state) |
| --- | ---: | ---: | ---: | --- |
| `(1,2)` | 1 | [**0**](theories/Values.v) | 1 | Zero is already minimal |
| `(2,2)` | 6 | [**3**](theories/Values.v) | 9 | `1RB0RB_1LA1LB` (A) |

The waiting witness is different from the machine maximizing the BBB score.
It visits A at indices `0, 2, 5, 9, ...`, so observing only indices 6 through
8 would miss the next beep. The exhaustive proof establishes that every
two-state, two-symbol machine that beeps in a particular state at or after 6
does so by 9.

## The exact claim

For a fixed beep state `q`, [Spec.v](theories/Spec.v) defines:

```coq
FutureBeep tm q B := exists t, B <= t /\ VisitsAt tm q t.
BeepWindow tm q B w :=
  exists t, B <= t /\ t <= B+w /\ VisitsAt tm q t.
WaitBound ns ms B w := forall tm, Admissible ns ms tm ->
  forall q, FutureBeep tm q B -> BeepWindow tm q B w.
BBBWait_is ns ms B w :=
  BBBSt_is ns ms B /\ WaitBound ns ms B w /\
  forall v, WaitBound ns ms B v -> w <= v.
```

The [value proofs](theories/Values.v) establish both the universal waiting
bound and its minimality, together with the existing exact BBB cutoff:

```coq
BBB_wait12_value : BBBWait_is 1 2 1 0.
BBB_wait22_value : BBBWait_is 2 2 6 3.
```

`wait_silence_decision` proves that a state absent from the observation window
is absent forever from index `B` onward. If a state does occur in the window,
[Recurrence.v](theories/Recurrence.v) proves that it cannot eventually become
silent: otherwise its last-visit score would exceed `B`.

This is a bound on observation by simulation. It does not claim that every
algorithm examining a transition table must simulate that long. Beeps refer
to a chosen state. One recurring state alone does not establish that the
whole machine never quasihalts: another state could disappear. To decide
whole-machine quasihalting, compare the states visited before `B` with those
present in the observation window. A previously visited state missing from
the window is precisely a quasihalting witness; a never-visited state is not.
The theorem `wait_decides_quasihalting` proves this equivalence in Coq.

## Build and independently audit

From the repository root, with the native Coq 8.18 toolchain available:

```sh
make proof-wait-small BUILD_JOBS=2
```

With the toolchain already activated, the equivalent direct command is:

```sh
make -C wait proof -j2
```

This builds the required existing `(1,2)` and `(2,2)` proofs and the waiting
proofs, runs full recursive `coqchk`, and prints the statements, definitions,
and assumptions. It does not run the larger censuses. Logs are written to
`wait/build/coqchk.log` and `wait/build/report.log`. Only the existing
`FunctionalExtensionality.functional_extensionality_dep` assumption is used.

The finite checks cover all **25** labeled `(1,2)` tables and **6,561** labeled
`(2,2)` tables, including undefined transitions. [Checker.v](theories/Checker.v)
proves permanent silence using missing incoming transitions, a closed state,
or a drift into a blank half-tape. The Coq coverage proof relates the finite
enumeration to every admissible machine; bounded search alone supplies no
proof of non-recurrence. The new development is separate from the existing
proof sources and their frozen manifests.

Next candidates are `(2,3)` and `(3,2)`. Their known BBB cutoffs provide starting
points, but longer gaps between recurring beeps can require stronger
certificates than those used here. No larger waiting value is claimed yet.
