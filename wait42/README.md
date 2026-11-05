# Four-state, binary quasihalting decision horizons

This development investigates `BBB_qh_decide(4,2)` and its instruction counterpart,
starting with the state value. The exact waiting values remain open.

```text
BBB_qh_decide    = BBB    + BBB_wait
BBB_qh_decide_tr = BBB_tr + BBB_wait_tr
```

Both existing BBB cutoffs are **32,779,478**. Choose one state as the beeping
state, or one instruction slot for instruction beeps. The waiting window includes
its endpoints: `[BBB, BBB + BBB_wait]`. Once a sufficient waiting bound is proved,
if that chosen target beeps in the window, it will beep infinitely often;
otherwise it will never beep again. A target that beeped previously and becomes
permanently silent witnesses quasihalting. The bound applies uniformly to every
choice of beeping target; a machine does not need multiple beepers.

The repository also defines an aggregate predicate, `QuasiHaltsSt` (or
`QuasiHaltsTr`), meaning that **some** previously visited target becomes silent.
For that predicate, the decision procedure checks all previously visited targets.
This aggregate rule and the single designated-beeper rule are distinct views of
the same per-target waiting guarantee. Never-visited targets do not witness the
repository's quasihalting predicate.

These are minimum horizons for this observation rule, not running-time lower
bounds on arbitrary algorithms that inspect transition tables.

## Current records

See [SCOREBOARD.md](SCOREBOARD.md) for proof status and the census frontier.

| Convention | Horizon lower bound | Extra-wait lower bound | Witness | Target |
| --- | ---: | ---: | --- | --- |
| State | 258,372,146 | 225,592,668 | `1RB1RC_1LA0LA_0RD0RC_1LD1LA` | B |
| Instruction | 487,181,856 | 454,402,378 | `1RB0LD_1RC1RB_1LA1LC_0RC1LA` | D0 |

These are lower-bound witnesses, not established maxima. The state record was
found in a sweep of the 432 historical rare-fire candidates. That input list is
not an exhaustive census of four-state machines.

## Proof structure

- [Spec.v](theories/Spec.v) defines the waiting and total-horizon statements on
  the existing four-state binary machine model.
- [Recurrence.v](theories/Recurrence.v) proves the whole-machine decision rule.
- [Transport.v](theories/Transport.v) handles reflection, non-start state swaps,
  nonhalting completions, and correctly shifted cutoffs for equivalent tails.
- [BinaryScan.v](theories/BinaryScan.v) checks finite witnesses using binary
  fuel, without constructing a unary numeral for hundreds of millions of steps.
  [WitnessRecord.v](theories/WitnessRecord.v) and [Examples.v](theories/Examples.v)
  supply the state and instruction lower-bound theorems.
- [Periodic.v](theories/Periodic.v) proves a translated cycle of period P gives
  a waiting upper bound of P−1 at every cutoff after its anchor.
- [Ranked.v](theories/Ranked.v) retains quantitative bounds from decreasing
  ranks, giving waiting certificates from finite abstract closures.
- [Census.v](theories/Census.v) reuses the existing TNF expansion and queue
  machinery with new waiting obligations for every accepted leaf.

The old score census and its 5,156 deferred rows do not by themselves cover this
new quantity. Qualitative recurrence leaves also need quantitative certificates.
[CENSUS_PLAN.md](CENSUS_PLAN.md) documents the inventory and coverage requirements.

## Build and search

Activate the repository's native Coq 8.18 environment, then run:

```sh
make -C wait42 proof-foundation -j2  # definitions, solvers, and census contracts
make -C wait42 proof -j2             # additionally replay and audit lower bounds
make -C wait42 test                  # untrusted search-tool regression checks
make -C wait42 search                # state sweep of 432 historical candidates
```

The lower-bound replay simulates hundreds of millions of transitions and takes
longer than the generic foundation checks. `proof` prints the statements and
assumptions only after recursive `coqchk` passes. Its success message explicitly
leaves the exact waiting values open. No existing small or four-state proof
source is changed.

Search output lives under `wait42/build/`, with source hashes and explicit
simulation limits. A missing observation at a finite cap means unresolved, not
permanent silence. A search solver's result has zero kernel proof credit until
its certificate is replayed in Coq.
