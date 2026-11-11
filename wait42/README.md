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

The [champion-pattern note](research/champion-patterns.md) explains the state
bursts and isolated instruction beeps, with transition-derived recurrences and
a clear distinction from the finite Coq lower-bound proofs.

These are lower-bound witnesses, not established maxima. The state record was
found in a sweep of the 432 historical rare-fire candidates. That input list is
not an exhaustive census of four-state machines.

## Proof structure

- [Spec.v](theories/Spec.v) defines the waiting and total-horizon statements on
  the existing four-state binary machine model.
- [Recurrence.v](theories/Recurrence.v) proves the whole-machine decision rule.
- [FirstVisit.v](theories/FirstVisit.v) proves that every state or instruction
  ever reached has already appeared strictly before the state BBB bound. Stop
  on the first observation to turn it into a last visit in a machine of the
  same size. Thus a target never observed before BBB is never observed at all.
  This does not bound the return gaps of previously visited targets.
  The lemmas take the existing global BBB statement as a hypothesis; the
  first-visit reductions themselves add no axioms.
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
- [Batch.v](theories/Batch.v) replays periodic certificates for state and
  instruction windows, including every completion of a partial table.
  [RankedCompletion.v](theories/RankedCompletion.v) supplies the corresponding
  nonhalting and completion guarantees for finite n-gram certificates.
- [RepeatedWord.v](theories/RepeatedWord.v) proves numerical waiting bounds
  from finite repeated-word graphs. [ResidualReplay.v](theories/ResidualReplay.v)
  and [ResidualReplayMore.v](theories/ResidualReplayMore.v) check 25 concrete
  holdouts; [the index](research/repeated-word-proved.tsv) names their theorems.
- [Resume.v](theories/Resume.v) removes only checked leaves from a frontier
  and preserves all other completion obligations. [ReplayPilot.v](theories/ReplayPilot.v)
  reduces the 391-node pilot frontier to 21 pending subtree roots and 29 prior
  unknown nodes. Its coverage theorem explicitly requires proofs for those
  remaining families. This pilot and the full exploratory worklist are separate
  coverage stages.
  [ReplayCoverage.v](theories/ReplayCoverage.v) reuses that frontier at any proposed
  waiting width of at least 4,096, so harder residuals can use the larger record
  bound while the easy leaves keep their small certificates.
- [Sweep.v](theories/Sweep.v) bounds directional sweeps using the blank tape's
  finite support after B steps. [SweepResiduals.v](theories/SweepResiduals.v)
  checks 745 current residual families with state waiting width B+2 for B≥6.
- [InvariantTimedRank.v](theories/InvariantTimedRank.v) bounds a growing rank
  at the cutoff using a step-closed invariant and a separate growth potential.
  [ThreeStateCounter.v](theories/ThreeStateCounter.v) applies it to
  `0RB---_0LC0RB_1LD1RD_1RB0LD`, proving state waiting width B+1 for B≥2.
  Both results cover every completion of the partial machine tables.
- [SweepGeneral.v](theories/SweepGeneral.v) also handles scans through zeros.
  A future beep is required: scanning into blank tape may instead escape forever.
  [SweepGeneralResiduals.v](theories/SweepGeneralResiduals.v) checks another
  473 families with state waiting width B+2 for B≥6.
- [ControlRank.v](theories/ControlRank.v) checks count-and-control certificates:
  a short anchor, closed control invariant, descending ranks for each target,
  and a numerical bound. [ControlRankReplay/Tight.v](theories/ControlRankReplay/Tight.v)
  proves a waiting bound of 98,338,439 at cutoff 32,779,478 for all 2,874 indexed
  counter families and every completion of their partial tables.
- [MonotonePhase.v](theories/MonotonePhase.v) checks conditional exits from
  monotone scanning phases. [PhaseRank.v](theories/PhaseRank.v) composes at most
  two cyclic phases with checked control progress and preserves the future-beep
  witness. [PhaseRankReplay/Union.v](theories/PhaseRankReplay/Union.v) proves
  width 98,338,534 at cutoff 32,779,478 for 7,095 additional indexed families
  and every completion, including 1,263 coarsened phase certificates.
- [FiniteObservation.v](theories/FiniteObservation.v) replays finite observation
  windows from the blank tape. Its `observation_batch_completion` theorem covers
  every completion when all states are observed, or when an observed total,
  closed tail excludes all missing states. It also checks each local width fits
  the proposed global width.
- [FiniteInstructionObservation.v](theories/FiniteInstructionObservation.v)
  provides the instruction counterpart: all eight slots are observed, or both
  slots of every state in a total, closed tail are observed. Its completion
  theorem independently checks instruction waiting windows for partial tables.

The old score census and its 5,156 deferred rows do not by themselves cover this
new quantity. Qualitative recurrence leaves also need quantitative certificates.
[CENSUS_PLAN.md](CENSUS_PLAN.md) documents the inventory and coverage requirements.

## Contribute an observation proof run

An eight-core Linux or WSL machine can independently replay a fixed batch of
16,384 successful observation candidates in Coq:

```sh
make -C wait42 proof-observations BUILD_JOBS=8
```

The runner saves audited batches and resumes with the same command. See
[VERIFYING_OBSERVATIONS.md](VERIFYING_OBSERVATIONS.md) for setup, a one-batch
smoke run, resource controls, and the distinction between individual family
proofs and the unfinished universal census. The input list is a set of
**nominations**, not a claim that all 16,384 proofs have already been replayed.

For instruction waiting, replay the 9,480 short nominations from the desktop
scan with a separate command and output directory:

```sh
make -C wait42 proof-instruction-observations BUILD_JOBS=8
```

See [VERIFYING_INSTRUCTION_OBSERVATIONS.md](VERIFYING_INSTRUCTION_OBSERVATIONS.md)
for resume instructions and scope. Another 507 longer nominations and 6,397
scan holdouts remain explicit. This sample does not cover the full instruction
census, and the state proof receipts are unchanged.

## Build and search

Activate the repository's native Coq 8.18 environment, then run:

```sh
make -C wait42 proof-foundation -j2  # definitions, solvers, and census contracts
make -C wait42 proof -j2             # additionally replay and audit lower bounds
make -C wait42 proof-replay -j2      # 204 periodic, 10 n-gram, and 25 holdout proofs
make -C wait42 proof-timing -j2      # 11,188 indexed completion families
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

The replay target uses small frozen samples, including all 124 periodic
certificates missed by a deeper search pass. Each accepted certificate is
recomputed by Coq and recursively checked. Rejections, timeouts, and malformed
reports cannot discharge a proof obligation. Passing the sample target does
not establish exhaustive census coverage.

The current timing checkpoint contains **11,188 distinct families** from the
merged 213,950-row residual worklist. Their windows at the BBB cutoff are at
most **98,338,534** steps, below the current state waiting lower bound of
225,592,668. The [proof index](research/proved-residuals.tsv) records each exact
table and unused-state pointer with its theorem; the [phase index](research/phase-rank-proved.tsv)
records the new 7,095 entries. Exact bookkeeping leaves **202,762** research
holdouts. The preceding 4,093-family index is retained at Git ref `1af5c043`, path
`wait42/research/proved-residuals.tsv`; its hash is recorded in the validation.

All promoted phase sources and their aggregate completion theorem passed a
recursive audit. The final combined `proof-timing` target also passed for all
11,188 indexed families; see [round-four validation](research/round4-validation.json)
for the separate scratch, promoted-module and full-target checks. The census still needs
coverage assembly; these family proofs do not establish its universal bound.

`tools/probe_control_ranks.py --input <residual.tsv> --output <directory>`
searches a chosen residual snapshot for new count/control certificates. Its
manifest records the input hash, every rejection, and quantitative candidate
bounds. Nomination alone earns no proof credit; the checked-in batch statements
are independently replayed by `proof-timing`.
