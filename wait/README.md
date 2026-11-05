# Quasihalting decision horizons and waiting times

`BBB_wait(n,m)` is the least number of **additional transitions** after the
known state-based cutoff `B = BBB(n,m)` needed to detect every state that will
be visited again. For instruction-based beeps, `BBB_wait_tr` uses the cutoff
`B = BBB_tr(n,m)` and a target `(state, read symbol)`.

`BBB_qh_decide` and `BBB_qh_decide_tr` are the corresponding **total horizons**:

```text
BBB_qh_decide    = BBB    + BBB_wait
BBB_qh_decide_tr = BBB_tr + BBB_wait_tr
```

The symbol count defaults to two. The observation window includes
configuration `B`, already reached after `B` transitions. A wait of `w`
observes indices `B, B+1, ..., B+w`. The repository scores a last visit at
index `s` as `s+1`.

| Domain | State BBB | State wait | State horizon | Instruction BBB | Instruction wait | Instruction horizon |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `(1,2)` | 1 | [0](theories/Values.v) | [1](theories/Decision.v) | 1 | [0](theories/ValuesTr.v) | [1](theories/Decision.v) |
| `(2,2)` | 6 | [3](theories/Values.v) | [9](theories/Decision.v) | 8 | [9](theories/ValuesTr.v) | [17](theories/Decision.v) |
| `(3,2)` | 55 | [38](theories/Value32.v) | [93](theories/Decision32.v) | 55 | [173](theories/Value32.v) | [228](theories/Decision32.v) |
| `(2,3)` | 59 | [32](theories/Value23.v) | [91](theories/Decision23.v) | 67 | [693](theories/Value23.v) | [760](theories/Decision23.v) |

Waiting champions maximize the delay to the first post-cutoff beep. They can
be different from the machines maximizing BBB itself. All programs below
start by moving right; the target is a state or instruction slot.

| Domain | State waiting champion | Target | Instruction waiting champion | Target |
| --- | --- | --- | --- | --- |
| `(1,2)` | `0RA---` | A | `0RA---` | A0 |
| `(2,2)` | `1RB0RB_1LA1LB` | A | `1RB0LB_1LA0RA` | B1 |
| `(3,2)` | `1RB1LA_1RC1LB_1LA0RB` | A | `1RB0LC_1LC0RA_1LA1LB` | C1 |
| `(2,3)` | `1RB2LA1RA_1LB1LA2RB` | B | `1RB2LA1RA_1LA2RA2RB` | B1 |

For example, the binary two-state instruction witness never fires B1 at
indices 8 through 16, then fires it at 17. The ternary instruction witness
last fires B1 before the cutoff, stays silent throughout indices 67 through
759, then fires B1 at 760. These witnesses prove the positive waits are
necessary. Zero is already the smallest possible wait for one-state machines.

## The exact claims

For a chosen state `q`, [Spec.v](theories/Spec.v) defines:

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

[SpecTr.v](theories/SpecTr.v) gives the instruction counterpart using
`FiresAt` and the instruction BBB cutoff. [DecisionSpec.v](theories/DecisionSpec.v)
defines the total horizon by an exact waiting value and `D = B+w`, and proves
uniqueness and minimality among observation horizons at or after `B`.

The exported waiting claims are:

```coq
BBB_wait12_value    : BBBWait_is   1 2 1  0.
BBB_wait22_value    : BBBWait_is   2 2 6  3.
BBB_wait32_value    : BBBWait_is   3 2 55 38.
BBB_wait23_value    : BBBWait_is   2 3 59 32.
BBB_wait12_tr_value : BBBWaitTr_is 1 2 1  0.
BBB_wait22_tr_value : BBBWaitTr_is 2 2 8  9.
BBB_wait_tr32_value : BBBWaitTr_is 3 2 55 173.
BBB_wait_tr23_value : BBBWaitTr_is 2 3 67 693.
```

[Recurrence.v](theories/Recurrence.v) and
[RecurrenceTr.v](theories/RecurrenceTr.v) prove that a target absent from the
observation window is absent forever from `B` onward. A target present in the
window cannot eventually become silent, because its last-visit score would
then exceed BBB. They also prove the whole-machine decision rule: quasihalting
holds exactly when some target visited before `B` is absent from the window.
Never-visited targets do not count as quasihalting witnesses.

These quantities concern a uniform observation rule. They are not lower
bounds on the runtime of every possible algorithm analyzing a machine's
transition table. Seeing one recurrent state also does not rule out another
state becoming permanently silent; the whole-machine rule considers all
targets.

## Build and independently audit

Use the repository's native Coq 8.18 toolchain. From the repository root:

```sh
make proof-wait-small BUILD_JOBS=2  # (1,2) and (2,2), both conventions
make proof-wait-3 BUILD_JOBS=2      # (3,2), both conventions
make proof-wait-2-3 BUILD_JOBS=2    # (2,3), both conventions
make proof-wait-all BUILD_JOBS=2   # all eight values and total horizons
```

With the toolchain already activated, the direct all-values command is
`make -C wait proof-all -j2`. The build compiles the required existing BBB
values, the waiting proofs, and their decision-horizon corollaries. It then
runs full recursive `coqchk` and prints the exact statements, definitions,
assumptions, and success banner. Compilation parallelizes; the recursive
kernel audit is serial and takes longer than the native census checks.

The all-values audit log is `wait/build/coqchk-all.log`. The reports are
`wait/build/report.log`, `report32.log`, and `report23.log`. Individual targets
use `coqchk.log`, `coqchk32.log`, and `coqchk23.log`. A successful build reports
only the existing `FunctionalExtensionality.functional_extensionality_dep`
assumption. There are no admitted proofs or additional axioms.

The two larger censuses each cover all **4,826,809** labeled partial tables,
including arbitrary first transitions and undefined instructions. Each has
13 first-transition shards; the Coq assembly proves that those shards cover
every admissible machine. It does not trust a generator's machine count.
The smaller domains cover all 25 and 6,561 tables.

Closed control-flow masks and translated cycles handle most tables. The
three-state instruction proof also uses history-augmented n-gram coverage;
the ternary instruction proof uses a repeated-word abstraction for its final
44 parity-sensitive cases. Only tail coverage is required, because the
observation window already contains every permissible tail label.
[Fast.v](theories/Fast.v) proves the optimized checks sound, and
[Monotone.v](theories/Monotone.v) lets the ternary census certify most tables
using a shorter window before trying the full bound.

Search tools and profile choices are untrusted. The census recomputes every
certificate inside Coq, and `coqchk` independently rechecks the resulting
proofs. Existing proof sources and frozen manifests are unchanged. No waiting
value for `(4,2)` or `(2,4)` is claimed here.
