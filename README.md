# Coq-BBB4

[![CI](https://github.com/carrino/Coq-BBB4/actions/workflows/ci.yml/badge.svg)](https://github.com/carrino/Coq-BBB4/actions/workflows/ci.yml)

Coq proofs of Beeping Busy Beaver values for **state-based** and
**instruction-based (transition-based)** quasihalting. The proofs establish a maximum in two parts:
a concrete champion attains the stated score, and no machine of the same size
can attain a larger score.

The development builds on certificates from the
[BBB harness](https://github.com/carrino/BBB), following the approaches of
[Coq-BB5](https://github.com/carrino/Coq-BB5) and
[busycoq](https://github.com/carrino/busycoq). Search programs produce untrusted
certificates; Coq checks the machine behavior and exhaustive coverage.

## The result

`BBB(n,m)` denotes the state-based value for `n` states and `m` tape symbols;
`BBB_tr(n,m)` denotes the instruction-based value. The symbol count defaults to
2 when omitted. All values below use the counting convention defined next.

Each domain links to its proof. Champion programs are shown with the first move
to the right; reflecting the tape preserves both scores. Entries marked `≥`
are proved lower bounds. The [program notation](#champion-programs) is explained
below.

### State quasihalting

| Domain | Max steps | Champion |
| --- | ---: | --- |
| [`BBB(1)`](small/theories/Value12.v) | **1** | `1RZ---` |
| [`BBB(2)`](small/theories/Value22.v) | **6** | `1RB1LB_1LB1LA` |
| [`BBB(3)`](small/theories/Value32.v) | **55** | `1RB0LB_1LA0RC_1LC1LA` |
| [`BBB(4)`](theories/Closeout/BBB4_Value.v) | **32,779,478** | `1RB1LD_1RC1RB_1LC1LA_0RC0RD` |
| [`BBB(2,3)`](small/theories/Value23.v) | **59** | `1RB2LB1LA_2LB2RA0RA` |
| [`BBB(2,4)`](four/theories/Champion.v) | **≥ 205,770,076,433,044,242,247,860** | `1RB2LA1RA1LB_0LB2RB3RB1LA` |

### Instruction quasihalting

| Domain | Max steps | Champion |
| --- | ---: | --- |
| [`BBB_tr(1)`](small/theories/Value12.v) | **1** | `1RZ---` |
| [`BBB_tr(2)`](small/theories/Value22.v) | **8** | `0RB1LB_1LA1RB` |
| [`BBB_tr(3)`](small/theories/Value32.v) | **55** | `1RB0LB_1LA0RC_1LC1LA` |
| [`BBB_tr(4)`](theories/CloseoutTr/BBBT4_Value.v) | **32,779,478** | `1RB1LD_1RC1RB_1LC1LA_0RC0RD` |
| [`BBB_tr(2,3)`](small/theories/Value23.v) | **67** | `1RB2LA0RB_1LA0LB1RA` |
| [`BBB_tr(2,4)`](four/theories/Champion.v) | **≥ 205,770,076,433,044,242,247,860** | `1RB2LA1RA1LB_0LB2RB3RB1LA` |

For **`(2,4)`**, [`champion_exact`](four/theories/Champion.v) proves the displayed
champion's exact score at both levels. The complete **state-based** equality
build is under verification and still awaits a successful final recursive
audit. Follow the
[scoreboard](https://github.com/carrino/Coq-BBB4/issues/261) and
[state proof build guide](docs/VERIFYING_BBB24.md).

## What quasihalting means

Machines start in state `A` on a two-way infinite tape filled with symbol `0`.
Each defined transition writes a symbol, moves left or right, and enters a
state. An undefined transition halts. The quantification includes every table
of the requested size, including halting machines and arbitrary first
transitions.

Configuration index `n` means the configuration **after `n` transitions**, so
the initial configuration has index `0`.

* A machine **state-quasihalts** if some state is visited at least once but only
  finitely often. Such a state has a last visit at some index `s`.
* A machine **instruction-quasihalts** if some `(state, read symbol)` pair is
  visited at least once but only finitely often. The pair identifies an
  instruction slot; the written symbol and next state are not part of its
  identity.
* A state's or instruction's **score is `s + 1`**, where `s` is its last visit
  index. A machine's score is the largest score among its finitely visited
  states or instructions. The BBB value is the maximum over all machines of
  that size.

Never-visited states and instructions do not witness quasihalting. Halting
machines are included: their final configuration counts as a visit to its state
and instruction slot, even when that slot contains an undefined transition.
If every visited state, or every visited instruction, recurs at arbitrarily
large indices, the machine does not quasihalt at that level.

This counting convention matters for `(2,4)`. The champion's final state `A`
visit and final `A3` instruction visit are at index
**205,770,076,433,044,242,247,859**. Its final transition out of `A` leads to a
permanent `B0` drift at index **205,770,076,433,044,242,247,860**, giving the
repository's score. The [four-symbol guide](four/README.md#how-the-large-prefix-is-proved)
connects both numbers to the published analyses.

### The formal maximum claim

For `(4,2)`, the relevant definitions in
[`BBB4_Statement.v`](theories/BBB4_Statement.v) and
[`BBB4_Spec.v`](theories/BBB4_Spec.v) are:

```coq
Definition VisitsAt (tm : TM) (q : St) (n : nat) : Prop :=
  exists c, stepn tm n InitES = Some c /\ fst c = q.

Definition QuietAfter (tm : TM) (q : St) (s : nat) : Prop :=
  VisitsAt tm q s /\ forall n, s < n -> ~ VisitsAt tm q n.

Definition Attains (tm : TM) (B : nat) : Prop :=
  exists q s, QuietAfter tm q s /\ S s = B.

Definition BBB4_is (B : nat) : Prop :=
  (exists tm, Attains tm B)
  /\ (forall tm B', Attains tm B' -> B' <= B).

Definition champion_score : nat := N.to_nat 32779478.
Definition BBB4_statement : Prop := BBB4_is champion_score.
```

`QuietAfter` requires an actual last visit. `Attains` gives its score. The two
clauses of `BBB4_is` say **the bound is attained** and **nothing exceeds it**.
The quantifier `forall tm` ranges over all machines in the model, not just
normalized tables or machines found by a search.

The proof exports `champion_attains : Attains tm_champion champion_score` and
`BBB4_value : BBB4_statement`. Together they identify the named champion as a
machine attaining the global maximum. `BBB4_is_unique`, proved in the spec,
shows that two numbers satisfying this maximum claim must be equal.

For instruction quasihalting,
[`BBBT4_Statement.v`](theories/BBBT4_Statement.v) defines `FiresAt tm t n` as
a visit to instruction slot `t` at configuration index `n`, and
[`BBBT4_Spec.v`](theories/BBBT4_Spec.v) states the corresponding maximum:

```coq
Definition QuietAfterTr (tm : TM) (t : Instr) (s : nat) : Prop :=
  FiresAt tm t s /\ forall n, s < n -> ~ FiresAt tm t n.

Definition AttainsTr (tm : TM) (B : nat) : Prop :=
  exists t s, QuietAfterTr tm t s /\ S s = B.

Definition BBBT4_is (B : nat) : Prop :=
  (exists tm, AttainsTr tm B)
  /\ (forall tm B', AttainsTr tm B' -> B' <= B).

Definition BBBT4_statement : Prop := BBBT4_is champion_score.
```

`BBBT4_value : BBBT4_statement` proves this second maximum. The small-machine
specifications in [`small/theories/Spec.v`](small/theories/Spec.v) use the same
attainment-and-upper-bound form, with `Admissible` restricting the common
carrier to the requested machine size.

For `(2,4)`, [`ValueSpec.v`](four/theories/ValueSpec.v) states the state equality
as `BBB24_state_lower_bound score /\ (forall tm : TM, QHBound score tm)`.
Here `QHBound B tm` means every state's last-visit score is at most `B`.
[`Champion.v`](four/theories/Champion.v) supplies the named lower-bound witness;
the complete state build must verify the universal upper bound as well.

### Champion programs

A value can have multiple champion programs. The tables use the familiar
[wiki champions](https://wiki.bbchallenge.org/wiki/Beeping_Busy_Beaver#Champions)
for state quasihalting and versions of the instruction champions whose first
move is to the right.

Each three-character instruction gives write symbol, direction, and next state;
`_` separates state rows, and `---` is undefined. `Z` denotes halting in the
community notation: `1RZ---` has a halting first slot, represented by an
undefined transition in the Coq model. It has score 1 at both levels.

The one-state proof is in [`Value12.v`](small/theories/Value12.v). The other
small-machine witnesses are in [`Champions.v`](small/theories/Champions.v),
sometimes in reflected forms; [`Mirror.v`](small/theories/Mirror.v) and
[`Witness.v`](small/theories/Witness.v) prove the score-preserving transport.
The state `(2,2)` table uses the wiki's nonhalting champion, which attains the
same score 6 as the halting witness used by `BBB22_value`.

The instruction `(2,2)` champion starts by writing `0` and moving right. That
initial blank-writing move is included: fixing the first transition to `1RB`
instead gives the separately proved restricted maximum of
**7**, in [`Normalized22.v`](small/theories/Normalized22.v).
The `(2,4)` champion has a proved exact score; its global maximality remains
under verification at state level and is not established at instruction level.

## The verification ladder

1. **Read the statement.** The model and specifications above define the claim
   independently of the census, certificates, and closeout code. The detailed
   `(4,2)` claim and assumptions are in [`docs/CLAIMS.md`](docs/CLAIMS.md).
2. **Build from source.** The complete targets below rebuild the census and
   assemble the champion lower bound with the universal upper bound. Plain
   `make` builds proof components; use the appropriate complete target for a
   value theorem.
3. **Inspect the assumptions and audit the proof.** The complete `(4,2)` targets
   print the theorem and `Print Assumptions` output. The verification guide also
   gives standalone `coqchk` commands. The small-machine `check` target and the
   selected `(2,4)` state build include full recursive kernel audits.

All proofs are built from source. Full commands and expected outputs are in
[`docs/VERIFYING.md`](docs/VERIFYING.md), with the selected `(2,4)` build in
[`docs/VERIFYING_BBB24.md`](docs/VERIFYING_BBB24.md).

## Building and measured runtime

Use GNU make, Python 3, and Coq 8.18.0 with native computation enabled. The
documented toolchain uses OCaml 4.14.2. Installation instructions are in the
[verification guide](docs/VERIFYING.md).

For the small-machine state and instruction value proofs, activate the native
toolchain and run from the repository root:

```sh
eval "$(opam env --switch=census)"
make -C small -j2
make -C small check
```

For the complete `(4,2)` value proofs, choose a target:

```sh
make proof-all     # state value; make proof is an alias
make proof-tr-all  # instruction value
```

The wrappers select workers from CPU and available-memory limits; no outer
`make -j` is needed. `tools/census_toolchain.sh` finds a native-capable Coq,
activates the `census` opam switch, or bootstraps that switch. `proof-all` forces
a fresh state census walk; `make census` can resume a matching interrupted walk.

Completed fresh builds used Coq 8.18.0, OCaml 4.14.2, a four-CPU container quota,
and 16 GiB RAM:

| Target | Wall time | Result |
| --- | ---: | --- |
| `make proof-all` | 1 h 48 m 54 s | Passed |
| `make proof-tr-all` | 2 h 15 m 38 s | Passed |

These measurements include proof preparation, prerequisites, census, closeout,
and final theorem checks; the toolchain was already installed. Revision details
and historical measurements are in [`docs/CENSUS_RUNTIME.md`](docs/CENSUS_RUNTIME.md).

For the complete **state `(2,4)` build under verification**, run:

```sh
make proof-2-4 BUILD_JOBS=8 STATE24_PROVIDER_LIGHT=1
```

This prepares the selected source graph, compiles it, checks the exact statement
and numeric value, reports its assumptions, and runs both full recursive audits.
Only a successful complete run establishes the global state result. Its runtime
and peak memory remain under verification; the `(4,2)` measurements above do not
apply to this target. Resource settings, checkpoint resume, audit logs, and
success criteria are in [`docs/VERIFYING_BBB24.md`](docs/VERIFYING_BBB24.md).

## What is in the tree

| Path | Contents |
| --- | --- |
| [`theories/BBB4_Statement.v`](theories/BBB4_Statement.v), [`theories/BBB4_Spec.v`](theories/BBB4_Spec.v) | `(4,2)` machine model, state quasihalting, champion, and maximum claim |
| [`theories/BBBT4_Statement.v`](theories/BBBT4_Statement.v), [`theories/BBBT4_Spec.v`](theories/BBBT4_Spec.v) | Instruction quasihalting and its maximum claim |
| `theories/Checkers/`, `theories/Counters/`, `theories/Machines/` | Verified certificate checkers, symbolic recurrence tools, and machine proofs |
| `theories/Census/`, `theories/Closeout/` | Exhaustive state census and assembly of `BBB4_value` |
| `theories/CensusTr/`, `theories/CloseoutTr/` | Exhaustive instruction census and assembly of `BBBT4_value` |
| [`small/`](small/README.md) | Exact state and instruction values for `(1,2)`, `(2,2)`, `(3,2)`, and `(2,3)` |
| [`four/`](four/README.md) | `(2,4)` champion, census, certificate checkers, and state proof assembly |
| `theories/Tests/` | Corruption tests that reject invalid certificates and claims |
| `tools/` | Certificate searches, source generators, validators, and build tools |
| [`docs/`](docs/README.md) | Claims, verification guides, measured runtimes, and proof-method documentation |

## The trust story

The machine model and maximum specification determine what is proved. The
census coverage theorem and all machine certificates are checked in Coq;
search results, machine counts, and progress percentages are not proof premises.
The completed `(4,2)` closeouts discharge every deferred case inside Coq.

The completed `(4,2)` value proofs use the standard
`FunctionalExtensionality.functional_extensionality_dep` assumption.
`Print Assumptions` records each theorem's actual footprint.
The `(2,4)` state runner accepts only an empty footprint or that same standard
assumption, checks the exact public statement, and requires both recursive
audits before reporting success. Its generated `Value.v` alias is gated by the
first successful audit.

Search and generation tools are untrusted: the proof checks the certificates
they produce. Corruption tests check that altered certificates are rejected.
See [`docs/CLAIMS.md`](docs/CLAIMS.md) and
[`docs/BBBT4_REVIEW.md`](docs/BBBT4_REVIEW.md) for the `(4,2)` review details.

## Contributing

Independent builds and reviews of the statements are especially useful. For
`(2,4)`, the [scoreboard](https://github.com/carrino/Coq-BBB4/issues/261) tracks
the remaining verification work. When reporting a build, include the commit,
command, Coq and OCaml versions, available RAM, and final report or failure log.

## The instruction-level development

The completed `(4,2)` instruction census has its own recurrence obligations and
closeout. Its verified bound matches the state champion's score, giving
`BBB_tr(4,2) = 32,779,478`. The census uses 96 walk units and closes all 10,924
deferred rows. The final theorem is
[`BBBT4_value`](theories/CloseoutTr/BBBT4_Value.v).

Use `make proof-tr-all` for the full theorem. For component builds, `make instr`
builds the census prerequisites and `make instr-core` builds the slice used in
CI. See [`docs/CLOSEOUT_TR.md`](docs/CLOSEOUT_TR.md) and the
[reviewer's guide](docs/BBBT4_REVIEW.md) for the construction.

## Status and further reading

* [`docs/CLAIMS.md`](docs/CLAIMS.md) — the precise `(4,2)` claim and trust boundary.
* [`docs/VERIFYING.md`](docs/VERIFYING.md) — build commands and expected results.
* [`docs/VERIFYING_BBB24.md`](docs/VERIFYING_BBB24.md) — selected `(2,4)` state
  build, resource controls, audit diagnostics, and checkpoint resume.
* [`docs/CENSUS_RUNTIME.md`](docs/CENSUS_RUNTIME.md) — measured build conditions
  and runtimes.
* [`docs/RESIDUE_MAP.md`](docs/RESIDUE_MAP.md) — how the `(4,2)` state holdouts
  were proved.
* [`docs/REACHST_TIER.md`](docs/REACHST_TIER.md) and
  [`docs/LADDER_PLAN.md`](docs/LADDER_PLAN.md) — two of the proof methods used
  for difficult machines.
* [`SCOPING.md`](SCOPING.md) and [`NEXT_SESSION.md`](NEXT_SESSION.md) — the
  historical scope and development notebook.
