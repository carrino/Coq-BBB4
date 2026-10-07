# Reviewing BBB_tr(4) = 32,779,478

This is a guide for checking the instruction-level result yourself. It covers
what exactly is claimed, which files you must read to trust the claim, how the
proof is built, what is checked where, and what independent evidence agrees
with it. [`CLAIMS.md`](CLAIMS.md) has the authoritative statement. This page is
the path through it.

## 1. The claim

Over all 4-state, 2-symbol Turing machines (two-way infinite blank tape,
start state A, undefined transition = halt), score each *instruction*
(state, read symbol) by the step at which it fires for the last time. The
maximum over machines of a finite such score is **32,779,478**. It is
attained by the state-level champion `1RB1LD_1RC1RB_1LC1LA_0RC0RD`, whose
instruction (D, 0) fires for the last time at step 32,779,478.

In Coq (`theories/BBBT4_Spec.v`):

```coq
AttainsTr (tm : TM) (B : nat) : Prop :=
  exists t s, QuietAfterTr tm t s /\ S s = B

BBBT4_is (B : nat) : Prop :=
  (exists tm, AttainsTr tm B)                      (* ATTAINED *)
  /\ (forall tm B', AttainsTr tm B' -> B' <= B)    (* MAXIMAL  *)

BBBT4_statement : Prop := BBBT4_is champion_score  (* 32,779,478 *)
```

The value equals the state-level BBB(4). It cannot be smaller: the spec file
proves `BBB4_le_BBBT4 : BBB4_is v -> BBBT4_is v' -> v <= v'` with no axioms.
The instruction convention can only add scores. It is not larger: that is the
theorem.

## 2. What you have to read (the trusted surface)

There are four files, 588 lines in all. They import only each other and the
Coq standard library:

| File | Lines | Contents |
|---|---|---|
| `theories/BBB4_Statement.v` | 191 | The machine model: `TM`, `step`, `stepn`, `InitES`, `VisitsAt` |
| `theories/BBBT4_Statement.v` | 175 | `Instr`, `FiresAt`, `QuietAfterTr`, `QuasiHaltsTr`, and bridges to the state level |
| `theories/BBB4_Spec.v` | 115 | `tm_champion`, `champion_score = N.to_nat 32779478` |
| `theories/BBBT4_Spec.v` | 107 | `AttainsTr`, `BBBT4_is`, `BBBT4_statement`, and sanity lemmas |

Nothing else needs to be read to understand what is claimed. The census,
the checkers and the 626 closeout batches are all *proof*, and the kernel
checks them.

### Mapping to the harness convention

These are the definitions in the harness README (carrino/BBB, "Transition-level
bookkeeping"):

| Harness | Coq |
|---|---|
| transition = (state, read symbol), S·K of them | `Instr := (St * Sym)`, 8 for (4,2) |
| transition fires at step n+1 | `FiresAt tm t n`: after `n` steps the machine is in `fst t` reading `snd t` |
| quasihalts iff some transition fires ≥ 1 time but finitely often | `QuasiHaltsTr`: some `t` with `FiredTr` and `QuietFromTr` |
| score = last firing step among such transitions | `QuietAfterTr tm t s` (last fire at index `s`), score `S s` |
| never-fired transition (class N) does not count | `QuietAfterTr` contains the fire |
| halting machines quasihalt trivially | no configuration after the halt, so every fired instruction is quiet |

The harness README's own example is checked in Coq, in
`theories/Tests/ConventionTr_Example.v`. That example is `1RB1LA_0LA1RA`,
which quasihalts at transition level with B0 last firing at step 7, but does
not quasihalt at state level. Our predicates say the same: `example_qh_tr`,
`example_not_qh_st`, `example_B0_step7` and `example_score_le7`.

## 3. How it is proved

```
BBBT4_value : BBBT4_statement                                   CloseoutTr/BBBT4_Value.v
 ├─ ATTAINED: champion_attains_tr                               BBBT4_Champion.v
 │    champion_quiet_after_D0 : QuietAfterTr tm_champion (D,0) 32779477
 │      one binary-fuel vm_compute pins (D, 0) at index 32,779,477;
 │      the state proof's tail lemma: only C is entered from 32,779,478 on
 └─ MAXIMAL: bbbt4_bound : forall tm, QHBoundTr 32779478 tm     CloseoutTr/CloseoutFinalTr.v
      ├─ census_tr : forall tm, QHBoundTr B_tr tm \/ Deferred D_tr tm
      │    96 native-compute walk units over the TNF tree        CensusTr/Compute/
      │    in-walk decider + 7,353 never-QH / 5,534 QH proven machines
      └─ closeout_tr_complete : Deferred D_tr tm -> QHBoundTr B_close tm
           626 batch files, 10,924 rows, each with a coversTr proof  CloseoutTr/
```

The census transports `Deferred` through state swaps, mirroring and completion
of undefined entries, the same quotient the TNF tree uses. A closeout batch
row proves `coversTr h`: every machine that completes the partial machine `h`
satisfies `QHBoundTr 32779478`. Many of these are never-quasihalting proofs,
which satisfy the bound vacuously.

## 4. Trust boundary and axioms

- **Axioms.** Only `functional_extensionality_dep`, the same single axiom as
  the state-level proof. There are no `Admitted`, and no switches for guard,
  positivity or universe checking anywhere in `theories/`.
- **Checked by CI on every push.** The core library; every closeout batch,
  in 6 shards; and `CloseoutTr.vo`, which contains `closeout_tr_complete` and
  the reflective split over all 10,924 rows.
- **From source, anywhere.** `BBBT4_Spec.v` and `BBBT4_Champion.v`, which
  take about 3 minutes, and the tests.
- **Box only.** The census walk (`make census-tr-walk`) uses
  `native_compute`. Each unit peaks near 5.8 GB, so it needs the census opam
  switch with `coq-native` and about 32 GB of memory. `CloseoutFinalTr.v` and
  `BBBT4_Value.v` load its output. Expect roughly 9 CPU-hours, or about 2 h
  wall time at 5 jobs. With `native_compute`, the native compiler, and so the
  OCaml toolchain, is part of the trusted base. The state-level census has the
  same dependency.

## 5. Independent evidence (untrusted, re-runnable)

None of this is needed by the kernel. All of it would be embarrassing if it
disagreed.

- **The champion, re-simulated.** `tools/bbbt4/refire.c`, a 100-line C
  simulator unrelated to the Coq development, was run to 40,000,000 steps.
  (D, 0) fires 5,105 times, last at index 32,779,477. Every other
  instruction except (C, 0) is quiet earlier: (D, 1) at 32,779,476, (A, 1) at
  32,769,237, (C, 1) at 32,769,236, and (A, 0), (B, 0) and (B, 1) by 11.8M.
  (C, 0) fires at every step from 32,779,478 on.
- **Negative controls.** `theories/Tests/ChampionTr_Corruption.v`: (D, 1)
  does not fire at 32,779,477, and (D, 0) does not fire at 32,779,478.
- **The harness's hardest machines.** See the next section.

## 6. The 432 machines the harness could not decide

`SCOPING_INSTR.md` §2, written before the census, expected the
instruction-level value to be far above 32,779,478. Its evidence was the
harness's `results/champhunt/cull.csv`: 432 machines undecided at 10^10 steps.
They are rare-fire counters, and their quietest instructions had last fired
billions of steps in. If any of them really went quiet, its score would be
in the billions. `tools/bbbt4/cull_audit.py` checks what the proof says about
each of them, and what it predicts.

**Coverage.** Every one of the 432 is settled by a kernel-checked object:

| Settled by | Machines |
|---|---|
| a closeout batch, `coversTr` of a deferred row it completes | 312 (`CBT_SP` 206, `CBT_SPW` 52, `CBT_TA` 21, `CBT_TI` 17, `CBT_DXQ` 14, `CBT_AST` 2) |
| the census's proven tiers (`prov_tr` / `provqh_tr`) | 51 |
| the walk's own decider, inside `census_tr` | 69 |

**Prediction.** `bbbt4_bound` means no instruction can go quiet after firing
at an index of 32,779,478 or more. So every instruction seen firing at or
past that index must fire again after any horizon. `refire.c` checked this on
every machine. It recorded which instructions fired at or past 32,779,478 by
a horizon of 10^9, then kept running until each of them fired again:

**3,395 instructions on 432 machines were predicted to fire again, and all
3,395 did.** The latest re-fire was at step 7,794,655,204
(`1RB0LD_1RC1RB_1LA1LC_0RC1LA`), and the median at about 1.43 × 10^9. Not
one instruction contradicted the theorem.

Past the harness's own horizon:

The 8 machines with the stalest instructions in the harness's own 10^10
data were run again to 10^10 and beyond (cap 2 × 10^11). These are the
machines where some instruction had been silent since about 1.2–1.3 × 10^9.

- **The harness agrees with the independent simulator.** All 64
  per-instruction fire counts and last fires at 10^10 match `cull.csv`
  exactly. The harness's last-fire *step* is always our configuration
  *index* + 1, which is the `S s` convention of §2.
- **Every stale instruction fired again.** In the stalest machine,
  `1RB0RC_1RC1RB_1LD1RA_1LB1LD`, A0 fired 8 times by 10^10, the last at step
  1,202,895,087, and then again at 19,247,442,615. In the other seven, the
  silent instructions came back at about 1.18 × 10^10. These are binary
  counters whose rare instruction fires once per overflow, at roughly
  geometric intervals. The theorem says they never stop. The harness alone
  could not tell them apart from a quasihalt with a score in the billions.

Raw output: [`bbbt4_horizon_1e10.txt`](bbbt4_horizon_1e10.txt). The format
is `T<q><a>:<count>:<last index before 10^10>:<next fire>`.

Rerun:

```
gcc -O2 -o refire tools/bbbt4/refire.c
cut -d, -f1 cull.csv | tail -n +2 | ./refire 1000000000 30000000000 > refire.out
python3 tools/bbbt4/cull_audit.py cull.csv refire.out --tsv audit.tsv
./refire 10000000000 200000000000 < stalest8.txt > horizon.out   # past 10^10
```

The per-machine table is [`bbbt4_cull_audit.tsv`](bbbt4_cull_audit.tsv).

## 7. Reproducing the proof

One command, on a fresh clone, mirrors the state level's `make proof-all`:

```
git clone https://github.com/carrino/Coq-BBB4 && cd Coq-BBB4
make proof-tr-all 2>&1 | tee proof-tr-all.log
```

It does the following:

- Sets up a Coq with `native_compute` via `tools/census_toolchain.sh`,
  creating the `census` opam switch if needed.
- Checks that the generated files match the commit.
- Walks the census (`census_tr`).
- Builds the 626 closeout batches and `CloseoutTr.vo`, the champion, and the
  instruction-level tests.
- Compiles `CloseoutFinalTr.v` (`bbbt4_bound`) and `BBBT4_Value.v`
  (`BBBT4_value`).

The `Axioms:` block it prints for `BBBT4_value` should list
`functional_extensionality_dep` and nothing else. Nothing committed is
trusted, because the instruction-level walk has no committed `.vo`. Memory
sets the job counts: a walk unit peaks near 5.8 GB. Override with
`WALK_TR_JOBS=` and `CLOSEOUT_TR_JOBS=`. Budget several hours on an
8-core, 32 GB machine.

The same steps by hand:

```
make census-tr-walk WALK_JOBS=4
make -f Makefile.coq theories/CloseoutTr/CloseoutTr.vo theories/BBBT4_Champion.vo \
  theories/Counters/BlankTailTr.vo
coqc -Q theories BBB4 theories/CloseoutTr/CloseoutFinalTr.v
coqc -Q theories BBB4 theories/CloseoutTr/BBBT4_Value.v
```

For an independent re-check of the compiled terms, run
`coqchk -o -Q theories BBB4 BBB4.CloseoutTr.BBBT4_Value`. See
[`VERIFYING.md`](VERIFYING.md) for the census switch and the coqchk caveats.

## 8. Status

| Item | State |
|---|---|
| Claim stated (`BBBT4_Spec.v`) | done |
| Lower bound (`BBBT4_Champion.v`) | done, builds from source |
| Closeout: 10,924 of 10,924 rows (`closeout_tr_complete`) | done, CI |
| Upper bound and value (`CloseoutFinalTr.v`, `BBBT4_Value.v`) | **done, verified end to end** (§8.1) |
| `coqchk` of the full chain | pending, box |
| Independent reproduction on a second machine | pending |

### 8.1 The verification run (2026-10-06)

`make proof-tr-all` was run on a fresh clone at commit
`d9dc41d08d0b19138af88d414ab458d302ad69e9`. That commit's tree,
`f52855192fde74694f2ef647877f9658ec1a322f`, is identical to main after
PR #242. The toolchain was Coq 8.18.0 with OCaml 4.14.2 (the `census` opam
switch, native compiler present), on an 8-core / 32 GB WSL2 box at 4 walk
jobs and 9 batch jobs. The run did the following:

- built the walk prerequisites;
- walked all 96 census units: `>>> units done: 96 / 96`, then
  `census_tr : forall tm, QHBoundTr B_tr tm \/ Deferred D_tr tm -- CHECKED`;
- compiled all 626 closeout batches, `CloseoutTr.vo`, the champion and the
  instruction-level tests;
- compiled `CloseoutFinalTr.v` and `BBBT4_Value.v`, which printed:

```
Axioms:
FunctionalExtensionality.functional_extensionality_dep
  : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
    (forall x : A, f x = g x) -> f = g
------------------------------------------------------------
proof-tr-all COMPLETE at d9dc41d08d0b19138af88d414ab458d302ad69e9.
BBBT4_value : BBBT4_statement  (BBBT4_Spec.v: BBB_tr(4) = 32,779,478)
```

The first attempt stopped in the closeout step. `COQNATIVE` overflowed
the default 8 MB stack on `CBT_AST_134`..`136`. That was a build-script
problem, not a proof failure, and PR #243 fixes it by raising the stack as
`make all` does. The run resumed with `ulimit -s unlimited`, kept every
finished `.vo`, re-checked the walk assembly and completed.

The run took most of a day of wall time. Two RepWL stages,
`ProvTr_RW_14` and `ProvTr_RW_15`, took about 4 h 20 min and over 2 h on
one core each, and gated the walk. The walk itself took 13.1 CPU-h: a
median of 435 s per unit and a slowest unit (`UnitTr_63`) of 1,313 s, so
about 3.3 h of wall time at 4 jobs. Per-unit times are in
[`bbbt4_walk_times_2026-10-06.txt`](bbbt4_walk_times_2026-10-06.txt).
Cutting the build time is the next piece of work.
