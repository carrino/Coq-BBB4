# Coq-BBB4

[![CI](https://github.com/carrino/Coq-BBB4/actions/workflows/ci.yml/badge.svg)](https://github.com/carrino/Coq-BBB4/actions/workflows/ci.yml)

A Coq formalization of the Beeping Busy Beaver problem on 4-state,
2-symbol Turing machines, culminating in the kernel-checked value
theorem **BBB(4) = 32,779,478** — built from the certificates of the
[BBB harness](https://github.com/carrino/BBB) on the patterns of
[Coq-BB5](https://github.com/carrino/Coq-BB5) and
[busycoq](https://github.com/carrino/busycoq).

## The result

**BBB(4) = 32,779,478.**

The claim is stated in [`theories/BBB4_Spec.v`](theories/BBB4_Spec.v) —
that file plus the machine model it imports
([`theories/BBB4_Statement.v`](theories/BBB4_Statement.v)) is the
entire trusted statement surface: two short files, and nothing in
either depends on the census, the checkers, or the closeout:

```coq
tm_champion    : TM                       (* 1RB1LD_1RC1RB_1LC1LA_0RC0RD  *)
champion_score : nat := N.to_nat 32779478

Attains tm B   : Prop := exists q s, QuietAfter tm q s /\ S s = B

BBB4_is B      : Prop :=
  (exists tm, Attains tm B)                       (* ATTAINED *)
  /\ (forall tm B', Attains tm B' -> B' <= B)     (* MAXIMAL  *)

BBB4_statement : Prop := BBB4_is champion_score
BBB4_is_unique : forall B B', BBB4_is B -> BBB4_is B' -> B = B'
```

`make proof` builds and reports the proof
(`theories/Closeout/BBB4_Value.v`, kernel-checked, `Qed`):

```coq
BBB4_value       : BBB4_statement
champion_attains : Attains tm_champion champion_score
```

Some state of some (4,2) Turing machine makes its last visit at
configuration index 32,779,477 — score exactly **32,779,478** in the
harness convention (last visit + 1) — and no state of any (4,2) machine
is ever quiet after a later index.  The witness is the champion
`1RB1LD_1RC1RB_1LC1LA_0RC0RD`, whose state `D` goes quiet at exactly
that index (kernel-checked by two binary-fuel `vm_compute` runs in
`theories/Machines/Counters/Champion_*.v`); the upper bound is the
census + closeout chain (`bbb4_target`) with its residue disjunct
discharged — as of 2026-08-01 the residue lists are **empty** (0 core
rows, 0 shadows; the frozen census's 5,156 deferred rows are settled
5,156-for-5,156), so `~ skipped [] tm` closes the last gap
(`not_skipped_nil`, `BBB4_Value.v`).

The two-disjunct reading survives as `bbb4_unconditional`: every (4,2)
machine either quasihalts with score at most 32,779,478 or never
quasihalts — no skips, no residue.

What "BBB" means here — the state-level quasihalting convention, and
what this does *not* claim (it is not BB(4), and machine-count
bookkeeping stays untrusted) — is stated precisely in
[`docs/CLAIMS.md`](docs/CLAIMS.md).

**Axiom footprint: `functional_extensionality_dep`, and nothing else**
(`BBB4_is_unique` is axiom-free).  There are zero `Admitted` in
`theories/`.  Verify with `Print Assumptions BBB4_value` (printed
during `make proof`) or independently with `coqchk -o`.

### And at instruction level: BBB_tr(4) = 32,779,478

The harness's second convention scores the last fire of each
*instruction* (state, read symbol) instead of each state's last visit.
Its value is the same number, attained by the same champion:

```coq
AttainsTr tm B   : Prop := exists t s, QuietAfterTr tm t s /\ S s = B
BBBT4_is B       : Prop :=
  (exists tm, AttainsTr tm B) /\ (forall tm B', AttainsTr tm B' -> B' <= B)
BBBT4_statement  : Prop := BBBT4_is champion_score

BBBT4_value      : BBBT4_statement     (* theories/CloseoutTr/BBBT4_Value.v *)
```

The claim is [`theories/BBBT4_Spec.v`](theories/BBBT4_Spec.v), with
[`theories/BBBT4_Statement.v`](theories/BBBT4_Statement.v) for
`FiresAt` and `QuietAfterTr`.  One command proves it from a fresh
clone:

```sh
make proof-tr-all 2>&1 | tee proof-tr-all.log
```

It ends with `proof-tr-all COMPLETE` and the `Print Assumptions
BBBT4_value` block, which should list `functional_extensionality_dep`
and nothing else.  It was verified end to end on 2026-10-06
([`docs/BBBT4_REVIEW.md`](docs/BBBT4_REVIEW.md) §8.1).  It needs the
same census opam switch as `make proof` and about 6 GB of RAM per
walk job.  It is much longer than the state build: most of a day on
8 cores / 32 GB, with work under way to bring that down.  Details are
in [`docs/VERIFYING.md`](docs/VERIFYING.md), Tier C.

## The verification ladder

Three rungs for BBB(4), in increasing order of paranoia — each needs
strictly less trust than the one before — and a fourth that proves the
instruction-level value the same way.  A fresh clone carries **no binaries**: since
2026-10-07 the census `.vo` are not committed either, so the full proof
is one from-source build on your own machine.

1. **Read the claim.**  [`theories/BBB4_Spec.v`](theories/BBB4_Spec.v)
   (with [`theories/BBB4_Statement.v`](theories/BBB4_Statement.v)) is
   the complete formal statement;
   [`docs/CLAIMS.md`](docs/CLAIMS.md) states in prose exactly what is
   proved — and what is not.  Trust: the authors.
2. **`make`** (stock Coq 8.18, no opam, ~1–2 h).  Rebuilds every
   checker, every board theorem, the champion's exact score, and
   `closeout_partial` — the entire boarding argument — **from source**.
   Trust: the Coq kernel.
3. **`make proof`** (= `make proof-all`) — **the whole claim from
   source, one command, ~80–90 min.**  The state-level base build, then
   the census walk on your machine, then the closeout chain and
   `Print Assumptions BBB4_value`.  Nothing is precompiled; the `Axioms:`
   block at the end is the entire trust surface.  Trust: the kernel
   alone.

   Measured end to end 2026-08-12 on 8 physical cores / 31 GB, from
   `git clean -fdx` with nothing pre-configured: **79 m 38 s**
   (742 core-min) — a ~40 min base build, a **42 m 36 s** census walk,
   and the closeout chain.  The walk alone is
   `make census-verify WALK_JOBS=8`.  Nothing to set up and no `-j` to
   pass: `tools/census_toolchain.sh` finds a native-capable Coq, or
   activates the `census` opam switch (`opam env` does not survive a
   new terminal), or creates that switch — the only step needing your
   package manager is installing `opam` itself.  It sizes the
   base build from `nproc` (`BUILD_JOBS`) and the walk from *physical*
   cores (`WALK_JOBS`) — the walk is memory-bandwidth bound, so SMT
   threads do not help it.  The walk is resumable per-unit, so
   an interrupted walk picks up where it stopped.  Needs ~10 GB RAM
   (`Compute/Census_Theorem.v` runs alone at 6.3 GB) and the census
   opam switch.
4. **`make proof-tr-all`** — **the instruction-level claim from
   source, one command.**  `BBBT4_value : BBBT4_statement`
   (BBB_tr(4) = 32,779,478): the instruction-level census walk, the
   10,924-row closeout, the champion, and `Print Assumptions
   BBBT4_value`.  Nothing is precompiled.  Trust: the kernel alone.
   Most of a day on 8 cores / 32 GB as of 2026-10-06; same toolchain
   as rung 3, and about 6 GB of RAM per walk job.

For the extra-careful, `coqchk -o` re-verifies compiled proof terms
with the standalone checker at any rung.  Full instructions and the
expected outputs for every rung: [`docs/VERIFYING.md`](docs/VERIFYING.md).

## Building

Requires Coq 8.18 and Python 3 (the Python is reporting/generation
tooling only — it carries no proof weight).

```sh
make -j8        # the full from-source build: every checker, board and
                # the closeout, on stock Coq -- no committed binaries
make proof      # the whole claim from source: base build, census walk,
                # BBB4_value and its report (~80-90 min, census switch)
make proof-tr-all  # the instruction-level claim from source:
                # BBBT4_value, BBB_tr(4) = 32,779,478 (census switch,
                # ~6 GB per walk job; most of a day on 8 cores / 32 GB)
```

**Or, to trust nothing but the kernel, one command:**

```sh
make proof-all  # base build + re-walk the census + the closeout chain
                # 79 m 38 s measured on 8 cores / 31 GB, from a clean
                # tree (~40 min build, 42 m 36 s walk).
                # Needs the census opam switch and >= 10 GB RAM.
                # Out of the box.  It uses a native-capable coqc if you
                # have one, otherwise activates the census opam switch,
                # otherwise CREATES it (opam is user-level -- the only
                # manual step is installing opam itself).  It also
                # regenerates Makefile.coq for that toolchain and sizes
                # both fan-outs (build from nproc, walk from physical
                # cores).  Override:
                #   make proof-all BUILD_JOBS=16 WALK_JOBS=8
                #   make proof-all CENSUS_SWITCH=my-switch
```

High `-j` is fine on a big machine: the nine memory-heavy
`IRules_Batch_*` files (~6–8 GB each at peak) are throttled to at most
three concurrent builds by order-only chains in `Makefile.coq.local`,
so `make -j16` budgets ~24 GB for them while the rest of the tree fills
the remaining slots.  On a ~16 GB box use `make -j2`, or tighten the
chains in `Makefile.coq.local` to a single column.

`make proof` (the same as `make proof-all`) additionally walks the census
(`theories/Census/Compute/`, a 385-core-minute `native_compute`
enumeration of the whole (4,2) space) on your machine.  It needs
`native_compute`, so it runs under the census opam switch (OCaml 4.14.2,
Coq 8.18.0, `coq-native`), which `tools/census_toolchain.sh` sets up:

```sh
make proof-all       # everything from source, 79 m 38 s (recommended)
make census-verify   # just the walk: 42 m 36 s at WALK_JOBS=8 on 8
                     # physical cores / 31 GB, measured 2026-08-12.
                     # 303 core-min; RAM no longer binds above ~10 GB.
```

[`docs/VERIFYING.md`](docs/VERIFYING.md) walks through every
verification tier, from "check one machine" to "re-walk the census".

## What is in the tree

| Path | Contents |
| --- | --- |
| `theories/BBB4_Statement.v` | The (4,2) machine model and the quasihalting semantics: `VisitsAt`, `QuietFrom`, `QuietAfter`, `QuasiHaltsSt`, `NeverQuasiHaltsSt` |
| `theories/BBB4_Spec.v` | The claim: `tm_champion`, `champion_score`, `Attains`, `BBB4_is`, `BBB4_statement`, `BBB4_is_unique` — with `BBB4_Statement.v`, the entire trusted statement surface; depends on nothing census-side |
| `theories/Checkers/` | The verified certificate checkers: cyclers, translated cyclers, n-gram closures with ranking/pattern measures, RepWL, fuel/drift rules, inductive-rules (irules) engines, quasihalt wrappers |
| `theories/Closure.v` | The generic covering-abstraction / liveness engine the n-gram and RepWL checkers instantiate |
| `theories/Machines/` | Per-machine theorems: the generated boards (`Bulk/`, batch files) plus individually proved counter machines (`Machines/Counters/`) — thousands of files; `tools/closeout/audit.py` prints the live count |
| `theories/Counters/` | The windowed-run toolkit for hand-proved machines: `WTape`, `LapGlue`/`WaveCounter`/`MeasureGlue` closers, shared counter encodings |
| `theories/Checkers/ReachSt.v`, `ReachStI.v` | The termination checker behind the REACHST tier: a machine's liveness obligation for one state, discharged as termination of the STATE-DELETED sub-machine (`docs/REACHST_TIER.md`) |
| `theories/Checkers/Ladder*.v`, `theories/Machines/Ladder/` | The ladder: counter segments carried as a value-indexed rule family, its fill law read off the machine rather than assumed (`docs/LADDER_PLAN.md`) |
| `theories/Census/` | The trusted census: TNF enumeration, the in-walk deciders, the frozen deferred tables, and the walk units (`Compute/`, run by `make proof`) ending in `census_decided` |
| `theories/Closeout/` | The assembly: generated stages bridging every decided frozen row to its board, `closeout_partial`, `census_boarded`, `bbb4_target`, and the hand-written `BBB4_Value.v` — the BBB(4) = 32,779,478 value theorem |
| `theories/BBBT4_Statement.v`, `theories/BBBT4_Spec.v`, `theories/BBBT4_Champion.v`, `theories/CensusTr/`, `theories/Checkers/*Tr.v`, `theories/Machines/CountersTr/` | The **instruction-level (transition-level) development**: the claim BBB_tr(4) = 32,779,478, the beeping semantics at instruction granularity, the ported checkers, the transition-level census walk and its proven tier — see the section below |
| `theories/Tests/` | Negative controls in the BBB corruption-test tradition: mutated certificates, periods, sides and claims must all fail |
| `tools/` | **Untrusted** certificate search, generators, and differential validators — a wrong certificate fails to compile, never proves a false theorem |
| `docs/` | The prose claim, verification guide, and closing-campaign write-ups, plus the historical lab notebook — [`docs/README.md`](docs/README.md) is the index |

## The trust story

* The kernel checks everything: every certificate emitted by the
  untrusted Python is re-derived or re-checked inside Coq
  (`vm_compute`/`native_compute`), so `tools/` need not be read to
  believe a theorem.
* Every checker feature ships with corruption tests
  (`theories/Tests/*_Corruption.v`) that must reject tampered
  certificates.
* Nothing precompiled is trusted: no `.vo` are committed, and
  **`make proof` re-derives the census and the whole value theorem
  from source in ~80–90 min** on 8 cores / 32 GB.  The census `.vo`
  used to be committed and hash-guarded; that cache was removed on
  2026-10-07, so the proof is one from-source build.
* The partition audit (`tools/closeout/audit.py`) is untrusted Python —
  but with the residue empty it carries no weight for the value
  theorem: `not_skipped_nil` discharges the skip disjunct inside Coq,
  so no table edit can change `BBB4_value`.  It remains bookkeeping
  for the frozen tables and per-row attribution.

## Contributing

The burndown is DONE — `tools/closeout/core_rows.txt` and
`tools/closeout/shadow_rows.tsv` are empty, and
`python3 tools/closeout/audit.py` reports 5,156 of 5,156 settled.  What
remains valuable now is **verification**: independent re-runs of the
ladder above (especially `make census-verify` on hardware that can
afford it), `coqchk -o` over the full closure, and scrutiny of the
statement in [`docs/CLAIMS.md`](docs/CLAIMS.md).
[`docs/TERMINOLOGY.md`](docs/TERMINOLOGY.md) has the vocabulary and
[`NEXT_SESSION.md`](NEXT_SESSION.md) the accumulated traps;
[`docs/RESIDUE_MAP.md`](docs/RESIDUE_MAP.md) records how each family of
machines fell.

## The instruction-level development

The BBB harness's second convention scores a machine by the last time
each *instruction* (state, read symbol) fires rather than each state.
The obligation "every fired instruction recurs" (`NeverQuasiHaltsTr`,
`theories/BBBT4_Statement.v`) is strictly stronger than the state one,
so the census has to be re-decided.  This tree carries that
re-decision alongside the finished state-level proof, without touching
it:

* `theories/BBBT4_Statement.v` — `Instr`, `FiresAt`, `QuietAfterTr`,
  `QuasiHaltsTr`, `NeverQuasiHaltsTr`, and the bridges to the state
  level.
* `theories/Checkers/*Tr.v`, `theories/ClosureTr.v`,
  `theories/CensusTr/RepWLTr.v`, `theories/Counters/LapGlueTr.v` — the
  checkers ported to instruction targets (cyclers, translated cyclers,
  n-gram closures with rank/lex certificates, history-augmented
  n-grams, RepWL, the inductive-rules engine, lap certificates), each
  with a soundness theorem concluding `NeverQuasiHaltsTr`.
* `theories/CensusTr/` — the transition-level census: `TNF_QHTr`
  (the census contract at the raised bound `B_tr = 32,779,478`),
  `DecideTr`/`RunTr` (the in-walk decider), `RunTr_Split` (the
  kernel-checked frontier split), the frozen deferred tables
  (`DeferredTr_*`, 10,924 rows) and the two proven tiers: `prov_tr`,
  7,353 never-quasihalting machines as certificate stages
  (`ProvTr_TC_*` translated cyclers, `ProvTr_Lap_*` lap boards from
  `Machines/CountersTr/`, `ProvTr_RW_*` RepWL at the tape period,
  `ProvTr_IR_*` and `ProvTr_RK_*` the state census's irules
  certificates and rank rungs re-checked at instruction level), and
  `provqh_tr`, 5,534 quasihalting machines with every quiet
  instruction's last fire proved at most `B_tr` (`ProvTr_QH_00..02`
  translated cyclers via `Checkers/TCyclerQHTr`, `ProvTr_QH_03..15`
  the `LAPQ_*` counter boards via `Counters/LapGlueQHTr`,
  `ProvTr_QH_16..39` quiet-instruction bouncers via the wrapped RepWL
  tier and `CensusTr/QHConveyorTr`).
* The census theorem `census_tr : forall tm, QHBoundTr B_tr tm \/
  Deferred D_tr tm` is assembled from 96 native-compute walk units
  (`theories/CensusTr/Compute/`, generated; not part of the default
  build).  Last checked 2026-09-24 against the v10 tables (10,924
  deferred rows) with the 7,353 + 5,534 proven machines:
  `make census-tr-units && make census-tr-walk WALK_JOBS=5` (a unit
  peaks near 5.8 GB, so 5 at once fit a 32 GB box with no swap; the
  job count is a memory budget, see the Makefile).  `Print Assumptions` on `census_tr` and on the proven
  tiers' `prov_tr_all` and `provqh_tr_all` reports
  `functional_extensionality_dep` and nothing else -- the same single
  axiom as the state-level proof.

The census is now frozen at v10.  The deferred rows are settled
outside it by batch files in `theories/CloseoutTr/` (`make closeout-tr`,
checked by CI in seconds, no re-walk), in parallel workstreams:
[`docs/CLOSEOUT_TR.md`](docs/CLOSEOUT_TR.md).  As of 2026-10-05 all
10,924 rows are boarded (626 batches).  `closeout_tr_complete`
(`CloseoutTr/CloseoutTr.v`, CI) closes every deferred row.
`bbbt4_bound : forall tm, QHBoundTr B_tr tm` (`CloseoutFinalTr.v`)
is the unconditional instruction-level upper bound, after
`make proof-tr-all` (the instruction-level `make proof-all`; native
toolchain, most of a day; see Tier C of
[`docs/VERIFYING.md`](docs/VERIFYING.md)).  The same champion attains it (`BBBT4_Champion.v`), so
**BBB_tr(4) = 32,779,478**: `BBBT4_value : BBBT4_statement`
(claim in `theories/BBBT4_Spec.v`, proof in
`theories/CloseoutTr/BBBT4_Value.v`, box only;
[`docs/CLAIMS.md`](docs/CLAIMS.md); reviewer's guide and cross-checks:
[`docs/BBBT4_REVIEW.md`](docs/BBBT4_REVIEW.md)).

Build: `make proof-tr-all` for the value theorem.  For partial
builds, `make instr` builds the walk's prerequisites (statement,
checkers, proven tiers, deferred tables; ~9 CPU-hours beyond the
BBB(4) build) and `make instr-core` builds the slice CI compiles.
`SCOPING_INSTR.md` is the running record
of the scoping, the measured population, the routes per machine class
and the open classes (section 7), and `tools/censustr/` holds the
untrusted generators (`gen_walk_units.py`, `gen_listburn.py`,
`gen_provtr_*.py`, `rw_period_rows.py`, `proven_specs.py`).

## Status and further reading

* [`docs/CLAIMS.md`](docs/CLAIMS.md) — what is proved, exactly,
  including what is **not**.
* [`docs/RESIDUE_MAP.md`](docs/RESIDUE_MAP.md) — the residue map,
  now closed out: how each shape and blocker fell.
* [`docs/REACHST_TIER.md`](docs/REACHST_TIER.md) — the tier with the
  shortest explanation: a counter's liveness is a TERMINATION question
  about the state-avoiding sub-machine, which is usually far simpler than
  the machine.  127 rows over two waves.
* [`docs/LADDER_PLAN.md`](docs/LADDER_PLAN.md) — the ladder, the
  endgame's main producer: a counter segment carried as a value-indexed
  rule family whose fill law, code and step are read OFF the machine
  rather than assumed.  A design record with its append-only build log.
* [`docs/VERIFYING.md`](docs/VERIFYING.md) — how to check any of this
  yourself.
* [`SCOPING.md`](SCOPING.md) — the original inventory and phased plan
  (historical).
* [`NEXT_SESSION.md`](NEXT_SESSION.md) — the internal development log:
  per-wave findings, traps, and the compute playbook.  Kept verbatim as
  the project's lab notebook.
