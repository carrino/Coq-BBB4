# Verifying this repository

_What to run, what to expect, and where you are being asked to trust
something.  The claim itself is in [`docs/CLAIMS.md`](CLAIMS.md)._

The `(4,2)` development has three tiers. **Tier A needs no opam**; it verifies every board and
the whole boarding argument.  Tier B adds the census walk and the value
theorem: `make proof`, the whole claim from source in one command.  Tier C is
the instruction-level value, BBB_tr(4) = 32,779,478: `make proof-tr-all`, also
one command. No `.vo` are committed (since 2026-10-07); a fresh source
checkout starts without compiled project artifacts.

For the exact `(1,2)`, `(2,2)`, `(3,2)` and `(2,3)` values, use the separate
[small-machine build](#small-machine-proofs) below. It proves both state and
instruction values without running the `(4,2)` exhaustive census.

## Reproduce the complete targets

The tested native toolchain is **Coq 8.18.0, OCaml 4.14.2 and `coq-native`**,
with GNU make and Python 3. Completed fresh builds on Linux with a four-CPU
quota and 16 GiB RAM took **1 h 48 m 54 s for `proof-all`** and
**2 h 15 m 38 s for `proof-tr-all`**. Lower-memory configurations and a
sub-hour desktop run have not been validated. See
[`CENSUS_RUNTIME.md`](CENSUS_RUNTIME.md) for exact conditions and history.

Install opam and its system prerequisites, then set up the tested switch once:

```bash
opam switch create census 4.14.2
opam install --switch=census coq.8.18.0 coq-native
eval "$(opam env --switch=census)"
```

The proof wrappers can also find an existing native-capable Coq, activate
`census`, or bootstrap it through `tools/census_toolchain.sh`. Automatic setup
may download and build the toolchain; that one-time cost is outside the
reported installed-toolchain timings. The helper checks native availability;
the versions above identify the measured configuration.

Choose `make proof-all` (or its alias `make proof`) for the state theorem,
or `make proof-tr-all` for the instruction theorem. No outer `make -j` is
needed: the wrappers size their workers from CPU and available-memory limits.
For a timed TR run with a preserved exit status and full log, use Bash:

```bash
set -o pipefail
unset OCAMLPARAM OCAMLRUNPARAM CAMLRUNPARAM COQRUNPARAM
mkdir -p work
python3 tools/time_command.py --log work/proof-total.jsonl \
  --phase proof-tr-all -- make proof-tr-all 2>&1 | tee work/proof-tr-all.log
```

For the state target, substitute `proof-all` in the phase, target and log name.
Use separate fresh source checkouts for comparable full-build timings. Retain
the full log, exit status and actual final `Print Assumptions` block. Under
`census_probes/`, retain `proof-state-times.jsonl` / `state-unit-times.jsonl`
for state, or `proof-tr-times.jsonl` / `censustr-unit-times.jsonl` for TR.
Those records are nested measurements; do not add them to the full-target
total. Native/data preparation is included; checkout preparation and optional
offline hint/certificate search are separate. A standalone `coqchk -o` audit
is an additional check outside
these target timings.

A TR rerun can reuse current proof objects and completed walk units. In
contrast, `proof-all` calls `census-verify`, which forces a state re-walk while
allowing eligible base proof objects to be reused. Either run is incremental
if it starts with compiled artifacts. A missing, legacy or changed toolchain
stamp causes both proof wrappers to clean compiled proof/native artifacts
before rebuilding; this migration/setup work belongs in the next build's cost.

## Small-machine proofs

Use the native toolchain installed above: **Coq 8.18.0, OCaml 4.14.2 and
`coq-native`**. From the repository root:

```bash
eval "$(opam env --switch=census)"
make -C small -j2             # compile all small value proofs
make -C small check -j2       # build if needed, then recursively run coqchk
```

`make -C small check -j2` also works as the single build-and-audit command
from a fresh checkout. The small Makefile uses the active toolchain; activate
the switch first, since it does not invoke the `(4,2)` toolchain bootstrap
wrappers. The root `make proof-all` and `make proof-tr-all` targets still
build the `(4,2)` results; they do not build these separate small modules.

Expected exact results:

| States, symbols | State | Instruction | Final theorem |
| --- | ---: | ---: | --- |
| `(1,2)` | 1 | 1 | [`BBB12_value`](../small/theories/Value12.v) |
| `(2,2)` | 6 | 8 | [`BBB22_value`](../small/theories/Value22.v) |
| `(3,2)` | 55 | 55 | [`BBB32_value`](../small/theories/Value32.v) |
| `(2,3)` | 59 | 67 | [`BBB23_value`](../small/theories/Value23.v) |

The build compiles the required existing binary certificates from
[`small/legacy/targets.txt`](../small/legacy/targets.txt), then the small
censuses and final value modules. All four final theorems are unconditional;
the `Conditional` modules in the `(2,3)` development are intermediate lemmas
whose premises are discharged by `Value23.v`. No certificate search is needed
to build the proofs.

The `check` target re-verifies the final modules and their dependencies with
`coqchk -silent -bytecode-compiler yes`, including the normalized `(2,2)`
result and regressions. Success is exit status 0. The audit can run quietly
for several minutes; Coq's native-to-VM fallback warnings are expected here.
The final `Print Assumptions` blocks report only
`FunctionalExtensionality.functional_extensionality_dep`. Incremental builds
may skip already compiled modules and therefore not reprint those blocks.

To inspect the `(2,3)` theorem and its assumptions after building:

```bash
coqtop -quiet -Q theories BBB4 -Q small/legacy SmallLegacy \
  -Q small/theories SmallBB <<'COQ'
From SmallBB Require Import Spec Value23.
Check BBB23_value.
Print BBB23_statement.
Print Assumptions BBB23_value.
COQ
```

This shows `BBB23_value : BBB23_statement`, with the statement expanding to
`BBBSt_is 2 3 59 /\ BBBTr_is 2 3 67`. The instruction values allow an
unrestricted first transition. [`Normalized22.v`](../small/theories/Normalized22.v)
separately proves the restricted value 7 when `A0=1RB`; the unrestricted
`(2,2)` value is 8.

See [`small/README.md`](../small/README.md) for the model, champions, and
optional search reproduction. The
[`Small BBB proofs` workflow](../.github/workflows/small.yml) runs the same
build-and-audit command, followed by the extraction regression.

## Four-symbol champion

The isolated `four/` development proves the exact score of
`1RB2LA1RA1LB_0LB2RB3RB1LA` for both state and instruction quasihalting:
**205,770,076,433,044,242,247,860**. This establishes two global lower bounds;
the global BBB(2,4) maxima remain unresolved. The last `A` / `A3` configuration
index is one less, matching this repository's existing score convention.

With the Coq 8.18.0 / OCaml 4.14.2 switch installed above, run from the root:

```bash
eval "$(opam env --switch=census)"
make -C four check -j2
python3 four/tools/generate_champion.py --check
python3 four/tools/generate_census.py --check
python3 four/tools/generate_affine.py --check
python3 four/tools/generate_pipeline_examples.py --check
python3 four/tools/generate_advanced_examples.py --check
```

The build recursively audits `BBB24.Champion`, `BBB24.Bootstrap`,
`BBB24.AffineExamples`, the closure and affine checkers, symmetry/shadow
transport, census closeout, and the certificate rejection checks.
`BBB24.PipelineExamples` replays all 76 closure-pilot successes and attaches
their completion proofs to census coverage. `BBB24.AdvancedExamples` checks the
33 finite/history/repeated-word pilot successes. The Python commands reproduce the
champion certificate, census DAG, affine examples, and both closure pilots without
changing them. Census reproduction
requires a C++17 compiler (`g++`). `make -C four` alone
builds without the independent audit. Alphabet reduction automatically builds
the completed `SmallBB.Value23` theorem; it does not require the BBB(4) census
or the unrelated (3,2) legacy dependencies.

Inspect the final statements and assumptions:

```bash
coqtop -quiet -Q four/theories BBB24 <<'COQ'
From BBB24 Require Import Spec Champion Bootstrap IRuleCensus TotalCompletion.
Check champion_exact.
Check BBB24_lower_bounds.
Check bootstrap_coverage.
Check ir_check_sound.
Check totalize_scores.
Check global_bounds_from_total_and_halts.
Print Assumptions champion_exact.
Print Assumptions BBB24_lower_bounds.
Print Assumptions bootstrap_coverage.
Print Assumptions ir_check_sound.
Print Assumptions totalize_scores.
Print Assumptions global_bounds_from_total_and_halts.
COQ
```

The first four assumption reports should contain only
`functional_extensionality_dep`; the two completion theorems are closed under
the global context (no axioms).
The census covers every table but explicitly defers unresolved partial-table
families; its coverage theorem is not a global upper bound. The build uses VM
computation throughout, avoiding native compilation of the large certificate DAG.
The binary run-length replay uses 2,934 accelerated operations with proved exact
costs; it never expands the enormous tape or simulates every transition. See
[`four/README.md`](../four/README.md) for the three rules and proof boundary.
The [four-symbol burndown](../four/BURNDOWN.md) explains the remaining families
and how to reproduce their machine-level inventory and proof-status ledger.
`BBB24.TotalCompletion` proves the reduction to fully defined tables for
non-halting machines and states the separate halting-time obligation. The
[grouping report](../four/GROUPING.md) distinguishes exploratory reductions
from checked coverage and compares the current survey to the BBB(4) pipeline.
The [pipeline guide](../four/PIPELINE.md) documents the new checker tiers,
resumable sweeps, proof-status boundaries, and the optional full affine replay:

```bash
make -C four check-affine-batch
coqtop -quiet -Q four/theories BBB24 <<'COQ'
From BBB24 Require Import PipelineExamples Symmetry Shadow.
Check bootstrap_pipeline_coverage.
Check pipeline_families_discharged.
Check perm_bounds.
Check shadow_check_sound.
Print Assumptions bootstrap_pipeline_coverage.
COQ
```

The affine batch reconstructs its proof shards under the ignored build directory
and audits them. It does not require rerunning the external affine search.

For the larger census closeout, including the 4,096-family closure replay,
all conditional shadow links, and the combined transported-family board:

```bash
make -C four check-wave -j2
```

This target reconstructs and recursively audits every required generated shard
from tracked compact inputs; ignored survey logs are not required. The
[second-wave guide](../four/WAVE2.md) lists the constituent targets and loadpaths
for `BBB24Wave.WaveCloseout.wave_coverage` and its explicit remaining obligation.
The original census weights are preserved; the new theorem excludes proved
families and their completions from a refined residual.

For the stronger campaign, including separate state-only boards, weighted
certificates, longer cycles, alphabet reduction, and recurring-suffix reuse:

```bash
make -C four list-campaign
make -C four check-campaign
# Optional on a 16 GiB host:
make -C four check-campaign CAMPAIGN_JOBS=2
```

The [third-wave guide](../four/WAVE3.md) explains the distinct search and proof
counts, the dependency-aware replay targets, and the generated per-machine
burndown lists. The original large generated Coq files are not tracked.

## Tier A — everything except the census walk

`theories/Closeout/Closeout.v`'s dependency closure contains **no census walk
output**.  Its direct census imports are
`theories/Census/{TNF_QH,Deferred_Defs,Deferred_Data}.v`; the walk output
(`Census_Theorem`, `GG_*`, `GGH_*`, `G_*`, `Run_Split*`) is loaded only by
`CloseoutFinal.v`, `BBB4_Theorem.v` and `BBB4_Value.v`.  So this tier needs
no `native_compute` and stock apt Coq builds it.

```bash
sudo apt-get install -y coq          # must be 8.18.0; Ubuntu 24.04 ships it
git clone https://github.com/carrino/Coq-BBB4 && cd Coq-BBB4
make Makefile.coq
make -f Makefile.coq -j2 theories/Closeout/Closeout.vo
```

`Makefile.coq` is generated — the committed `Makefile` regenerates it, so do
not run `coq_makefile` yourself.  Budget one to two hours on four cores; it is
~2,800 files.

Then, in a scratch `.v`:

```coq
From BBB4.Closeout Require Import Closeout.
Require Import List.
Check closeout_partial.
Print Assumptions closeout_partial.
Eval vm_compute in (List.length remaining_rows).
```

Expected:

```
closeout_partial : forall tm, Deferred D_census tm ->
                              boarded tm \/ skipped D_remaining tm
Axioms: FunctionalExtensionality.functional_extensionality_dep
     = 0
```

(`remaining_rows` is empty — that is what lets `BBB4_Value.v` discharge
the `skipped` disjunct at tier B.)

And the two checks the kernel does not do for you:

```bash
python3 tools/closeout/audit.py                    # expect: OK, exact partition
grep -rn "Admitted\." theories --include='*.v'     # expect: no output
```

`audit.py` matters.  The kernel proves `closeout_partial` about whatever
tables are baked into the sources; `audit.py` is what checks those tables
against the frozen census list — that `proven_rows` covers all 5,156
frozen deferred rows exactly, nothing missing, invented, or duplicated —
and `audit.py` is untrusted Python.  The 5,156-of-5,156 coverage figure
is bookkeeping, not kernel output (with the residue empty it carries no
weight for the value theorem itself; see `docs/CLAIMS.md`, trust
boundary).

### Deeper: re-check the compiled proofs independently

`Print Assumptions` trusts the `.vo` it loads.  `coqchk` does not — it
re-verifies the proof terms with the standalone checker:

```bash
coqchk -o -Q theories BBB4 BBB4.Closeout.Closeout
```

It also reports what `Print Assumptions` is silent about: reliance on
type-in-type, unsafe (co)fixpoints, and assumed positivity — all expected to
be `<none>`.  On a small closure (`BBB4.Counters.NestedLapLift`) this takes
~30 s and prints `functional_extensionality_dep` and three `<none>`s.  Over
the full `Closeout` closure it runs for a long time; treat it as an overnight
check rather than a quick one.

## Tier B — chaining to the census

`theories/Closeout/CloseoutFinal.v` gives `census_boarded`,
`theories/Closeout/BBB4_Theorem.v` gives `bbb4_target`, and
`theories/Closeout/BBB4_Value.v` gives `BBB4_value : BBB4_statement` —
the end-to-end value theorem `make proof` walks, builds and reports.  (The
claim itself, `BBB4_statement := BBB4_is champion_score`, is stated
in `theories/BBB4_Spec.v`, with no census dependence; reading that file plus
`theories/BBB4_Statement.v` gives every definition in the theorem.)  These
three files are the only ones that load the census walk output (they
are deliberately not in `_CoqProject`, so the default `make` never
touches them), and the walk needs `native_compute`, so the census opam
switch. Use the setup above or let `make proof` select it through
`tools/census_toolchain.sh`.

`make proof` (the same target as `make proof-all`) builds the state
chain, walks the census from source, compiles the three files with
`coqc` (watch for the single `Print Assumptions BBB4_value`
`Axioms:` block in the output — expect exactly
`functional_extensionality_dep`; `BBB4_value` consumes `bbb4_target`,
so one footprint covers the chain.  `BBB4_is_unique` prints closed
under the global context during the default `make`, from
`BBB4_Spec.v`), and prints the report: the value theorem and what it
means.  (The report has a legacy skipped-machine mode from the burndown
era; the empty residue never reaches it.)

apt's Coq has **no `native_compute`** and cannot do the walk at all, which is
why the census switch exists. Compiled objects depend on the toolchain;
do not reuse them across toolchains without the proof wrapper's stamp check.

### Native compilation and stack limits

The build raises its stack limit with `ulimit -s unlimited` for generated
OCaml modules. Census lookup tables now use separate files of at most 250
machine definitions, avoiding the expensive native compilation of the former
5,270–6,517-definition modules. Other large generated boards still benefit
from the larger stack. If your environment limits it, set `STACK_KB` to a value
allowed by `ulimit -Hs`. A lower stack limit is not a tested equivalent
performance configuration. State walk workers explicitly select OCaml's
default GC settings with an empty `WALK_OCAMLRUNPARAM`; TR inherits its normal
Coq/OCaml defaults when the environment variables above are unset.

The whole claim from source is one command:

```bash
make proof                # = make proof-all: base build + walk + closeout chain
```

It runs the state base build, then `census-verify` (the walk), then the
three closeout files and `Print Assumptions`. A fresh checkout has no compiled
project inputs; the final compiler's `Axioms:` block gives the assumptions.
Historically, on 2026-08-12, 8 physical cores / 31 GB, un-niced, measured
**79 m 38 s end to end** (742 core-min), from `git clean -fdx` with
nothing pre-configured — a ~40 min base build plus the 42 m 36 s walk.
The base build and walk have since been optimized. Current fresh-build
measurements and their conditions are in [`CENSUS_RUNTIME.md`](CENSUS_RUNTIME.md).

To re-walk on its own, without the closeout chain:

```bash
make census-verify
```

This moves any previous walk output to a timestamped backup directory
(`census_probes/vo-backup-*` — nothing is destroyed, and no manual `.vo`
deletion is ever needed) and re-walks from source, on a native Linux
filesystem — not `/mnt/c` under WSL2, where the drive bridge breaks
`native_compute`.

### Historical state-walk measurements (August 2026)

The following measurements and estimates describe their original revisions.
Use the completed fresh-build results above for current resource planning;
in particular, configurations below 16 GiB have not been validated recently.

**How long: it used to depend almost entirely on how many jobs your RAM
allowed.**  The walk is 385 core-minutes (measured end to end,
2026-08-09) at 93% parallel efficiency, and RAM used to be what stopped
you spending them in parallel:

    WALK_JOBS = min(cores, (available RAM − 2 GB) / 7 GB)

because each unit peaked **~6.8 GB**.  On 8 cores that is 4 jobs on a
32 GB box and **1 h 44 m** — the measured figure, and the reason a
32 GB desktop could not reach the one-hour goal.

**79% of that 6.8 GB was never the walk.**  It was the environment each
unit `Require`d — the boarded-machine theorems behind `proven_all`,
which the walking half of a unit never looks inside.  The lookup tiers
are now emitted as data (`Census/Proven_List.v` and friends), the units
build their tables from those, and `Census/Run.v` re-attaches the
certificates by a kernel convertibility check.  A lean unit measures
**0.371 GB** natively against 6.758 GB.

### Measured: the first full lean walk (2026-08-10)

Run on 8 physical cores (16 threads) / 31 GB, `tools/walk_rss_report.py` over all 154 units:

| | peak RSS |
|---|---|
| `GGH_*` (104 lean units) | max **0.60 GB** |
| `GG_1LC_*` (16 lean units) | max **0.61 GB** |
| `G_*` (24: 16 lean + 8 assemblers) | max **2.77 GB** |
| `Run_Split*` (9) | max **2.76 GB** |
| `Census_Theorem` (alone) | **6.30 GB** |
| **all 154** | max 6.30 / p90 2.76 / **median 0.51** / min 0.40 |

**The whole walk took 1 h 19 m 42 s** — every one of the 154 `.vo`
written inside that window, at 7 jobs, under `nice -n19`.  For contrast
the pre-lean walk measured 1 h 43 m at 4 jobs, and could not have run 7
jobs at all: 7 × 6.8 GB is 48 GB.

Predicted wall by job count, from the LPT schedule of the measured
per-unit CPU with the layer barriers modelled:

| jobs | wall | scaling |
|---|---|---|
| 4 | 108 min | 98% |
| 6 | 75 min | 94% |
| **8** | **62 min** | **85%** |
| 12 | 50 min | 70% |
| 16 | 44 min | 60% |

So the RAM term no longer binds anywhere, and what is left is load
spread *inside* the two big layers.  A layer cannot finish faster than
its longest single unit, however many cores you have, and `GG_1LC` is
16 units run in one wave.  (It is **not** the `Run_Split` layers, which
look like the obvious culprit and are 1.2 core-min between them —
`walk_rss_report.py` prints the per-layer makespan and what sets each
layer's floor, so read that rather than guessing.)

**Core-time came in at 421 min against the pre-lean walk's 385.**  The
lean units did not get cheaper in CPU — a single-unit control had
suggested 1.93x, and that did not transfer.  Read it as "no worse":
the 385 was measured at 4 jobs and the 421 at 7–14, where memory
bandwidth and SMT contention inflate per-unit CPU, so the two are not
a clean comparison and neither is a regression.

Two job counts, because 15 of the 154 files did not get lean: the 7
`Census/Run_Split_<tag>.v` and the 8 `Compute/G_*` assemblers prove
`NodeDecided`, which needs `decider_WF`, which needs the boards.  Coq
loads a library's environment whole, so there is no way to name
`decider_WF` without paying for it.  Those run at `WALK_ASM_JOBS`
(`WALK_ASM_RSS_GB`, **3.5 GiB**) while the 136 lean computation files run
at `WALK_JOBS` (`WALK_RSS_GB`, **2 GiB**, with default GC). The former
1 GiB setting used more aggressive GC. Each pool is capped by physical
cores, container CPU quotas, and available memory; the final census theorem
runs alone.

The historical final census assembly measured **6.30 GB**, motivating a
rough 9 GB minimum at that revision. The 2026-10-17 fresh build was validated
with **16 GiB** available to the container; lower memory limits were not tested.
Reducing worker counts does not reduce the memory required by a serial assembly.

The Makefile is authoritative for all of these, and all are settable:
`WALK_JOBS=N` / `WALK_ASM_JOBS=N` force the fan-outs, `WALK_RSS_GB=N` /
`WALK_ASM_RSS_GB=N` change the per-file peaks the sizing assumes.  Every
walk records wall time, CPU time, and peak child RSS per unit to
`census_probes/state-unit-times.jsonl`. When GNU `time` is installed, the
legacy `census_probes/walk-rss.tsv` is also available to
`python3 tools/walk_rss_report.py`. These measurements let subsequent runs
use the host's own data to select job counts.

### Measured: 42.6 minutes (2026-08-12)

The walk that settled it: `WALK_JOBS=8`, un-niced, nothing else running,
8 physical cores / 31 GB.

| | 2026-08-10 | **2026-08-12** |
|---|---|---|
| wall | 1 h 19 m 42 s (7 jobs, `nice -n19`, box in use) | **42 m 36 s** (8 jobs, idle) |
| core-time | 421 min | **303 min** |
| peak RSS max / p90 / median | 6.30 / 2.76 / 0.51 GB | 6.30 / 2.76 / **0.51** GB |

`Print Assumptions census_decided` printed exactly
`functional_extensionality_dep`, and the queue closed — which is what
says the RepWL node-size cut this round added lost no catch.

Two changes account for it, and they are independent.  **The lean walk
units stopped being three separate `xargs` passes**: `GG_1LC`, `GGH`
and the lean half of `G_` have no dependency on each other, so the
three barriers were costing each layer its longest unit instead of its
share.  Merged into one pool of 136 they pack to `core-min/jobs`
exactly.  And **the RepWL closure gained a node-size cut** (M4), which
abandons a closure once it pops a node carrying more than 32 run-length
items — worth 28% of the walk's core-time.

The memory picture is unchanged: the floor is still ~9 GB, still set by
`Compute/Census_Theorem.v` running alone at 6.30 GB.  More cores help
until about 12; past that the pool is bounded by core-time, not by any
single unit.

### The WSL2 memory trap — read this before quoting a walk time

**WSL2 gives the VM half the host's RAM by default** (up to 8 GB on older
builds).  A 32 GB Windows box is a 16 GB Linux box unless `.wslconfig`
says otherwise.  Nothing warns you, and since the units were made lean
this can affect both parallelism and the final theorem. Lean workers use a
2 GiB budget plus a shared 2 GiB reserve, while `Census_Theorem`, the very
last file, runs alone and historically needed about 6–7 GiB. A
**16 GB Windows box defaults to an 8 GB VM, which is under
the ~10 GB floor**: you find out after the other 153 files are done.
Check inside the VM, never from Windows:

```bash
free -g        # what the VM actually has -- this is what WALK_JOBS reads
nproc
```

To give it the whole box, create `%UserProfile%\.wslconfig` on the Windows
side and `wsl --shutdown` to apply:

```ini
[wsl2]
memory=28GB      # leave a few GB for Windows; 32 GB host -> 28
processors=8
swap=0
```

Then re-check `free -g` inside the VM before starting.  The same trap in
the other direction is worse: **do not override the job counts upward
without checking available RAM**. Assemblers use a separate 3.5 GiB budget,
based on the historical 2.77 GiB measurement. Older builds had 5–7 GiB
workers and exhausted memory on 2026-07-22 on a 16 GB box and again on
2026-08-08 under WSL2. On any memory-constrained box prefer
`WALK_MEMFREE=8G` (GNU parallel), which gates each unit launch on free RAM
and suspends-and-requeues instead of letting the OOM killer choose a
victim.

`make census` is **resumable and per-unit**: finished units are skipped on re-run,
and a walk-stamp quarantines any `.vo` that was not produced by walking the
current tree. An interrupted walk can resume with that target; `census-verify`
and `proof-all` deliberately force a re-walk instead.
`python3 tools/census_cache.py --print-hash` prints the
census input hash the walk-stamp records.

## Tier C — the instruction-level value: `make proof-tr-all`

The claim is `BBBT4_statement := BBBT4_is champion_score` in
[`theories/BBBT4_Spec.v`](../theories/BBBT4_Spec.v): the largest step at
which any instruction (state, read symbol) of any (4,2) machine fires for
the last time.  It uses `FiresAt` and `QuietAfterTr` from
`theories/BBBT4_Statement.v` and the machine model and champion from the
state-level files; nothing in it refers to a proof.
`BBBT4_value : BBBT4_statement` is proved in
`theories/CloseoutTr/BBBT4_Value.v`.  Like `BBB4_Value.v`, it loads the walk
output, so it is not in `_CoqProject`.

From a fresh clone:

```bash
git clone https://github.com/carrino/Coq-BBB4 && cd Coq-BBB4
set -o pipefail
make proof-tr-all 2>&1 | tee proof-tr-all.log
```

It uses the same toolchain as Tier B (`tools/census_toolchain.sh` finds or
creates the `census` switch) and runs four steps:

1. **Generated files.** It checks the closeout split, walk units, IRules parts
   and advisory hint data for consistency with their sources.
2. **The census walk.**  It walks 96 native-compute units and assembles
   `census_tr : forall tm, QHBoundTr B_tr tm \/ Deferred D_tr tm`.  The
   prerequisites include the proven tiers (`ProvTr_*`).
3. **The closeout, the champion and the tests.**  It builds the 626 batches,
   `CloseoutTr.vo` (`closeout_tr_complete`, all 10,924 deferred rows),
   `BBBT4_Champion.vo` and the instruction-level corruption tests.
4. **The value.**  It compiles `CloseoutFinalTr.v` (`bbbt4_bound`) and then
   `BBBT4_Value.v`.

The supplied advisory table covers all 96 units: 256,390 rows in 251 modules
of at most 1,024 rows. Each selected checker still verifies the actual machine;
missing, invalid or failed hints use the original fallback. Stored RW data
likewise passes the existing Coq certificate checker. These inputs add no
axiom. Ordinary verification compiles/checks the data and does not run the
offline hint collector or certificate finder. See
[`tools/censustr/hints/README.md`](../tools/censustr/hints/README.md) for data
maintenance.

The full TR wrapper omits coqdoc `.glob` indexes, while retaining proof objects
and native proof evaluation. Standalone, state and documentation builds retain
their normal index behavior.

Expected end of the log:

```
Axioms:
FunctionalExtensionality.functional_extensionality_dep
  : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
    (forall x : A, f x = g x) -> f = g
------------------------------------------------------------
proof-tr-all COMPLETE at <commit>.
BBBT4_value : BBBT4_statement  (BBBT4_Spec.v: BBB_tr(4) = 32,779,478)
```

Inspect this actual compiler assumption block, not only the explanatory
completion banner. Resources:

* **Memory sets the job counts.**  The walk units load only the
  computation layer (`RunTr_WalkCompute`), not the proven-tier boards, and
  avoid allocating the published unary bound in each worker. The walk runs
  one job per 3 GiB available, after a 2 GiB reserve,
  (`WALK_TR_JOBS`), capped at the physical cores.  The batches run one job
  per 3 GiB (`CLOSEOUT_TR_JOBS`). The walk's prerequisites (the proven
  tiers, built before the walk) also use 3 GiB (`PREREQ_TR_JOBS`);
  the large state IRules batches are no longer dependencies of this target.
  All three phases respect physical cores and container CPU limits.
  With sufficient available memory, a four-core / 16 GiB container gets
  four jobs in each phase; an eight-core / 32 GiB box gets eight.
  These are scheduling estimates, not process caps. The completed v4 build's
  largest child used 9.80 GiB during the serial final theorem; lowering the
  worker count does not reduce that requirement.
  To override:
  `make proof-tr-all PREREQ_TR_JOBS=3 WALK_TR_JOBS=4 CLOSEOUT_TR_JOBS=6`.
* **Time.** The latest completed fresh run took **2 h 15 m 38 s** on the
  four-CPU / 16 GiB configuration, still 15 m 38 s over the two-hour goal.
  See [`CENSUS_RUNTIME.md`](CENSUS_RUNTIME.md) for exact build conditions.
  Historically, the clean-tree
  build verified 2026-10-12 at `bb35b8d9` ran in three parts, after two
  out-of-memory stops that are now fixed, totalling 7 h 15 min
  ([`BBBT4_REVIEW.md`](BBBT4_REVIEW.md) §8.3).  The first
  verified run, on 2026-10-06 before the speedups of PR #246, took most of
  a day (§8.1).
* **Stack.**  Steps 3 and 4 raise the stack limit themselves, as `make all`
  does, because `COQNATIVE` overflows 8 MB on the largest batches.  If your
  hard limit is lower, set `STACK_KB` to a value permitted by `ulimit -Hs`.
* **Resuming.** A compatible rerun keeps finished `.vo` and walked units.
  Use a fresh source checkout for a fresh full-build measurement.

To re-check the compiled terms with the standalone checker:

```bash
coqchk -o -Q theories BBB4 BBB4.CloseoutTr.BBBT4_Value
```

This is an overnight-scale job, as for Tier B.  The reviewer's guide,
including cross-checks on the hardest machines, is
[`BBBT4_REVIEW.md`](BBBT4_REVIEW.md).

## Traps

* **`BBB4_Statement.vo` is the root of the entire tree — deleting or
  touching it forces a full 1–2 h rebuild** (every file in the tree
  imports it transitively).  The one time deleting it is necessary: an error of the
  shape *"contains library `BBB4_Statement` and not library
  `BBB4.BBB4_Statement`"*, which means a stray `coqc` run **without**
  `-Q theories BBB4` left a wrongly-named `.vo` shadowing the real one,
  and `make` (seeing it up to date) will never fix it on its own.
  Prevention is cheap: always compile one-off files as
  `coqc -Q theories BBB4 <file.v>`, never bare `coqc`.
* **Compiled objects depend on the toolchain.** The full proof wrappers stamp
  the actual Coq/native compiler configuration and generated-code optimizer
  inputs. A missing, legacy or changed stamp cleans stale proof/native caches
  before rebuilding. Failed probes or unsafe cache layouts stop the build.
  Plain `make` does not perform this wrapper check; choose one toolchain for
  standalone builds and do not mix its objects with another toolchain's.
* **Size `-j` for available memory.** The state IRules proofs are split
  into 34 independent parts of at most eight certificates. The largest
  part by total anchor steps measured 1.21 GiB peak RSS; scheduling budgets
  3 GiB per part plus the shared 2 GiB reserve. `Makefile.coq.local` caps
  concurrent parts using available memory and physical cores; override
  with `IRULES_JOBS=N`. Other files can use the remaining jobs. The build is incremental,
  so completed base objects can be reused after an interruption. Remember
  that `proof-all` still forces the state census to be re-walked.
* **`make proof` needs the census switch; plain `make` does not.**
  The walk is `native_compute`, and `CloseoutFinal.v`, `BBB4_Theorem.v`
  and `BBB4_Value.v` load its output, so they are kept out of
  `_CoqProject` and the default build stays apt-Coq-compatible.  Mixing
  toolchains fails with "inconsistent assumptions" while loading — that is
  the marshalling mismatch, not a proof failure.
* **CI does not run both complete proof targets.** A hosted runner has
  about 7 GB, close to the peak of the final census assembly alone.
  `.github/workflows/ci.yml` builds the core library, the closeout
  kit and two end-to-end machine-proof families from source, kernel-checks
  the instruction-level closeout batches (sharded over six runners,
  [`CLOSEOUT_TR.md`](CLOSEOUT_TR.md) "CI"), enforces zero `Admitted`, and
  runs the untrusted audits; tiers A and B above are local.
