# Verifying this repository

_What to run, what to expect, and where you are being asked to trust
something.  The claim itself is in [`docs/CLAIMS.md`](CLAIMS.md)._

There are two tiers.  **Tier A needs no committed binaries and no opam**; it
verifies every board and the whole boarding argument.  Tier B chains that to
the census, and is where the one trust decision lives.

## Tier A — everything except the census walk

`theories/Closeout/Closeout.v`'s dependency closure contains **zero committed
`.vo`**.  Its only census dependencies are
`theories/Census/{TNF_QH,Deferred_Defs,Deferred_Data}.v`, and none of those
are among the 154 committed binaries — those are all walk output
(`Census_Theorem`, `GG_*`, `GGH_*`, `G_*`, `Run_Split*`), which only
`CloseoutFinal.v`, `BBB4_Theorem.v` and `BBB4_Value.v` load.  So this
tier is entirely from source.

```bash
sudo apt-get install -y coq          # must be 8.18.0; Ubuntu 24.04 ships it
git clone https://github.com/carrino/Coq-BBB4 && cd Coq-BBB4
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
the end-to-end value theorem `make proof` builds and reports.  (The
claim itself, `BBB4_statement := BBB4_is champion_score`, is stated
in `theories/BBB4_Spec.v`, with no census dependence; reading that file plus
`theories/BBB4_Statement.v` gives every definition in the theorem.)  These
three files are the only ones that load the committed walk output (they
are deliberately not in `_CoqProject`, so the default `make` never
touches them), and they need the toolchain that produced it:

```bash
opam switch create census 4.14.2
opam install coq.8.18.0 coq-native
eval $(opam env --switch=census)
make proof
```

`make proof` checks the census cache hash, compiles the three files
with `coqc` (watch for the single `Print Assumptions BBB4_value`
`Axioms:` block in the output — expect exactly
`functional_extensionality_dep`; `BBB4_value` consumes `bbb4_target`,
so one footprint covers the chain.  `BBB4_is_unique` prints closed
under the global context during the default `make`, from
`BBB4_Spec.v`), and prints the report: the value theorem and what it
means.  (The report has a legacy skipped-machine mode from the burndown
era; the empty residue never reaches it.)

apt's Coq has **no `native_compute`** and cannot do the walk at all, which is
why the census switch exists.  Note the OCaml version is load-bearing: `.vo`
are OCaml-marshalled, so a 4.14.2 `.vo` will not load under 4.14.1 and vice
versa.

### The build raises its own stack limit, and needs to

Under the census switch — and only there — `coqnative` compiles each
`.vo` into an OCaml module and the OCaml compiler recurses over its
structure.  The census lookup tiers (`Census/Proven_List.v` and friends)
are 5,270–6,517 machine definitions apiece, and on the **default 8 MB
stack that overflows**:

```
COQNATIVE theories/Census/Proven_List.vo
Fatal error: exception Stack overflow
Error: Native compiler exited with status 2
```

`make` therefore does `ulimit -s unlimited` before building, so this
should never reach you.  It is worth knowing anyway, because the failure
has an unusually good disguise: plain `coqc` compiles those files
without complaint, so it is invisible on any build without a native
compiler, and it appears only on the census switch — the path someone
takes precisely *because* they want to check the thing themselves.

If your environment forbids raising the soft limit, `make STACK_KB=...`
takes any value your hard limit allows (`ulimit -Hs`), and Coq's own
hint in that error is the fallback.  Measured 2026-08-11: 8192 KB fails,
unlimited builds all three lists clean.

**Trusting those 154 `.vo` is a decision.**  To avoid it, re-derive them:

```bash
make census-verify
```

This moves the committed walk output to a timestamped backup directory
(`census_probes/vo-backup-*` — nothing is destroyed, and no manual `.vo`
deletion is ever needed) and re-walks from source, on a native Linux
filesystem — not `/mnt/c` under WSL2, where the drive bridge breaks
`native_compute`.

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
(`WALK_ASM_RSS_GB`, **3.5 GB** — measured 2.77) while the other 139 run
at `WALK_JOBS` (`WALK_RSS_GB`, **1 GB** — measured 0.61).  On 32 GB
both tiers now get the full core count.

**Minimum RAM is ~9 GB, and no job count fixes it below that**: the last
file, `Compute/Census_Theorem.v`, runs alone and measured **6.30 GB**.

The Makefile is authoritative for all of these, and all are settable:
`WALK_JOBS=N` / `WALK_ASM_JOBS=N` force the fan-outs, `WALK_RSS_GB=N` /
`WALK_ASM_RSS_GB=N` change the per-file peaks the sizing assumes.  Every
walk records its own peak RSS and CPU per unit to
`census_probes/walk-rss.tsv`; `python3 tools/walk_rss_report.py` prints
the distribution and the jobs it supports, so the second walk on a box
can be sized from that box's data rather than from this table.

### The WSL2 memory trap — read this before quoting a walk time

**WSL2 gives the VM half the host's RAM by default** (up to 8 GB on older
builds).  A 32 GB Windows box is a 16 GB Linux box unless `.wslconfig`
says otherwise.  Nothing warns you, and since the units were made lean
this bites in a nastier place than it used to: the lean layers still get
your full core count on 16 GB, so the walk looks fine for its whole
length — and then `Census_Theorem`, the very last file, wants ~7.2 GB and
runs alone.  A **16 GB Windows box defaults to an 8 GB VM, which is under
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
without checking free RAM** — and `WALK_ASM_JOBS` is now the dangerous
one, since those files are still ~5–7 GB each.  Four of them on a VM
sized for two is ~28 GB of demand against ~16 GB, and the OOM killer can
take the whole distro down, not just the walk (this happened:
2026-07-22 on a 16 GB box, and again 2026-08-08 under WSL2, when every
file was that heavy).  On any memory-constrained box prefer
`WALK_MEMFREE=8G` (GNU parallel), which gates each unit launch on free RAM
and suspends-and-requeues instead of letting the OOM killer choose a
victim.

The walk is **resumable and per-unit**: finished units are skipped on re-run,
and a walk-stamp quarantines any `.vo` that was not produced by walking the
current tree.  So it can be spread over days, and a *sample* is meaningful —
re-walk a few `Run_Split_*` / `GG_*` / `G_*` units and check they reproduce
the committed output, without paying for the whole walk.

Afterwards, `python3 tools/census_cache.py --print-hash` should match the
committed hash, confirming your walk covered the same inputs.

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
* **Switching toolchains is invisible to `make`.**  If you build the tree with
  apt Coq and then switch to the census opam switch, `make` sees thousands of
  up-to-date `.vo` and skips them — but the opam Coq cannot load apt-built
  `.vo`.  Decide which Coq you are doing the long build with before you start.
* **`make all` at high `-j` can run out of memory.**  There are nine
  `theories/Machines/IRules_Batch_*.v` at ~6–8 GB peak each.
  `Makefile.coq.local` chains them (order-only) into three columns, so even
  `-j16` schedules at most three together (~24 GB); on a ~16 GB box use
  `-j2`, or edit the chains down to one column.  The build is incremental,
  so an OOM costs only the in-flight files — re-run and it resumes.
* **`make proof` needs the census switch; plain `make` does not.**
  `CloseoutFinal.v`, `BBB4_Theorem.v` and `BBB4_Value.v` are the only
  files that load the committed `.vo`, and they are kept out of
  `_CoqProject` so the default build stays all-source.  On the wrong toolchain `make proof` fails with
  "inconsistent assumptions" while loading — that is the marshalling
  mismatch, not a proof failure.
* **CI runs only the light tier.**  A hosted runner has ~7 GB, so neither
  the full build (the IRules batches peak at ~6–8 GB) nor the walk can live
  there.  `.github/workflows/ci.yml` builds the core library, the closeout
  kit and two end-to-end machine-proof families from source, enforces zero
  `Admitted`, and runs the untrusted audits; tiers A and B above are local.
