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

**Trusting those 154 `.vo` is a decision.**  To avoid it, re-derive them:

```bash
make census-verify
```

This moves the committed walk output to a timestamped backup directory
(`census_probes/vo-backup-*` — nothing is destroyed, and no manual `.vo`
deletion is ever needed) and re-walks from source.  Budget
**~24 hours** on ≥16 GB of RAM, on a native Linux filesystem — not `/mnt/c`
under WSL2, where the drive bridge breaks `native_compute`.  Parallelism
sizes itself: each walk unit peaks ~4–5 GB, and `WALK_JOBS` defaults to
`min(cores, (available RAM − 2 GB) / 5 GB)` — override with
`WALK_JOBS=N`, and on a big box add `WALK_MEMFREE=6G` (GNU parallel) to
gate each unit launch on free RAM instead of trusting the estimate.

The walk is **resumable and per-unit**: finished units are skipped on re-run,
and a walk-stamp quarantines any `.vo` that was not produced by walking the
current tree.  So it can be spread over days, and a *sample* is meaningful —
re-walk a few `Run_Split_*` / `GG_*` / `G_*` units and check they reproduce
the committed output, without paying for all 24 hours.

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
