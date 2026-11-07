# Replay an observation batch on eight cores

This job uses successful simulation observations as **inputs to Coq**, then
independently checks the resulting proofs with recursive `coqchk`. The bundled
input contains 16,384 distinct completion families from the current state
waiting worklist. It is suitable for a resumable overnight or weekend run.

It proves bounds for those families. It does **not** prove the universal
`BBB_wait(4,2)` value or complete the census. A simulation result, an unfinished
batch, or a failed audit earns no proof credit.

## Requirements

- Linux or WSL, Python 3, GNU Make, and the repository's native Coq 8.18 toolchain.
- Eight available CPU cores and preferably at least 32 GiB of RAM for eight workers.
- Several GiB of free disk space for generated sources, compiler output and logs.

The runner uses only the Python standard library. It runs locally and does not
upload results. Each compiler/checker process receives a 2 GiB address-space
limit and a 64 MiB stack limit when the inherited hard limits permit it.
Compiler children add some memory overhead. The runner also preserves a disk
reserve and limits the combined compilation and audit time for each batch.

A real 16-family pilot took 6 minutes 23 seconds for compilation plus full
recursive checking on one cloud core, with a peak process RSS of about 612 MiB.
At that rate, the 1,024 batches would take about **14 hours on eight comparable
cores**, plus dependency preparation. This is an estimate from one batch;
hardware, memory bandwidth and individual machines affect the actual runtime.
The [pilot validation record](research/observation-runner-validation.json)
records the toolchain, timings and audit log hashes.

## Run

From the repository root, with the native Coq environment active:

```sh
make -C wait42 proof-observations BUILD_JOBS=8
```

If your toolchain is in the `census` opam switch, the equivalent command is:

```sh
opam exec --switch=census -- make -C wait42 proof-observations BUILD_JOBS=8
```

First the target prepares the Coq dependencies. Then it processes independent
batches of 16 families, with at most eight batches active. Each batch gets its
own generated source, compilation log and recursive audit log.

For a smoke run, process just the first batch:

```sh
make -C wait42 proof-observations BUILD_JOBS=1 OBSERVATION_MAX_BATCHES=1
```

After that succeeds, run the eight-worker command to continue with the rest.
The limit counts new batches launched during that invocation. Repeating the
smoke command checks the saved receipts and starts the next pending batch.
It changes how much work is scheduled, not the identity of the input or batch
partition. A limited run reports that the full input is still incomplete.

## Stop and resume

Press Ctrl-C to stop. Completed, audited batches remain on disk; interrupted
batches are retried. Run the same command again to resume. Do not use
`git clean -fdx` or `make clean`: they remove the saved work.

Before reusing a receipt, the runner checks the input, proof sources, toolchain,
dependencies and saved artifacts. Changing the worker count is allowed.
Changing the worklist, checker, toolchain or batch partition requires a fresh
output directory if the existing identity no longer matches.

The default output is `wait42/build/observation-proof`. A separate run can use:

```sh
make -C wait42 proof-observations BUILD_JOBS=8 \
  OBSERVATION_STATE=build/observation-proof-new
```

Only one runner may write a given output directory at a time. Keep the checkout,
output directory and compiled dependencies at the same paths and unchanged
while a run is active. Resume also requires the same toolchain environment.

The default scheduling budget is 48 hours. At that point the runner stops
starting new batches and lets active batches finish; a partial run can be
resumed. You can change the budget, or use fewer workers:

```sh
make -C wait42 proof-observations BUILD_JOBS=4 OBSERVATION_MAX_HOURS=12
```

Other controls are `OBSERVATION_MEMORY_GIB`, `OBSERVATION_TIMEOUT` (combined
compilation and audit seconds per batch), and `OBSERVATION_DISK_RESERVE_GIB` (free GiB to
preserve in the output filesystem). Resource failures remain explicit and do
not count as proofs.

## Progress and results

The runner prints a progress update at least every 30 seconds during proof
work. From a second terminal at the repository root, inspect its saved status:

```sh
python3 -m json.tool wait42/build/observation-proof/progress.json
```

After the run stops, share `summary.json` from that directory. It distinguishes
checked, resumed and pending cases, and records failed batches. `COMPLETE`
means this selected input finished; it does not mean the full census is proved.
A scheduling limit gives `PARTIAL`, Ctrl-C gives `INTERRUPTED`, and a failed
proof or audit gives `FAILED`.

Keep the output directory for replay and aggregation. It contains
`manifest.json`, plus `Part000000.v`, `.vo`, `.compile.log`, `.audit.log` and
`.receipt.json` files for each batch. If a batch fails, share its receipt and
logs along with the summary. A later successful retry retains the old attempt
under `attempts/`.

To verify saved receipts without launching another proof batch:

```sh
make -C wait42 proof-observations BUILD_JOBS=8 OBSERVATION_MAX_BATCHES=0
```

## What the proof checks

The cutoff is **32,779,478**, and the proposed extra waiting width is
**225,592,668**. Each nominated family supplies a shorter observation window.
Coq checks the actual execution from the blank tape and accepts a family if:

- Every state appears in its inclusive observation window; or
- The endpoint lies in a total, closed set of states, all of which appeared
  in that window. This excludes any later appearance of a missing state.

The theorem covers every completion of the nominated partial transition table.
Encountering an undefined instruction is not treated as proof that every
completion halts. A formal numerical gate checks that the local observation
width is at most the proposed global width.

The worklist and its provenance are in
[observation-weekend.json](research/observation-weekend.json) and
[observation-weekend.tsv](research/observation-weekend.tsv). The selection limits
observed tape span and window length to keep the initial replay batch manageable.
These selection conditions are performance choices, not proof premises.

Every completed batch is checked recursively, including its dependencies and
computed Boolean gate. No dependency-admission or nonrecursive audit option
is used. The only permitted semantic assumption is the repository's existing
functional extensionality assumption.

Generated sources and compiled objects stay under the output directory and
are not checked into Git. Successful family proofs still need to be connected
to the full census coverage theorem before any universal waiting result can
be announced.
