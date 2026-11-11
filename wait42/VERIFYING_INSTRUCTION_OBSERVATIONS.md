# Replay instruction waiting observations

This job independently proves instruction waiting bounds for selected partial
machine families. It uses the same resource controls and receipt checks as the
[state observation runner](VERIFYING_OBSERVATIONS.md), with a separate Coq
checker, namespace, input identity and output directory.

The full instruction waiting value and its exhaustive census remain open.
`COMPLETE` means this selected input finished, not that `BBB_wait_tr(4,2)` has
been proved universally.

## Input and scope

The desktop instruction scan covered the 16,384 families selected for the state
observation run, from cutoff **32,779,478** to a cap of **500,000,000**. It took
2,245.720 seconds on eight workers. The archive's worker results, summary,
source hashes and canonical aliases were checked against the frozen input.
The scan itself has no Coq proof credit.

| Group | Families | Next action |
| --- | ---: | --- |
| Short successful observations | 9,480 | Default Coq replay input; local widths at most 65,536 |
| Longer successful observations | 507 | Separate queue for replay or shorter certificates |
| Cap reached without the instruction closure test succeeding | 6,397 | Further search or another certificate method |

The proposed common extra waiting width is **454,402,378**, giving total horizon
**487,181,856**. The scanner's largest first post-cutoff instruction visit was
425,726,748 for A0 of `1RB0RC_1LD0RA_1LC0LD_1RB1LD`. It does not exceed the
existing lower-bound witness. A missing visit at the finite simulation cap
does not prove permanent silence.

These are instruction obligations for a state-selected sample, not an
exhaustive instruction census. They are separate from the state proof counts.

## Run and resume

With the repository's native Coq 8.18 environment active, run from its root:

```sh
make -C wait42 proof-instruction-observations BUILD_JOBS=8
```

For an opam switch named `census`:

```sh
opam exec --switch=census -- make -C wait42 proof-instruction-observations BUILD_JOBS=8
```

This prepares the generic dependencies and replays 593 independent batches:
592 batches of 16 families and one batch of eight. Each successful batch must
compile, report only the allowed assumptions, and pass full recursive
`coqchk`. Generated sources, compiled objects and logs stay under
`wait42/build/instruction-observation-proof`.

A real first-batch pilot passed in **333.642 seconds**: 64.188 seconds compiling
and 269.041 seconds in recursive `coqchk`, plus bookkeeping. Two additional
closed-tail cases also passed. Both runs successfully reused their receipts
with eight workers and zero new batches. The
[pilot validation record](research/instruction-runner-validation.json) records
the exact inputs, artifact hashes and assumptions. The full batch has not been
replayed here. Scaling this single-batch measurement gives roughly seven hours
on eight comparable cores; plan for an overnight run because hardware and
individual cases affect runtime.

Run one batch first if desired:

```sh
make -C wait42 proof-instruction-observations BUILD_JOBS=1 OBSERVATION_MAX_BATCHES=1
```

Then use the eight-worker command to resume. Ctrl-C preserves completed,
audited batches. Do not clean the output directory. Changing worker count is
allowed; changing input, proof sources, toolchain or batch partition requires
a new output directory if its identity no longer matches. Only one runner may
write each output directory, and its sources and dependencies must remain
unchanged while it runs.

The state runner and its input remain unchanged; state receipts cannot be
reused as instruction receipts. To verify saved instruction receipts without
starting another batch:

```sh
make -C wait42 proof-instruction-observations BUILD_JOBS=8 OBSERVATION_MAX_BATCHES=0
```

The defaults are 2 GiB address space per compiler/checker process, a 64 MiB
stack where permitted, 3,600 seconds per compile-plus-audit batch, a 48-hour
scheduling budget and a 2 GiB disk reserve. Prefer at least 32 GiB RAM for eight
workers. Use `OBSERVATION_MEMORY_GIB`, `OBSERVATION_TIMEOUT`,
`OBSERVATION_MAX_HOURS` and `OBSERVATION_DISK_RESERVE_GIB` to adjust these.
`INSTRUCTION_OBSERVATION_SPEC` selects the spec;
`INSTRUCTION_OBSERVATION_STATE` selects a separate output directory.

## Results to share

The runner prints progress and writes `progress.json` and `summary.json`.
After the run stops, create a compact archive from the repository root:

```sh
(
  cd wait42/build/instruction-observation-proof &&
  tar -czf ~/bbb-wait42-instruction-receipts.tar.gz \
    manifest.json summary.json progress.json \
    Part*.v Part*.receipt.json Part*.compile.log Part*.audit.log
)
```

Keep the full output directory for resume. The archive supports review of the
recorded audits; a fresh kernel check requires rebuilding the compiled objects.
No upload is performed by the runner.

## What Coq proves

[FiniteInstructionObservation.v](theories/FiniteInstructionObservation.v)
proves `instruction_observation_batch_completion`. For every nominated partial
table, **every completion** satisfies `WindowBoundTr` at the supplied cutoff
and common width: any designated instruction that ever beeps at or after the
cutoff already beeps in the inclusive observation window.

Coq executes the original table from the blank tape and accepts either:

- All eight instruction slots were observed in the local window; or
- The endpoint lies in a total, closed state set, and both instruction slots
  of every state in that set were observed in the window.

The all-eight branch needs no nonhalting premise. The tail branch requires
defined transitions throughout its invariant; an undefined transition is not
evidence of silence for arbitrary completions. A numerical gate checks that
each local width is at most the common width. The only permitted semantic
assumption is the repository's existing functional extensionality assumption.

There are 9,229 all-eight nominations and 251 total-tail nominations in the
short batch. The preparer maps scan coordinates back to the original partial
tables and adds one transition to each local window so the endpoint reaches
the proposed tail set. Coq verifies those proposals independently. No formal
symmetry transport is needed for the generated family proofs.

The [spec](research/instruction-observations.json) pins the
[short input](research/instruction-observations.tsv). The
[longer queue](research/instruction-observations-slow.tsv) and
[scan holdouts](research/instruction-scan-holdouts.tsv) retain original
`source_index`, `machine` and `ptr` identities. Holdout mask bits enumerate
`A0,A1,B0,B1,C0,C1,D0,D1`; a set bit means no post-cutoff visit was recorded.
Replay `tail_mask` fields instead contain four **state** bits `A,B,C,D`.

The [scan validation record](research/instruction-scan-validation.json) pins
the original archive and output hashes. Given that exact uploaded archive,
reproduce the preparation with:

```sh
python3 wait42/tools/prepare_instruction_observations.py \
  --archive ~/bbb-wait42-instruction-scan-01.tar.gz
```

This writes an identical input set to `wait42/build/instruction-nominations`.
Preparation and nomination counts give no kernel proof credit. Successful
family proofs still need an exhaustive coverage theorem before announcing a
universal waiting value.
