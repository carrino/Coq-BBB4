# Work on an instruction holdout

Generate the complete list with Python; Coq and the old build directories are
not needed for this step:

```sh
python3 four/tools/instruction_worklist.py
```

Open `four/build/instruction-worklist/index.html` in a browser. It works offline
and lets you search by machine, family ID, state-case ID or owner, filter by
work lane and batch, and download the filtered TSV. The same directory contains
the complete open `machines.tsv`, a suggested `next64.md`, and `summary.json`.
GitHub Actions publishes these files in the **instruction-burn1** artifact.
For evidence links in a PR snapshot, pass `--ref` with the published commit SHA.

Each family has a stable ID such as `tr24-237695161`, obtained from its exact
base-17 table code. The list retains the original table used by Coq and also
displays its reflected form with the first move to the right. Keep the family
ID when submitting a proof. The 256 stable batches, `b00` through `bff`, use
the low byte of that code; current batch sizes are in the generated summary.
They divide work without introducing new machine equivalences; proving one row
does not change another row's ID or batch.

## Current work lanes

This snapshot includes the [first worker wave](INSTRUCTION_WAVE1.md). The
generated summary updates when accepted proof inventories or search evidence change.

| Attached evidence | Open families | Suggested work |
| :-- | --: | :-- |
| All attached closure attempts timed out | 49 | Retry with bounded extra time |
| At least one closure certificate was rejected | 111 | Refine the abstraction or try another recipe |
| A diagnostic instruction appeared sparsely | 30 | Prove its counter or phase returns |
| A diagnostic instruction appeared frequently | 1 | Refine its graph or history |
| An individual state proof is available | 73 | Adapt its invariants or macros to instructions |
| No instruction diagnostic attached here | 28,350 | Triage and attach the next bounded search result |
| **Total open** | **28,614** | |

The lanes are scheduling hints. A rejection concerns one certificate; a timeout
does not settle the machine. Finite observations do not prove recurrence or
permanent extinction. An empty diagnostic field does not mean that a family has
never been searched. The state references include the final case S071.

## Claim a batch or a machine

Export one stable batch, or inspect a single family:

```sh
python3 four/tools/instruction_worklist.py --batch b00
python3 four/tools/instruction_worklist.py --machine tr24-237695161
```

Put claims in [`research/instruction-claims.json`](research/instruction-claims.json)
and include that edit in a PR. For example:

```json
{
  "schema_version": 1,
  "batches": {
    "b00": {"owner": "your-github-name", "status": "in_progress"}
  },
  "machines": {
    "tr24-237695161": {
      "owner": "your-github-name",
      "status": "proposed",
      "note": "Certificate ready for Coq replay",
      "pr": "PR URL"
    }
  }
}
```

A machine claim overrides its batch claim. Supported work statuses are
`unclaimed`, `in_progress` and `proposed`. Claims and notes are separate from
generated files, so regeneration preserves them. The HTML file is a read-only
snapshot; it does not save claims back to the repository.

## What closes a row

Submit the exact family ID, a replayable certificate or proof source, the named
instruction-bound theorem, and its bound. The proof must cover every completion
of the family, prove its original census membership, and provide the exact
inventory checked by Coq. A successful full recursive kernel audit is required
before adding that inventory to the accepted instruction ledger. The bound
must be proved no greater than the champion score for the eventual maximum
theorem.

A simulation result, state-only theorem, proposed certificate, or checked issue
box does not close a row. The generator reads proof status exclusively from
the accepted instruction inventories and rejects a manual `proved` claim.
See the [instruction scoreboard](INSTRUCTION_BURNDOWN.md) for proof replay and
the distinction between this historical cohort and the full global census.
