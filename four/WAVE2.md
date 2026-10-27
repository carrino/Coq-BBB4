# Continuing the BBB(4) census and closeout workflow

This wave keeps the exhaustive bootstrap fixed. Search selects useful
certificates; Coq checks the core proofs, table transformations, and original
pending-family membership. A combined closeout theorem excludes the proved
families and all their completions from a refined residual. It does not rerun
the census or reinterpret search failures as mathematical holdouts.

## Search versus checked closeout

The finite/history/repeated-word sweep starts with the **180,177** surviving
core representatives from the first cheap sweep. Its parameters and measured
outcomes are in [`advanced-full.json`](research/advanced-full.json); candidates
still require kernel replay. Timeouts stay unresolved and continue to later
stages.

| Stage | Additional candidates | Remaining core families |
| --- | ---: | ---: |
| Finite n-gram, width 2, fuel 128 | 1,145 | 179,032 |
| History n-gram, depth 1, width 2, fuel 128 | 2,620 | 176,412 |
| Repeated-word, length 2, threshold 2, fuel 256 | 43,227 | **133,185** |

The finite/history stages use four growth rounds. All three stages use anchor
128 and proposed state/instruction bounds 4,096. Across both full sweeps there
are **140,784 search candidates** and **133,185 unresolved cores**. The latter
include all 13 repeated-word timeouts. These two sets are disjoint and cover the
273,969-core inventory; neither search count is a count of kernel proofs.

Of the remaining cores, 124,395 have fully specified tables and 8,790 are
partial families. That distinction helps target deeper branching walks while
the broader checker ladder works on the concrete tables.

Separately, the proof work includes:

- All 628 accepted affine proofs are attached to the census. Together with the
  earlier closure pilot, this closes all 637 previously proved sample families.
- A 4,096-family batch from the first sweep's 93,792 candidates is replayed in small
  shards. Each shard proves both bounds at 4,096, non-halting, and membership in
  the original census remainder before its families are discharged.
- All 33 advanced-pilot successes are replayed, including finite and history
  n-grams. These overlap earlier results; only two are new relative to the
  previous 637-family sample proof set.
- All 10,572 blank-prefix shadow relations are checked, together with original
  pending membership. These are conditional transports, not 10,572 newly solved
  families. A core bound `B` becomes shadow bound `B+1`.
- Symbol/reflection images and shadows of proved cores receive their own
  checked table relations and pending-membership checks. They enter the
  closeout only after their core proof is available.

The combined audit proves and census-links **11,336 distinct families**.
The 4,706 distinct source families expand to 10,550 symbol/reflection images;
131 newly covered shadow representatives add another 786 family images.
These transfers contribute 6,630 families beyond the source proofs, with both
scores bounded by 4,096 or 4,097. The original 1,024-family sample now has
**649 checked and census-linked families**, 140 unresolved checker rejections,
and 235 without a certificate.

The combined result is in [`wave2-summary.json`](research/wave2-summary.json).
[`wave2-families.tsv`](research/wave2-families.tsv) counts each machine-string
family ID once even when several methods prove it. The
[current sample ledger](research/wave2-sample.tsv) covers the original 1,024
sample rows separately. None of these counts is a revised raw-table weight or
a count of deleted eight-step census leaves. The earlier reports remain frozen.

## Rebuild the proofs

With the repository's Coq 8.18 toolchain active, from the repository root:

```bash
make -C four check -j2
python3 four/tools/generate_advanced_examples.py --check
make -C four check-wave -j2
```

`check-wave` rebuilds and audits the affine closeout, closure batch, conditional
shadow links, transported family proofs, and combined coverage theorem. It
uses tracked compact inputs. It does not need the external affine search
binary, full survey logs, or a network connection. Generated proof shards stay
under ignored `four/build/` directories. The closure batch can reuse a shard
only when its source, dependency, and compiled-artifact hashes agree; the final
recursive `coqchk` still audits the complete aggregate.

The constituent targets are `check-affine-closeout`, `check-closure-batch`,
`check-shadow-links`, and `check-transport`. Their reports are published only
after successful compilation and recursive audit. `--refresh` on a tool
recomputes its report after checking intentionally changed inputs; ordinary
replay refuses stale evidence.

The final theorem is `BBB24Wave.WaveCloseout.wave_coverage`: every table satisfies
both champion bounds or belongs to `wave_pending`.
`wave_families_discharged` proves that each boarded family and every completion
was originally pending, is bounded, and is excluded from that residual.
`wave_upper_if_remaining` states the remaining global proof obligation.

After `check-wave`, inspect them with:

```bash
coqtop -quiet \
  -Q four/theories BBB24 \
  -Q four/build/affine-batch BBB24Batch \
  -Q four/build/affine-closeout BBB24AffineCloseout \
  -Q four/build/closure-batch BBB24ClosureBatch \
  -Q four/build/family-transport BBB24Transport \
  -Q four/build/wave-closeout BBB24Wave <<'COQ'
From BBB24Wave Require Import WaveCloseout.
Check wave_coverage.
Check wave_families_discharged.
Check wave_upper_if_remaining.
Print Assumptions wave_coverage.
COQ
```

The combined proof uses only the preexisting functional extensionality axiom.
The generic certified-board and board-union lemmas are axiom-free.

## Repeat or escalate the search

After reproducing the first sweep's ignored survivor list as described in
[`PIPELINE.md`](PIPELINE.md), run:

```bash
python3 four/tools/advanced_sweep.py --build --sample 0 --workers 2 \
  --output-dir four/build/advanced/local-full \
  --report four/build/advanced/local-full/report.json
```

Each stage has a per-row timeout, and interrupted logs resume without dropping
unprocessed rows. Add `--check` to validate completed saved logs. Keep new runs
in separate directories when parameters, code, or toolchain change.

The next step follows the same playbook: escalate the remaining core work list,
replay accepted certificates in bounded shards, transfer their proofs to
siblings and shadows, and group the genuinely persistent cases by shared
submachines or recurrence structure. More fuel alone does not repair every
affine rejection: a diagnostic sample found block-representation and auxiliary
rule replay failures as well as search-budget limits.
