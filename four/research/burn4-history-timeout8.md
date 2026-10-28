# Eight-second instruction-history timeout retry

This retry uses the exact certificates from the earlier 378-family state-history
batch. It selects only the 138 instruction checks that exhausted the earlier
two-second native budget. The 160 previously audited instruction successes and
80 completed native rejections are excluded. Selection also checks the original
113-board campaign and the frozen 28-board supplement for accepted instruction
families.

The master input sorts the 138 distinct machine IDs by SHA-256. The first 16 form
the pilot; the remaining 122 form the continuation. Each native check receives
eight seconds, with one worker and a 2 GiB address-space limit. Certificate
parameters are unchanged: width 4/history 3 or width 3/history 5, anchor 4096,
fuel 16384, extension 32, and bound 4096.

| Native batch | Attempted | Candidates | Completed rejections | Timeouts |
| --- | ---: | ---: | ---: | ---: |
| Pilot | 16 | 5 | 6 | 5 |
| Continuation | 122 | 16 | 64 | 42 |
| Total | 138 | 21 | 70 | 47 |

A native rejection describes this particular certificate; it does not prove a
machine is unsolvable. A native success is a candidate until its Coq replay and
complete dependency audit finish. The saved search reports and ledgers preserve
all three outcomes separately.

Proof replay uses the existing `AdvancedPipeline` checker and unchanged
`check_closure_wave.py` source renderer. Each machine has its own shard, with a
600-second compilation limit and one worker under a 3 GiB address-space limit.
The proof wrappers cover both bounds, every completion of a partial table, exact
inventory, and census membership. All selected machines already belong to the
audited 378-family state board, so these boards add instruction coverage only.

From the repository root, after following the [toolchain and shared-theory build
instructions](../../docs/VERIFYING.md):

```sh
python3 four/tools/check_burn4_history_timeouts.py \
  --batch pilot --resume --timeout 600 --audit-timeout 5400
python3 four/tools/check_burn4_history_timeouts.py \
  --batch rest --resume --timeout 600 --audit-timeout 5400
```

The compact proof inputs are tracked; native search is not needed to replay the
proofs. These commands perform a full recursive `coqchk` audit by default. The
optional `--audit-cache PATH` accepts local build receipts only: the V3 validator
checks the current source/object/toolchain/dependency snapshot and follows each
reused module back to a successful recursive audit. Every new module is checked.
The original pilot audit reused the unchanged dependencies from the recursive
`burn3-history-instruction` receipt, and the continuation uses that validated
ancestry through the pilot receipt.

Published `*-checked.json` reports and `*-machines.json` inventories are immutable.
Replay verifies their stable fields and writes a fresh runtime receipt under
`build/burn4-history-timeout8/`. The proof runner checks its inputs, sources, and
shared proof objects before and after compilation and audit. Aggregate descriptors
are stored in each checked report's `descriptor` field.

The native selection and saved results can be checked separately:

```sh
python3 four/tools/search_burn4_history_timeouts.py --batch pilot --check
python3 four/tools/search_burn4_history_timeouts.py --batch rest --check
```

These search checks require the original native ledgers and executable under
`build/`; the proof replay commands above do not.
