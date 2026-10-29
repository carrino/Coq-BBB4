# History graph-growth continuation

This bounded 64-family search adds **three state bounds of 4,096** and no
instruction bounds. Each family is outside the fifth supplementary checkpoint
and the earlier single-family graph-growth proof.

| Family | State bound |
| --- | ---: |
| `1LB0RB1LA2LA_1RB2RA3LB2RB` | 4,096 |
| `1LB2LA1RB0LA_0RB3RA3LB2LA` | 4,096 |
| `1LB2LB1RA1RA_3RB2LA3RB1RA` | 4,096 |

Earlier diagnostics found that graph closure failed before ranking on most
sampled remaining families. Increasing exploration fuel alone found no new
candidate in the 16-family diagnostic pilot. Increasing growth rounds to 128
produced the preceding single-family proof. This continuation uses the same
successful configuration: width 4, history depth 4, anchor 4,096, fuel 131,072,
and 128 growth rounds. Its four-second native budget gave three candidates,
52 completed rejections and nine timeouts in 82.28 seconds. Native outcomes
are search results, not proofs.

The three candidates were replayed through the existing `StatePipeline`
checker. Two resource-aware proof shards, an aggregate and an exact inventory
compiled in 178.38 seconds. The complete recursive kernel audit checked all
270 dependency modules without reuse. The board proves every completion of
each partial table and original census pending membership. Only the existing
functional-extensionality assumption is used.

From the repository root, after building the shared four-symbol theories with
the [documented toolchain](../../docs/VERIFYING.md), replay with:

```bash
python3 four/tools/check_burn4_history4_continuation_growth64.py \
  --resume --timeout 600 --audit-timeout 2400
```

The compact proof input, search report and shard plan suffice for replay; the
native executable, full search queue and native cost ledger are unnecessary.
Do not pass `--select` when replaying the published package. It is only for the
initial conversion from a completed native search. Exact inventory and report
bytes remain frozen; generated Coq and current audit receipts stay under
`four/build/burn4-history4-continuation-growth64/proof/`.

The subsequent 451-family search uses the untested remainder of the same
configuration. Its candidates are excluded from this package until their
separate Coq replay and complete audit finish.
