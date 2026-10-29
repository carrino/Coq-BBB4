# One state proof from longer history-graph growth

`1LB2RB0LB0RA_2RB3RA1RB3LA` has a certified state-quasihalting bound of 4096.
The proof includes exact inventory, original census membership and coverage of
all completions. It makes no instruction-bound claim. This family is disjoint
from the six history4 continuation families and the marker-composition family.

The preceding 32-family refinement pilot yielded no candidates when increasing
history length or window width. A diagnostic pass found that 30 of those 32
families failed graph closure before reaching the recurrence-ranking checks.
The next pilot selected 16 of these failures by smallest observed graph size.
Increasing exploration fuel alone to 131072 still rejected all 16. Increasing
the growth budget from 32 to 128 rounds then found this candidate in 0.760
seconds; the other outcomes were 12 rejections and three timeouts. Width and
history length remained 4, and the anchor remained 4096. These native results
guided search and do not establish any bound themselves.

Three generated Coq modules compiled in 75.432 seconds. Full recursive
`coqchk` checked all 269 dependency modules without reuse in 74.149 seconds.
The resulting board has state bound 4096 and no instruction bound.

After `make -C four all`, replay from the repository root:

```bash
python3 four/tools/check_burn4_history4_continuation_closure.py \
  --resume --timeout 600 --audit-timeout 2400
```

Portable replay requires the files with prefix
`research/burn4-history4-continuation-closure-` and suffixes `proof-input.json`,
`shard-plan.json`, `search.json`, `checked.json` and `machines.json`, plus the
runner and its existing repository dependencies. Native diagnostic executables,
search logs and input selection files are not required. Do not pass `--select`
when replaying the frozen package.

The descriptor is `descriptor` in the checked report; its module is
`BBB24Burn4History4Closure.HistoryInventory`, with theorem `inventory_exact`.
New audit receipts and generated sources remain under ignored
`four/build/burn4-history4-continuation-closure/proof/`. This proof is separate
from checkpoint 5 and must enter a combined census audit before its published
totals change.
