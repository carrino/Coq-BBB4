# Reuse state witnesses from capacity near misses

The five remaining state obligations in the capacity near-miss lane already
have suitable saved graphs. Each graph contains an ordinary recurrent
instruction for state A and another for state B. Their missing instruction
targets obstructed the instruction-bound search but do not obstruct the
state-bound checker.

All five families now have kernel-audited state bounds of 4,096, including
all-completion bounds, original census pending membership, and exact inventory.
No instruction bound is claimed. These IDs are disjoint from the other boards
in this round, the 2,801-row repeated-word input and the 207-row priority input.

| Family | Graph nodes | Chosen A instruction | Chosen B instruction |
| --- | ---: | --- | --- |
| `1LB1LB---2RA_1RB3LB1RA0RA` | 114 | A1 | B1 |
| `1LB2LA1RA2LB_3RB3LB1RA0RA` | 79 | A2 | B0 |
| `1LB2LB2LA0RA_1RB3LA3RA0RA` | 194 | A0 | B0 |
| `1LB2RA3LB1LB_0RB3LB2LA3RA` | 118 | A1 | B0 |
| `1LB1RB---3LA_3RA2LB3RB2LA` | 86 | A1 | B2 |

Every selected graph has width 2, anchor 4,096 and the original orientation.
The compact bundle contains only graph contexts and the two instruction
choices. The unchanged `WeightedState` checker recomputes closure and ordinary
ranking; no capacity witness, LP result, or new theorem is needed. Native
`ranked` flags guide extraction and are not trusted by Coq.

## Reproduce

After `make -C four all`, run from the repository root:

```bash
python3 four/tools/check_burn2_weighted_state.py \
  --input four/research/burn3-capacity-state-input.json \
  --report four/research/burn3-capacity-state-checked.json \
  --inventory four/research/burn3-capacity-state-machines.json \
  --output-dir four/build/burn3-capacity-state/proof \
  --namespace BBB24Burn3CapacityState --shard-size 1 \
  --timeout 300 --audit-timeout 1200 --resume
```

Replay requires only the tracked 2,185-byte bundle and core proof sources.
The extraction script `select_burn3_capacity_states.py` also records historical
source hashes; rerunning extraction requires the saved discovery graphs and
previous checkpoint's state remainder under ignored `build/` paths. Those
discovery artifacts are not required to replay the proof.

The seven generated modules compiled in 8.388 seconds and passed a full
recursive kernel audit in 40.420 seconds on the original run. Generated proof
objects remain ignored; the compact inputs, checked report and inventory are
tracked separately.
