# Fifth supplementary checkpoint

Five audited boards add **13 instruction bounds** and **seven state bounds**
to the [fourth checkpoint](BURN4.md). The supplement now has 35 boards.

| Bound | Covered in the 133,185-family cohort | Remaining | Remaining before this checkpoint |
| --- | ---: | ---: | ---: |
| Instructions | 101,703 | **31,482** | 31,495 |
| State | 132,647 | **538** | 545 |

The full union contains **124,905 families with both bounds** and **155,849
with a state bound**. The exact ledger is
[`burn5-burndown-summary.json`](research/burn5-burndown-summary.json).
Every board proves all-completion soundness, exact inventory and membership
in the original census pending predicate. Raw census weights are unchanged;
the global BBB(2,4) upper bound remains open.

## New proofs

| Board | New instruction bounds | New state bounds |
| --- | ---: | ---: |
| [Ternary counter](research/burn4-ternary-counter.md) | 1 | 0 |
| [Ternary templates](research/burn4-ternary-template.md) | 7 | 0 |
| [Instruction history retry, pilot](research/burn4-history-timeout8.md) | 5 | 0 |
| [State history continuation](research/burn4-history4-continuation.md) | 0 | 6 |
| [Marker/history composition](research/burn4-marker-composition.md) | 0 | 1 |

The counter proof establishes an exact instruction score of **4** for
`1LB2LB3LB2RA_3RA1RA1LB1RB`. An inductive macro describes arbitrarily long
counter phases; direct simulation is needed only for the short entry prefix.
The template theorem transfers the six active transitions to seven more
families, including arbitrary dormant tape suffixes. Their instruction
bound is **7**, and both counter packages have state bound **0**. These seven
template bounds are upper bounds, not claims of exact scores.

The five instruction-history proofs use bound **4,096** and upgrade families
already covered by the earlier state-history board. The six new state-history
proofs also use **4,096**. The composition proof uses a marker invariant for
one state's recurrence and a history certificate for the other, giving state
bound **0**. Exact-ID subtraction verifies that the seven state additions are
disjoint from earlier coverage and one another.

## Reproduce

With the [Coq toolchain](../docs/VERIFYING.md) on `PATH`, run from the repository
root:

```bash
make -C four list-burn5-campaign
make -C four check-burn5-campaign
```

The [34-step build plan](research/burn5-campaign-build.json) replays all earlier
supplementary boards before checking the combined coverage theorem. The
composition step depends on the relaxed-marker package; the template step
depends on the original ternary-counter package. No native discovery search
is required. `CAMPAIGN_JOBS=2` allows independent proof batches to run together.

Rebuild the original campaign as well to regenerate the combined ledger:

```bash
make -C four check-campaign
python3 four/tools/summarize_next_burndown.py \
  --supplement-manifest four/research/burn5-campaign-input.json \
  --supplement-report four/research/burn5-campaign-summary.json \
  --report four/research/burn5-burndown-summary.json \
  --output-dir four/build/burn5-burndown
```

Repeat the Python command with `--check` to compare every report and ledger
byte. Summary delta fields compare against the original 113-board campaign;
the difference from checkpoint four is the gain reported above. Published
inputs and reports remain frozen, while generated Coq and runtime audit
receipts stay under ignored build directories. Later retries and symmetry
extensions are excluded from this checkpoint.
