# S052: a six-phase recursive counter

The exact complete table is `1LB2LB1RA2LA_0RB3LB3RB1RA` (S052 in the original 78). This package proves `NonHalt` and `QHBound 0`, with no instruction claim.

Define `M(k)` as A scanning 0, with an empty right word and nearest-first left word `11 3^(6k+4) 0`. The actual blank execution reaches `M(0)` after 142 steps. Six phases transform `M(k)` into `M(k+1)` in a positive number of ordinary steps. Local scan lemmas handle arbitrary untouched contexts; a mutual induction proves the four recursive helper families needed by the outer return.

`Outer.v` states its construction with four explicit helper premises. `Proof.v` discharges all four using `Odd.v`, so the final return and state-bound theorems have no pending helper premise. Arbitrarily late A and B visits follow from positive returns. The exact-table wrapper and inventory connect the theorem to the complete census family. No fitted native whole-cycle time formula is needed for the proof.

Build and recursively audit from the repository root with the census Coq toolchain on PATH:

```bash
python3 four/tools/replay_state_case_proofs.py --checkpoint additional --only burn26-s052-counter
```

The frozen [checked report](burn26-s052-counter-checked.json) pins the inputs, all four proof modules, regressions, generated wrappers and exact inventory. The replay generates a current recursive receipt under `four/build/` without changing that report. The mutual helper and main return are axiom-free; final tape/function transport uses the repository's existing functional extensionality axiom.
