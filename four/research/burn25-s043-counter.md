# S043: a growing unary counter

The exact complete table is `1LB2LA3RB2LA_2RB2LA3RA0LB` (S043 in the original 78). This package proves `NonHalt` and `QHBound 0`, with no instruction claim.

Define `M(n)` as A scanning 0, with an empty left word and right word `2^5 1^(2n) 01`. The actual blank execution reaches `M(254)` after 100,852 steps. Universal scan lemmas prove

```text
M(n) -> M(3n+3) in 12n^2 + 66n + 84 steps.
```

The positive return duration and a B visit inside each cycle establish arbitrarily late visits to both states. The exact-table wrapper and inventory connect that recurrence to the complete census family. Native finite controls are provenance and regression checks; the parameterized Coq return theorem supplies the unbounded argument.

Build and recursively audit from the repository root with the census Coq toolchain on PATH:

```bash
python3 four/tools/replay_state_case_proofs.py --checkpoint additional --only burn25-s043-counter
```

The frozen [checked report](burn25-s043-counter-checked.json) pins the inputs, templates, generated sources, exact inventory and original recursive audit. The replay generates a current recursive receipt under `four/build/` without changing that report. Final tape/function transport uses the repository's existing functional extensionality axiom.
