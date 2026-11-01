# Instruction BBB(2,4) burndown

The state maximum is proved. The instruction maximum remains open; its known
lower bound is **205,770,076,433,044,242,247,860**, attained by
`1RB2LA1RA1LB_0LB2RB3RB1LA`. See the [formal specification](theories/Spec.v)
and [champion proof](theories/Champion.v).

This scoreboard resumes the **28,653 exact census families** left by the
historical instruction checkpoint. A family may have undefined transitions;
its bound must cover every completion. These counts concern the historical
hard cohort, rather than the entire global instruction census.

| Checkpoint | New instruction proofs | Remaining families |
| :-- | --: | --: |
| Historical resumed inventory | — | 28,653 |
| Stronger history closure certificates | 11 | 28,642 |
| Finite prefixes followed by one recurring instruction | 4 | **28,638** |

Both new batches passed full recursive `coqchk`, with zero skipped or reused
audit modules. Their all-completion bounds and exact inventories are proved in
Coq. They add no state coverage to the completed state result.

The [baseline](research/instruction-baseline.json) freezes every remaining ID
in compact base-17 form, its exact machine-text hash, and the historical
checkpoint identity. It is research accounting, not a replacement for a global
coverage theorem. The [current summary](research/instruction-burndown-summary.json)
deduplicates the new proved inventories against that baseline. Historical
search outcomes, failed attempts and timeouts receive no proof credit.

## First resumed batches

The history pilot selected 128 families by increasing
`SHA256("instruction-resume-v1:" + machine)`. It tried width/history pairs
`(4,3)`, `(3,5)` and `(5,2)`, removing successes between stages. Each attempt used
bound and anchor 65,536, fuel 32,768, 64 growth rounds and a 0.5-second native
budget. The 366 attempts produced 11 candidates; all 11 passed the existing
instruction-mode checker in Coq. Their common upper bound is **65,536**.
These are upper bounds, not exact score claims. The remaining 117 sampled
families remain open.

The finite-tail package reuses four unchanged prefix proofs from the state
development. A new small theorem proves that a suffix firing only `B0` cannot
contain a late last firing of any instruction. It yields these instruction
results (programs are displayed with their first move to the right):

| Machine | Instruction score or upper bound |
| :-- | --: |
| `1RB2RB1LB1LA_1LB3RA3LA2RB` | = 2,333,909 |
| `1RB2LB3RA2LA_3LB3RA0RB1RB` | = 2,501,552 |
| `1RB2RB3LA2RA_2LB1LA0RB3RA` | ≤ 1,012,664,081 |
| `1RB2RA1LA2LB_2LB3RB0RB1RA` (former champion) | = 67,093,892,759,901,295 |

The exact results prove both attainment and the matching upper bound, under
the repository's last-index-plus-one convention. The fourth prefix is proved
by symbolic macros; replay does not simulate its enormous number of steps.
The [tail theorems](proof-sources/instruction-tails/FiniteTails.v),
[all-completion board](proof-sources/instruction-tails/Board.v) and
[regressions](proof-sources/instruction-tails/Regression.v) are tracked sources.
The board uses a common conservative bound of 2^56 for inventory registration.
Its assumptions contain only the existing functional-extensionality axiom.

## Replay and follow along

With the [Coq toolchain](../docs/VERIFYING.md) on `PATH`, run from the repository
root:

```sh
make -C four Makefile.coq
make -C four -f Makefile.coq theories/AdvancedPipeline.vo theories/BoardManifest.vo -j2
ulimit -S -s 65536
python3 -m unittest discover -s four/tools -p 'test_instruction_residual.py'
python3 four/tools/check_instruction_closure.py
python3 four/tools/check_instruction_tails.py
python3 four/tools/report_instruction_burndown.py --check
```

Each replayer uses one compilation worker and a 3 GiB process address-space
limit. It reconstructs the proofs from tracked inputs, then audits the entire
dependency closure. No discovery executable, old proof object or historical
receipt is needed. Published reports stay frozen; current logs and receipts go
below `four/build/instruction-burn1/` and `four/build/instruction-tails/`.
The reporting command writes the exact remaining list to
`four/build/instruction-burndown/remaining.txt`. GitHub Actions runs both proof
replays from source.

The next steps are to expand the successful history pilot in bounded batches,
classify the unsolved instruction targets, and extend the counter/phase proofs
where closure abstractions lose sparse returns. A final result will also need
the complete instruction census assembled into a universal upper-bound theorem
and paired with the champion's exact lower bound.
