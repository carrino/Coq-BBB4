# Expanded-source conjugacy

The existing conjugacy sweep used eight earlier source boards. Repeating the
table lookup against the current checked instruction inventory found 1,399
remaining families whose state-swapped, symbol-renamed and optionally mirrored
tables extend a checked source. Ordinary relabeling and completion lookup found
no additional residual families.

Of those table matches, 512 already belong to the repeated-word replay queue.
The remaining 887 were tested for intersections between their A-start and
B-start blank-tape runs, using at most 4,096 steps from each start. There were
67 matches, all confirmed by exact Python tape comparison. Each is outside the
repeated-word queue, the capacity near-miss selection and the fresh state-search
selection. All 67 already have state bounds; their new contribution is to the
instruction ledger.

The mathematical argument uses the existing `IndexedConjugate` theorem. It
checks partial-table inclusion and exact finite configuration equality, then
transfers the source's nonhalting behavior and both bounds. The destination
prefix cost is included: source bounds are 4,096, the longest destination prefix
is 568, and the resulting uniform bound is 8,192. The longest source prefix is
422. Table relabeling alone is not used as an execution equivalence between
different initial states.

Reproduce from the repository root with the Coq toolchain on `PATH`:

```bash
python3 four/tools/replay_burn2_structural.py --resume
python3 -m unittest discover -s four/tools -p test_check_burn2_structural.py
```

The runner reconstructs only the 64 distinct source certificates used by these
transports: 60 from the closure-wave input, one from the first supplementary
timeout batch, and three weighted portfolios. Source reconstruction uses pinned
tracked bundles; it requires neither prior generated source boards nor a new
discovery search. Thirteen generated modules, proof objects, current runtime
records and complete recursive kernel-audit receipts live under ignored
`four/build/burn2-structural/proof/`. The `Inventory` module checks the exact
67-machine inventory, all-completion bounds and original pending membership.

The checked report is `burn2-structural-checked.json`. The portable adapter
verifies the exact source/helper pins in that frozen report, so later unrelated
Coq files do not enlarge its recorded source set. It regenerates identical proof
sources, compiles current objects and records a new complete recursive audit
under `build/`; the historical report is checked unchanged before and after the
replay. `--generate-only` checks inputs and source regeneration but does not
certify a proof replay. The six
regression tests reject altered source pins, wrong source tables, wrong prefix
intersections, changed budgets and duplicate targets.

The 820 unmatched fresh table candidates remain unresolved by this experiment.
A larger finite search budget, or a more general relation between the two
initial trajectories, may produce additional transport witnesses. Failure to
find an intersection at this budget proves no negative claim about a machine.
