# Behavior-guided state search

The second supplementary round inspected 32 remaining state obligations for
one million ordinary steps each. Every sample continued to visit both states;
the finite traces alone establish no quasihalting bound. The traces suggested
two search groups: 21 machines with short same-state runs and 11 with longer
excursions. The exact observations and input partition are recorded in
`burn2-state-diagnostics.json` and `burn2-state-diagnostic-plan.json`.

For the 21 short-run machines, the existing state history checker with window
width 4, history length 3, anchor 4096, fuel 16384 and 32 growth rounds found
nine candidates. A width-3/history-5 fallback found no additional candidate
among the other twelve. The two repeated-word configurations tried on the
eleven long-excursion machines found no candidates. These are bounded search
results, not a classification of the remaining behavior.

All nine history candidates passed the existing Coq state checker, original
census pending-membership proofs, all-completion bounds and an exact-inventory
theorem. A full recursive `coqchk` audit checked all 277 dependency modules
without reuse. The bound is 4096, for state quasihalting only. These nine IDs
are disjoint from the 873 weighted-state and 135 ordinary families accepted
by the other fresh-state batches in this round.

After building the core with `make -C four all`, replay from the repository
root:

```bash
python3 four/tools/check_burn2_diagnostic.py \
  --timeout 300 --audit-timeout 1200
```

The compact packed input is `burn2-diagnostic-short-proof-input.json`.
`burn2-diagnostic-short-checked.json` records the source and input hashes,
accepted inventory, descriptor and original local audit receipt. The replay
regenerates the exact sources, compiles and recursively audits current proof
objects, and preserves the published research reports. It saves current
runtime evidence under ignored `four/build/burn2-diagnostic-short/proof/`.
No native search executable or finite simulation log is needed for this
proof replay. The census module is
`BBB24Burn2DiagnosticShort.HistoryInventory` and its exact inventory theorem
is `inventory_exact`.
