# Additional state proofs for BBB(2,4)

This checkpoint supplies 30 accepted families in ten packages: seven newer individual proofs and the earlier 23 history-marker proofs. Together with the [initial 36 cases](STATE-CASE-PROOFS.md), these provide source replay for all 66 accepted cases at this freeze. Twelve of the original 78 holdouts remain. The global state upper bound and instruction upper bound remain open. Follow the [public scoreboard](https://github.com/carrino/Coq-BBB4/issues/261) for later progress and census assembly.

## Build and audit

Use the tested Coq 8.18.0 / OCaml 4.14.2 toolchain with `coq-native`, GNU make and Python 3; see [toolchain setup](../docs/VERIFYING.md#reproduce-the-complete-targets). From the repository root:

```bash
eval "$(opam env --switch=census)"
python3 four/tools/replay_state_case_proofs.py --checkpoint additional --list
python3 four/tools/replay_state_case_proofs.py --checkpoint additional
```

The default checkpoint still builds the initial 36 cases. To reproduce all 66, run both:

```bash
python3 four/tools/replay_state_case_proofs.py
python3 four/tools/replay_state_case_proofs.py --checkpoint additional
```

For one additional package, select its name from the table:

```bash
python3 four/tools/replay_state_case_proofs.py --checkpoint additional --only burn26-s052-counter
```

The wrapper verifies frozen source/input hashes, builds public prerequisites and runs the selected drivers sequentially. Every package compiles the exact transition table, universal machine lemmas, census-family wrapper and exact inventory, then performs a full recursive `coqchk` audit. Logs and current audit receipts are generated under `four/build/`; no compiled files or old audit receipts need to be downloaded. The wrapper saves its additional-checkpoint result under `four/build/state-case-proof-replay/additional/`.

## Cases and claims

| Cases | Package / proof sources | State bound | Frozen report |
| --- | --- | ---: | --- |
| S043 | [burn25-s043-counter](proof-sources/burn25-s043-counter/) | 0 | [checked](research/burn25-s043-counter-checked.json) |
| S010 | [burn26-s010-crossing](proof-sources/burn26-s010-crossing/) | 0 | [checked](research/burn26-s010-crossing-checked.json) |
| S030 | [burn25-s030-finite](proof-sources/burn25-s030-finite/) | 2,199,023,255,552 | [checked](research/burn25-s030-finite-checked.json) |
| S040 | [burn27-s040-word-cycle](proof-sources/burn27-s040-word-cycle/) | 0 | [checked](research/burn27-s040-word-cycle-checked.json) |
| S066 | [burn28-s066-frontier](proof-sources/burn28-s066-frontier/) | 0 | [checked](research/burn28-s066-frontier-checked.json) |
| S052 | [burn26-s052-counter](proof-sources/burn26-s052-counter/) | 0 | [checked](research/burn26-s052-counter-checked.json) |
| S074 | [burn29-s074-even-counter](proof-sources/burn29-s074-even-counter/) | 0 | [checked](research/burn29-s074-even-counter-checked.json) |
| S007, S018, S019, S023, S025, S026, S028, S029, S033, S037, S038, S039, S041, S058, S072, S078 | closed16 / [HistoryMarker](proof-sources/burn12-history-marker/) | 0 | [checked](research/burn12-history-marker-closed16-checked.json) |
| S008, S049, S054, S073 | closed4 / [HistoryMarker](proof-sources/burn12-history-marker/) | 0 | [checked](research/burn12-history-marker-closed4-checked.json) |
| S017, S021, S035 | closed3 / [HistoryMarker](proof-sources/burn12-history-marker/) | 0 | [checked](research/burn12-history-marker-closed3-checked.json) |

The [additional manifest](research/state-case-proofs-additional.json) identifies every exact machine, report digest, prerequisite and frozen source/input hash. A zero state bound follows from arbitrarily late visits to both states. S030 instead proves exact state score **1,367,354,345,129**, below the convenient table bound `2^41`.

The closed16/4/3 batches instantiate the same universal historical-marker theorem with frozen machine/parameter tuples. The wrapper first rebuilds its generic prerequisite and validates the current complete source/object/runtime closure. The separate `replay_history_state_batches.py` command then regenerates the original batch statements and inventories, compiles them and audits their complete dependency closures without reuse. Original reports and drivers remain immutable; current compiled objects are validated against current recursive receipts rather than historical object-byte hashes.

Native controls support discovery and regression checks; they do not supply proof credit. Universal Coq lemmas and checked finite prefixes supply the proofs. Final tape/function transport can use the repository's existing functional extensionality axiom; inspect the generated `Print Assumptions` blocks and recursive audit logs. These individual results still need to be connected to the complete census before they yield a global upper bound.

The [additional state-case workflow](../.github/workflows/state-cases-additional.yml) replays these ten packages in three independent source checkouts. Existing workflows retain their original checks.
