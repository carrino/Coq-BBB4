# Recent state proofs for BBB(2,4)

These eleven packages extend the [initial 36 cases](STATE-CASE-PROOFS.md) and [additional 30 cases](STATE-CASE-PROOFS-ADDITIONAL.md) to 77 independently reviewed families from the original 78 holdouts. The remaining case at this freeze is S071, `1LB2RA3LA2RB_0RB3LB0LA1RA`. These results do not establish the global upper bound: census assembly also remains in progress. No instruction-based bound is claimed here. Follow the [public scoreboard](https://github.com/carrino/Coq-BBB4/issues/261) for later progress.

## Build and audit

Use the tested Coq 8.18.0 / OCaml 4.14.2 toolchain with `coq-native`, GNU make and Python 3; see [toolchain setup](../docs/VERIFYING.md#reproduce-the-complete-targets). From the repository root:

```bash
eval "$(opam env --switch=census)"
python3 four/tools/replay_state_case_proofs.py --checkpoint recent --list
python3 four/tools/replay_state_case_proofs.py --checkpoint recent
```

To reproduce all 77 accepted cases in the three source checkpoints:

```bash
python3 four/tools/replay_state_case_proofs.py
python3 four/tools/replay_state_case_proofs.py --checkpoint additional
python3 four/tools/replay_state_case_proofs.py --checkpoint recent
```

For one recent package:

```bash
python3 four/tools/replay_state_case_proofs.py --checkpoint recent --only burn35-s070
```

The wrapper verifies frozen source/input/report hashes, builds public prerequisites and runs the selected drivers sequentially. Every package compiles its exact transition table, universal machine lemmas, regressions, all-completion census wrapper and exact inventory, then performs a full recursive `coqchk` audit. Generated objects, logs and current receipts stay under `four/build/`. The recent-checkpoint result is saved under `four/build/state-case-proof-replay/recent/`.

## Cases and claims

| Case | Package / sources | State bound | Frozen report |
| --- | --- | ---: | --- |
| S036 | [burn31-s036](proof-sources/burn31-s036/) | 0 | [checked](research/burn31-s036-checked.json) |
| S020 | [burn30-s020-counter](proof-sources/burn30-s020-counter/) | 0 | [checked](research/burn30-s020-counter-checked.json) |
| S064 | [burn33-s064](proof-sources/burn33-s064/) | 18,014,398,509,481,984 | [checked](research/burn33-s064-checked.json) |
| S042 | [burn32-s042](proof-sources/burn32-s042/) | 0 | [checked](research/burn32-s042-checked.json) |
| S059 | [burn36-s059-counter](proof-sources/burn36-s059-counter/) | 0 | [checked](research/burn36-s059-counter-checked.json) |
| S061 | [burn34-s061](proof-sources/burn34-s061/) | 0 | [checked](research/burn34-s061-checked.json) |
| S070 | [burn35-s070](proof-sources/burn35-s070/) | 0 | [checked](research/burn35-s070-checked.json) |
| S015 | [burn38-s015-normalizer](proof-sources/burn38-cut-siblings/) | 0 | [checked](research/burn38-s015-normalizer-checked.json) |
| S076 | [burn39-s076](proof-sources/burn39-s076/) | 0 | [checked](research/burn39-s076-checked.json) |
| S014 | [burn39-s014-normalizer](proof-sources/burn38-cut-siblings/) | 0 | [checked](research/burn39-s014-normalizer-checked.json) |
| S016 | [burn42-s016](proof-sources/burn42-s016/) | 0 | [checked](research/burn42-s016-checked.json) |

The [recent manifest](research/state-case-proofs-recent.json) records every exact machine, report digest, prerequisite and frozen source/input hash. A zero state bound follows from arbitrarily late visits to both states. S064 instead proves a convenient bound `2^54`: a kernel-checked binary macro computation reaches permanent B-only behavior after 12,762,141,566,885,339 steps. That drift-entry time is not asserted to be its exact state score.

S036 uses a context-parametric thirteen-phase return; S020 and S059 use closed binary-token languages; S042 uses a universally sound affine run-block checker; S061 and S076 use recursive word grammars. S070 combines a universal scanner theorem with an eight-state finite automaton and a checked prefix relation. The automaton was synthesized as untrusted input; its finite laws and preservation are proved in Coq. S014, S015 and S016 use byte-identical copies of a shared token normalizer, with separate exact tables and guarded continuation proofs.

## Replay prerequisites

S036's original frozen runner also checks an author-only preservation map referring to unrelated historical workspace artifacts. The wrapper therefore uses the separate `replay_s036_source.py` command. It pins the same report, six compact inputs, original templates, generated statements, source closure and exact inventory, then freshly compiles and recursively audits all five original modules. The preservation-map bytes remain pinned as provenance; its unrelated target files are not mathematical dependencies. Original reports and drivers remain unchanged.

S042's original runner invokes its native regression check, which expects an ignored copy of the original 78-machine list. The wrapper creates that exact scratch copy from the already-published, hash-checked `research/state-holdouts-78.txt`; it refuses to overwrite different bytes. No native search or old compiled object is required. Other recent cases use their original standalone drivers.

Native controls support discovery and regression checks and receive no proof credit. The Coq statements, universal lemmas and checked finite entries supply the proof. Final tape/function transport can use the repository's existing functional extensionality axiom; inspect each `Print Assumptions` block and recursive audit log. The [recent state-case workflow](../.github/workflows/state-cases-recent.yml) replays all eleven packages in three independent source checkouts, alongside the existing proof workflows.
