# Fresh state search, second supplementary round

The fixed input contains 2,089 state obligations from the first supplement's
remaining 2,504 families. It excludes all 409 state obligations in the existing
repeated-word/timeout replay queue and six of the capacity pilot's near misses.
`burn2-state-input.json` records the exact input hash and ordering. Every family
is still subject to kernel replay; discovery is not proof evidence.

The first 256 inputs produced 119 weighted state certificates and 14 disjoint
ordinary n-gram certificates. All 133 passed their bound, original-pending,
all-completion and exact-inventory proofs, followed by recursive `coqchk`.
The increment is 119 state-only families plus 14 families with both bounds.

The existing weighted-state search previously used window width 2 and anchor
256. This search uses width 3, anchor 4096, fuel 8193, 33 growth rounds, at most
4096 graph nodes, 0.5 seconds per native graph orientation and 3 seconds per LP
attempt. The 256-row pilot took about 181 seconds. Its weighted certificates
compiled in 128.612 seconds and audited in 75.646 seconds. The 14 ordinary cases
compiled in about 33.5 seconds and audited in about 53.6 seconds. Every replay uses one
worker and a 3 GiB address-space cap.

The graph producer reports `ordinary_candidate` when its ordinary ranking
procedure handles every target, and then omits that graph from its output.
Those rows must be collected separately from weighted certificates. Their Coq
replay uses the existing n-gram checker and proves both bounds at 4096; an
untrusted native status is never accepted as a proof.

## Reproduce the pilot proofs

Build the core with `make -C four all`, then run from the repository root:

```bash
python3 four/tools/check_burn2_weighted_state.py \
  --input four/research/burn2-state-pilot-input.json \
  --report four/research/burn2-state-pilot-checked.json \
  --inventory four/research/burn2-state-pilot-machines.json \
  --output-dir four/build/burn2-state/weighted-pilot-proof \
  --namespace BBB24Burn2StatePilot --shard-size 4 \
  --timeout 300 --audit-timeout 1800 --resume

python3 four/tools/check_burn2_state_ordinary.py \
  --input four/research/burn2-state-ordinary-pilot-input.json \
  --report four/research/burn2-state-ordinary-pilot-checked.json \
  --inventory four/research/burn2-state-ordinary-pilot-machines.json \
  --output-dir four/build/burn2-state/ordinary-pilot-proof \
  --namespace BBB24Burn2StateOrdinaryPilot --shard-size 2 \
  --timeout 300 --audit-timeout 1800 --resume
```

No search logs, native discovery binary or LP package are required for replay.
Both runners reproduce exact source bytes and accepted inventories, compile
and audit current proof objects, and preserve their published reports.
Historical object bytes, compiler versions and timings are not portability
requirements. Current-runtime evidence goes under ignored `four/build/` paths.
`--refresh` is only for initial publication and refuses to replace an existing
report or inventory. Generated Coq and proof objects remain untracked.

The full continuation searched the remaining input prefix without changing these
pilot boards. Its 754 weighted-state families and 121 ordinary families passed
exact inventory, census membership, typed bounds, and full recursive audits.
Together with the pilots, this lane contributes 873 state-only families and
135 families with both bounds. The full boards use shard sizes 4 and 2
respectively; their exact replay commands are in
[`burn2-campaign-build.json`](burn2-campaign-build.json). `select_burn2_state.py --offset 256` produces disjoint continuation
inputs in compact compressed bundles. Complete native graph snapshots retained
under `four/build/burn2-state/graph-snapshots/` are optional discovery material
for future solver experiments, not proof dependencies.
