# Wave-3 residue staging — the irules-QH corollary harvest

_Written 2026-07-22 (branch `claude/coq-bbb4-wave-3-harvest-jha79p`), on
top of the merged PR #19 (wave-2 staged; `D_census` committed tables at
9,364, wave-2 wire pending → 7,255)._

Wave 3 implements SWEEP §6 step 3 (`tools/recon_20260721_sweep/SWEEP.md`):
the **single highest-value new checker** — the irules-QH corollary — and
harvests the list-C residue with it.  Everything here is **STAGED, not
wired** (the census re-cert was pending; no census `.v` input was
touched; `tools/census_cache.py --check` still reports the pre-wave-2
input hash).  The batched wire follow-up is mechanized:
**`tools/wire_wave3.py --box`** (wires wave-2 AND wave-3, regenerates
`Deferred_*` via `regen_residue.py --wave3`, then `make census-verify` +
`census_cache.py --update` on stable hardware).

## The new checker (the ONE new trust surface)

The landed IRules Meta engine builds, from an untrusted certificate, a
faithful forward-behavior model: every configuration from the anchor on
fires a transition in the meta-cycle's fired set `F`, and every
transition in `F` fires unboundedly often.  The landed checkers extract
`NeverQuasiHaltsSt` when every prefix-visited state owns a transition in
`F`.  The **dual extraction** — this wave's only new lemma — concludes
from the SAME model:

- a witness state `qz` that is prefix-visited but owns NO transition in
  `F` is silent from the anchor on → `QuasiHaltsSt` (witness `qz`);
- states in `F` recur unboundedly → never quiet; states outside `F` are
  additionally checked unvisited in the window `[min B anchor, anchor)`
  → every quiet state's last visit `< B` → `QHBound B`;
- the tiling covers every index → `NonHalt`.

Together: the census R_QH tier triple `NonHalt /\ QHBound 2000 /\
QuasiHaltsSt`.  Two engine variants, both new FILES (no landed file
touched, census input closure unchanged):

| file | checker | certs |
|---|---|---|
| `theories/Checkers/IRules/MetaQH.v` | `irules_check_qh` + `_sound` | v1 |
| `theories/Checkers/IRules/MetaBlkPfxQH.v` | `irulesblkpfx_check_qh` + `_sound` | v3/v5/v6/v7 (the ones the residue actually has) |

`Print Assumptions` = `functional_extensionality_dep` only for both.

**Corruption tests (`theories/Tests/IRulesQH_Corruption.v`, MUST-fail
controls, all `vm_compute`-closed):** a genuinely never-QH machine (its
own verified irules certificate, all states live) is rejected for EVERY
witness choice on BOTH engines; a halting machine is rejected; a live
state offered as the witness is rejected; and the score-window gate is
load-bearing (B=2000 accepts a machine whose quiet state last-visits at
~1459, B=100 refuses it).

## The harvest (UNTRUSTED sweep → kernel-checked boards)

`bin/irules --max-steps 200000` over the **5,656** unboarded list-C
residue machines (6,247 minus the 591 wave-2 LCStage never-QH boards),
2 nice workers, cert per decided machine
(`BBB/results/certs_wave3/irules/`).  State-level classification from
each cert's `claim_trans` lines (a state is quiet iff it has an F
transition and no I one).  The Coq kernel re-checks every claim; the
emitters only transcribe.

### Track 1 — state-QH → R_QH tier (the mis-binned quasihalters)

- Emitter `tools/gen_irulesqh_certs.py` → files
  `theories/Machines/IRulesQHStage/IQHStage_NN.v` (100/file),
  manifest `tools/irulesqh_manifest.tsv`
  (`machine, theorem, file, quiet_state, last_visit, anchor, cert_ver`).
- Per machine: `cqh_w3_NNNNN : iqh tm_w3_NNNNN` with `iqh tm` =
  `NonHalt tm /\ QHBound 2000 tm /\ QuasiHaltsSt tm`, closed by
  `irulesblkpfx_check_qh_sound` at B=2000, cfuel 2e5 / fuel 3e5.
- Machines whose quiet state last-visits at ≥ 2000 cannot satisfy
  `QHBound 2000` and are SKIPPED (reported by the emitter; they stay
  deferred — same class as the wave-1 `provenqh_stay` pair).
- **Yield: 1,090 machines** (`IQHStage_00..10.v`; SWEEP §5 projected
  ~1,047 — beaten).  Max quiet-state last visit across the whole
  harvest: **1,459 < 2000**, so ALL 1,090 board; zero skipped.

### Track 2 — state-never-QH → proven (R_NeverQH) tier (the IRules share)

- Emitter `tools/gen_irulesnqh_stage.py` → files
  `theories/Machines/ListCStage2/LCS2_NN.v` (100/file), manifest
  `tools/irulesnqh_manifest.tsv`.
- Per machine: `nqh_n3_NNNNN : NeverQuasiHaltsSt tm_n3_NNNNN` via the
  LANDED `irulesblkpfx_check_neverqh_sound` (MetaBlkPfx) — **no new
  trust surface**; corruption coverage is the landed Phase-2 engine's.
- **Yield: 963 machines** (`LCS2_00..09.v`; SWEEP §4 projected ~560 —
  beaten, the bigger budget over the full 5,656 recovered more).

**Sweep totals:** 5,656 machines swept, 2,053 certs (36.3%): 1,090
state-QH + 963 state-never-QH, zero contradictions, zero unclassifiable.
After the combined wave-2+3 wire: `D_census 9,364 − 1,518 − 591 −
1,090 − 963 = 5,202`.

Compile cost (measured, apt coqc 8.18, vm_compute): **~1 s/machine**,
~80 s per 100-machine file, memory far below the Phase-2 fuel-3e5
batches (these certs are shallow: mostly ≤ a few rules).  The old
"~8 GB, -j2, 10/file" rule was for the 50 deep Phase-2 holdout certs
and does NOT bind here; 100/file at -j2 is comfortable.

## Wire + regen (box follow-up, mechanized)

`tools/wire_wave3.py --box` performs (idempotence guarded):

1. `theories/Census/RerootQH_Data.v` ← + `RRStage_00..15` (wave-2) +
   `IQHStage_*` (wave-3), `reroot_qh_list` + `Forall_app` chain
   (`rrqh`/`iqh` are definitionally the tier predicate).
2. `theories/Census/Proven_Data.v` ← + `LCStage_00..11` (wave-2) +
   `LCS2_*` (wave-3), `proven_list` + chain.
3. Drop lists: `reroot_boarded.txt` += RRStage machines (184 → 1,702);
   `proven_listc_dropped.txt` = LCStage + LCS2 manifests;
   `iqh_boarded.txt` = IQHStage manifest.
4. `_CoqProject` gains the staged block (still outside the census
   target closure — `CENSUS_VO_HASH` changes only via `Deferred_*`).
5. `regen_residue.py --wave3` — all subset/disjoint/no-double-drop
   asserts live there; regenerates `Deferred_*`.

Then on the box: `make census-verify`; `Print Assumptions
census_decided` must stay `functional_extensionality_dep` only;
`census_cache.py --update`; commit census `.vo` + hash.

Expected `D_census` after the combined wire:
`9,364 − 1,518 (RRStage) − 591 (LCStage) − |IQHStage| − |LCS2|`.

## Reproduce (UNTRUSTED)

Scratchpad drivers: split the target list
(`census_residue.txt` list-C rows minus `listc_caught.tsv`), run
`bin/irules --max-steps 200000 --cert-dir …` (2 nice workers), then the
two emitters over the produced certs, then `coqc -Q theories BBB4` per
staged file.
