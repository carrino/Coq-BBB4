# Wave-4 residue staging — listB QHBound recovery + listC fuel/drift harvest

_Written 2026-07-23 (branch `claude/coq-bbb4-wave-4-harvest-rdhj28`), on top
of the merged/staged wave-3 (PR #20): the MetaBlkPfxQH checker + 2,099 boards
(1,090 R_QH IQHStage + 1,009 R_NeverQH), post-wire target `D_census` = 5,156._

Wave 4 is the marginal-residue harvest that wave-3's §6 step-4 left open.
Everything here is **STAGED, not wired** — the census re-cert was running on
the box, so **no census `.v` input was touched** and `tools/census_cache.py
--check` still reports the frozen-input mismatch (EXPECTED; do not "fix" it).
All boards use LANDED checkers — **no new trust surface, no new corruption
tests**.  Every staged file compiles under `coqc -Q theories BBB4` and
`Print Assumptions` = `functional_extensionality_dep` only.

## Task A — list-B QHBound recovery at n=5/6 (R_QH)

The 1,475 list-B machines in `tools/provenqh_uncaught.txt` resisted the census
QHBound gates at n≤4, t≤1024.  Re-running the **`gen_provenqh.py`
growing-closure machinery** (`find_plain` / `find_lex_rich` →
`ngram_check_qhbound(_lex)_sound`, `theories/Checkers/Wrap.v`) at the higher
closure orders **n ∈ {5,6}, KEEPING t ≤ 1024** (B_census = 2000 caps the
`S t → 2000` lift; t=4096 is unsound) recovers **20 machines** (13 plain gate
+ 7 lex gate; 18 at n=5, 2 at n=6; all t=64; max closure only 84 contexts).

- Emitter `tools/gen_provenqh_stage.py` (UNTRUSTED; n=5/6 search + RRStage-shaped
  emit).
- File `theories/Machines/ProvenQHStage/PQHS_00.v` — self-contained,
  RRStage-shaped: `Definition pqhs (tm) := NonHalt tm /\ QHBound 2000 tm /\
  QuasiHaltsSt tm`, per machine a `Lemma cpq_NNNNN : pqhs tm_pq_NNNNN` (the
  sound lemma proves the middle conjunct unfolded at `S t`, then `qhbound_mono`
  lifts it to `QHBound 2000` since t<2000), plus one nested `Forall_cons` term
  `pqhstage_00_all : Forall pqhs pqhstage_00`.
- Manifest `tools/provenqh_stage_manifest.tsv` (20 rows);
  `tools/provenqh_stage_uncaught.txt` (1,457 still-uncaught — the deep core).

All 20 verified in listB residue (`wrap_qh − qhb − qlx`), disjoint from the
boarded provenQH map and the wave-2/3 drops.  **Board R_QH**: append
`pqhstage_00` to `reroot_qh_list` (Census/RerootQH_Data.v), exactly as the
IQHStage / RRStage wave-3 R_QH boards.

## Task B — remaining list-C harvest (fuel/drift → R_NeverQH; high-n quiet → R_QH)

**Pool: the 3,557 still-unboarded list-C residue** = listC target 6,247
(ground truth `core − rw` = `wrap_residue_survivors − repwl_residue_caught`)
minus the wave-2/3 boards that landed in it: `irulesqh_manifest` (1,090) +
`irulesnqh_manifest` (810) + `listc_stage_manifest` (591 wave-2 + 199 step-4 =
790).  All three are subsets of listC, pairwise disjoint; 6,247 − 2,690 =
3,557.  (Derivation: `tools/` sweep TSVs; no census input read.)

The BBB sweep (`bin/quietngram`, ≤2 nice(15) workers, `--max-n 8 --t 5e6`,
certs under `BBB/results/certs_wave4/`) over that pool, boarded through LANDED
checkers:

### B1 — fuel (R_NeverQH)  — `--neverqh --rank --fuel`

`bin/quietngram --neverqh --rank --fuel` → certs `BBB/results/certs_wave4/fuel/`.
Adapter `tools/gen_listc_stage3.py --mode fuel` re-derives the Coq fuel-checker
params (`gen_fuel_certs.fw_decide`) and emits self-contained LCStage-shaped
files `theories/Machines/ListCStage3/LCS3_fuel_NN.v` — per machine a TM + a
class-refined fuel certificate + `NeverQuasiHaltsSt` via
`ngram_check_neverqh_fuelw_sound` (`Checkers/FuelWide.v`), plus
`lcstage3_fuel_NN : list TM` + `Forall NeverQuasiHaltsSt`.

- **Yield: _pending_ — fuel sweep in progress (`LCS3_fuel_00..NN`).**

### B2 — drift (R_NeverQH)  — `--neverqh --rank --drift`

`bin/quietngram --neverqh --rank --drift` over the pool minus the fuel catches
(so fuel/drift boards stay disjoint) → certs `BBB/results/certs_wave4/drift/`.
Adapter `tools/gen_listc_stage3.py --mode drift` re-derives via
`drift_prover.dw_decide` and emits `theories/Machines/ListCStage3/LCS3_drift_NN.v`
— `NeverQuasiHaltsSt` via `ngram_check_neverqh_driftw_sound` (`Checkers/Drift.v`).

- **Yield: _pending_ — drift sweep queued (`LCS3_drift_00..NN`).**

### B3 — high-n ngram-quiet (R_QH)  — state-QH mis-binned into list-C

A quiet (non-`--neverqh`) pass looks for list-C machines with a QUIET state
whose QHBound closure closes at n=5..8 — the census R_QH route through the
existing `Wrap.v` QHBound gate (same shape as Task A `pqhs`).  Implemented by
running the `gen_provenqh_stage.py` growing-closure QHBound search extended to
n ∈ {5,6,7,8} (t ≤ 1024) over the remaining pool; catches emit as
`theories/Machines/ProvenQHStage/PQHS_LC_NN.v` (RRStage-shaped, predicate
`pqhs`), manifest `tools/listc_qh_manifest.tsv`.  **Board R_QH** like Task A.

- **Yield: _pending_ — quiet pass queued (`PQHS_LC_00..NN`).**

Sweep totals and the still-uncaught list-C remainder recorded in
`tools/listc_stage3_manifest.tsv`, `tools/listc_qh_manifest.tsv`, and
`tools/listc_wave4_uncaught.txt`.

## Compile / axiom discipline

- Task A `PQHS_00.v`: ~7 s, `Print Assumptions pqhstage_00_all` clean.
- Task B fuel/drift LCS3 files: ~1 s/machine (shallow certs), 50/file.
  `Print Assumptions lcs3_*_NN_nqh` / `pqhs_lc_NN_all` clean.
- Everything validated standalone (`coqc -Q theories BBB4 <file>`); the staged
  files are NOT in `_CoqProject` (wire step adds the block — same convention as
  RRStage/LCStage/IQHStage/LCS2).

## Wire + regen (box follow-up)

Wave 4 lands the zero-walk-cost conveyor-belt way (per-machine theorem → drop
at regen).  On the box, AFTER the wave-3 wire (`tools/wire_wave3.py --box`,
which creates `reroot_boarded.txt` / `proven_listc_dropped.txt` /
`iqh_boarded.txt`):

1. **R_QH tier** (`Census/RerootQH_Data.v`): append `pqhstage_00` (Task A) and
   the `pqhs_lc_*` lists (Task B3) to `reroot_qh_list`, extend the `Forall_app`
   chain (`pqhs` is definitionally the tier predicate).
2. **proven R_NeverQH tier** (`Census/Proven_Data.v`): append the
   `lcstage3_fuel_*` / `lcstage3_drift_*` lists (Task B1/B2) to `proven_list`,
   extend the chain.
3. `_CoqProject`: add the staged block (`theories/Machines/ProvenQHStage/*`,
   `theories/Machines/ListCStage3/*`) — still outside the census target
   closure, so `CENSUS_VO_HASH` changes only via `Deferred_*`.
4. **`tools/regen_residue.py --wave4`** — the new drop-list branch (subsumes
   `--wave3`; drops `provenqh_stage_manifest` + `listc_stage3_manifest` +
   `listc_qh_manifest`, all residue-side, all subset/disjoint/no-double-drop
   asserted).  Regenerates `Deferred_*`.
5. `make census-verify` on stable hardware; `Print Assumptions census_decided`
   must stay `functional_extensionality_dep` only; `census_cache.py --update`;
   commit census `.vo` + hash.

**Cross-file theorem-name note (wire-time):** the fuel/drift emitters name
theorems `nqh_<sanitized-machine>`; wave-4 machines are provably disjoint from
every previously-boarded proven/LCStage/LCS2 machine (pool = residue minus all
prior boards), so the concatenated `proven_list` has no name clash.  Task A/B3
`cpq_*` names are per-chunk unique.

Expected `D_census` after the combined wave-4 wire+regen:
`5,156 − 20 (PQHS) − |LCS3 fuel+drift| − |PQHS_LC| ` (Task B counts finalized once the sweeps land; projection ≈ 4,850 ± 100).

## Reproduce (UNTRUSTED)

```
# pool
python3 -c "…"   # listC (core−rw) minus iqh/inqh/listc-stage manifests -> listc_pool.txt

# Task A
python3 tools/gen_provenqh_stage.py tools/provenqh_uncaught.txt 100

# Task B1/B2 (2 nice workers, split the pool)
bin/quietngram --neverqh --rank --fuel  --max-n 8 --t 5000000 --cert-dir BBB/results/certs_wave4/fuel  <pool>
bin/quietngram --neverqh --rank --drift --max-n 8 --t 5000000 --cert-dir BBB/results/certs_wave4/drift <pool_minus_fuel>
python3 tools/gen_listc_stage3.py --mode fuel  --cert-dir BBB/results/certs_wave4/fuel
python3 tools/gen_listc_stage3.py --mode drift --cert-dir BBB/results/certs_wave4/drift

# Task B3
python3 tools/gen_provenqh_stage.py <pool_minus_fuel_drift> 100   # n=5..8 variant

# validate every staged file
coqc -Q theories BBB4 theories/Machines/ProvenQHStage/*.v theories/Machines/ListCStage3/*.v
```
