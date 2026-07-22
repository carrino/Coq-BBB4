# Wave-2 residue staging — ready-to-board manifest + wire/regen steps

_Written 2026-07-22 (branch `claude/coq-bbb4-residue-wave-2-5vnmxc`), on top
of the merged PR #18 (`D_census = 9,364`)._

This session proved **more residue machines** as SELF-CONTAINED
`theories/Machines/**` files that are **NOT wired into any census input
yet** (the census re-cert was running on the stable box at
`D_census = 9,364`, so no census `.v` input was touched and
`tools/regen_residue.py` was NOT run).  Everything here is a **batched
FOLLOW-UP**: wire the staged lists into the tier assemblies, regen
`Deferred_*`, and re-cert on the box.

Both tracks land the **same conveyor-belt way** as wave 1: a per-machine
in-Coq theorem → the machine leaves `D_census` at **zero walk cost** via a
direct `PositiveMap` lookup in the tier's map (`Run.v`).  No in-walk tier
was strengthened (Rule 4 respected).

Trust: every `.v` here compiles under `coqc -Q theories BBB4 <file>` and its
`Print Assumptions` is **`functional_extensionality_dep` only**.  Everything
under `tools/` is UNTRUSTED — the Coq kernel re-checks every proof; the
emitters only choose which sound lemma to apply.

---

## Track 1 — re-root untapped `≤3`-state list-B cores  →  R_QH tier

**What & why.**  Wave 1 boarded only **184 / 1,742** of the `≤3`-state
list-B re-root machines, because it discharged the re-root core's
`NeverQuasiHaltsSt` obligation (the second premise of
`Census/Reroot.v:qh_reroot`) with a **single** recipe, `rw_tier` at the
census rungs.  The `≤3`-state cores are tiny growing bouncers/counters that
`rw_tier`'s block closure mostly cannot close, but the **NGram + Bellman
ranking** tier (`RankSearch.rank_tier`) decides at `n=3`.

`tools/gen_reroot.py` gained a **`--staged`** mode that adds base-checker
recipes for that one premise — all already-proven sound, so **no new trust
surface**:

| recipe name | lemma | boards |
|---|---|---|
| `rk_3_20000_64`  | `RankSearch.rank_tier_sound`        | 1,437 |
| `rw_2_2_8192`    | `RepWLSearch.rw_tier_sound` (wave-1)| 77 |
| `rk_4_20000_128` | `RankSearch.rank_tier_sound`        | 4 |

The recipe per core was chosen by a Coq **`Eval vm_compute` oracle** (the
exact boolean each `*_sound` lemma consumes — no untrusted re-implementation
of a checker).

**Yield: 1,518 machines board R_QH** (`rrqh tm = NonHalt /\ QHBound 2000 /\
QuasiHaltsSt`), disjoint from wave 1's 184, all inside `census_residue.txt`.

**Files (staged, unwired):**
- `theories/Machines/RerootStage/RRStage_00..15.v` — 1,518 per-machine
  `cqh_s_XXXXX : rrqh tm_s_XXXXX`, plus per file `rrstage_NN : list TM` and
  `rrstage_NN_all : Forall rrqh rrstage_NN`.
- `theories/Tests/RerootStage_Corruption.v` — negative controls: the added
  recipes reject a halter and a genuine quasihalter; `rw_tier` genuinely
  misses a rank-caught core (the extension is load-bearing).
- `tools/reroot_stage_manifest.tsv` — `machine, theorem, file, recipe, tier`.

**Residual (not boarded, for a later pass):** 80 of the 1,598 untapped —
40 whose core no recipe in the ladder decided, and 40 with **no
`closed_b`-certifiable silent prefix state** (the genuinely-silent dropped
state is not outside the core's `closed_b` closure, so `qh_reroot`'s
`QuasiHaltsSt` witness cannot be built for them).  See
`tools/reroot_stage_uncaught.txt` (regenerate from the scratchpad driver).

### Wire + regen (follow-up, R_QH tier)

1. **Build** the staged modules (add to `_CoqProject`, staged section — see
   bottom — or `coqc` them directly).  They import only
   `RepWL NGram TNF_QH Decide Deferred_Defs RepWLSearch RankSearch Reroot`.
2. **Extend `reroot_qh_list`** in `theories/Census/RerootQH_Data.v`:
   - add `From BBB4.Machines.RerootStage Require Import RRStage_00 .. RRStage_15.`
   - `reroot_qh_list := rerootqh_00 ++ .. ++ rerootqh_04 ++ rrstage_00 ++ .. ++ rrstage_15.`
   - extend `reroot_qh_all`'s `Forall_app` chain with each `rrstage_NN_all`
     (`rrqh` is definitionally the tier predicate `NonHalt /\ QHBound 2000 /\
     QuasiHaltsSt`; convertible, no unfold needed — else `unfold rrqh`).
   - `Run.v` already folds `reroot_qh_list` into `qhmap`
     (`provenqh_list ++ reroot_qh_list`); nothing else changes there.
   - (Alternatively regenerate `RerootQH_*` in one shot from a combined
     caught-TSV of the 184 wave-1 + 1,518 wave-2 rows via the non-staged
     `gen_reroot.py` path.)
3. **Append** the 1,518 machine strings (column 1 of the manifest) to
   `tools/reroot_boarded.txt` (184 → 1,702).  They are all in the residue
   and disjoint from proven/provenQH/STAY, so the
   `regen_residue.py --reroot` asserts hold.
4. **Regen** on stable hardware:
   `python3 tools/regen_residue.py tools/census_holdouts_kept.txt theories/Census --reroot`
   — drops proven + provenQH + the 1,702 reroot machines from `D_census`.
5. **Re-cert**: `make census-verify` on the box; confirm
   `Print Assumptions census_decided` = `functional_extensionality_dep` only;
   `tools/census_cache.py --update`; commit the census `.vo` + `CENSUS_VO_HASH`.

Expected `D_census` shrink from track 1 alone: **9,364 − 1,518 = 7,846**.

---

## Track 2 — list-C never-QH  →  proven (R_NeverQH) tier

**What & why.**  SWEEP §4–6: ~26% of the list-C never-QH residue boards
today via the already-landed NGram-rank / IRules never-QH checkers.  This
track runs the untrusted **NGram closure + Bellman ranking** prover
(`tools/bulk_prover.py:decide`, the `gen_bulk_certs.py` engine) over the
**6,247 list-C residue machines** directly (each is a valid TM; the checker
simulates from blank), and emits a `NeverQuasiHaltsSt` theorem per decided
machine, closed by `vm_compute` through
`NGram.ngram_check_neverqh_lex_sound`.

`tools/gen_listc_stage.py` (new) is the staged emitter — a fork of
`gen_bulk_certs.py` pointed at the list-C residue, adding the per-file
`Forall` assembly so the follow-up can append it to `proven_list` verbatim.

**Yield: 591 machines board R_NeverQH.**  The untrusted prover decided
599 / 6,247 list-C machines (9.6%, a shuffled full sweep); **8 were then
rejected by the Coq `ngram_check_neverqh_lex` re-check** (a Python-oracle /
kernel discrepancy — dropped, never trusted), leaving **591 Coq-verified**
(n=2: 316, n=3: 54, n=4: 221).  This is the NGram-rank share only; the
IRules-only list-C machines (~1/3 of the boardable per SWEEP §4) are a
further follow-up — they need the heavy `IRules/Meta*` fuel-3e5 batches,
out of scope for a container session.  Corruption coverage: this track
reuses the landed `NGram.ngram_check_neverqh_lex_sound` path verbatim
(`gen_bulk_certs.py` engine), already guarded by
`theories/Tests/Bulk_Corruption.v`; no new checker feature is introduced.

**Files (staged, unwired):**
- `theories/Machines/ListCStage/LCStage_00..11.v` — 591 per-machine
  `nqh_<machine> : NeverQuasiHaltsSt tm_lc_XXXXX`, plus per file
  `lcstage_NN : list TM` and `lcstage_NN_nqh : Forall NeverQuasiHaltsSt`.
- `tools/listc_stage_manifest.tsv` — `machine, theorem, file, tier, n, t,
  contexts`.
- `tools/listc_caught.tsv` — the Coq-verified boardable set (`machine, n`).

### Wire + regen (follow-up, R_NeverQH tier)

1. **Build** the staged modules (they import only
   `BBB4_Statement CTape NGram`).
2. **Extend `proven_list`** in `theories/Census/Proven_Data.v`: add
   `From BBB4.Machines.ListCStage Require Import LCStage_00 ..`, append the
   `lcstage_NN` lists to `proven_list`, and extend `proven_all`'s
   `Forall_app` chain with each `lcstage_NN_nqh`.  `Run.v` already builds
   `pmap := dmap_of proven_list`; nothing else changes there.
3. **Drop from the residue.**  The list-C machines are *residue* (not the
   3,670 *holdouts* that `proven_dropped.txt` carries).  Add a residue drop
   list analogous to the re-root one: write the boarded list-C machine
   strings to e.g. `tools/proven_listc_dropped.txt`, then extend
   `regen_residue.py`'s `--reroot` branch (or add a `--listc` branch) to
   subtract it from `residue` with the same shape of asserts the re-root
   drop uses (`⊆ residue`; pairwise-disjoint from proven / provenQH / reroot;
   no double-drop; `newset == old − …`).
4. **Regen + re-cert** exactly as track 1 step 4–5.

Expected `D_census` shrink from track 2: **− 591** (the boarded count).

**Combined both tracks:** `9,364 − 1,518 − 591 = 7,255` after the follow-up
wires + regens + re-certs on the box (assuming the two staged sets are
disjoint — they are: track 1 is list-B, track 2 is list-C).

---

## `_CoqProject` staging note

The staged files are intentionally **absent from `_CoqProject`** so the base
`make` and the census cache are untouched this session.  To include them in
CI/`make` (recommended once wiring begins), append a clearly-marked block —
they do **not** enter the census-target transitive closure, so
`CENSUS_VO_HASH` is unaffected:

```
# --- STAGED wave-2 residue proofs (NOT wired into census inputs) ---
theories/Machines/RerootStage/RRStage_00.v
...
theories/Machines/RerootStage/RRStage_15.v
theories/Machines/ListCStage/LCStage_00.v
...
theories/Tests/RerootStage_Corruption.v
```

## Reproduce (scratchpad drivers, UNTRUSTED)

- Track 1 recon+recipe: `reroot_recon.py` (per-machine q*/t*/core/closure/qz
  from `reroot_mapping_16022.tsv`; validated byte-exact vs the 184 wave-1
  boards), `oracle3.py`/`assign.py` (Coq `Eval` recipe oracle),
  `make_reroot_tsv.py` → `gen_reroot.py --staged`.
- Track 2 sweep: `listC_sweep.py` (`bulk_prover.decide` over list-C) →
  `gen_listc_stage.py`.
