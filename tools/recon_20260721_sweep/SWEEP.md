# RESIDUE CERT-SWEEP (2026-07-21)

How much of the 16,022-machine census residue falls to the BBB harness's
own cert-generating provers, and how much of that is boardable through the
**already-landed** verified Coq checkers.

All numbers here are **untrusted measurement**. No `theories/**` touched, no
Coq compiled, no existing tool modified. New files live only in this recon
dir (`tools/recon_20260721_sweep/`) and in `BBB/results/certs_residue_sample/`.

Provenance motivation (today's Discord find): the residue is by construction
the class whose *forward behavior an inductive decider can model exactly*
— exactly what the BBB cert families cover — so the catch rate should be high.
This sweep turns that into numbers.

---

## 0. TL;DR

| tier | reps | census machines | route | landed checker? |
|---|---|---|---|---|
| ≤3-state core | 680 | 1,854 | bridge plan (out of scope) | n/a |
| **4-state listB (QH)** | **6,858** | **7,976** | ngram-quiet → `Wrap.v` QHBound | **YES — 100%** |
| 4-state listC (neverQH-core) | 4,595 | 6,192 | never-QH cascade + irules | partial (see §4) |
| **total** | **12,133** | **16,022** | | |

- **listB is a solved mass-board today**: the ngram-quiet decider catches
  **966/966** sample listB reps, every cert verifies PASS, and the emitter
  (`tools/gen_residue_wrap.py`) + checker (`theories/Checkers/Wrap.v`,
  `ngram_check_quiet_sound`) are already landed. That is 6,858 reps / **7,976
  census machines** boardable with zero new Coq.
- **listC splits three ways** on a representative sample (§4): a solid
  boardable-neverQH fraction (NGram/Fuel/Drift/RepWL/IRules checkers), a
  comparable QH-decidable-but-not-yet-boardable fraction (irules-QH,
  wraprwl/wrapfar/wrapctl, bouncer — need a quiet-checker over the tighter
  closures, or an irules-QH corollary), and a hard uncaught remainder.

---

## 1. Data & reproducible sample

Inputs: `tools/census_residue.txt` (16,022), the re-root/dedup mapping
`tools/recon_20260719/reroot_mapping_16022.tsv` (columns
`census_machine, upstream_tnf, upstream_status, cert_family, list, mode,
nstates_after, dropped`), and the QH split carried in the mapping's **`list`
column** (`B`=wrap-QH 9,775, `C`=never-QH core 6,247 — matches
`wrap_residue_caught.tsv` / `wrap_residue_survivors.txt`).

**Deduped structure (distinct re-root reps = `upstream_tnf`):**

| | distinct reps | census machines (mult) |
|---|---|---|
| ≤3-state core (skip: bridge plan) | 680 (676 s3 + 4 s2) | 1,854 |
| 4-state, listB (QH) | 6,858 | 7,976 |
| 4-state, listC (neverQH-core) | 4,595 | 6,192 |
| **4-state total** | **11,453** | **14,168** |

**Primary sample (deliverable, reproducible):** the first **1,000** of
`sort` (lexicographic) over the 11,453 distinct **4-state** reps.
`sample_1000_reps.tsv` / `sample_1000.txt` (+ `_listB_qh` / `_listC_neverqh`
splits). Skipped the ≤3-state rows (680 reps / 1,854 machines) per the
bridge plan.

> **Sampling caveat (important).** Lexicographic-first draws an all-`1RB---`
> prefix block, which is wrap-QH-dense and start-state-abandonment-rich: the
> primary sample is **966 listB / 34 listC**, versus the global 4-state rep
> ratio of 6,858 / 4,595 (≈60/40). It is faithful and reproducible but **not
> representative** of listC. §4 therefore adds a **uniform-random 400-rep
> listC sample** (seed 20260721, `suppl_listC_400.txt`) for the projection.

---

## 2. Build & method

`cd /home/user/BBB && make` → 13 C binaries (`bin/{harness,verify,quietngram,
quietrwl,quietfar,quietctl,quietseg,bouncer,irules,wrap,…}`), all `-O3`.
CPU discipline held: ≤2 nice(15) worker processes at any time; no Coq run.

Cascade entry points (batch, one machines.txt per binary):

| prover | invocation | cert `type` | proves |
|---|---|---|---|
| harness | `bin/harness --max-steps 1e8` | halt/tcycler/inplace | halt or cycle |
| ngram-quiet | `bin/quietngram --max-n 8 --t 5e6` | `wrapngram` | **QH** (state quiet) |
| ngram-rank | `bin/quietngram --neverqh --rank` | `neverqh` | neverQH |
| ngram-fuel/drift | `… --fuel` / `--drift` | `neverqh_fuel/_drift` | neverQH |
| rwlrank | `bin/quietrwl --rank` | `wraprwl` | **QH** (RepWL closure) |
| irules | `bin/irules --max-steps 2e5` | `irules` | **QH or neverQH** (`claim_qh T/F`) |
| bouncer | `bin/bouncer` | `bouncer` | **QH** |
| quietfar / quietctl | `bin/quietfar` / `bin/quietctl` | `wrapfar`/`wrapctl` | **QH** (DFA/CTL closure) |

**Landed-checker map** (from `NEXT_SESSION.md` + `theories/Checkers/`):

- neverQH boardable: `neverqh`→`NGram.v`, `neverqh_fuel`→`Fuel.v`,
  `neverqh_drift`→`Drift.v`, `neverqh_rwl`→`RepWL.v`
  (`rw_check_neverqh_sound`), `irules*` with `claim_qh F`→`IRules/Meta*.v`
  (`*_check_neverqh_sound`; all irules Coq checkers are **neverQH-only**;
  NOT v4 mmrow).
- **QH boardable: `wrapngram` only** → `Wrap.v` `ngram_check_quiet_sound`
  (proves `NonHalt ∧ QuietAfter ∧ QuasiHaltsSt`; the census's own
  `gen_residue_wrap.py` route).
- **NO landed checker:** `wraprwl`, `wrapfar`, `wrapctl` (quiet over the
  RepWL/DFA/CTL closures — `Wrap.v` only has the ngram closure), `bouncer`,
  and any **irules `claim_qh T`** (the irules checker cannot board a QH claim).

---

## 3. Primary sample results (1,000 reps)

**listB (966 reps, QH): 966/966 caught by ngram-quiet, 100% boardable.**
Exactly the 966 listB reps get a `wrapngram` QH cert (`claim_qh T`, QHBound);
the 34 listC reps get none — a clean split confirming **listB ≡ the
ngram-quiet-caught set**. Certs verified: **120/120 sampled PASS** (and
966/966 emitted); all 966 census riders are present in
`wrap_residue_caught.tsv`. Board today via `Wrap.v` — **no new Coq**.

**listC (34 reps):** 15/34 caught, but this slice is dominated by the
lexicographic bias — **14/34 are start-state-abandoned** (state A fires once,
nothing returns to A → trivial QH score 1), against a global listC rate of
**0.8%**. Breakdown: 2/34 boardable-neverQH (`neverqh_fuel/drift` +
`irules claim_qh F`), 13/34 QH-not-boardable (`wraprwl`×10, `wrapfar`×3),
19/34 uncaught (harness, ngram-quiet, fuel, drift, and irules@1e6 all miss).
Because of the bias this row is **not** used for the projection — see §4.

Per-machine: `results_per_machine_1000.tsv`.

---

## 4. Representative listC sample (400 reps, seed 20260721)

Start-state-abandoned here: ~0.8% (representative). This measures the genuine
never-QH core. Per-machine: `suppl_results_400.tsv`.

<!-- REPR_UNION_TABLE -->

Per-prover raw catches (each on the 400):
`irules 142 (64 neverQH + 78 QH)`, `ngram-rank <RANKN> neverQH`,
`rwlrank 71 QH (wraprwl)`, `wrapfar 51 QH`, `bouncer 25 QH`,
`wrapctl 11 QH`, `ngram-quiet 4 QH (the abandoned ones)`. fuel/drift not run
to completion on the 400 (they refine rank; census weight is marginal —
62 fuel + 17 drift vs 2,611 rank).

**Surprise:** a large share of the "never-QH core" (listC) is actually
**QH-decidable** — irules alone proves 78/400 ≈ 20% of listC quasihalting
with an exact bound, and rwlrank/wrapfar/bouncer confirm more. These are
sound (verify PASS) QHBound verdicts that the *ngram*-quiet wrap sweep
missed (their closure does not close under the ngram abstraction at the swept
n,t — which is exactly why they landed in listC). They are decided but **not
yet boardable**: no landed quiet-checker exists for the RepWL/DFA closures,
and the irules Coq checker is neverQH-only.

---

## 5. Projection to the full deduped residue

<!-- PROJECTION_TABLE -->

---

## 6. Recommended mass-run shape & next-session implementation plan

<!-- PLAN -->
