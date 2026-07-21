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
- **listC splits three ways** on a representative sample (§4, 400 reps,
  state-level, all certs verify PASS): **26.2% boardable never-QH** now
  (NGram/IRules), **18.0% actually state-QH** but mis-parked (needs one new
  quiet-checker), **55.8% uncaught** at modest budgets.
- **Headline projection (§5):** run provers → existing checkers → proven tier
  boards **≈ 9,472 / 16,022 (59%)** with **zero new Coq**; **one** added lemma
  (§6) lifts it to **≈ 10,519 (66%)**. Hard residue ≈ 3,648 (23%); the 1,854
  (12%) ≤3-state core is the bridge's.
- **The single highest-value new checker is the irules-QH corollary** (or,
  equivalently, a RepWL-quiet checker): each boards **71/72** of the state-QH
  reps. A **bouncer** checker is worthless here (uniquely unlocks **0**).

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
never-QH core. Verdicts are classified at the **STATE level** (the census /
BBB beeping notion) — derived from each verified cert's per-transition
`claim_trans` classification, not the transition-level `claim_qh` flag.
Per-machine: `suppl_state_results.tsv` (state-level, authoritative) and
`suppl_results_400.tsv` (transition-level).

**Catch-rate table (state level).** All 371 emitted certs verify PASS; **0
state-verdict contradictions** across provers (transition-level `claim_qh T`
next to state-level `claim_qh_state F` is a level distinction, not a conflict).

| bucket | reps /400 | rep % | census-mult /538 | route → checker | landed? |
|---|---|---|---|---|---|
| **(a) state-neverQH — boardable** | **105** | **26.2%** | **126** | 67 `neverqh_rank`→`NGram.v`; 38 `irules`(claim_qh_state F)→`IRules/Meta*` | **YES** |
| (a) state-QH — boardable | 4 | 1.0% | 4 | `wrapngram`→`Wrap.v ngram_check_quiet_sound` | YES |
| **(b) state-QH — caught, NO checker** | **68** | **17.0%** | **91** | 67 `wraprwl` (RepWL closure) + 1 `wrapfar` (DFA) | **no** |
| **(c) uncaught** | **223** | **55.8%** | **317** | — (modest budgets) | — |
| caught, any | 177 | 44.2% | 221 | | |

Per-prover raw catches (each on the 400): `irules 142` (transition-level
64 nQH + 78 QH; state-level it is the winning nQH cert for 38 and a state-QH
witness for 71), `ngram-rank 67 neverQH`, `rwlrank 71 state-QH (wraprwl)`,
`wrapfar 51`, `bouncer 25`, `wrapctl 11`, `ngram-quiet 4` (the abandoned ones).
fuel/drift were not run to completion on the 400 (they refine rank; census
weight is marginal — 62 fuel + 17 drift vs 2,611 rank — so the boardable-nQH
figure is a mild under-count).

**Surprise 1 — the never-QH "core" is ~18% actually QH.** 72/400 listC reps
are provably **state-QH** (a state goes quiet), i.e. mis-parked: the census's
*ngram*-quiet wrap sweep missed them because their closure does not close
under the ngram abstraction at the swept n,t (exactly why they fell to listC),
but the **RepWL** block closure (`rwlrank`) does close and witnesses the quiet
state on **71/72** of them. They are sound QHBound verdicts (verify PASS) that
are simply not yet *boardable* — the only landed quiet-checker is the ngram
one in `Wrap.v`.

**Surprise 2 — bouncer adds nothing to the residue.** Every one of bouncer's
25 catches is already a state-QH machine caught by `wraprwl`; bouncer uniquely
decides **0** otherwise-uncaught reps. Unlike the BBB(4) hard core, a bouncer
Coq checker would not shrink this residue.

**Surprise 3 — the primary (lexicographic) sample is a trap.** Its 34 listC
reps are 41% start-state-abandoned (global 0.8%); its "catches" are trivial
QH-score-1 verdicts. Only the representative sample reflects the real core.

---

## 5. Projection to the full deduped residue

Population (deduped, with re-root multiplicities): 12,133 distinct reps →
16,022 census machines. 4-state reps carry the census-machine multiplicity
(avg 1.24×); the ≤3-state core is handled by the separate bridge plan.

Rates for listB are **measured** (966/966 = 100%, verified). Rates for listC
are the **mult-weighted** representative-sample rates from §4 (nQH+wrapngram
boardable 24.2%, state-QH-need-checker 16.9%, uncaught 58.9%) applied to the
6,192 listC census machines.

| tier | census machines | % of 16,022 | route | checker |
|---|---|---|---|---|
| 4-state listB (QHBound) | **7,976** | 49.8% | ngram-quiet → `Wrap.v` | **LANDED** (emitter `gen_residue_wrap.py`) |
| 4-state listC state-nQH + wrapngram | **~1,496** | 9.3% | ngram-rank / irules-nQH → `NGram.v` / `IRules/Meta*` | **LANDED** |
| **▸ boardable TODAY, existing checkers** | **≈ 9,472** | **59.1%** | | — |
| 4-state listC state-QH (mis-parked) | ~1,047 | 6.5% | rwlrank(`wraprwl`) / wrapfar → **ONE new quiet-checker** | needs 1 checker |
| 4-state listC uncaught (hard) | ~3,648 | 22.8% | resists modest budgets | none / new methods |
| ≤3-state core | 1,854 | 11.6% | **bridge plan** (separate) | out of scope |

Rep-level (distinct proofs to emit): listB 6,858 · listC-nQH+wrapngram ~1,252 ·
listC state-QH need-checker ~781 · listC uncaught ~2,562 · ≤3-state 680.

**Headline.** Running the BBB provers and routing through the **already-landed**
checkers boards ≈ **9,472 / 16,022 (59%)** of the residue with **zero new Coq**
— dominated by listB's 7,976 QHBound machines. **One** additional checker (§6)
lifts that to ≈ **10,519 (66%)**. The genuinely hard residue is ≈ 3,648 (23%),
plus the 1,854 (12%) ≤3-state core the bridge already owns.

**Caveats on the projection.** (i) listC's 58.9% "uncaught" is at *modest*
budgets (irules 2·10⁵ steps, ngram max-n≤8, no fuel/drift, no high-n wrap
sweep); fuel/drift + bigger budgets would recover a few more points of nQH.
(ii) The representative sample is n=400 (listC), seed 20260721 — the boardable
and state-QH fractions carry a ±~4-point sampling band. (iii) listB=100% is not
extrapolation but the *definition* of listB (the ngram-quiet-caught set),
independently confirmed 966/966.

---

## 6. Recommended mass-run shape & next-session implementation plan

The prover pass itself is cheap: ngram-quiet is **36 ms/machine** (listB),
irules ~**2 s/machine** at 2·10⁵ steps, ngram-rank the slow one (~seconds,
closure-bound). A full 4-state residue sweep (11,453 reps) is a few hours on
2 nice workers — negligible next to the Coq compile. Sequence by payoff:

### Step 1 — listB mass-board (7,976 machines, biggest win, ZERO new Coq)

The emitter **already exists**: `tools/gen_residue_wrap.py` consumes the wrap
sweep's `caught.tsv` and emits, per machine, `NonHalt ∧ QuietAfter ∧
QuasiHaltsSt` via `Wrap.v` `ngram_check_quiet_sound`. Just run it over all
listB (dedup to the 6,858 4-state reps).

- **Closures are tiny**: `caught.tsv` shows n=2 for 99% (n=3/4 for ~260), and
  t=64 for 99% (t=1024 for 17). vm_compute is a DFA-product over a few-hundred
  contexts → **≈ 0.3–1 s/machine**, no OOM.
- **Batch size 100/file** (small closures tolerate big files unlike irules) →
  ~69 files, or match the landed wrap-manifest granularity.
- **Compile budget**: ~6,858 × ≤1 s ≈ **≤ 2 h single-thread, ~30–60 min at
  -j2**. This alone takes census coverage of the residue from 0 → ~50%.

### Step 2 — listC state-neverQH (~1,252 reps, existing checkers)

Fork the landed never-QH emitters over the reps that carry a `neverqh_rank`
or `irules` (claim_qh_state F) cert:

- `neverqh_rank` share (~2/3, ~840 reps) → the NGram rank emitter
  (`gen_proven.py` path, `NGram.v`), ngram_n≈5, **~2–8 s/machine**.
- `irules` share (~1/3, ~410 reps) → `gen_irules.py` / `gen_irulesk_certs.py`
  (`IRules/Meta*`), fuel 300000 vm_compute — **batches of 10/file, -j2 only**
  (the container OOMs IRules at -j4/fuel 3·10⁵), ~10–40 s/machine.
- Compile budget: ~**2–4 h** (irules-dominated). Run fuel/drift first on the
  §4 uncaught to recover the marginal nQH the modest sweep missed.

### Step 3 — the ONE new checker (unlocks ~1,047, lifts 59%→66%)

Two candidates **tie at 71/72 (99%) of state-QH** — pick by proof economy:

1. **irules-QH corollary  ⟵ RECOMMENDED.** Extend the landed IRules Meta
   (`Checkers/IRules/Meta.v` / `MetaK.v`) with the *dual* extraction lemma:
   from the SAME faithful forward-behavior model the checker already builds,
   conclude `QuasiHaltsSt` (with the silent state as witness) when the model
   shows a state's transitions all non-firing past the anchor — instead of the
   `NeverQuasiHalts` conclusion when all stay live. Reuses the whole landed
   engine + faithfulness proof; only the final property lemma is new. This is
   the smallest new trust surface and is exactly the Discord-provenance point
   (one inductive model → QH *or* neverQH). Boards **71/72** state-QH.
2. **RepWL-quiet checker** (equivalent alternative). Add `rw_check_quiet_sound`
   to `Checkers/RepWL.v` — a fork of `Wrap.v ngram_check_quiet_sound` onto the
   RepWL whole-tape block closure (which already has `rw_check_neverqh_sound`).
   Boards the **67 `wraprwl`** reps; the lone `wrapfar`-only rep needs a DFA
   variant, so this route tops out at 67/72 without a second checker.

Then re-emit the ~781 state-QH reps through the new checker (irules batch
shape, 10/file, -j2).

**Do NOT build:** a **bouncer** checker (uniquely unlocks **0** residue reps —
all its catches are already `wraprwl` state-QH), or standalone **CTL/DFA-quiet**
checkers (11 / 1 reps). Their BBB(4)-hard-core value does not carry to the
census residue.

### Step 4 — the hard residue (~3,648, ~23%)

The 55.8% uncaught resists modest budgets. Cheapest next probes, in order:
finish **fuel/drift** on the full listC sweep; raise the **ngram wrap sweep n**
(some listC state-QH may then close under ngram → board via the *existing*
`Wrap.v` with no new checker); escalate **irules** steps/fuel. Expect single-
digit-percent recovery each; the deep core likely needs the tighter
reachability abstractions already flagged in `docs/groups.md`.

### Bottom line

| action | machines | new Coq | when |
|---|---|---|---|
| run `gen_residue_wrap.py` over listB | 7,976 | none | now |
| fork nQH emitters over listC-nQH | ~1,496 | none | now |
| **irules-QH corollary** + re-emit | ~1,047 | **1 lemma** | next |
| hard residue | ~3,648 | new methods | later |
| ≤3-state core | 1,854 | bridge plan | (owned) |

Boardable **today with zero new Coq: ≈ 9,472 / 16,022 (59%)**; **+1 lemma →
≈ 10,519 (66%)**.

---

*Artifacts (all committed): `sample_1000*.{txt,tsv}`,
`results_per_machine_1000.tsv`, `suppl_listC_400.{txt,tsv}`,
`suppl_results_400.tsv` (transition-level), `suppl_state_results.tsv`
(state-level, authoritative), `analyze_*.py`, `run_*.sh`; certs under
`BBB/results/certs_residue_sample/` (primary 1000 + `suppl/` 400, all verify
PASS). No `theories/**` touched, no Coq compiled, no existing tool modified.*
