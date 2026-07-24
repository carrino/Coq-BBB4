# Wave-6 — the NGramHist closeout: history-augmented n-gram closure

_Written 2026-07-24 (branch `claude/ngramhist-closeout-wave6-ci4h3w`).  The
"one new trust surface" of this wave is a **history-augmented n-gram
closure** checker — a new instance of the `theories/Closure.v` engine over an
augmented tape alphabet — plus its wrap/QHBound fork, corruption tests, a
pilot, and a harvest of the census residue._

## 0. The gap this wave closes (oracle-backed)

mxdys' Coq-BB5 BB4 pipeline decides **all 858,909** TNF (4,2) machines with a
generic decider stack; the residue that BBB4's checkers could not board maps
**100 % to NGramCPS** — and the resistant tail needs the **history-augmented**
variant `NGRAM_CPS_IMPL1` (mxdys `TM.v` `Σ_history`, `Decider_NGramCPS.v`).
BBB4's `NGram.v` has **no** history augmentation — that is the gap.

The provenance oracle `BB4_verified_enumeration.csv`
(machine→decider+params, downloaded from the CoqBB5 v1.0.0 release; kept out
of git for size, see `tools/nghist/BB4_verified_enumeration.README`) is the
per-machine targeting oracle.  Of the 5,129 census-residue machines, 1,420
match mxdys' table by string (the rest are the same machines under a
different TNF relabeling): ~63 % plain n-gram (`IMPL2`), ~37 % history
(`IMPL1`, dominantly `history=2, gram=2, gas=1600`), all `nonhalt`.

mxdys' augmentation (`TM.v:1234`): `Σ_history := Σ * list (St*Σ)` — each tape
cell carries a **bounded record of the last `k` `(state,read)` updates**;
`TM_history k tm` writes `(o, firstn k ((s,i0)::i1))` and is otherwise `tm`
(the history is pure decoration, projected away by `fst`).  Running plain
NGramCPS over `Σ_history` de-merges n-gram contexts that plain windows
conflate, so the closure finitizes for machines plain n-gram cannot close.

## 1. THE safety ≠ liveness correction (the load-bearing design point)

A finite closed augmented set proves **NonHalt only**.  It does **not** imply
every state recurs: a state visited only in the transient prefix, then never
again, still has its early contexts sitting in the closed set — that machine
is a genuine **quasihalter**, not never-QH.  So never-QH must come from the
**existing liveness gates** (`Closure.live_ok` / `rank_ok` / `lex_ok` /
`runner_ok`) run *over the augmented closure*, never read off closure alone.
The prior-session claim "a finite closed set ⇒ every state recurs" is exactly
the trap; corruption test #1 pins it.

## 2. Pilot (UNTRUSTED python prototype, `tools/nghist/`)

`nghist_pilot.py` implements mxdys' history-augmented NGramCPS closure
(alphabet-generic MidWord/xset over `TM_history k`) plus a BBB4-faithful
never-QH liveness pass (per-state: `rank` acyclicity OR `runner` fuel OR a
`lex` count-of-1s measure with no positive q-avoiding cycle — a proxy for the
`ngcomp` lex certificate the Coq kernel re-checks).  Seeded past the transient
(step `t`), exactly as BBB4's `closure_check_neverqh` seeds from `csteps t c0`.

`pilot_batch.py`, 40-machine representative sample, `history=2, gram=2`,
`t=150`:

| population (oracle) | n | plain closes | **hist closes** | SCC-recurrent | **never-QH boards** |
|---|---|---|---|---|---|
| `IMPL1` counters (history-needed) | 18 | 1 | **18** | 16 | **16 (89 %)** |
| `IMPL2` plain-decidable | 12 | 12 | 12 | 1 | 1 |
| wave-4 uncaught (`provenqh_stage`) | 10 | 10 | 10 | 0 | 0 |

Findings (the two rates the task asks for, measured separately):

- **Closure rate** — history is load-bearing: 17/18 counters *cannot* close
  under plain n-gram (spurious `halt` from over-approximation); **all 18
  close at `history=2`**.  Mechanism confirmed end-to-end.
- **Liveness-discharge rate** — 16/18 counters board never-QH via the
  augmented closure + a `lex-Left` count measure.  The 2 that close+recur but
  the single-measure proxy misses are the "liveness lags closure" case →
  richer lex / higher history (the tail the task says to tune).
- The `IMPL2` / wave-4 population **closes but is quasihalters**: a state
  (e.g. `A`) is visited only at step 0 then goes quiet forever (verified by
  direct simulation).  Correctly *rejected* by the never-QH gate — they route
  to the **QHBound/wrap** variant (R_QH: `NonHalt /\ QHBound 2000 /\
  QuasiHaltsSt`), not never-QH.  This is why both shapes are built.

Conclusion: history augmentation is a **closure** lever (counters) *and* a
liveness-granularity lever (phase-gated measures); the never-QH harvest is the
counter tail, the QHBound harvest is the quasihalter tail.

## 3. The Coq checker — construction (see `theories/Checkers/NGramHist.v`)

The BBB4 tape infrastructure (`BBB4_Statement`, `CTape`, `Closure`) is fixed
to `Sym = {S0,S1}`, so mxdys' "reinstantiate the whole engine over `Σ_history`"
is not available.  Instead the augmentation lives in the **node type** of a
`Closure.v` instance, with `covers` relating an augmented node to the
*original* machine's `ExecState` through an existential over the augmented
configuration:

- `HSym := Sym * Hist`, `Hist := list (St*Sym)` truncated to `k`
  (`hcell`); augmented computable config `hcconf`; augmented step `hcstep`
  writing `(o, firstn k ((s,i0)::i1))`; projection `hproj : hcconf -> cconf`
  (drop histories).  Simulation lemma: `hproj (hcstep hc) = cstep (hproj hc)`
  and halting matches — **this is the new soundness proof for the
  augmented-alphabet abstraction.**
- Node `A` = augmented n-gram context over `HSym` windows; `a_state = St`
  (history is *not* part of the state, so `covers_state`/liveness see the
  original machine's states);
  `covers A c := exists hc, hproj hc = c /\ hng_abstracts A hc` (windows of
  `hc` match `A`, deep `HSym` windows in the gram sets).  `succs_sound` steps
  the witness `hc` under `hcstep` and re-abstracts — an `HSym` fork of
  `NGram.ng_succs_sound_some`.  The gram sets are over `HSym` windows, so the
  far-cell branch is history-constrained — this is the closure refinement.
- The `Closure.v` liveness gates (`live_ok`, `rank_ok`, `lex_ok`, the
  `closure_check_neverqh_lex_sound` theorem) are **reused verbatim**.  Count
  and pattern measures read the *bit* projection, so `comp_exact` reduces to
  `NGram.ngm_exact`/`pm_exact`.
- The QHBound/wrap fork mirrors `Wrap.v` over the augmented `succs`/`covers`:
  wrap state `q` to halt, close the augmented set, `live_ok` bounds every
  quiet state's last visit ⇒ `NonHalt /\ QHBound (S t) /\ QuasiHaltsSt`.

Axiom footprint: `functional_extensionality_dep` only (per file class,
`Print Assumptions`).  Everything in `tools/` is untrusted; the kernel
re-checks every emitted certificate; kernel-refused certs are never boarded.

### Files (all compile, all `functional_extensionality_dep` only)
- `theories/Checkers/NGramHist.v` — the never-QH checker.  Exports:
  `hcstep_proj` (the simulation), `hng_succs_sound_some` (closure
  refinement), `ngramhist_check_neverqh` + `_sound` (rank gate),
  `ngramhist_check_neverqh_lex` + `_sound` (lex gate, phase-dependent count
  measures via the `hcomp` cert type), and `ngramhist_closed` + `_sound`
  (safety-only ⇒ `NonHalt`, for the trap controls).
- `theories/Checkers/NGramHistWrap.v` — `ngramhist_check_qhbound_lex` +
  `_sound` ⇒ `NonHalt /\ QHBound (S t) /\ QuasiHaltsSt` (the R_QH tier),
  a fork of `Wrap.v` over the augmented instance.
- `theories/Tests/NGramHist_Corruption.v` — the four MUST-fail controls,
  all kernel-verified (see §2's safety!=liveness note): `ctl_plain_misses`
  + `ctl_hist_boards` (feature load-bearing), `qh_closes`+`qh_rejected`
  (the trap), `halt_rejected`, `mut_rejected`.
- `tools/nghist/nghist_prove.py` — UNTRUSTED prover: grows the gram sets to
  a fixpoint (mirroring `hng_succs`), computes phase-dependent count-measure
  lex certs (Bellman-Ford potentials), emits staged Coq.  It also enforces
  the never-QH obligation over PREFIX-visited states (a bug the kernel
  caught: without it the prover boarded a quasihalter, which `vm_compute`
  then rejected — the safety!=liveness trap in miniature).

**End-to-end validation:** `coqc … vm_compute` proves `NeverQuasiHaltsSt`
for real residue counters that plain n-gram cannot close (e.g.
`0RB---_0LC0RA_0LD---_1RA1LC`, 33 augmented contexts), `Print Assumptions`
clean.  The kernel re-checks every cert; a mismatch (prover claims, kernel
rejects) is recorded and never boarded.

## 4. Harvest — `theories/Machines/NGHStage/`

Sweep of the unboarded census residue (`tools/census_residue.txt`, 5,129;
minus the staged-not-wired v5/v5b manifests) with
`tools/nghist/harvest_sweep.py` (≤2 nice workers, `history=2` then `4`,
`gram=2`).  Emitter: staged files 100/machines-per-file, per-file
`Forall NeverQuasiHaltsSt`, manifest `tools/nghstage_manifest.tsv`
(`machine,theorem,file,k,n,t,fuel,nctx`).  Every file is
`coqc -Q theories BBB4`-validated (a 100-machine file ≈ 70 s `vm_compute`)
and committed on landing.

Measured never-QH yield ≈ **10 %** of the residue swept (the honest rate
AFTER quasihalters are correctly rejected — the pre-fix 36 % included
mis-boarded quasihalters the kernel would refuse).  The rejected majority is
dominated by genuine quasihalters (a state quiet after the transient), which
route to the QHBound/wrap variant (`NGramHistWrap.v`) as R_QH facts, not
never-QH — exactly the listB/listC mix the design anticipated.  Both shapes
feed the Assembly `Forall`; they live in separate files.  Final counts:
`tools/nghstage_manifest.tsv`.

Oracle provenance (`tools/nghist/residue_provenance.csv`, from
`BB4_verified_enumeration.csv`): of the residue machines that match mxdys'
table by string, the never-QH-boarded ones concentrate in the
`NGRAM_CPS_IMPL1_params_2_2_2_1600` (history-augmented) column — the machines
plain n-gram genuinely could not close.

## 5. Wire / regen — the two routes (wire is OPTIONAL now)

The staged `theories/Machines/NGHStage/*.v` accumulate toward the `Forall`
over the frozen 5,156 `D_census` list = `tools/census_holdouts_kept.txt` (27)
+ `tools/census_residue.txt` (5,129), materialized as `Deferred_*.v`.  A
`theories/Census/Assembly.v` file does not yet exist on any branch; wave-6
produces the per-file `Forall`s that a closeout `Assembly.v` composes.

- **Route A — Assembly `Forall` (no census walk).**  Each NGHStage file
  proves `Forall NeverQuasiHaltsSt ngh_NN` (and the wrap files
  `Forall (fun tm => NonHalt tm /\ QHBound 2000 tm /\ QuasiHaltsSt tm)
  nghw_NN`).  A future `Census/Assembly.v` `app`-chains these per-file
  `Forall`s (+ the wave-2/3/4 stage `Forall`s) into one
  `Forall boarded D_census`, entirely by kernel term composition — **no
  `native_compute` census walk, no stable-hardware step.**  This is the
  route wave-6 uses; it keeps `CENSUS_VO_HASH` MATCH (no census `.v` input
  touched) and the census `.vo` frozen.
- **Route B — legacy wire + regen (stable hardware).**
  `tools/regen_residue.py` drops the boarded machines from the `Deferred_*`
  tables (shrinking `D_census`) and `make census-verify` re-certifies the
  native walk.  This CHANGES a census input (`Deferred_*`) so
  `census_cache.py --check` goes MISMATCH until the box re-walks.  Not
  needed for the Assembly path; documented for parity with waves 2/3.

**Dedup** (so NGHStage never re-boards): the sweep subtracts, from
`census_residue.txt`, the staged-not-wired manifests
(`listc_v5_manifest.tsv`, `listc_v5b_manifest.tsv`; and, against the wave-4
branch, `listc_stage3_manifest.tsv` + `provenqh_stage_manifest.tsv`).  The
wired boards are already absent from `census_residue.txt`.

## 6. Follow-ups
- QHBound/wrap harvest: `NGramHistWrap.v` is landed and axiom-clean; the
  prover's wrap-cert emitter (find the quiet state, wrap, close, cert) is the
  next tooling step to harvest the quasihalter tail into `NGHWStage/`.
- Pattern measures: the lex cert currently uses count measures (`ngmeas`);
  the `NgPattE` pattern-measure vocabulary (`pm_exact`) would recover the
  "liveness lags closure" tail the single count measure misses.
- History escalation: the sweep tries `history=2,4`; the oracle shows a
  small `history=6,8` tail — raise `PARAMS` if the yield plateaus.
