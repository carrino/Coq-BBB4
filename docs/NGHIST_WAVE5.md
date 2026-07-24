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

## 4. Harvest, yields, oracle provenance
_(filled in as the harvest runs — see `tools/nghstage_manifest.tsv`.)_

## 5. Wire / regen note
The staged `theories/Machines/NGHStage/*.v` accumulate toward the `Forall`
over the frozen 5,156 `D_census` list (`tools/census_holdouts_kept.txt` +
`tools/census_residue.txt`).  Two routes exist: (a) the Assembly.v `Forall`
path needs **no** census walk (the staged per-file `Forall`s compose directly);
(b) the legacy wire+regen path (`regen_residue.py`) drops boarded machines
from `Deferred_*` and re-certifies on stable hardware.  Wave-6 uses route (a).
