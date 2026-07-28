# Wave-23 — the no-visit-witness bucket closes: avoidance IS in the chains

_Branch `claude/residue-list-refinement-cxzdax`, off main at `D_remaining`
511 (the wave-22 merge).  This wave took the residue prompt's ranked item
(2) — the 15 "no visit witness (`StA` is targeted)" machines — and boarded
**all 15**.  `D_remaining` **511 → 496** (4,660 / 5,156 = 90.4% settled).
All 15 are `LAPQ_*` boards through one new checker extension;
`Print Assumptions` = `functional_extensionality_dep` only on every one
(checked individually).  `census_cache --check` MATCH; `theories/Census/`
untouched; `audit.py` OK (exact partition)._

## 1. Scoreboard

| | |
|---|---:|
| boards | **15** (the whole bucket) |
| `D_remaining` | 511 → **496** |
| frozen rows settled | 4,645 → **4,660 / 5,156 (90.4%)** |
| new Coq | `Counters/LapGlueQuiet.v` (glue, funext-only) + `Checkers/LapAvoid.v` (checker, axiom-FREE) |
| existing checkers | `LapDecider.v`, `LapGlue.v`, `LapGlueQH.v`, `LapGlueAbs.v` all UNTOUCHED |
| board axiom footprint | `functional_extensionality_dep` only, on all 15 |
| census | MATCH throughout |

## 2. What these machines are, and why the queued closers could not take them

WAVE16 §6b's analysis was right and complete: the 15 are genuine
QUASIHALTERS whose quiet state is `StA` — last visit at step 4–11
(re-simulated this wave: all run ≥ 2M steps, `StA` silent after step 11) —
and both existing R_QH closers fail for structural reasons:

* `LapGlueQH.glue_qh` needs `StA` to be TARGETED BY NOTHING; on all 15
  something targets it (e.g. `D1 -> 1LA`), it just never fires again.
* `LapGlueAbs.glue_qh_abs` needs an absorbing state set excluding `StA`;
  `closed_b` is a DIGRAPH fact over all symbols, so any set holding the
  targeting state must hold `StA`.  Impossible in principle, not in search.

The missing fact is trajectory-level ("that transition never fires after
the boot").  §6b proposed building it symbol-aware (`StD` never READS `S1`
after the boot).  **What this wave noticed is that no new invariant needs
to be found at all**: the lap certificates ARE a faithful forward model —
`LapDecider.v`'s own header quotes mxdys' condition ("my inductive decider
can only decide a TM when it can model the forward behavior exactly") —
so whether `StA` ever fires inside a lap is COMPUTABLE from the chain the
board already carries.  Every window step of every `sstep` is concrete,
and a cycle's iterations repeat one window's states under deeper frames.

## 3. The build

Two additive files; per-board cost is three `vm_compute` booleans.

* **`Checkers/LapAvoid.v`** (axiom-free):
  - `wavoid` re-runs a window checking states at offsets `0..n-1`;
  - `cycL_avoid`/`cycR_avoid` — `WTape.cycL`/`cycR`'s inductions carrying
    `AvoidRun` instead of the endpoint, so ONE `wavoid` check covers every
    iteration of a cycle;
  - `savoid`/`srun_avoid` mirror `sstep`/`srun`; `srun_avoid_sound` says a
    passing chain's CONCRETE trace — all `ca*j+cb` steps, for every `j`
    and every opaque tail — never visits the state.  **No new certificate
    data**: the booleans are recomputed from the same chains.
* **`Counters/LapGlueQuiet.v`** (funext-only):
  - `AvoidRun tm qa n c` + composition (`avoid_add`);
  - `cavoid`/`bootquiet_chk`/`bootvis_chk` — the finite bootstrap window
    and the last-visit witness as one-`vm_compute` booleans;
  - `glue_qh_quiet`: bootstrap at a CONCRETE `t0`, laps that avoid `qa`,
    visits for the other states, `qa`'s visit at `s0`, and the checked
    `qa`-free window `(s0, t0)` give
    `NonHalt /\ QHBound (S s0) /\ QuasiHaltsSt` — the R_QH triple with the
    EXACT last-visit bound (4–11 on these 15; weakened to the census
    tier's 2000 at the board).

The coverage argument: the run from `t0` on is exactly the concatenation
of laps (`glue_reach`'s induction kept at the `lift` level), and every
global index in `[T, T+n)` projects into its lap by `csteps_prefix` +
`csteps_lift`, where `AvoidRun` speaks.  No coinduction, no closure, no
invariant search.

## 4. The emitter route

`emit_lapcert.py` gains the AVOID route (prefix `LAPQ_`): when the ONLY
missing visit witness is `StA`, `absorb_search` fails, and simulation
confirms the quiet shape (`avoid_probe`: last `StA` visit `s0 < t0`, none
later), the board renders with the same chains plus `av_*` booleans, the
concrete-boot lemma, `bvis`/`bq` window checks, and the `glue_qh_quiet`
close.  Emitted boards match `mirror_common`'s existing `_mirrorize_qh`
shape, so the mirror transfer needed NO changes.  Template hygiene: the
pre-change emitter and this one render byte-identical sources on committed
flat and split boards (checked).

All 15 derive on the MIRROR with encodings `Kp` (7, all mode=split),
`Alph_00_10_1` (6) / `Bp` (1) / one more (mode=one); boots are 7–18 steps;
`s0` is 4–11.

## 5. Negative controls

`theories/Tests/LapAvoid_Corruption.v` (all `vm_compute`):

* a NEVER-quasihalting board's overflow chain (which really fires `StA`)
  is REJECTED by `srun_avoid` — the exact mutation a wrong `LAPQ` board
  would carry;
* on a boarded machine, the same boolean asked about each RECURRING state
  refuses (state-sensitivity), and a chain that overruns its window is
  `false`, not vacuously `true`;
* `bootquiet_chk` with the window slid one step earlier (so it contains
  the last `StA` visit) is `false`; `bootvis_chk` at a wrong index is
  `false`; a window containing index 0 (the blank tape starts in `StA`)
  can never pass.

## 6. Kernel verification

`inventory.py` → `gen_stages.py` → `audit.py` OK (exact partition,
`D_remaining` = 496), and `make -f Makefile.coq -j2
theories/Closeout/Closeout.vo` re-checks the closeout end to end in-tree.
`CloseoutFinal.v` remains a box job (OCaml 4.14.2 census `.vo` vs apt
4.14.1 — WAVE16 §4b), as always.

## 7. What is next, in measured order (unchanged from wave-22 minus this bucket)

1. **The 41 `QUAD`/`QUAD`** — the largest population that has never had a
   design pass; `Bounce_8.v`'s `MeasureGlue` nesting is the precedent.
2. **The 235 no-anchor** — `alphabet_infer.py` first.
3. The 60 "no inner family" survivors, the 65 "no exit chain"
   (identification, not chains), and the 5 `SCycR`-entry-offset machines
   (a `LapDecider.v` extension with soundness + corruption tests).

One transferable observation: the avoidance route is not `StA`-specific —
`srun_avoid` takes any state, and `glue_qh_quiet` any `qa`.  If a future
bucket contains quasihalters whose quiet state is `StB`/`StC`/`StD` under
a lap family, the same two files take them with only emitter work.
