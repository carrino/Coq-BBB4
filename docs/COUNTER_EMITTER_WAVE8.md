# Wave-8 — the interleaved-counter auto-emitter (residue burn-down)

_Written 2026-07-24 (branch `claude/bbb4-residue-reduction-h68aaj`).  This wave
cracked the quasihalter half of the residue (1,100 sawtooths) and PROVED the
counter route end-to-end (first interleaved counter boarded through the
kernel).  What remains is a codegen job: clone the validated template across
the ~2,480 interleaved-counter core.  This doc is the spec._

## 0. State at hand-off (measured, authoritative)

Residue unboarded: **3,887 → 2,787** this wave.

| bucket | count | route | status |
|---|---|---|---|
| sawtooth quasihalters | 1,100 | `bin/irules` → `MetaBlkPfxQH` conveyor (`IQHStage_11..21`) | **BOARDED** |
| interleaved-counter core (NQH-shaped, nghist+irules+rank all fail) | **~2,480** | the `Jp`/`LapGlue` emitter (this doc) | template proven; codegen TODO |
| irules-missed quasihalters (quasihalting counters) | 298 | counter emitter, R_QH glue variant | TODO |
| wave/bounce counter+sawtooth composites (√-growth) | ~8 | `WaveCounter.v` / `BounceCounter.v` | TODO (few) |

Machine lists: `tools/nghist/wave8_counters_todo.txt` (the 2,480),
`tools/nghist/wave8_qh_missed_machines.txt` (the 298).  Sweep record:
`tools/nghist/wave8_irules_sweep.csv`.

**Why these looked hard for days (the resolved mystery):** every *closure*
method (n-gram, RepWL, rank) manufactures a spurious carry-free cycle on a
binary counter, and irules' single-decrement meta-cycle cannot model a
*doubling* carry chain — so all the generic deciders bounce off simultaneously.
Structurally they are the most regular machines in the space.  The
determinism "hammer" was REFUTED (0/300 determinize at k≤12); the route is
per-machine lap proofs, mechanized by cloning one template.

## 1. The proven route (WAVE 0 + WAVE 1, both landed + committed)

- **`theories/Counters/JpCounter.v`** (WAVE 0) — the complemented interleave
  encoding.  `Jp` = `ILCounter.Ip` with the data cell `S0`/`S1` swapped:
  the census's comb-free interleaved counters decode to a value that DESCENDS
  within each doubling block (carry runs in the complement sense), so the
  anchor tape is `Jp p`.  Three mirror decomposition lemmas
  (`cview_some_J`/`cview_none_J`/`Jp_head`), `pair_rot`, and the overflow
  measure `tovf` (`tovf_succ`/`tovf0_allones`).  **Zero axioms** (Closed under
  the global context).  Reused verbatim by every counter board.
- **`theories/Machines/Counters/Interleave_TGT.v`** (WAVE 1) — the first
  interleaved counter, `NeverQuasiHaltsSt 0RB---_0LC1RB_1LA1LD_1LC0RB`,
  `functional_extensionality_dep` only.  THE TEMPLATE the emitter clones.
  Anatomy (all per-machine parts marked):
  - `tm_T` : the transition table (per machine).
  - `Cc p := (edge_state, (Jp p ++ [S0], head, []))` : anchor config (per
    machine: edge state, head).
  - 6 unit windows `U_P1/U_RIP/U_STPI/U_STPO/U_RET/U_FIN` + `U_VA`, each a
    `wsteps … = …` closed by `reflexivity` (per machine; **derived by
    simulation**, see `lapTGT.py`).
  - phase wrappers `phP1/phRIP/phSTPI/phSTPO/phRET/phFIN/phVA` (framing by the
    unit's `bl/br`: `wsteps_frame` / `wsteps_frame_l` / `cycL` / `cycR`).
  - `lap_exact` : the increment `Cc p → Cc(succ p)`, two `cview` branches
    (interior carry `j` / overflow `2ʲ−1`).  The rep-algebra junctions are
    SETTLED: interior open `rewrite HJp, <- app_assoc; change …; rewrite
    app_assoc, pair_rot`; overflow open `rewrite HJp, pair_rot`; **pin
    `phRET`'s `k`** (`apply (phRET (2*j))` interior, `apply (phRET (2*(S j')))`
    overflow after `change (S1::S1::rep[S1;S1]j'++[S0]) with (rep[S1;S1](S
    j')++[S0])`); middle bullet `rewrite HJs,…,rep_dbl; cbn [Nat.mul]; rewrite
    rep_slide, <- !app_assoc; reflexivity`.
  - `lap_T` : the lift version (wraps `lap_exact`).
  - `boot_T` : `exists 5; vm_compute; …` (per machine: the boot step count).
  - `vis_A` : well-founded on `tovf` (the log-rare edge state).  `vis_T` :
    B@0, C@1, D via `phBD` (2 steps), A via `vis_A`.
  - `Theorem nqh_<SPEC> := glue_neverqh tm_T Cc p0 boot_T lap_T vis_T`.
- **`tools/counters/lapTGT.py`** — the untrusted differential lap validator:
  builds `Cf(m)`, runs the single-sweep skeleton across both branches, checks
  step-count + config + next-anchor vs raw sim, `dump_units()` prints the 6
  windows.  This is the emitter's trace stage.

## 2. The emitter — what to BUILD next (the codegen job)

A per-machine untrusted tool (fork `lapTGT.py`/`executor.py`) that emits
`Interleave_<id>.v` cloning `Interleave_TGT.v`.  The kernel re-checks every
emission; a wrong constant fails to TYPECHECK (never mis-proves).

**DETECTION** (raw simulation per machine): (1) parse SPEC → `tm` (the anchored
run must avoid head-on-`(StA,S1)` or a reflexivity window fails = bad fit).
(2) box-growth fingerprint: `box=log` ⇒ this route; `sqrt`/`lin` ⇒ route OUT
(§4). (3) the per-increment anchor = `(edge_state, head-at-fixed-frontier,
blank head, empty far side)` whose visit count grows ~LINEARLY (distinct from
the ~log digit-extension events at the deep edge). De-interleave the counter
list over increments: value ASCENDS ⇒ `Ip`; DESCENDS within each width block
⇒ `Jp`. (4) orientation = {growth side L/R, digit order lsb/msb, marker parity
even/odd, carry direction Ip/Jp, overflow edge-side}. (5) `p0` (=1 or cert
`amin`), boot `T` by vm_compute probe.

**GENERATION**: (6) `lapNN.py` over `executor.py` with the FIXED comb-free
skeleton [P1 prologue; `cycL` RIP over set pairs; `conc` STPI OR STPO off the
deep edge (edge state fires); `cycR` RET; `conc` FIN]; executor derives
endpoints + asserts wall discipline; differential-validate m=1..300 across both
branches; `dump_units` → the 6 windows. (7) string-emit `Interleave_<id>.v`
per the template. (8) `Print Assumptions` MUST be `functional_extensionality_dep`
only or the board is rejected. (9) append to `tools/counters_manifest.tsv`.

## 3. The wave plan (0+1 done)

- **WAVE 0** — `JpCounter.v`. ✅ landed.
- **WAVE 1** — the template `Interleave_TGT.v` + majority orientation
  (native LEFT-growth / LSB-nearest / edge-state-B / complemented). ✅ template
  landed; **emit the rest of this orientation next** (roughly half the core).
- **WAVE 2** — remaining orientations.  Opposite-growth (~50%) via
  `mirror_tm` + `Mirror.mirror_never_qh` around the SAME `lap_T`/`JpCounter`
  (inspect `theories/*/Mirror*.v` first — not yet wired).  msb-order /
  odd-parity via ≤3 more `Jp`-variant decomposition lemmas + anchor transforms.
  Wide-stride ~2% (`2^(2k)`, `2^(3k+1)`) via one stride parameter on RIP/STP.
- **WAVE 3 — route the √/Gray tail OUT** (do not force through `Jp`): translated
  cyclers → a Lin/TCycler decider; some map onto boarded `Mono`/`Spacer`/
  `Double`/`Wave`/`Bounce` templates; a handful are bespoke.  The 298
  quasihalting counters need the R_QH glue variant of `glue_neverqh` (quiet
  edge state + counter recurrence — a `glue_qh` sibling to write).

## 4. First actions for the next session (ordered)

1. **Confirm the counter census.** Run a growth-law + encoding fingerprint
   pass over the full 2,480 (`wave8_counters_todo.txt`): how many are
   `Jp`-interleaved (this route) vs `Ip` vs orientation variants vs
   √/Gray tail.  This sizes each wave accurately (the ~2,480 supersedes the
   synth's mid-sweep ~1,006 estimate).
2. **Build the emitter** (fork `lapTGT.py` → `emit_interleave.py`): detection
   + generation + the compile-repair loop, cloning `Interleave_TGT.v`.
3. **Emit + validate WAVE 1 orientation in batches of ~25**, `coqc` +
   `Print Assumptions` green per machine, commit per batch, extend
   `counters_manifest.tsv`.  These land in the **proven (R_NeverQH) tier** the
   same conveyor-belt way as the holdout counter boards.
4. **WAVE 2** (mirror + variant lemmas), then **WAVE 3** tail routing +
   the `glue_qh` variant for the 298.

## 4b. Dead levers — measured, do NOT retry

- **RepWL over the counter core: DEAD.** Swept 60 random counter-core machines
  through `tools/repwl_prover.py` at rungs `(L,T) ∈ {2,3,4}×{2,3,4}`, `t=0`,
  cap 6,000 nodes: **0 closed, 0 caught**.  RepWL's counted-block abstraction
  cannot finitize a binary counter for the same reason n-gram cannot — the
  digit pattern differs on every increment, so no finite block set closes.
  (This closes the "was RepWL ever pointed at today's residue?" question:
  it was not, and it would not have helped.)
- **The determinism "hammer": REFUTED** (0/300 determinize at k≤12) — see
  `docs/TERMINOLOGY.md`.
- **Wide-vocabulary NGramHist on the counter core: 0/572.**  See
  `tools/nghist/wave8_nqh_fail.txt`.
- **The nghist WRAP route on the 298 quasihalting counters: 0 boards.**  They
  are quasihalting *counters*; they need the counter route's `glue_qh` variant.

## 5. Non-negotiables (unchanged)

- Everything in `tools/` is UNTRUSTED; the kernel re-checks every board.
- `Print Assumptions` = `functional_extensionality_dep` only on every new file
  (JpCounter is even axiom-free).  Reject any board that prints more.
- NEVER touch `theories/Census/`; `python3 tools/census_cache.py --check`
  stays MATCH.
- `coqc`-validate each file (native off is fine — these are `vm_compute`/
  `reflexivity`; the census cmi mismatch is orthogonal), commit + push per
  compiling batch.
- Keep the machinery pointed at the residue, away from the 27 holdouts.
- Env: `export OPAMROOT=/root/.opam; eval $(opam env --switch=census)`.

## 6. Pointers
- `theories/Machines/Counters/Interleave_TGT.v` — the template (spec by example).
- `theories/Machines/Counters/Interleave_18.v`, `_35.v` — prior interleaved
  boards (the comb variant; `_TGT` is the simpler comb-free one).
- `theories/Counters/{JpCounter,ILCounter,LapGlue,MonoCounter,WTape}.v`.
- `tools/counters/{lapTGT.py,executor.py}` — the trace/validate stage.
- `docs/TERMINOLOGY.md` — census/residue/holdout glossary + the refuted hammer.
