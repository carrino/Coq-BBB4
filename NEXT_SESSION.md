_**Internal development log.**  Nothing in this file is needed to verify the
results — start at [README.md](README.md) and [docs/CLAIMS.md](docs/CLAIMS.md).
This is the project's lab notebook: the compute playbook and the per-wave
findings and traps, kept verbatim for future sessions._

# PLAYBOOK — read this first, before any census/proof work

_Written 2026-07-21 after a ~3-day slog that was almost entirely wasted
fighting the compute ENVIRONMENT, not the math. Its whole purpose is to keep
the next session from repeating that. Read all three parts, then the dated
history below._

## 0. TL;DR
- The math is cheap; the **native_compute census walk is the only expensive
  thing**, and this remote **container CANNOT run it** — it preempts every
  few-to-30 min, and heavy census subtrees are ~25-30 min of *unbroken*
  `native_compute` (not resumable mid-unit). Do not try to out-engineer this.
- So: **heavy native_compute runs on STABLE hardware** (real Linux / WSL2,
  ≥16 GB RAM, no preemption; ~1-2h at high `-j`), and the **built census
  `.vo` are committed + hash-guarded** so every container session builds ON
  TOP of a pre-verified census instead of re-deriving it.
- **Proving more machines is container-safe and fast** (per-machine
  `vm_compute`/`reflexivity`). **Re-certifying the census** (after moving
  machines Deferred→proven) is the expensive step — batch it, run it on the
  box, keep it LIGHT via the proven tier.

## 1. Compute / build discipline (the hard-won rules)

**Rule 1 — Classify every task container-safe vs needs-the-box FIRST.**
- CONTAINER-SAFE (do it here): per-machine `NeverQuasiHaltsSt` proofs
  (`vm_compute`/small `native_compute`, seconds-to-minutes each), checker
  development, sweeps, tooling, docs, and `make` (the base build, ~10 min).
- NEEDS STABLE HARDWARE (never grind here): the full census walk
  (`make census`), or ANY single `coqc` unit projected to run longer than one
  container window (~15-30 min). Unbroken `native_compute`, not resumable
  mid-unit.

**Rule 2 — Decide "this needs the box" on minute one, not day three.**
The 07-19/20 session tried to beat preemption with deep-splitting, grinders,
and parallel partitions; ALL lost to restarts (~1-2 WEEKS projected,
"structurally impossible in this environment"). If a unit won't fit a
window, it goes to the box. Full stop.

**Rule 3 — Cache/commit the expensive artifacts; build on top (Part 2).**
Native `.vo` load fine across machines with the SAME arch + Coq 8.18 +
OCaml 4.14 (this container and a WSL2 x86_64 box match).

**Rule 4 — Keep the census walk LIGHT; NEVER un-defer into in-walk tiers.**
The load-bearing lesson: shrink `D_census` by PROVING machines (they drop out
via the zero-cost proven tier at regen), NOT by strengthening the in-walk
qhb-lex/RepWL tiers (levers B/C). In-walk tiers made the walk ~100x slower
per pop (~46 ms vs ~0.1 ms) → residue-heavy subtrees became >2.5h single
walks. Their tables (Deferred@12,974, gen_gsplit_deeper, DEEP_SPLIT_PLAN.md)
are committed but DEAD unless a stable long-lived native env appears.

**Env:** `export OPAMROOT=/root/.opam; eval $(opam env --switch=census)`
(OCaml 4.14.2 + Coq 8.18.0 + coq-native; apt's coqc has NO native_compute).
On a fresh box: `opam init` → `opam switch create census 4.14.2` →
`opam install coq.8.18.0 coq-native` (~30-40 min). Build on the native Linux
FS (`~/…`), **NEVER on `/mnt/c/…`** — the Windows-drive bridge breaks/slows
`native_compute`. Axiom footprint stays `functional_extensionality_dep` only;
everything in `tools/` is UNTRUSTED; every checker feature gets corruption
tests that MUST fail.

## 2. The committed-census mechanism (pay the walk ONCE)

Goal: a fresh container never re-walks, but the proof stays honest — a real
walk produced the committed `.vo`, and editing the census forces a re-walk.

- **Commit the census `.vo` bundle** on the branch: `Census_Theorem.vo` + the
  144 `theories/Census/Compute/{GG_1LC,GGH,G}_*.vo` + the base census `.vo`
  they need (`Run.vo`, `Decide.vo`, `Deferred_*.vo`, `Proven_*.vo`,
  `Run_Split*.vo`) + matching `.coq-native/*.cmxs`.
- **`CENSUS_VO_HASH`** — a committed hash of the census `.v` INPUTS. A setup
  step compares it to the working tree: MATCH → `touch` the `.vo` newest so
  `make` skips the walk (container builds instantly); MISMATCH → warn
  "census edited — re-walk on stable hardware" (the only wall, and it's
  deliberate).
- **`make census-verify`** — force-delete the census `.vo` and re-walk from
  source. The CORRECTNESS phase; run on the box or a timed CI runner.
  `Print Assumptions census_decided` must be `functional_extensionality_dep`
  only. (Not an axiom shortcut — the committed `.vo` ARE genuine walk output.)
- **Size:** small → plain git commit; fat → git-LFS / release asset restored
  by a SessionStart hook. Decide after the first green walk measures it.
- Status: census **CERTIFIED green on stable hardware 2026-07-21** (Print
  Assumptions clean); the `.vo`-commit mechanism itself is still to be wired.

## 2b. Wave-9 (2026-07-25) — the counter emitter, corrected

Full write-up: `docs/COUNTER_EMITTER_WAVE9.md`.  Two things the wave-8 hand-off
got wrong, both now measured (`tools/counters/anchor_profile.py`):

- The template needs the lap to be affine in the carry length `j` on BOTH
  branches (interior AND overflow).  Wave-8 only ever checked the interior.
  Control: 17/17 already-boarded counters pass both; **0/40 of the 298
  quasihalting counters do** — their overflow lap grows like `2^j`.  Do NOT
  re-point the single-sweep template at that list; it is not encoding-blocked.
- The encoding IS a real blocker, but on the never-QH core: 15/80 of a random
  sample are template-shaped and 10 of those are `Ip` (~440 / ~290 extrapolated
  over the 2,328 unboarded).

`tools/counters/emit_ip.py` boards them (12 committed, all recompiled from a
clean `.vo` state, `functional_extensionality_dep` only).  It also needed the
anchor HEAD symbol, the anchor TAIL and the anchor's FAR side (a blank *cell*,
not the empty *list*) to become parameters — the encoding alone was not enough.

## 2b2. Wave-34 (2026-07-30) — `ReachStI`, and Drozd's 26 measured

Full write-up: `docs/WAVE34_REACHSTI.md`.  The tier `docs/REACHST_TIER.md`
§8e asks for -- `ReachSt` relativised to an invariant -- now exists
(`theories/Checkers/ReachStI.v`).  **It boards none of Drozd's 26.**  Read
the write-up before spending a session on this front; the three things worth
carrying forward:

- **The 14 `1RB---` rows are NOT never-quasihalters.**  `StA` fires once at
  index 0 and nothing targets it, so they quasihalt with score 1 and their
  target is `iqh`, not `NeverQuasiHaltsSt`.  `tools/reachst/bothhalves.py`
  skips them ("boards via its completions"), so they had never been measured
  by the ReachSt tier at all.  For those rows `ReachSt tm q` is not merely
  unprovable, it is **false** -- `(StA, ([], S1, []))` halts on the spot.
- **The measure replaces the flavour lemmas.**  `drop_ok` is a computable
  certificate (`B * ones l + C * ones r + rk (q, chd l, h, chd r)`, strict
  drop per goal-avoiding step, Bellman-Ford search in
  `tools/reachsti/cert_search.py`) and certifies a state on **25 of the 26**
  rows -- against `ReachSt.v`'s four hand-written flavours.  It also returns
  `NonHalt`, which the `iqh` rows cannot get anywhere else.
- **The counter reading was being taken at the wrong RADIX.**  `kcopy_classify.py`
  (KCOPY<k>/SEP<k>) and `alphabet_infer.py` (a positive-recursion) can only
  return a BASE-2 counter, and so can every alphabet in `theories/Counters`
  (Ip, Jp, Kp, Dp, Bp, Mp).  `1RB---_0LB1RC_0RD0RC_1LB1LD` is a **base-3**
  counter -- 2-cell digits over {00,01,11}, anchor snapshots decoding to
  1,2,3,... over 10^4 visits, lap `4 + 4j`.  That is why `emit_kp.py` derives
  0 of 17.  New tool `tools/counters/radix_infer.py`; results in
  `tools/counters/RADIX_DROZD26.txt`.  **5 rows are affine in the carry
  length, all of them `1RB---`.**
- **THREE ROWS BOARDED** (core 65 -> 62): `1RB---_0LB1RC_1LB0RD_1LB0RC`,
  `1RB---_1LC0RD_0LC1RB_1LC0RB`, `1RB---_1LC0RD_0LC1RD_1LC0RB`, all as `iqh`
  off the new role-parameterised closer `theories/Counters/KpWallQH.v`.
- **The counter route needs no ReachStI and no closure**, which is the real
  lesson: a lap gives every state's liveness at once plus `NonHalt`.
  `LapGlueQuiet.glue_qh_quiet` is already the right closer (`qa = StA`,
  `s0 = 0`, `t0 = 1`; `StA`-freedom is free because nothing targets `StA`),
  and `BNC_1RB____1LC0RB_1LD1RB_1LC1RB.v` is a `1RB---` row already boarded
  that way.  For the three radix-2 affine rows the encoding (`KpCounter.Kp`)
  and the closer both exist; **the missing piece is an emitter pairing `Kp`
  with the QH closer** -- `emit_kp.py` emits never-QH, `emit_qh.py` emits the
  `iqh` triple but is hard-wired to `Jp`.  Cross those two first.
- **For the liveness-engine route the blocker is the wall.**  On all 14 `1RB---` rows
  the NGramHist closure certifies *exactly* the states `ReachStI` does.  9 of
  the 17 rows swept are short by exactly ONE state, always the state whose
  liveness is "the leftward sweep stops at the counter's wall".  13 of the 54
  missing states have a pure one-direction avoid sub-machine, so the sized
  next piece is `FuelWide`'s runner rule wired into the one-state-lifted
  path (`ClosureExt`); the other 41 still want the wall itself.

## 2b3. Wave-35 (2026-07-31) — the 24 three-state core rows are NINE machines

Full write-up: `docs/CORE_3STATE.md`.  **12 of the 24 `1RB---` core rows
board** -- half the population; core 62 -> 50.  Read that file before touching this population
again.

  [MERGE NOTE, added when this wave was merged with the LADDER track (PR #90,
  core 62 -> 59).  The two board sets are DISJOINT -- the ladder took three
  rows this wave never touched -- so the joint figure is **47**, not 50 or
  59.  `audit.py` OK at 47 core + 21 shadows.]  The four things worth carrying:

- **The 24 rows are 9 sub-machines.**  `StA` fires once and (on 23 of the 24)
  is the target of nothing, so everything after step 1 is the `{B,C,D}`
  sub-machine on a tape with one `1`.  Up to relabelling those three states
  the population collapses to NINE.  Two rows sharing a sub-machine differ
  only in their BOOTSTRAP, so one role-parameterised closer plus one boot
  probe boards a whole group.  Wave-34 wrote `KpWallQH.v` for one such group
  without noticing the grouping; three more groups fell this session the same
  way.
- **The anchor's HEAD SYMBOL was hard-coded S0 everywhere.**  These are wall
  counters read with the head ON the wall cell, so their anchor head is `S1`,
  and `derive_tail_best`/`_far` (hence `emit_lapcert.anchors`) scanned only
  `h == 0`.  `emit_lapcert.py` now carries `HD` as a module global, searched
  S0-first, and `anchors` proposes every family with a long consecutive run
  rather than the single best-scoring one.  Regression checked
  (`1RB1RC_1LC0RD_0LC1RD_0RB0LA` still derives the same certificate).
- **Part of the residue is NOT BASE 2.**  Every alphabet in `theories/Counters`
  and every measurement tool is base 2; `radix_infer.py` had already read
  `1RB---_0LB1RC_0RD0RC_1LB1LD` as base 3 with a `4j+4` lap, and
  `residue_map.tsv` calls the same row "EXP3" because it is fitting the wrong
  radix.  `Counters/TernCounter.v` (base-3 numerals, TWO increments — with
  and without a terminator past the top digit), `Counters/LapGlueIx.v`
  (`LapGlueQuiet` over an arbitrary index, since a base-3 counter has no
  `positive` to index by) and `Counters/Ter3Wall.v` board those three rows.
- **`Checkers/LapDecider.v` cannot express an ALTERNATING sweep**, and two of
  the boarded groups need one.  `SCycL`/`SCycR` require the unit run to
  return to its own state; an alternating sweep does so only every second
  cell, and a fixed 2-cell unit covers only even runs while `j` is
  universally quantified.  That is an expressiveness gap, not a search gap —
  closing it means a state-SET in `sconf`, i.e. re-founding `srun_sound`.
  The hand-written closers (`KpWallAlt.v`, `KpWallScan.v`) carry "still one
  of the two" existentially instead, which covers both parities at once.

**Ranked next moves on the remaining 12** (details in `docs/CORE_3STATE.md`
section 3): (1) the 11 rows whose lap is super-affine (`6,16,36,82,196` at
carry lengths 0..4) — those are NESTED counters and `nestcert.py` is
`S0`-anchor-only, so thread a second head symbol through its INNER anchor;
(2) `1RB---_1RC1LB_0LB1RD_0RA0RC`, the one row that targets `StA` — and
`0RA` DOES fire, at indices 19, 66, 257, 1024, 4095, 16382, … (~4^k, measured
to 2·10^6), so that row's target is `NeverQuasiHaltsSt`, NOT `iqh`, and its
closer is `glue_neverqh`.  It is the only one of the 24 that does not
quasihalt.

## 2c. Wave-14 (2026-07-26) — the HOLDOUT front opened; wave family CLOSED

Full write-up: `docs/HOLDOUTS_WAVE14.md`.  First session pointed at the 27
holdouts rather than the residue.  Headlines:

- **The 27 are 16 boarded / 11 unproven** (was 5/22; this line said
  "11 boarded / 16 unproven" until 2026-07-27 — that was the mid-wave count
  and it went stale as the rest of the wave landed.  Re-derived against the
  authority: `census_holdouts_kept.txt` ∩ `closeout/frozen_unproven.txt` = 11,
  complement = 16, which matches `docs/HOLDOUTS_WAVE14.md` §1).  `#6` and `#24` landed
  (`theories/Machines/Counters/Wave_6.v`, `Wave_24.v`), so **all six
  `wave_counter` machines are now boarded** off the one `WaveCounter.v`
  closer — it needed no change.  `docs/HOLDOUTS_WAVE14.md` §1 has the full
  family decomposition of the remaining 20 (tower 4, double 3, blockdbl 3,
  xd 3, fractal 2, wave4 1, wrap-QH 2, v4-irules 1, open 1).
- **#6 was EASIER than #27, not harder**, despite the "4-step 0-writing
  cross" warning: its rightward return leaves the tape byte-for-byte
  unchanged, so the whole `relaid`/`bridge_l` borrow algebra disappears.
  The one piece of real design is `decp` (the deposit decrements the NEWEST
  laid run, which is `base[0]` only when the carry stopped immediately).
- **#24 was nearly free:** `mirror_tm tm_24` is `tm_6` with the states
  relabelled by `(StA StC)(StB StD)`.  That bijection MOVES `StA`, so it is
  not a `TM_swap` transport — but the file transcribes under the
  substitution, and `Wave_24.v` compiled on the first try.  New tool
  `tools/counters/sibling_scan.py` looks for exactly this.
- **`sibling_scan.py` found four unproven holdouts that are relabellings of
  BOARDED machines**, which said their dynamics are inside our engines'
  reach.  Acting on that, `tools/nghist/holdout_sweep.py` ran NGramHist over
  all 20 — and **boarded 4 of them at the CHEAPEST rung (k=2, n=2)**:
  `theories/Machines/NGHHold/NGHHold_{00..03}.v`.  Those are the whole
  `xd_counter` family (#1/#25/#29) **and
  `1RB0RB_1LC1RC_0RA1LD_1RC0LD` — the machine this file has called "no known
  proof anywhere" for a year.  It now has a kernel-checked
  NeverQuasiHaltsSt theorem.**
- **[SCOPE, 2026-07-27: the holdouts now have DEDICATED sessions of their own.
  The rule below stands as a finding, but a RESIDUE session should not act on
  it -- do not open the holdout front or sweep `census_holdouts_kept.txt`.
  `docs/NEXT_SESSION_PROMPT.md` is residue-only.]**
- **RETIRE the "keep the machinery away from the 27" discipline**
  (`docs/TERMINOLOGY.md`).  It rested on mxdys' deciders failing at HIS
  parameters; ours is a different tool.  New rule: sweep the holdouts with
  every engine at every rung BEFORE hand-writing a parametric proof.  The 16
  survivors resisted (2,2)/(4,2)/(6,2) never-QH and the R_QH tier; still
  untried are n=3, k=8, bigger fuel/MAXCTX, RepWL, irules-QH and LapDecider.
- Two leads CLOSED OFF (do not re-chase): the `1RB---` wrap pair is not just
  wiring (`provenqh_stay.txt` records the QHBound tier probe-failing on
  both), and tower/xd are ~1,500/~1,100-line table interpreters, i.e. a
  checker-port project, not a session.
- blockdbl (#11/#13/#28) reconnoitred (`tools/counters/probe_bd.py`,
  j = 2..7 exact).  Caution: one lap is Θ(m²) with Θ(m) turnarounds, so it
  needs `MeasureGlue`-style nesting like `Bounce_8.v`, not flat `LapGlue`.
  Do #13 first (mdbl = 0, mb = 0).
- **Env:** apt's `coq` is exactly 8.18.0 and is all the holdout front needs
  (no `native_compute`).  `make -j4` OOMs on `IRules_Batch_02` (~6.3 GB);
  use `-j2` or targeted `make -f Makefile.coq <file>.vo`.

## 2d. Wave-16, HOLDOUTS track (2026-07-27) -- mxdys' S(n) claim, and FOUR holdouts boarded

Full write-up: `docs/HOLDOUTS_MXDYS_SN.md`.  John relayed two claims from
mxdys about the 11 live holdouts; both were tested.

- **"1RB0LD_1RC0RC_1LA1RB_0LC0LD is bouncer counter, simpler than sync
  bouncer counter" -- PROVED.**  Sampled at StA on the leftmost visited cell
  the tape is `1 0^(3v+3) 1 <binary counter of value v>`: a bouncer whose
  length is affine in the counter's VALUE.  BBB's blockdbl reading (a solid
  block doubling, `18*4^n + 22*2^n - 2` steps per macro lap, `Theta(2^n)`
  turnarounds) is what made this look like a MeasureGlue job; the bouncer
  reading makes ONE SWEEP a complete lap, `12v + 4*carry(v) + 27` steps.
  The "simpler" is load-bearing: a pair of BLANK cells past the top digit is
  a digit-0 pair, so overflow and interior carry are the same rule.
  `theories/Counters/BCtrCounter.v` + `BCtr_11.v`; **#13 transcribes** under
  `sigma = StA->StC, StB->StA, StC->StB` (checked, `sigma(tm_11) = tm_13`).
- **The two `1RB---` wrap machines are boarded**, off John's reading ("it
  keeps bouncing until it finds zero on the right then moves the wall over
  one... only 3 states, zeros on the way out, 1s on the way back").  They
  quasihalt (StA fires once; {StB,StC,StD} is closed), so they take the
  QHBound route via `LapGlueAbs.glue_qh_abs`.  `WrapBouncer.v` +
  `WrapBc_R.v`/`WrapBc_L.v`.  Their macro block doubles `K -> 2K+1` and the
  bounce COUNT is explicit in the anchor, so a plain induction replaces the
  MeasureGlue that the nested counters needed.
- **mxdys' general S(n) claim holds on 8 of the 11, measured** (table in
  `HOLDOUTS_MXDYS_SN.md` section 2), including exact closed forms for every
  transition's usage count.  The 3 misses are a limitation of the SEARCH
  (it assumes a constant RLE shape word); tower #20's record tape is a word
  over the blocks `10`/`110`, i.e. a counter in another alphabet, which a
  fixed shape can never match.  Nothing measured contradicts the claim.
- **Next board, already reconnoitred:** `1RB1RA_0RC0RB_1LC1LD_0RA0LA` is the
  same two-level bouncer with `(w, m) -> (w+1, 3m)`, `m = 3^(w+1)`, bounce
  `mkB (j+1) k -> mkB j (k+1)` in `6k+10` steps and the count explicit.
  Anchors measured out to `t = 1,307,750,844`.  See section 5.

STATE: holdouts 11 -> 7 unproven; `D_remaining` 1,016 -> 1,012.  Stage
regeneration + `Closeout.vo` rebuild still to do (they need the full board
`.vo` closure).

  [MERGE NOTE, added when the two wave-16 tracks were merged.  This track's
  own closeout run landed at `D_remaining` 1,010 (6 boards), not the 1,012
  written above.  Both numbers are now superseded: the stage regeneration
  named here HAS been done, over the MERGED board set, and the joint figure
  is **884** = 1,016 - 126 (residue track) - 6 (this one).  `audit.py` OK.
  The `Closeout.vo` rebuild is still outstanding for both tracks.]

## 2e. Wave-16, RESIDUE track (2026-07-27) — the lap never had to close exactly

Full write-up: `docs/WAVE16_FINDINGS.md`.  Took the ranked item (1) of the
wave-15 prompt (the `AFFINE/AFFINE` bucket, filed as "a CONFIRMED search
gap") and found **the gap is not in the search**.

- `derive_chain` DOES find these chains.  What rejected them was the test for
  having ARRIVED: the chain lands one trailing blank past the anchor, and
  `CTape.lift_side l = fun n => nth n l S0` cannot see a trailing blank.
  `LapDecider.lap_of_run` and `LapGlue`'s `Hlap` **already ask only for a
  `lift` equality** — the emitted overflow branch already exploited it, and
  the hand-written `WLS_*` boards use `WTape.lift_app_blank` for exactly this.
  Two spots were stricter than the theorem: `lapcert.side_eq` (its
  trailing-blank leniency is dead whenever a side carries no rep, because
  `sden_parts` folds everything into `P`) and `_shape_to` (syntactic
  `pre/u/a/b`, and no rotation can delete a blank).
- **126 boards, `D_remaining` 1,016 -> 890** (4,266/5,156 = 82.7% settled;
  **884 / 82.9% after merging the holdouts track above**).  The merged
  closeout is KERNEL-VERIFIED: `Closeout.vo` + all 43 `CB_*.vo` compile and
  `closeout_partial` is Qed at `functional_extensionality_dep` only.
  `CloseoutFinal.vo` (the chain to `census_decided`) is NOT buildable in a
  container -- the committed census `.vo` are OCaml 4.14.2 and apt coq here
  is 4.14.1, so it is a box job, not a proof failure.  See
  `docs/WAVE16_FINDINGS.md` section 4b,
  all `functional_extensionality_dep` only.  New Coq is one additive file,
  `Counters/LapCertGlueLift.v`: `reach_ovf_lift`/`vis_via_ovf_lift` redo
  `LapCertGlue`'s induction in `stepn`/`lift` space (where
  `LapGlue.glue_reach` already chains), and `glue_neverqh_lift` is
  `glue_neverqh` with the visit premise weakened to what its own proof
  consumes.  `LapDecider.v`, `LapGlue.v`, `LapCertGlue.v` untouched.
- The emitter's `lift` flag defaults to FALSE and the exact route is tried
  first; the lift route is a fallback.  Threading it into `_win_candidates`
  is load-bearing (the target-aware cuts decide whether the winning cut is
  offered at all), and `_shape_to` must SCORE rotations rather than accept
  the first denotational match — otherwise it returns the empty rotation and
  leaves the rep side misaligned.
- **DO NOT RETRY on this bucket** (each 0 of 31): depth-aware memo in
  `derive_chain` (the `seen` set IS depth-blind, and it fires on 29 of 31 —
  it is still not the blocker), `SFold` at m=3,4, rotation-enabling window
  cuts, more search budget (`maxdepth=24` is NEVER reached: `dhit=0`,
  `dmax` 7-21), blank-padding the anchor's `FAR` (1 of 11).
- `ovfshape` re-run over the current 1,016 gives **175 `AFFINE/AFFINE`**, not
  the 141 in `WAVE15_FINDINGS.md` §5b; that number no longer reproduces.
- THE LESSON: when a population is "in model but the search cannot find it",
  **check what the search is being asked to prove before widening it**.
  `LapGlue`'s premises are the specification; the emitter's templates are one
  implementation of them.
- Also fixed: `BlankTail.v`, `MpCounter.v` and `Alph_01_11_011.v` existed but
  were absent from `_CoqProject`, so `make` never built them.

## 2f. Wave-17 (2026-07-27) -- double #32 boarded; the (4,2) holdouts are 4

Full write-up: `docs/HOLDOUTS_MXDYS_SN.md` section 5b (kept as measured; the
board confirmed it verbatim).  `theories/Machines/Counters/Double_32.v`.

- **`1RB1LD_1RC0RB_1LA0RC_0LD0LA` (double #32) is a COMB COUNTER read at the
  LEFT RECORD.**  BBB's macro anchor is head-on-rightmost-1 with comb count
  `a = 2^j`, one lap `36k^2 + 29k - 4` steps -- a `Theta(k^2)` bounce, and
  BBB's notes record an earlier `a = 2^j-1` guess as having TIMED OUT.
  Sampled instead at the left record (head on the leftmost visited cell,
  StA, reading blank) the machine is a rewriting system on `(001)^j` +
  a block word, with three uniform rules R1/R2/R3 costing `8j+2m+5`,
  `8j+5`, `8j+11`.  One turn of R1;R2;R3 grows the comb by ONE, in
  `24j + 2m + 29` steps.  **The macro doubling falls out of iterating that;
  it is never assumed, so the quadratic macro lap is never modelled.**  Same
  move as blockdbl #11/#13/#28 and the two wrap machines: BBB's macro anchor
  was the expensive reading and a finer phase makes one sweep a whole lap.
- **The closer was free.**  `WaveCounter.wglue_neverqh` takes an ARBITRARY
  anchor type with a total successor and a preserved invariant, which is
  exactly `(j, block word)`.  No closed form for either component is needed
  at any point and no new closer was written -- the second board (after the
  six wave machines) to come off that one file unchanged.
- **New in the transcription, worth reusing:** carry a repeated tape unit as
  an ACCUMULATOR fixpoint (`comb j X = (001)^j ++ X`, plus its two phase
  shifts `outp`/`inp`) instead of `rep u j ++ X`.  Every rewrite then stays
  in cons form and reduces by `cbn`; the `rep_shift`/`app_assoc` junction
  plumbing that the earlier counter boards spend real lines on disappears.
  Cost: three three-line shift lemmas.
- **Trap paid for (again): `change (csteps tm 1 X) with (Some Y)` leaves an
  unreduced `match` and the next `rewrite` cannot find its subterm.**  State
  a one-step lemma and `rewrite` it.  Second trap: `replace (S k) with (1+k)`
  hits EVERY `S k` in the goal, including the one inside `repeat _ (S k)`
  that `cbn` then cannot reduce -- `cbn` first, `replace` second.
- **Method held: nothing was written in Coq until it passed a CTape-faithful
  Python mirror.**  `tools/counters/gadgets32.py` (the nine gadgets) was
  green from the previous session; `tools/counters/rules32.py` is new and
  covers the four sweep inductions, R1/R2/R3 and the composed lap in the
  exact form the Coq states them, plus a 40-lap orbit replay.  The one thing
  the traces had wrong on paper: R1/R2 use `rc5^(j-1)`, not `rc5^(j-2)`.

STATE: (4,2) holdouts 5 -> 4 unproven (`census_holdouts_kept.txt` n
`closeout/frozen_unproven.txt`: fractal #3/#5, wave4 #15, tower #20);
`D_remaining` 1,010 -> 1,009.  `census_cache --check` MATCH throughout
(nothing under `theories/Census/` was touched).

**Next: wave4 #15 (`1RB0RC_0LC1LB_0LD1LC_1RD0RA`) -- DONE in wave-18, see
section 2g below.  What follows is the wave-17 handoff, kept because its
reading of the machine is what the board was built from.**

#15 is a PLAIN BINARY COUNTER, not the mod-4 odometer this file used to
predict.  John's reading: each bit is a zero-STRIPE's position mod 2, the
2nd stripe is the LSB, and the parity offset alternates.  Number the stripes
`z0 = 0` (the anchor's own blank), `z(k+1)` the k-th after it; then
`bit k = (z(k+1) + k) mod 2`, and the TOP stripe-bit is always 0 -- it is the
implicit leading 1 of a `positive`.  ONE LAP IS `p -> p+1` with NO exceptions
(1,493 consecutive laps, p = 2..1495, no gaps; the "spawn" is the carry out
of the top).  So it takes `LapGlue.glue_neverqh` -- BCtr_28's closer -- with
NO invariant, and the "~80 line mod-4 arithmetic layer" is ZERO lines.

Sampled at the left record the tape is `1^lead 0 1^v0 0 1^v1 0 ...` and the
encoding is a structural recursion on the positive:

    pod p = p mod 2
    venc 2 = [2], venc 3 = [3], venc m = (m + pod (m/2)) :: venc (m/2)
    lead = 1 + pod p

The lap is binary increment made physical.  `p` EVEN is the no-carry case and
is a SINGLE 10-step window (`ruleA`) -- constant cost, no induction.  `p` ODD
is the carry: `entry5 . outward . out6s . deposit . backsweep`.

ALREADY IN THE FILE AND COMPILING:
  - the machine, 9 single-step joints, 7 gadgets, BOTH deposit cases;
  - `out6s` / `ret1s` / `bBs` / `lay` sweeps;
  - `outward` -- one induction over the carried blocks (a carried block has
    EVEN length 2a+2; `out6^a` eats it two cells at a time until two remain,
    then `carry5` crosses the stripe.  Cost 6a+5);
  - `Deb` / `backsweep` -- the return as ONE structural recursion over the
    debris (`cross7` eats a stripe group, `ret1` a single 1, `exit1` lands on
    the new left record), plus `lay_Deb`/`owdeb_Deb`, which prove the outward
    phase lays exactly what the return can consume;
  - `back_lay` / `back_owdeb` / `bta` -- pure list lemmas pushing `back`
    through both shapes, so what the debris turns back into needs no machine;
  - `venc` / `Cf15`, agreeing with the measured vectors on the nose.
  The KERNEL confirms by vm_compute: boot `csteps tm_15 17 c0 = Cf15 2`;
  `csteps tm_15 10 (Cf15 p) = Cf15 (p+1)` for p = 2,4,16; and the odd laps
  at n = 34, 38, 70, 138, 270 for p = 3,5,7,15,31.

WHAT IS LEFT -- one step, then the wiring:
  1. the composition.  Needs the decomposition
        wblocks (venc p) = owtape l (repeat S1 (2a+1) ++ S0 :: wblocks rest)
     -- carried blocks are the EVEN ones, the deposit block is the first ODD
     one (checked in the mirror: every odd p has one).  Cleanest as an
     inductive relation `Scan bl l a rest` with two constructors, plus
     `Scan bl l a rest -> wblocks bl = owtape l (...)` by induction on Scan,
     and existence `forall p odd, exists l a rest, Scan (venc p) l a rest`.
     Then the result side: show `back <debris> <tail>` is
     `repeat S1 (1 + pod (p+1)) ++ S0 :: wblocks (venc (p+1))`, for which the
     arithmetic fact is
        venc (xO q)      -> venc (xI q)       : head +1, tail same   (rule A)
        venc (xI q)      -> venc (xO (q+1))   : head +2 and tail +1 if q even,
                                                head +0 and tail recurses if q odd
  2. `LapGlue.glue_neverqh` at p0 = 2, boot (t = 17), visits (all four states
     occur in the first handful of steps), then corruption tests,
     `_CoqProject`, `counters_manifest.tsv`, closeout regen, `-j2` build.

TOOLS (all green, run them first): `tools/counters/lap15.py` (rules, step
counts, gadgets EXHAUSTIVELY over |L|,|R| <= 4, the counter reading, the
closed form, `venc`) and `tools/counters/asm15.py` (replays the lap from the
verified gadgets alone as pure list ops and diffs against the raw simulator;
green for p = 2..1199).

TRAPS PAID FOR ON THIS BRANCH, do not re-learn:
  - rule B's branch is on the INDEX (`i < last` vs `i = last`), NOT on the
    residue.  Fitting the reachable orbit alone gives the wrong rule.
  - A SAMPLED gadget check is not a check.  The deposit passes a 42-context
    sample and a naive window search and fails the exhaustive check on 496 of
    961; it is a SWEEP (the bounce walks back over the laid 1s), not a window,
    and splits into `dep0`/`dep2` by the symbol the bounce lands on.  `dep0`
    goes through chd/ctl so the spawn is free.
  - the mod-4 block-vector model and its `WInv4` invariant (earlier commits on
    this branch) are TRUE but UNNECESSARY.  Do not port them.

STATE: (4,2) holdouts 5 -> 4 unproven (`census_holdouts_kept.txt` n
`closeout/frozen_unproven.txt`: fractal #3/#5, wave4 #15, tower #20);
`D_remaining` 1,010 -> 1,009.  `census_cache --check` MATCH throughout
(nothing under `theories/Census/` was touched).

**Next: wave4 #15 (`1RB0RC_0LC1LB_0LD1LC_1RD0RA`) -- micro-lap already
MEASURED, not yet transcribed.**  `tools/counters/probe15.py` (mirror) +
`tools/counters/lap15.py` (checker, green over 1,495 anchors to t = 3e6).
Same left-record move as #32: `(StC, ([], S0, 1^lead 0 1^v0 0 1^v1 0 ...))`,
`lead` alternating 1/2, `v` frontier-first.  Rule A (`lead 1->2`) is
`v[0] += 1` in a CONSTANT 10 steps; rule B (`lead 2->1`) is the mod-4 carry
-- scan to the least `i` with `v[i] % 4 /= 0`, then `v[i] += 2, v[i+1] += 1`
in `4*sum(v[0..i]) + 4i + 18`, or at the far end `v[i] += 1` and append `2`
in `+22`.  All counts exact, 0 mismatches.

**Trap, already paid for: rule B's branch is on the INDEX (`i < last` vs
`i = last`), NOT on the residue.**  On the reachable orbit residue 1 only
occurs with `i < last` and residue 3 only with `i = last`, so fitting the
orbit alone gives "residue 1 -> deposit, residue 3 -> spawn", which is false.
`[4,3,2]` stops at `i=1` with residue 3 and takes the INTERIOR branch, to
`[4,5,3]`.  `lap15.py`'s `probe_off()` pins it.

The safety invariant is SETTLED (verified on every anchor, inductive under
the composite over 2,988 vectors): walk the vector with a running parity bit
`p`; an even block is `0 mod 4`; an odd block is `1 mod 4` when `p` is even
and `3 mod 4` when `p` is odd (flipping `p`); the LAST block is `2 mod 4` if
`p` is odd, `3 mod 4` if `p` is even.  Equivalently -- and this IS `fp` in
disguise, so the mod-2 layer does port -- the number of odd blocks is odd and
the odd blocks alternate `1,3,1,3` mod 4.  It gives exactly what rule B
needs: the scan finds a block that is not `0 mod 4`, and that block is odd.
An even stop is not a third branch; measured, the machine then leaves the
anchor family altogether.

The tape gadgets are measured too (`lap15.py` `gadgets()`): eight single-step
joints uniform through `chd`/`ctl`, plus `ruleA` as a SINGLE 10-step window
(no induction -- that is why it is constant-cost), `entry5`, `out6`
(eats three 1s, hands one back: net -2 per unit in 6 steps, so a run of
length `2k+1` costs `6k` and leaves one 1 -- **that odd-length requirement is
the tape-level reason the invariant is mod 4**), and `ret1` (1 step/cell
back, giving rule B's 3+1 = 4 per cell).  LEFT TO DO: the deposit and
carry-continue windows at the turnaround, then the assembly and the Coq.
`wglue_neverqh` still needs no change.  `HOLDOUTS_MXDYS_SN.md` section 5b has
the full table and sizes the other three.

## 2g. Wave-18, HOLDOUTS track (2026-07-27) -- wave4 #15 boarded; #3/#5 follow in 2h, #20 does NOT

[CORRECTED 2026-07-28.  This heading used to read "then #3/#5/#20; the (4,2)
holdout list CLOSES".  The fractals #3/#5 were boarded (section 2h), but
**tower #20 never was** -- see 2k.  It has no `NeverQuasiHaltsSt`, no manifest
row, and is still in `tools/closeout/frozen_unproven.txt`.  The (4,2) holdout
list has ONE machine left.]

Full write-up: `docs/HOLDOUTS_MXDYS_SN.md` section 5b.
`theories/Machines/Counters/Wave4_15.v` (730 lines),
`theories/Tests/CountersW15_Corruption.v`.

- **`1RB0RC_0LC1LB_0LD1LC_1RD0RA` (wave4 #15) is a PLAIN BINARY COUNTER.**
  This file used to predict a "mod-4 wave odometer" and size the board as a
  port of `WaveCounter`'s parity layer plus ~80 lines of mod-4 arithmetic.
  John's reading -- each bit is a zero STRIPE's position mod 2, with an
  alternating offset, `bit k = (z(k+1) + k) mod 2`, and the top stripe-bit
  the implicit leading 1 of a `positive` -- makes ONE LAP `p -> p+1` with no
  exceptions.  So the closer is `LapGlue.glue_neverqh` (`BCtr_28`'s), with
  **NO invariant**, and the mod-4 arithmetic layer is ZERO lines.  The
  `WInv4` predicate this file recorded is TRUE but UNNECESSARY; it is in the
  branch history and should not be ported.
- **The tape is a structural recursion on the positive**, so `Cf15` needs no
  `2^k` arithmetic and no bit extraction:
  `venc 2 = [2]`, `venc 3 = [3]`, `venc m = (m + pod (m/2)) :: venc (m/2)`,
  `lead = 1 + pod m`.
- **The lap is binary increment made physical.**  `p` EVEN is the no-carry
  case: a SINGLE 10-step window (`ruleA`), constant cost, no induction.  `p`
  ODD is the carry, `entry5 . outward . out6s . deposit . backsweep`.
- **The composition is one inductive relation, `Scan bl l a rest bl'`**, and
  it carries the RESULT vector alongside the decomposition, so each
  direction of the lap is ONE induction over the SAME relation:
  `Scan_in` (`wblocks bl = owtape l (1^(2a+1) 0 wblocks rest)`) and
  `Scan_out` (`wblocks bl' = owtape l (wblocks (btail a rest))`).  Splitting
  this into a decomposition relation plus a separate `Bump` relation, and
  then having to link them, is the detour to avoid.
  - carried blocks are the EVEN ones, the deposit block is the first ODD one;
  - `btail a rest` is the deposit's whole arithmetic: `+2` here and `+1` on
    the next block when there is one, else `+1` here and a SPAWNED length-2
    block -- which is just the carry out of the top;
  - `Scan_venc` (the existence, and that the result IS `venc (Pos.succ p)`)
    is a structural induction on the positive: `xI (xO s)` stops at once
    (that block is odd) and `xI (xI s)` carries one block and recurses.
- **Rule A needs one lemma only**: `venc_bump` -- `venc (xO r)` and
  `venc (xI r)` differ in the HEAD by one, tail identical.  It is also what
  the `xI (xO s)` branch of `Scan_venc` needs, so it is written once.
- **The return sweep needs no second induction.**  `owtape_bta`
  (`S1::S1::bta l Y = owtape l (S1::S1::Y)`) says `bta` rebuilds exactly
  what `owtape` ate, so `back_frame` turns the whole debris back into the
  carried blocks in a single rewrite.  Outward and return are SEQUENTIAL
  inductions over the same shape, never nested.
- **Trap paid for, and it is the expensive one: A SAMPLED GADGET CHECK IS
  NOT A CHECK.**  The deposit passes a 42-context sample AND a naive
  "does the tail pass through" window search, and FAILS the exhaustive
  check on 496 of 961 contexts.  It is a SWEEP, not a window -- `A0 = 1RB`
  fills the stripe and bounces right into `StB`, which walks back over the
  1s just laid -- and it splits into `dep0`/`dep2` by the symbol the bounce
  lands on.  Check every gadget over ALL `(L,R)` with `|L|,|R| <= 4` before
  writing it.  `CountersW15_Corruption.v` pins the trap: on `dep2`'s
  context, six steps land MID-SWEEP in `StB` with `dep0`'s left list
  already built -- exactly what a window search calls a match.
- **`dep0` is stated through `chd`/`ctl`, so the SPAWN is free** -- the new
  stripe past the end of the list is not a separate case.
- **New Coq trap:** a two-place inductive constructor that must see the SAME
  term in two argument positions (here `ScanC`'s `(2*b+2)` in both `bl` and
  `bl'`) will not `apply` when the two are only numerically equal.  `replace`
  the second into the first's shape, then apply; the `x = 2*b+2` side
  condition variants (`ScanD'`/`ScanC'`) handle the first.
- **Method held.**  `tools/counters/lap15.py` (gadgets EXHAUSTIVELY over
  `|L|,|R| <= 4`) and `tools/counters/asm15.py` (the lap replayed from the
  verified gadgets alone as pure list ops, diffed against the raw simulator,
  `p = 2..1199`) were green before any Coq.  `tools/counters/comp15.py` is
  new: it mirrors the COMPOSITION layer -- `Scan`/`btail`/`venc` arithmetic,
  `back_frame`, and the assembled lap -- and diffs it against the simulator
  including the step count and the fact that NO earlier anchor occurs inside
  a lap.

STATE: (4,2) holdouts 4 -> 3 unproven (`census_holdouts_kept.txt` n
`closeout/frozen_unproven.txt`: fractal #3/#5, tower #20).  Merged
origin/main (the wave-16 RESIDUE track, PR #41) before the closeout regen,
so the number this board moves is `D_remaining` **883 -> 882**, not the
1,009 -> 1,008 it was against the pre-merge base.  `census_cache --check`
MATCH throughout (nothing under `theories/Census/` was touched).

**Next: tower #20 (`1RB0RD_1LC1LB_1RA0LB_1LC1RA`) -- RECONNOITRED here, and
it is much cheaper than BBB's decode suggests.**  `tools/counters/probe20.py`
(CTape-faithful mirror) and `tools/counters/lap20.py` (the checker) are new
and green.  John's reading -- "the record tape is a word over the blocks
`10`/`110`, a counter in another alphabet ... it looks very similar to #15
the way the head bounces off of the lsb and then passes through" -- checks
out on both halves:

  - **same sampling as #15/#32**: the LEFT RECORD, `StC`, reading blank, left
    list empty.  After a 3-record boot (t = 4, 18, 28) the family settles at
    t = 50 and STRICTLY ALTERNATES between two leads over the same tail `T`:
    `(StC, ([], S0, 1 1 0 1 0 ++ T))` and `(StC, ([], S0, 1 0 1 1 1 1 0 ++ T))`
    -- #15's alternating lead verbatim, over 606 anchors;
  - **rule A is a CONSTANT 10-STEP UNIFORM WINDOW** (A-type -> B-type),
    checked over all 511 tails with `|T| <= 8`.  Both left lists are empty so
    there is no `L` to quantify over.  #15's `ruleA` again;
  - **John's alphabet is right**: the tape after the lead factors greedily
    into `110` (`b`) and `10` (`a`), and when the residue is exactly `1` the
    WHOLE tape is a block word -- those are the sparse "tower" anchors
    (t = 142, 626, 1750: `babbaaab`, `bab^8abaaabb`, `bab^16ababbabbbb`).
    That is BBB's `pat ++ (2)^r ++ [1]` with the macro symbol `2 = 110`;
  - **the counter is unary in `b`**: at every A-type anchor the block word
    begins with a run of `b`s and THAT RUN LENGTH IS THE LAP INDEX --
    0,1,2,3,... with no exceptions over the 303 A-anchors reachable in
    400,000 steps.  One long lap is `r -> r+1`.

So the abstract state is `(r, rest)` and the closer should be FREE:
`WaveCounter.wglue_neverqh` takes an arbitrary anchor type with a total
successor and a preserved invariant -- the same closer double #32 used.  **No
closed form for `rest`, and no port of BBB's 14-template FSM, is needed for
`NeverQuasiHaltsSt`**; that FSM is BBB's route to a step-count BOUND, which
is not what we need.

  - **four gadgets of the long lap are already EXHAUSTIVELY checked** over
    every `(L,R)` with `|L|,|R| <= 4` (961 contexts -- the standard #15's
    deposit failed on 496 of):

        out5    (StC,(L,S0,       1 1 1 0 ++ R)) -5-> (StC,(1 0 1 ++ L, S0, 1 ++ R))
        cross5  (StC,(L,S0,       1 1 0 1 ++ R)) -5-> (StB,(1 0 1 ++ L, S1, 1 ++ R))
        ret3    (StB,(1 1 0 ++ L, S1,        R)) -3-> (StB,(L, S0, 1 1 1 ++ R))
        ret2    (StB,(1 0 ++ L,   S1,        R)) -2-> (StB,(L, S0, 1 1 ++ R))

    -- #15's shape exactly: the outward sweep eats four cells and hands one
    back (net +3 per five steps), `cross5` is the turnaround into StB, and
    the return is ONE STEP PER CELL filling with 1s.  The two remaining
    joints (B0 = 1LC, C1 = 0LB) read `chd L`, so like #15's they have to be
    stated through chd/ctl rather than as windows.

WHAT IS LEFT is the ASSEMBLY: which gadget fires where along the block word,
the invariant on `rest` the sweep needs, and the step count (the long lap
costs 36, 56, 52, 72, 68, 84, 84, 124, ... for r = 1,2,3,...).  It is #15's
job again, one size up.  **Do NOT write Coq from a sampled check** -- that is
the trap #15 paid for, and #20's sweep has the same bounce-and-walk-back
shape that made #15's deposit a SWEEP and not a window.  BBB's decode is in
`docs/HOLDOUTS_MXDYS_SN.md` section 5b under "tower #20".

<!-- --- fractal front CLOSED --- -->

## 2h. Wave-19 (2026-07-27) -- BOTH fractals boarded; the family is CLOSED

Full write-up: `docs/HOLDOUTS_FRACTAL.md`.  The two BBB `fractal` certs
(#3 `1RB0LA_1LC0RD_0LB1LA_0RB1LA`, #5 `1RB0LA_1LC1RD_0LC1LA_0RD0RB`) --
the pair for which **BBB had no proof to port** (its own soundness note:
the all-j closure "evidences but does not by itself mechanise the all-j
induction; that full rigor is the parallel Coq formalisation") -- now
carry kernel-checked `NeverQuasiHaltsSt` theorems.
`theories/Machines/Counters/Fractal_3.v`, `Fractal_5.v`, negative
controls `theories/Tests/CountersFractal_Corruption.v`, both axiom-clean.
`D_remaining` **882 -> 880**; the `fractal` family is CLOSED and the
(4,2) holdouts are **1** (tower #20).

**The decode in one line: both machines are BINARY COUNTERS WHOSE DIGITS
ARE BLOCKS.**  At every state-`B`-reading-blank the left half-tape is

```
#5 :  0^z      ++ 1   ++ b_0^1 ++ b_1^2 ++ .. ++ b_{j-1}^(2^(j-1))
#3 :  0^(2z+2) ++ 1 1 ++ b_0^2 ++ b_1^4 ++ .. ++ b_{j-1}^(2^j)
```

with `b_*` the binary digits of `z`: digit `i` occupies `2^i` cells
(`2^(i+1)` for #3).  One macro-step increments `z` and eats one blank on
the right (two, for #3).  A carry of length `m` is not a gadget -- it IS
the machine one level down.  That is the fractal, and it is why

```
#5   anchor (StB, (0^(2^k-1) ++ 1^(2^k), 0, [])) at 2*4^k - 2^k,
     lap 6*4^k - 2^k
#3   anchor (StB, (0^(2^k)   ++ 1^(2^k), 0, [])) at 9,31,111,403,...,
     lap 3*4^k + 4*3^k - 2^k
```

**Why they were boardable at all:** #3's lap carries a `3^k` term, so NO
certificate in the repo can express it (`LapDecider`'s `srun` is affine
in `j`).  `LapGlue`'s lap obligation is
`exists n, csteps tm n (Cf p) = Some c' /\ ...` -- an existential -- so
the cost is never written down.  This is `NestedLap.v`'s observation
("the lap obligation never mentions the cost"), and it generalises well
past its own family.  **Reach for it whenever a decode produces an exact
cost the certificate language cannot say.**

**The lever to reuse:** a mutual induction on the LEVEL where one rule
carries a FREE parameter that never constrains its own hypothesis
(`E2 q a b`'s `b`, for #5).  That is exactly mxdys' device in busycoq
`FractalType0.v` TM48 (`P1' n` with free `m`) -- the machine mxdys
flagged as similar to #5, and its transition table really does line up
with ours cell for cell.  With the free parameter the induction closes
with ZERO leftover glue:

```
SW(2q)  =  SW(q)[low half] ; inc1 ; INC(q) ; SW(q)[high half]
```

exact in shape AND in step count.  What ports from busycoq is the SHAPE,
not the text; and we close with `LapGlue.glue_neverqh`
(`NeverQuasiHaltsSt`), where TM48 closes with
`sigma_score_unbounded_nonhalt` (non-halting only).

**Try this on tower #20 next.**  Section 2g's handoff says #20 is #15's
shape one size up; but its record tape is a word over the blocks
`10`/`110` (section 2d), i.e. a counter in ANOTHER ALPHABET -- which is
the same sentence as "digits are blocks", one alphabet further out.  The
`Fractal_3.v` variant (two cells per digit) is already the general shape;
read #20's record word as digits before writing a table interpreter.

Reproduce every measurement with `python3 tools/counters/fractal_probe.py`
(all gadgets differentially validated over random left/right frames and
every level to 2^7 / 2^6; prints `ALL OK`).

<!-- --- tower #20: the last (4,2) holdout --- -->

## 2i. Wave-19 (2026-07-27) -- tower #20: assembly green, Coq to the middle

`tools/counters/asm20.py` (new, green), `theories/Machines/Counters/Tower_20.v`
(new, compiles, `Print Assumptions` clean).  **#20 has NO
`NeverQuasiHaltsSt` theorem yet**, so it is still a holdout: `D_remaining`
stays **880**, `census_cache --check` MATCH, closeout audit OK.  Nothing
under `theories/Census/` was touched.

**With section 2h's fractals boarded, tower #20 is the LAST (4,2) holdout.**
It is the only one of the three left in `tools/closeout/frozen_unproven.txt`
and the only one with no row in `tools/counters_manifest.tsv`.  Boarding it
closes the list.

**THE ASSEMBLY IS DONE AND IT IS THE GATE THAT WAS MISSING.**
`tools/counters/asm20.py` replays one lap from the verified gadgets alone as
PURE LIST OPS and diffs it against the raw simulator -- configuration AND
step count AND that the b-run increments -- for every anchor reachable in
400,000 steps, plus the check that no earlier left record occurs inside a
lap.  Green.  The lap is:

    B(r,rest) = (StC,([],S0, 1011110 ++ b^r ++ rest))       b = 110, a = 10

  1. `entry10` -- a uniform 10-step window -- leaves the left debris
     `E = [1;0;1;0;1;1]` and `R = 1 ++ b^r ++ rest`;
  2. `out5^r` eats the b-run one block at a time, laying `[1;0;1]` per
     block, so the left list becomes `lay r E = (101)^r ++ E`.  That
     `(101)^r` is John's "repeated 101" -- the empty bouncer body -- and it
     is confirmed exactly;
  3. **the MIDDLE**, which runs on into `rest` and turns around;
  4. **the RETURN**, the re-encoder: `rb3` eats `[1;0;1]` and emits `b`,
     `rb2` eats `[0;1]` and emits `a` -- ONE BLOCK PER UNIT.

**Where the +1 comes from, and it is free.**  Phase 4 over `lay r E` emits
`b^r` and then, off `E`, `b`, `a`, `b`.  Emissions PREPEND, and
`b ++ a = 1 1 0 1 0` is exactly the A-type lead, so the tape comes out as
`leadA ++ b^(r+1) ++ ...`.  **The spare `b` in the entry debris IS the
counter's increment.**  This is `bk_layE`, and it is proved.

**Two new gadgets**, both checked EXHAUSTIVELY over all 961 `(L,R)` with
`|L|,|R| <= 4` before being written (`tools/counters/lap20.py`'s
`exhaustive`):

    rb3   (StC,(1 0 1 ++ L, S1, R)) -3-> (StC,(L, S1, 1 1 0 ++ R))
    rb2   (StC,(0 1   ++ L, S1, R)) -2-> (StC,(L, S1, 1 0   ++ R))

The `retB3`/`retB2` written in the previous handoff are NOT the gadgets that
fire; they are the same three/two steps entered one cell earlier.  Use
`rb3`/`rb2`.  The sweep's last unit is `rb3e` (`L = [S1]`), which lands on
the new left record -- stated separately rather than through `chd`/`ctl`,
which is enough because `Rev`'s base case is `[S1]`.

**WHAT COMPILES** (`theories/Machines/Counters/Tower_20.v`, wired into
`_CoqProject`, NOT into `tools/counters_manifest.tsv` -- it has no theorem
to name):
- the eight single-step joints, through `chd`/`ctl`;
- the six gadgets as one-line `reflexivity` lemmas;
- `ruleA`: the whole no-carry lap, a constant 10-step window, uniform in the
  tail, both left lists empty so there is no `L` to quantify over;
- `entry10`, `out5s`, and `lapB_pre` composing them.  **After `lapB_pre` the
  configuration is `(StC, (lay r E, S0, S1 :: rest))` and NEITHER component
  mentions `r` again** -- this is the structural fact that makes the rest of
  the proof `r`-free;
- the return sweep as ONE inductive relation carrying both directions:
  `Rev W` (the units the sweep eats) with `bk` carrying the emitted word
  alongside, and `retsweep` a single induction over `Rev`.  `RevP`/`enc`/
  `bk_app`/`rcost_app` split it at the middle's debris;
- `lapB_post`: **the entire post-middle half of the lap, for ANY `RevP`
  debris `D`** -- `csteps (pcost D + rcost (lay r E)) (StC,(D ++ lay r E,
  S1, R)) = Some (CfA (S r, enc D R))`;
- `vis20` (all four states within four steps of the anchor) and `boot20`
  (t = 50, `vm_compute` + `ceqb_lift`).

**WHAT IS LEFT IS EXACTLY ONE LEMMA, AND IT IS MEASURED.**  The middle:

    forall rest, exists n D R', RevP D /\
      csteps tm_20 n (StC, (M, S0, S1 :: rest)) = Some (StC, (D ++ M, S1, R'))

**uniform in `M`** -- verified: the middle never reads below its own debris.
`D` is `RevP`-shaped in every lap measured.  Feed it to `lapB_post` and the
lap closes; `nextA (r,rest) = (S r, enc D R')`.

**AND THE MIDDLE IS #15's CARRY AGAIN.**  Write `rest` as `1^n1 0 1^n2 0
...`.  Because the head enters on a 1 the run it actually reads is `n_i + 1`,
so:

  - `n_i` EVEN -> the run read is odd, the sweep rides over it and continues;
  - `n_i` ODD  -> the run read is even, and that is the TURNAROUND.

**So the bits are the run lengths of `rest` mod 2, the carry rides over the
EVEN runs, and it stops at the first ODD one** -- #15's `Scan` with "even"
and "odd" swapped.  The lap index `r` is the leading b-run, i.e. the leading
2s of the run-length word.  Measured shape (`rest` run-lengths -> next,
debris, cost):

    [1,4]            -> [7]            D empty      8      n1 odd: turn at once
    [1,1,1,2,1]      -> [4,1,2,1]      D empty      8
    [1,2,5,1]        -> [5,5,1]        D empty      8
    [7]              -> [1]            D = baaa    11
    [4,1,2,1]        -> [5,1]          D = ba      15      n1 even: ride one
    [5,5,1]          -> [8,1]          D = aa      12
    [4,8,1]          -> [1]            D = bbaaaba 23      ride two
    [4,4,2,4,2,2,1]  -> [1]            D = bbbbabbaba 41

`n1` odd is a CONSTANT 8-STEP WINDOW (`[1,x,T] -> [x+3,T]`, no debris) --
that is the `cross5 ret2 bc` branch, and it is half of all laps.  Reproduce
the table with the middle-extractor pattern in `asm20.py`.

**Traps, in addition to #15's (which all still apply).**
1. The `A`-type and `B`-type leads are `1 1 0 1 0` and `1 0 1 1 1 1 0`;
   `ruleA` connects them in 10 steps and it is `reflexivity`.  Do not try to
   make one lap go A -> A directly: rule A and the long lap are separate.
2. `bk`'s base case emits a block (`S1::S1::S0::R`), so `bk` does NOT split
   as an accumulator over `++`.  That is what `RevP`/`enc`/`pcost` are for --
   `rcost (D ++ W) = pcost D + rcost W`, no subtraction.
3. Do NOT anchor at the "tower" configurations (t = 142, 626, 1750).  John's
   `110`/`111110`/`101010` block reading parses those cleanly and only those
   -- the dense A-anchors leave a residue.  Confirmed this session; the
   dense StC left-record family is the one with the `+1` lap.
4. Do NOT port BBB's 14-template FSM.  It is TRUE, and it is BBB's route to
   a step-count BOUND, which `NeverQuasiHaltsSt` does not need.

**THE ABSTRACT SUCCESSOR IS NOW CLOSED FORM AND VALIDATED**
(`tools/counters/nv20.py`, and the abstract-state section of `Tower_20.v`).
The state is just the RUN-LENGTH WORD `w` of the anchor's tail -- there is no
separate lap index, because the leading b-run IS the leading run of 2s
(`b = 110 = 1^2 0`; `wruns_blks`/`CfW_blks` bridge to the `blks`/`lay`
machinery already proved).  And

    nv  w           = 2 :: nv0 w              -- the leading 2 is the +1
    nv0 (n :: t)    = 1^(n/2-1) ++ 2 :: nv0 t                    n EVEN
    nv0 (n :: [])   = 1^((n-1)/2) ++ [2; 1]                      n ODD
    nv0 (n::n2::t2) = 1^((n-1)/2) ++ (n2+3) :: t2                n ODD

`nv0` is a STRUCTURAL recursion on the list, so `nv` is total -- no fuel and
no closed form for the tape is needed for `wglue_neverqh`'s `nextA`.  It
reproduces the orbit's A-anchor word for all 302 laps reachable in 400,000
steps AND on 25 synthetic anchors the orbit never visits; Coq's `nv`
`Compute`s the same chain, `[1;4] -> [2;7] -> [2;2;1;1;1;2;1] -> ...`.

**THE ONE OPEN POINT IS THE INVARIANT, AND IT IS A REAL STEP.**  The lap
needs the sweep to TURN, i.e. `w` must contain an ODD entry -- beyond the
tape's end every run has length 0, which is EVEN, so an all-even word sends
the head rightward for ever.  "Contains an odd" is true on every reachable
word (3000 laps of `nv` from `a0 = [1;4]`) but is NOT preserved by `nv` on
arbitrary words, and `nv20.py` records witnesses refuting the three natural
strengthenings:

    contains an odd            nv [5;1] = [2;1;1;4],  nv that = [2;2;4;4]
    last entry is 1            nv [3;1] = [2;1;4]
    last = 1 and the first
      odd is not 2nd-to-last   nv [1;1;2;3;1] = [2;4;2;3;1]

So `[5;1]` and `[3;1]` are simply not reachable, and the invariant has to say
why.  This is the analogue of #15's even-popcount discovery -- that one was
also the session's real idea, not a transcription.  A promising angle: the
turn copies `t2` (the word beyond the first odd's successor) VERBATIM, and
the turn-with-nothing-beyond case always appends `[2;1]`, so every reachable
word's tail is inherited; an invariant phrased on the INHERITED SUFFIX rather
than on the whole word is the shape to try.

**Then, and only then**: the ride/turn windows and the middle induction
(mechanical -- ride is `(StC,(M,S0,S1::wruns (n::t))) -(n+3)-> (StC, alt(n/2)
++ M, S0, S1::wruns t)` with `alt k` the alternating word of length `2k+1`;
the turn is the four-step `StB` walk-back derived above), then
`wglue_neverqh` at `w0_20 = [1;4]` (`boot20_W` is already proved), corruption
controls in `theories/Tests/` in `CountersW15_Corruption.v`'s tradition, then
`tools/counters_manifest.tsv`, `gen_stages.py`, `tools/closeout/audit.py`,
and `make -f Makefile.coq -j2 theories/Closeout/Closeout.vo` (`-j2`, NOT
`-j4`).  That takes `D_remaining` 880 -> 879 and **CLOSES the (4,2) holdout
list** -- #20 is the last one.

  [MERGE NOTE, added when the two 2026-07-27 tracks were merged.  They are
  DISJOINT -- the sections above board HOLDOUTS, section 2j boards RESIDUE --
  and the generated closeout tables were REGENERATED over the union rather
  than hand-merged, which is the only correct way to resolve a conflict under
  `theories/Closeout/`.  The joint figure is **D_remaining = 622**; every
  per-track number above and in 2j is that track's own and is superseded by
  it.  `audit.py` OK, `census_cache --check` MATCH, and the MERGED closeout is
  KERNEL-VERIFIED: `Closeout.vo` + all 46 `CB_*.vo` compile, `closeout_partial`
  is Qed at `functional_extensionality_dep` only, and
  `vm_compute (List.length remaining_rows)` = 622.]

## 2j. Wave-18, RESIDUE track (2026-07-27) — THE TASK lands: 258 boards

Full write-up: `docs/WAVE18_FINDINGS.md`.  Took **THE TASK** of the wave-15
and wave-16 prompts — the `AFFINE`/`EXP2` bucket, 500 of the 883 unproven
rows, whose overflow lap costs `Θ(2^j)` — and produced its first boards.

- **`D_remaining` 883 → 625; 4,531 / 5,156 = 87.9% settled** (from 82.9%).
  258 `NLAP_*` boards, every one `functional_extensionality_dep` only
  (checked per board), `audit.py` OK, `census_cache --check` MATCH.  The
  closeout is KERNEL-VERIFIED: `Closeout.vo` + all 46 `CB_*.vo` compile,
  `closeout_partial` is Qed at `functional_extensionality_dep` only, and
  `vm_compute (List.length remaining_rows)` = 625.  (`CloseoutFinal.v` still
  cannot be built in a container -- OCaml 4.14.2 census `.vo` vs 4.14.1 apt
  coq; WAVE16 section 4b.)
- **The blocker was wave-16's acceptance test, one level down.**
  `docs/NESTED_LAP_PLAN.md` had Stage A and Stage B done and Stage C stuck at
  "boot chain 1 of 12, and it is NOT a search budget".  That was true; the
  cause was the line three below it — *"9 cells, real is 11"*, i.e. the chain
  lands two TRAILING BLANKS past the inner anchor.  `nestboot.py` was written
  in wave-15 and calls `derive_chain` with the wave-16 flag's `False` default.
  Measured 2×2 (`tools/counters/nestboot2.py`, 30 machines, boot AND exit):
  best key + exact joints 5/30, every key + exact 7/30, best key + `lift`
  9/30, **every key + `lift` 17/30** — and on all 17 the inner family's own
  interior lap derives too.
- **New Coq is one additive file**, `Counters/NestedLapLift.v`:
  `inner_to_fill_lift` (NestedLap's induction in `stepn`/`lift` space, where
  the `Θ(2^j)` stays inside an `exists n`), `nested_overflow_lift` (pulled
  back to one `csteps` run by `LapCertGlueLift.stepn_csteps_at`),
  `vis_via_fill` (a state firing only in the EXIT half is still visited —
  8 of 30 need it) and `cview_fill_pow2`.  `LapDecider.v`, `LapGlue.v`,
  `LapCertGlue.v` and `NestedLap.v` are UNTOUCHED, and the nested route is a
  FALLBACK inside `emit_lapcert.derive`, so no existing board changes
  (regression: 39 of a 40-board sample re-derive; the one that does not fails
  identically on the pre-change tools).
- Emitter `tools/counters/nestcert.py`: inner-family search with keys
  ENUMERATED not ranked, the three chains, and a differential validation that
  replays every piece against the raw simulator — including each of the 246
  inner laps at `j = 2..7`, not just the endpoints.
- **DO NOT RETRY:** a wider inner-key tail.  `maxtail = 6` finds a family on
  13 of 40 machines that report "no inner family" at 3 (and `K ∈ {5,6,7}`
  changes nothing), but re-running the whole 299-machine failure set at 6
  boards ZERO — the 33 machines it unlocks all fail on the boot or exit chain.
  Key counts are 0-4, so `maxkeys` was never binding either.
- **THE LESSON, and it is wave-16's surviving a level of abstraction:** when a
  fix lands as a **defaulted flag**, grep for every caller of the function,
  not just the one that motivated it.  Two waves of "the boot is not a search
  problem" were spent on a call site that had never been revisited.
- Failure profile after the first 225 (at `D_remaining` = 658): 265 no inner family at `pow2 j`, 211 no overflow
  phase (the no-anchor bucket), 111 no exit chain, 105 no interior chain
  (QUAD 41, HIGHER 13, PARITY 13, EXP3 10, EXP4 6, AFFINE/AFFINE 14, EXP2 8),
  28 no anchor, 22 no boot chain, 15 no visit witness, 4 no inner interior.
- **AND THE TWO CHAIN BUCKETS ARE EXPONENTIAL, NOT SEARCH GAPS** (WAVE18 §4b).
  Measured the way `ovfshape` measures a lap, at the inner key the emitter
  actually selects: `no exit chain` is 0 AFFINE / 24 EXP on a 24-machine
  sample; `no boot chain` is 2 AFFINE / 14 EXP on 22.  No `srun` can express
  an exponential half, so no `derive_chain` widening can reach them.  What is
  wrong is the inner family's IDENTIFICATION: an exponential exit says the
  inner counting does not stop at `fill (pow2 j)`, an exponential boot that it
  did not start at `pow2 j`.  `NESTED_LAP_PLAN` §3 predicted exactly this
  ("a SUBSEQUENCE of a longer count satisfies that too").
- **AND THAT WAS BUILT TOO.**  Splitting the phase at the first inner fill and
  searching the second half finds a SECOND consecutive family on 11 of 16 --
  same state, same alphabet, SHIFTED TAIL.  That is mxdys' sync bouncer
  counter ("count 8->15, shift, count 8->15 again").  It needed ONE new lemma
  (`Counters/NestedLap2.boot_via_fill`, 12 lines) because
  `nested_overflow_lift`'s `Hboot` is an ARBITRARY `csteps` run: instantiate
  at the SECOND family and fold the first count into the boot.  **33 more
  boards; `D_remaining` 658 -> 625.**  What is left of that bucket is 8 "no
  shift chain" + 5 "no second exit chain".

## 2k. Wave-20 (2026-07-27) -- tower #20: the MIDDLE is proved; the invariant

`tools/counters/mid20.py` and `tools/counters/inv20.py` (both new, both
green), `theories/Machines/Counters/Tower_20.v` extended (compiles,
`Print Assumptions` clean).  **#20 still has NO `NeverQuasiHaltsSt`
theorem**, so it is still the last (4,2) holdout.  This wave boards
NOTHING: `D_remaining` is unchanged by it, and after the merge with the
RESIDUE track (2j) that figure is **622**, not the 880 this branch was cut
at.  `census_cache --check` MATCH, closeout audit untouched, nothing under
`theories/Census/`.

**THE MIDDLE -- section 2i's "exactly one lemma" -- IS DONE.**  The whole
long lap is now Qed for every tail that HAS an odd entry:

    lapB_full_ne : Forall (fun x => x <> 0) K ->
      csteps tm_20 ((10 + 5*r) + ((rcostK K + (2*k+8))
                    + (pcost (Dmid K k) + rcost (lay r E))))
        (CfB (r, wruns (wev K ((2*k+1) :: S n2 :: t2))))
      = Some (CfA (S r, enc (Dmid K k) (wruns ((S n2 + 3) :: t2))))

plus `lapB_full_z` for the nothing-beyond branch.  `wev K t` is the word
whose even prefix is `2k` for each `k` in `K`, so the hypothesis IS the
decomposition "(even prefix) ++ (odd entry) ++ (rest)" -- i.e. the sweep
turns -- and nothing else is assumed.

**How it is built** (all `reflexivity` or one induction each):
- five new joints, each checked in its EXACT stated form over all 961
  `(L,R)` with `|L|,|R| <= 4` before being written -- `ad2` (the two-step
  `A`/`D` stride), `fin2` (the ride's exit back into `StC`), `turn3`
  (`A0 = 1RB`, the bounce into `StB`), and the two walk-backs `wb4`/`wb1`.
  `ad2`, `wb4`, `wb1` READ the context, so -- trap 2 -- they are stated
  through `chd`/`ctl`;
- `walk`: the `A`/`D` stride iterated, ONE induction, uniform in the tail
  `Z`, so the SAME lemma serves the ride and the turn.  That uniformity is
  the whole trick -- the two cases differ only in what `Z` starts with;
- `ride`: `n = 2k` EVEN, a constant `n+3` steps, debris `(1 0)^k 1`.
  `out5` is the `k = 1` case and `k = 0` is a bare three-step window;
- `turn_bounce` at step `2k+4`, then `wb4` (next run nonempty) or `wb1`
  (next run empty, or the tape ends -- `chd [] = S0`, so it is the SAME
  branch, not a third one).  **The `n2+3` of the successor is the four 1s
  the walk-back lays, minus the one it consumed** -- `turn_ne` reads it
  straight off the tape;
- `rides`: the whole even prefix in one induction over `K`;
- `Dmid`/`Dmidz` and `RevP_Dmid`/`RevP_Dmidz`: the debris is `RevP`, so it
  drops into the already-proved `lapB_post` with no new sweep reasoning.
  **`RevP` needs every ridden run nonempty** (`dbl 0 [S1] = [S1]` is `Rev`'s
  TERMINAL unit, not a prefix unit, so a `0` entry breaks the decode) --
  that is this family's `Forall (1 <= _)`, the same side condition
  `WaveCounter` carries.

**THE INVARIANT IS STILL THE ONE OPEN POINT, AND IT IS DEEPER THAN IT
LOOKED.**  `inv20.py` establishes -- each check runs, none is a conjecture:

1. **The alphabet is finite**: every entry of every reachable word is in
   `{1,2,4,5,8}` (`7` occurs once, at lap 1, and never again).  `1` and `2`
   are FRESH, laid by the return sweep; `4 = 1+3`, `5 = 2+3`, `8 = 5+3` are
   BUMPED, and an entry is bumped at most twice (`1 -> 4`, `2 -> 5 -> 8`).
   Alphabet closure is exactly "the entry just after the first odd is in
   `{1,2,5}`".
2. **The leading 2-run is the lap index**: `nv (2^r ++ v) = 2^(r+1) ++ nv0 v`,
   so aliveness does not depend on `r` at all.
3. **POOR is a 2-lap invariant.**  Call `2^a ++ [1] ++ t` POOR.  The image
   of a POOR word has an odd IFF `Cond(t) = hasodd(X t)`, and two laps later
   the word is POOR again with tail `T(1::u) = 2 :: nv0 u`,
   `T(2::u) = 1 :: nv0 (1::u)`, `T([]) = []`.  One map, one obligation.
4. **THE ENGINE.**  With `E(u)` = "last entry odd" and `B(u)` = "the first
   odd sits at `|u|-2`",

        E(u) /\ ~B(u)  ==>  E(nv0 u)

   (200,000 random words, 9-letter alphabet).  So `E /\ never-B` suffices,
   and the obligation drops from the semantic "hasodd for ever" to the
   SYNTACTIC "never B" -- a condition on ONE position.  This is the real
   handhold; use it.
5. **The system is SELF-SIMILAR, and that is why every natural candidate
   fails.**  The phase is 4-periodic -- `2^r ++ [1;1] ++ U`, `2^r ++ [4] ++ U`,
   `2^r ++ [1;2] ++ nv0 U`, `2^r ++ [5] ++ nv0 U` -- and

        U_{k+1} = X(nv0 U_k),   and with U = 4::x,   U_{k+1} = 4 :: nv x.

   **FOUR LAPS AT ONE LEVEL ARE ONE LAP ONE LEVEL DOWN**, and `hasodd` at
   the `r = 3 mod 4` phase is exactly `hasodd` of the level-below word.  The
   obligation reproduces itself: there is no finite descent, and no
   bounded-depth predicate can close (deepest death over the 5-letter
   alphabet at `|v| <= 5` is 111 laps).  That also kills the hope that the
   maximal invariant is regular.

**REFUTED, with witnesses, each by exhaustive CLOSURE checking over the
5-letter alphabet to length 8 plus tens of thousands of random words** --
never by sampling the orbit.  `inv20.py` re-runs all of these; if one ever
comes back NOT REFUTED it is the invariant and the file is out of date:

    contains an odd                     nv [1;1] = [2;4]
    ends in 1                           nv [1;1] = [2;4]
    ends in 1, first odd not at |w|-2   nv [1;2;1] = [2;5;1]
    the Scan/After DFA                  nv [4;1] = [2;1;2;2;1]; it also
                                        REJECTS the reachable lap-3 word
                                        [2;2;2;4;1;2;1] outright
    alphabet & (rich | >= 2 odds)       nv [1;1] = [2;4]
    ends [2;1] & d != 2                 nv [1;2;2;1] = [2;5;2;1]
    ends [2;1], d not in {1,2}, plus
      the POOR/odd-head refinements     nv [5;2;2;1] = [2;1;1;5;2;1]

(`d(x)` = the number of entries after the first odd.)

**WHERE TO GO NEXT, in order.**
1. The LEVEL-1 orbit is visibly better behaved than the level-0 one: over
   3000 laps it always ends `[2;1]` and its `d` is never 1 or 2 (level 0
   ends `[2;1]`/`[5;1]`/`[8;1]` and does hit `d = 2`).  Anchor at level 1
   and the candidate `ends [2;1] /\ d not in {1,2}` survives 2000 laps --
   it fails closure only on words the orbit does not reach.  Closing that
   gap IS the problem, but the level-1 formulation is much the smaller one.
2. Because of (5), do not look for a regular/DFA invariant or a
   bounded-depth one; both are ruled out above.  The shape that fits a
   self-similar system is a predicate defined by well-founded recursion on
   the DESCENT (level `k` to level `k+1`), or a `CoInductive` safety
   predicate discharged by a productive `cofix` -- four laps of finite
   obligations per level, then the next level.  Either way what is needed
   is an invariant for the DESCENT map, not for `nv`.
3. Only after that: `wglue_neverqh` at the level-1 boot (recompute `t0` --
   `boot20_W`'s `vm_compute` pattern works at any `t`), corruption controls
   in `theories/Tests/`, `tools/counters_manifest.tsv`, `gen_stages.py`,
   `tools/closeout/audit.py`, `make -f Makefile.coq -j2
   theories/Closeout/Closeout.vo` (`-j2`, NOT `-j4`).

**Traps added this wave.**
1. The turn's bounce is at `2k+4`, NOT `2k+3` -- `cross5` (5 steps for
   `k = 0`) is the bounce PLUS one `StB` step, which is why the off-by-one
   is easy to make and why `mid20.py` diffs the cost as well as the config.
2. `dbl 0 [S1] = [S1]` is not `RevP`.  Any ride over an EMPTY run (`n = 0`)
   breaks the return sweep's decode, so `Forall (fun x => x <> 0) K` is a
   real hypothesis, not bookkeeping.
3. State the lap costs RIGHT-NESTED (`a + (b + c)`), not `(a + b) + c`:
   `csteps_add` peels one `+` at a time and left-nesting makes the first
   rewrite land on the wrong split.

## 2l. Wave-21 (2026-07-28) -- tower #20 CLOSED; the (4,2) holdout list is DONE

`theories/Machines/Counters/Tower_20.v` now carries
`nqh_tower20 : NeverQuasiHaltsSt tm_20` (`Print Assumptions` =
`functional_extensionality_dep` only).  **`D_remaining` 622 -> 621**, the
manifest gains its row, and #20 is off `frozen_unproven.txt`.  With that the
**(4,2) HOLDOUT LIST IS CLOSED**: every wave/counter/holdout machine the
project set out to board is boarded.  `census_cache --check` MATCH,
`tools/closeout/audit.py` OK (exact partition), nothing under
`theories/Census/`.

**THE INVARIANT, found.**  Section 2k's open point was "an invariant that
holds at the boot, is preserved by `nv`, and implies `hasodd`".  Every
*closure predicate* candidate was refuted (2k) because the system is
self-similar and the level boots do NOT cycle -- they GROW (level `2j+1` is
`[1;1] ++ 2^(2j+2) ++ [1]`, level `2j+2` is `[1;5] ++ 2^(2j+1) ++ [1]`).  The
fix is not a predicate but a **finite descent DESCRIPTOR** -- a mutual
inductive grammar `Vd`/`Ud` with:

- `decV`/`decU` decoding a descriptor to a run-length word;
- `stepV`/`stepU` the successor ON descriptors;
- `nv0 (decV v) = decV (stepV v)` and `Xf (nv0 (decU u)) = decU (stepU u)`
  (`nv0_dec_mut`, one mutual induction over 15 cases; the four phase maps
  `[1;1]++U -> [4]++U -> [1;2]++nv0 U -> [5]++nv0 U -> [1;1]++X(nv0 U)` are
  unconditional identities of `nv0`);
- every decode is alive (`existsb Nat.odd`) and zero-free (`alive_dec_mut`).

The growth is captured by the `UDD a v` constructor (a `4 :: 2^a ++ decV v`
block whose `stepU` bumps `a` and steps the nested `v`): the "obligation
reproduces itself" of 2k is exactly the nesting recursion, and it is
WELL-FOUNDED on the descriptor, so no cofix is needed.  The boot is `VA0`
(`decV VA0 = [1;4]`), so `Cf20 (0,VA0) = CfW [1;4]` and `Hboot20 = boot20_W`.

**The lap glue.**  `WaveCounter.wglue_neverqh` on state `(nat * Vd)`,
`Inv = fun _ => True` (aliveness is a theorem, not a carried hypothesis).
`Hlap20`: a general `decompose` writes any alive zero-free word as
`wev K ((2k+1) :: rest)`, then `lapA . lapB_full_{ne,end}`; the tape-output
`enc (Dmid/Dmidz K k) ...` is shown equal to `wruns (nv0 ...)` by
`enc_ne`/`enc_end` (a small `enc`/`rideW`/`arep` algebra: `enc_arep`,
`enc_app`, `enc_dblS`, `encride_core`).  The `rest = []` end-case lands one
cell short of a written `0`, so it closes up to a trailing blank via
`lift_app_blank` -- the only non-syntactic step.  `lapB_full_end` (turn on an
empty next run) is the one new lap lemma this wave; `lapB_full_ne` already
existed.

**Reconnaissance / validation tools.**  `tools/counters/inv20.py` (the 2k
refutations, still valid as history -- the descriptor is not a closure
predicate so it is not among the refuted candidates) and the new
`tools/counters/desc20.py`, which validates the descriptor MIRROR: the
descriptor orbit reproduces the raw `nv` orbit word-for-word for 4000 laps,
the step identities hold on 20k random descriptors, and the `enc` word-
successor holds over 35k contexts.  All green.

**NOT done here** (compute-bound, not #20-specific): the full
`theories/Closeout/Closeout.vo` kernel re-check of all 4,535 boards -- it
recompiles the whole board tree and belongs on the box (`-j2`, see 2k step 3
and the CI note).  What IS verified in-container: `Tower_20.vo` clean, the
generated `cov_12_0094` cover lemma re-checks against `CloseoutKit` (clean),
`audit.py` OK, `census_cache --check` MATCH.

## 2m. Wave-22, RESIDUE track (2026-07-28) -- the nested route grows two ends

Full write-up: `docs/WAVE22_FINDINGS.md`.  **110 boards, `D_remaining`
621 -> 511** -- the first crossing of **90% settled** -- and every front is
EMITTER work only; wave-18's composition theorems were already general
enough.

- **The "no shift chain" 8: an overflow phase can chain ANY number of
  counts.**  The 13 shift/second-exit machines carry a THIRD (sometimes a
  FOURTH) count in yet another shifted frame.  `NestedLap2.boot_via_fill` is
  generic in `(Cc, Cin1, Cin2)`, so it composes with itself and each extra
  count is one more application -- no new Coq.  `nestcert._more_counts`
  (recursive, backtracking, `MAXCOUNTS = 4`) plus a list-of-families
  emission (assert-style boot stack, per-shift defs, multi-count `visx_`).
  8 of 13 board.
- **The 5 survivors are a MEASURED checker gap**: their exit's return sweep
  enters its rightward cycle mid-unit against a non-matching post, which no
  rotation lstep can align -- `SCycR` has no entry-offset `m` the way
  `SCycL` does.  Boarding them = a `LapDecider.v` extension (new lstep +
  soundness + corruption tests) or hand boards.  Do not re-run the search.
- **The "no inner family at pow2 j" 22: the OFFSET family, reindexed.**  The
  bucket's dominant cluster (95 of 162) is an inner count running
  `2^(j+1)+c .. 2^(j+2)-1` -- fill reached, START offset, block count `j-1`:
  the wave-15 index-shift trap.  What works: reindex the WHOLE overflow
  branch at `j = S j'` (every side an ordinary sside in `j'`),
  `v0 = xO (xI (pow2 j'))` fed to the UNCHANGED `nested_overflow_lift`,
  `fill (xO (xI (pow2 j'))) = fill (pow2 (S (S j')))` by `cbn`, the `j = 0`
  case one CONCRETE run (`lapo0_`, the bootstrap lemma's `ceqb` pattern),
  and per-state concrete visit witnesses at `p = 1` (`visz_*`).
  `nestcert.derive_offset`; 22 board, all axiom-clean.
- **Traps paid for**: the boot landing INHERITS `b` from its source's count
  (`SCycL` transfers it), so `gbo_` normalizes via
  `replace (1*j+b) with (j+b); rewrite rep_add` -- do not try chain surgery,
  nothing unfolds a count into a post.  And positive constructors wrap
  LSB-OUTERMOST: `2^(j+2)+2 = xO (xI (pow2 j))`.
- **The Mp-outer cluster (80 more boards): the SPLIT inner lap.**  The
  cluster's inner lap is affine (4i+2) but only chains in SPLIT form (the
  carry sweep's period sits one cell into the unit): Z chain at i=0 +
  peeled P chains at count i-1 -- wave-13's j=0 split, ported to the
  inner-family glue.  The boot lands in a SHIFT1 frame and the exit only
  derives from the REPHASED fill; both bridge through one pinned
  application of a board-local `rrc_` lemma over `WTape.rep_rot`.
- **Measured zeros** (do-not-retry): octave-only families
  (`pow2 (j+oct)`, no reindex) -- 0 of 162; the multi-count route on the
  65 "no exit chain" / 22 "no boot chain" -- 0 of 87 (WAVE18 section 4b
  stands: identification, not chains).
- Template hygiene: the new `gso_`/`geo_`/`viso_` holes default to the old
  text; a committed nested board re-renders BYTE-IDENTICALLY.

STATE: `D_remaining` **511** (90.1% settled); `census_cache --check` MATCH
throughout; `audit.py` OK.  Next, in measured order: the 15
no-visit-witness, the 41 QUAD/QUAD, the 235 no-anchor, the 65 "no exit
chain" (identification, not chains), and the 5 second-exit machines
(the SCycR-entry-offset checker gap).

## 2n. Wave-23, RESIDUE track (2026-07-28) -- the no-visit-witness bucket closes

Full write-up: `docs/WAVE23_FINDINGS.md`.  Took the ranked item (2) -- the
15 "no visit witness (StA is targeted)" machines -- and boarded **all 15**:
`D_remaining` **511 -> 496** (4,660/5,156 = 90.4% settled).

- **The missing invariant never had to be found.**  WAVE16 6b said the
  needed fact is symbol-aware ("StD never READS S1 after the boot") and "a
  real build".  It is not: the lap certificates already model the forward
  behavior exactly (mxdys' condition, quoted in `LapDecider.v`'s own
  header), so "StA never fires after the boot" is COMPUTABLE from the
  chains the boards already carry.  No invariant search, no closure, no new
  certificate data -- three `vm_compute` booleans per board.
- **New Coq, both additive:** `Checkers/LapAvoid.v` (axiom-FREE) --
  `wavoid` window-trace check, `cycL_avoid`/`cycR_avoid` (the cyc
  inductions carrying avoidance: one window check covers every iteration),
  `savoid`/`srun_avoid` mirroring `sstep`/`srun`, soundness at every `j`
  and tail; `Counters/LapGlueQuiet.v` (funext-only) -- `AvoidRun`,
  `bootquiet_chk`/`bootvis_chk` one-`vm_compute` bootstrap-window checks,
  and `glue_qh_quiet`: concrete-`t0` boot + StA-avoiding laps + visits for
  the rest + checked `(s0, t0)` window => `NonHalt /\ QHBound (S s0) /\
  QuasiHaltsSt` with the EXACT last-visit bound (4-11 on these).
  `LapDecider.v`/`LapGlue.v`/`LapGlueQH.v`/`LapGlueAbs.v` untouched.
- **Emitter:** the AVOID route in `emit_lapcert.py` (prefix `LAPQ_`),
  taken when the only missing witness is StA, `absorb_search` fails, and
  `avoid_probe` confirms the quiet shape.  `_mirrorize_qh` needed NO
  change; pre-/post-change emitters render committed boards
  byte-identically (checked).  All 15 derive on the mirror, boots 7-18,
  `s0` 4-11.
- **Controls:** `theories/Tests/LapAvoid_Corruption.v` -- a never-QH
  board's chain (which really fires StA) is REJECTED; state-sensitivity on
  the recurring states; window-overrun chains are false, not vacuous;
  boot window slid onto the last visit is caught; wrong visit index caught.
- **The route is not StA-specific**: `srun_avoid`/`glue_qh_quiet` take any
  state, so a future quiet-StB/C/D lap family is emitter work only.

STATE: `D_remaining` **496** (90.4% settled); `census_cache --check` MATCH
throughout; `audit.py` OK (exact partition); the closeout is
KERNEL-VERIFIED in-container (`-j2`): `Closeout.vo` + all 47 `CB_*.vo`
compile, `closeout_partial` Qed at `functional_extensionality_dep` only,
`vm_compute (List.length remaining_rows)` = 496.

**Same session, the CASCADE reconnaissance (John: "the biggest category is
counters; there is talk of having to deal with some exp to get them").**
Full brief: `docs/CASCADE_EXIT.md`; tool: `tools/counters/cascade_probe.py`.
The 65 "no exit chain" + 22 "no boot chain" machines were range-scanned at
their true endpoints: **72 of 87 are a DESCENDING-OCTAVE CASCADE** -- main
count `2^j..2^(j+1)-1`, then TWO counts per level `l = j-1 .. 2` with tails
growing one unit per level, then a closing sweep.  Steps Theta(2^j) (4b's
exponential, confirmed) but the count of counts is AFFINE in j -- why
MAXCOUNTS=4 bought 0 and families() never saw it (octaves >= 0 only;
MAXTAIL=3 vs ~2j-cell tails).  The build is a `NestedLapCascade` level
induction; `inner_to_fill_lift` is already arbitrary-`v0`, the level chains
are sside-uniform in `l`.

**Wave-24 BUILT it — this is no longer the next wave's task.**
`docs/WAVE24_FINDINGS.md`.  All three per-level chains derive as single-index
chains (B→A needed both framing knobs: one peeled unit for its turnaround,
and a split one cell deeper because its eat reads into the growing region);
`theories/Counters/NestedLapCascade.v` is the level induction, funext-only;
`tools/counters/cascade_emit.py` renders the overflow branch per machine and
**57 of the 87 gate and compile**.  Two structural corrections to the
reconnaissance above: the cascade descends to level **0**, not to level 2,
and the main count IS the level-`j` second count, so the phase is uniform
from level `j` down.

`D_remaining` is UNCHANGED at 496: an overflow branch is not a board.  The
next wave's THE TASK (`docs/RESIDUE_PROMPT.md` item 0) is BOARDING these --
a third route in `emit_lapcert.derive`/`render` beside `nested` and `offset`,
whose one new piece is the visit witnesses (`cascade_vis_at` is stated at an
arbitrary level, but only level 0 is available at every outer index).  The
41 QUAD/QUAD, 235 no-anchor and the 5 SCycR-gap machines follow.
**[DONE in wave-25, section 2o below: all 57 boarded, `D_remaining` 439.]**

## 2o. Wave-25 (2026-07-28) -- the CASCADE boarded: 57 boards, D_remaining 439

Full write-up: `docs/WAVE25_FINDINGS.md`.  PR #54 merged wave-24's build with
nothing on the board (deliberately -- §2n above); this wave is the boarding
it named as next.  **All 57 gated machines carry kernel-checked
`NeverQuasiHaltsSt` theorems** (`theories/Machines/Counters/CASB_*.v`, 34
direct / 23 mirror), every one accepted on the FIRST render, all
`functional_extensionality_dep` only.  `D_remaining` **496 -> 439** (4,717 /
5,156 = 91.5% settled).

- **The wiring was measured before it was written** (survey over the 87):
  every gated machine's interior derives as a SINGLE chain (9 exact, 48 up to
  `lift` -- the wave-16 template unchanged), every one boots, and the visit
  map came out exactly as §6 of the wave-24 write-up predicted: the boot
  chain hosts most witnesses and EXACTLY ONE state per board fires only in
  the closing sweep.  No split interior, no quiet state, no QH closer
  anywhere in the population.
- **The one new lemma shape is `visc_*`** -- the sweep-only state, reached
  from an overflow anchor through the whole cascade by
  `NestedLapCascade.cascade_vis`: the boot landing (`gbo_*`) as its first
  premise, `vis_of_run` on the sweep chain (through `gcl_*`) as its second.
  Per-level chains can NEVER host a universal witness (at j = 0 there is no
  descent), so the emitter searches only the boot chain and the sweep.
- **Everything else is composition, in `lift` space throughout**: closer
  `LapCertGlueLift.glue_neverqh_lift` on all 57, interior via
  `INT_ONE`/`GLUE_ONE`/`GLUE_ONE_LIFT`, mirror transfer via `mirrorize`,
  all unforked.  `cascade_emit.py` gained `derive_board`/`process_board`
  (`--board`/`--boards`), and `emit_lapcert.process` falls back to the
  cascade route after flat/nested/offset -- tried LAST, it is the most
  expensive derive.  `PROTO` split into `PROTO_DOC + PROTO_CORE` (the
  committed `CASC_*` regression re-renders byte-identically, checked).
  `NestedLapCascade.v`, `LapDecider.v` and every glue file untouched.
- The 30 non-gated are unchanged from wave-24's measurement: 12
  octave-shifted main counts (emitter work: `families()` already carries an
  `oct`), 17 one/two-count phases (the `no boot chain` mirror half plus the
  odd-shaped rows), 1 main count at 4..7.

**Same session, the OCTAVE-DOWN 12: 8 more boards, `D_remaining` 431.**
`docs/WAVE25_FINDINGS.md` §7.  The 12 "octave-shifted" non-gated rows are
not a shifted top level -- the WHOLE cascade sits one octave down, there is
no main count, and the close is one more ASCENDING count at octave j+1
(Θ(2^j) -- why no sweep chain ever derived) between two affine chains.
`oct = -1` variant through extractor and emitter (`reps_low`/`LOW_*`,
gated render byte-identical); the reindex + concrete-p=1 devices are the
offset route's, and the p=1 lap is real: these machines' outer-index-0
overflow has NO cascade.  8 of 12 boarded first-render, funext-only.  The
4 left: their closing count enters ONE VALUE IN (`xI (pow2 j)`), an
emitter lemma-pair away -- see the write-up.

STATE: `D_remaining` **431** (4,725 / 5,156 = 91.6% settled); closeout
regenerated (`make closeout`), `audit.py` OK, `Closeout.vo` + stages
kernel-verified in-container; `census_cache --check` MATCH throughout.

## 2p. Ladder Stage B's CLOSURE (2026-07-31) -- the first machine boarded, and the gate answered

_Branch `claude/stage-b-closure-wlrpey`.  Full write-up in
`docs/LADDER_PLAN.md` 4i; this is the lab-notebook version -- the traps._

**The number.**  `1RB1LC_0LC0RB_1LA1LD_1RC0LD` is boarded end to end and
`tools/closeout/audit.py` went **62 -> 61 core undecided**, 5073 -> 5074
settled.  Before this the ladder had proved a pile of RULES and zero
machines.

**Trap 1: re-certify, always.**  The row was handed over as "7 arms"; the
stored `ladder_fixture_cert.json` says 8; at HEAD with `--kmax 9` it is
**12**.  The fixture predates three sections now.  `valfam.py --spec ROW` is
31 s -- there is never a reason to trust a stored cert.

**Trap 2 (the big one): the certificate's arms are NOT the closure's arms.**
The prover's arms are multi-variable patterns; `sside` carries ONE symbolic
run, so `emit_ladder.py` boards each with every run length but one pinned to
its lower bound.  Each keeps one free run length and so covers infinitely
many strings -- but with the others pinned there is no argument that they
TOGETHER reach every string of every width, and the only coverage claim
behind them is the prover's enumeration to `kmax = 9`.  Feed them to a
kernel and the kernel has nothing to do but enumerate alongside it.

The fix is that the class arms are BUILT from the `Fam` record, not mined:
one interior arm per digit below the top, one fill arm.  **12 arms become 2,
and an enumeration to `kmax = 9` becomes `digs_decomp`.**  `emit_ladder.py` does this now; if
you are boarding a new family and the arm count does not collapse, something
is wrong.

**Trap 3: the fill arm's pre-materialisation is not optional and now has a
measurement.**  4h recorded it; this session checked it.  The canonical
`rep u (1*j+1)` form for the fill arm finds **no chain at all**.  The
`u ++ rep u j` form finds one in six steps.  Do not "clean up" the emitter's
`pre` materialisation.

**Trap 4: `vis_of_run` does not want a PREFIX of the arm's chain.**  On this
row the fill arm's chain has no prefix landing in state D -- D is inside a
`SWinL 13` macro step.  Any chain from the same anchor will do, and
`[SWin 2; SCycL 2 0; SWin 1; SWinL 1]` reaches D.  4h's "the fill arm alone
fires all four states" is about the dev fixture; the general statement is
"all four are reachable from the fill's anchor", which is weaker and still
enough.

**The gate (4h's one open question) is ANSWERED: yes, with one widening, and
not the widening anyone expected.**  The `Class` RECORD does not move --
`cs_u ++ cs_t^n ++ cs_w ++ rest`, which is exactly the engine's `sside`
shape.  Measured by transcribing `fam_next` into Python and enumerating the
Gray row's family: parities mixed, the classes contradict each other; parity
fixed, **four classes of that record cover 4082 of 4082 interior strings at
widths 3..12**.  What widens is the PREMISE: `ClassSucc` now carries a
membership predicate, because a step other than 1 makes only part of each
width a member (4g) and for `(gray, 2)` the discriminator is the parity of
the WHOLE string -- global, so it cannot be pushed into `cs_u`/`cs_w`.
`(binary, 1)` instantiates it at `True`.

**Selection.**  4f made `order_ok` a kernel obligation.  Under a PROVED case
split there is nothing left to decide: the two classes are disjoint because
`digs_decomp` says so.  `sel` is a lookup in the arm list as data and
`covers`/`order_ok` are not built.  That is a smaller trust surface, not a
shortcut -- but it means 4f's argument does not survive contact with a
proved split, and the subsumption order is load-bearing for the SEARCH only.

**Where the other rows stop, measured.**  Swept all 61 remaining core rows.
Ten reach the closure's filter; two board.  The other eight stop at ONE
place and it was not on the list: **the carry ripple's step count is not
affine in the run length**, and `LRule` carries `ca*j + cb`.  Four rows are
two affine laws interleaved by the parity of the run length; two are
genuinely quadratic (`(n+1)(n+2)`); two find no chain at all.  Every row that
stops here has a ONE-cell digit word; all three that board have two-cell
words.  With a one-cell digit the head's parity across the run is part of the
state, so the cost alternates or accumulates.

`cls_side` carries a STRIDE now for this reason and the emitter tries
s = 1..4.  Not enough for the parity four: at s = 2 the odd residue derives
(4m+4) and the even one does not -- it needs the same guaranteed-block-copy
materialisation the fill arm has, and then m = 0 needs its own arm.  That
widening is known, small, and worth four boards.  The quadratic two are
RULE_LADDER 5's count language, not an emitter gap.

**The bucket that wants a human, and the one that does not.**  Of the 61
core rows swept, 15 had **zero** candidate families probed and 12 had 19-74
probed that then failed on coverage or the differential.  Those are
different failures and must not be added together.  The 12 are mechanical.
The 15 are the bucket the six Gray rows sat in, labelled "no counter reading
at any anchor", until John read one off the tape -- one read, six rows.
`tools/ladder/tapes.py` renders a machine's tape at successive returns to an
anchor, RLE'd, left side head-nearest-first; `tools/ladder/core15_unread.txt`
is the 15 with their two busiest anchors already dumped.  The tool
reproduces 4g's reading as a check (`--anchor C1` on
`1RB0RB_0LC0LD_1LC1LD_1RA0RA` gives 0, 2, 4, 6, 8, 10 in Gray).

**Compute note.**  `valfam.py` and `make -jN` fight over 4 cores badly; a
core sweep that should run at ~16 s/row ran at ~78 s/row against a build.
Run one or the other.

**Verified to the end.**  The full tree built clean (2,665 files, `-j3`, ~2 h
alongside the sweep -- do not run both at once, see the compute note) and
`make closeout` ran in full: all 51 `CB_*.vo`, `Closeout.vo`, and
`closeout_partial : forall tm, Deferred D_census tm -> boarded tm \/
skipped D_remaining tm` with **`D_remaining` at 59 rows**, funext only, and
`census_cache.py --check` MATCH.  So the 62 -> 59 is the kernel's number and
not only `audit.py`'s.

## 3. The long-tail roadmap

### Scoreboard (2026-07-21 session end, authoritative — README's coverage table is STALE)
- **3,693 / 3,713 holdouts have a committed Coq theorem** (3,675
  `NeverQuasiHaltsSt` + 18 QH-with-exact-score). **20 unproven** (19
  C-certified-only: tower 4, double 3, blockdbl 3, xd 3, wave 2 (#6/#24),
  fractal 2, wave4 1, v4 irules 1; plus 1 upstream-open). Boarded this
  session: 50 irules Phase 2 + wave #17/#27/#36/#7 + double #9 (+55).
  Residue burn-down measured: see tools/recon_20260721_sweep/SWEEP.md
  (59% boardable today, 66% with the irules-QH corollary, bouncer
  checker measured WORTHLESS -- cancel FAR_DESIGN item 3).
- **`D_census` = 16,065 = 43 deferred holdouts (18 wrap-QH + 25 unproven) +
  16,022 residue** (9,775 wrap-QH survivors + 6,247 never-QH survivors).
  REGENERATED but NOT yet re-certified: the last certified census is the
  committed 16,115 `.vo`; `census_cache --check` correctly reports the
  input mismatch. Run `make census-verify` + `census_cache --update` on
  stable hardware to certify 16,065.
- Only `1RB0RB_1LC1RC_0RA1LD_1RC0LD` (the "residue-3 nested/mixed tower") has
  **no known proof anywhere**. Everything else is grind-able.

### The distinction that governs order
- **CLASS 1 — pure per-machine proofs (container-safe, fast):** every item
  below except the final re-cert. Board them HERE.
- **CLASS 2 — census re-certification (stable hardware):** after a batch, regen
  `Deferred_*` to drop the newly-proven machines, re-run `make census` on the
  box. Kept LIGHT by the proven tier (dropped machines add ZERO walk cost).
  **Batch Class-1 work so Class-2 is paid rarely.**

### The sustainable loop
1. Prove machines (Class 1, container). 2. Add to the proven table
(`gen_proven.py`) → regen `Deferred_*` (`regen_residue.py`/`gen_deferred.py`)
to drop them. 3. Re-run `make census` on stable hardware (Class 2) → new lower
`D_census`, certified.

### Work items, by leverage (all Class 1 unless noted)
1. **irules Phase 2 — DONE 2026-07-21 (see the "irules Phase 2 LANDED"
   section below): all 50 boarded, proven tier at 3,670, D_census
   regenerated to 16,065 (re-cert on stable hardware pending).**
2. **Re-root bridge (~1,300 residue machines).** `BRIDGE.md`. A `*_reroot`
   lemma family (~20-30 lines, StA-variant of `visits_swap`/`quiet_swap`) +
   per-machine ≤4-step `reflexivity` re-roots the census-only first-write-0
   machines onto upstream `1RB` cores: ~1,295 reduce to ≤3-state cores
   (trivially decided), ~107 cert-boardable, dedups 12,897→9,917 rows. Big
   residue-mass lever, cheap proof. (Recon ran on the old 12,974 residue —
   re-validate counts against the 16,022.)
3. **Bouncer / segment checker (residue mass lever).**
   `FAR_DESIGN.md:172-186`. Verified checker over upstream `certs_bouncer`
   (`period_records` + `segments`) → per-machine certs → proven tier. New
   checker SHAPE (step-template induction), 2-4 sessions. The right big lever
   for the never-QH residue.
4. **Counter tail (23 machines):** wave 6, tower 4, double 4, blockdbl 3,
   xd 3, fractal 2, wave4 1. busycoq-style individual proofs via
   `LapGlue`/`MeasureGlue`; `double` needs a new `creach_iter` O(k²) closer.
   Hard, one-at-a-time; inventory `NEXT_SESSION.md:436-487`.
5. **Residue-gate strengthening (lower priority, TRAP-ADJACENT):** wrap-QH
   survivors (9,775) → stronger measure/pattern QHBound-lex gate; never-QH
   survivors (6,247) → rwlrank / bigger RepWL rungs. Do these by PROVING the
   machines individually (Class 1, drop via proven tier), NOT as in-walk tiers
   (that is the Rule-4 trap).
6. **DEFER / SKIP:** irules v4 `mmrow` (1, orthogonal matrix-meta proof,
   shared by zero others); FAR tier (100% non-halt but liveness-dead
   0-3/60 — do not build); `1RB0RB_1LC1RC_0RA1LD_1RC0LD` (no known proof —
   last / upstream).

---

## provenQH tier LANDED (2026-07-22, branch claude/coq-bbb4-harvest-wave-1-rkqdnm)

The **R_QH sibling of the proven tier** — the theorem shape the whole
harvest boards through. Machines with a committed census-grade quasihalting
theorem (`NonHalt /\ QHBound B /\ QuasiHaltsSt`) now leave `D_census` by a
direct PositiveMap lookup returning `R_QH`, at ZERO walk cost — same
conveyor-belt mechanism as the proven (R_NeverQH) tier.

**Landed + pushed (base `make` green on every tier file; commits on the
branch):**
- `Census/Decide.v`: section vars `ProvQH` + `HPQ`
  (`Forall (fun tm => NonHalt tm /\ QHBound B tm /\ QuasiHaltsSt tm)`);
  `decide_easy` takes the `qm` map, looked up ahead of the deferred
  fallthrough, returning `R_QH`; `decide_easy_WF` discharges it from `HPQ`.
- `Machines/QHBoard/QHB_XX.v`: per-machine census-grade QHBound theorems,
  closed by `ngram_check_qhbound_sound` (PLAIN gate) or
  `ngram_check_qhbound_lex_sound` (LEX gate), `vm_compute`.
- `Census/ProvenQH_XX.v` + `ProvenQH_Data.v`: `provenqh_list` + its
  `Forall` cert `provenqh_all`, wired into `Run.v`'s `decider`/`decider_WF`.
- `Tests/Census_Corruption.v`: proven-QH tier controls (exact lookup:
  hit / mutant-miss / nonmember-miss; and the earned-verdict guard —
  `R_QH` only with the map entry, `R_Unknown` absent).
- `tools/gen_provenqh.py`: the emitter (PLAIN then LEX per machine).
- `tools/regen_residue.py --provenqh`: drops the boarded machines
  (proven + provenqh, split holdout/residue via `provenqh_map.tsv`) from
  `D_census`. Asserted; honest at any scale.

**THE LOAD-BEARING BUG (do not re-introduce):** the census `R_QH` contract
needs `QHBound` (every quiet state bounded), which is STRICTER than the
wrap sweep's `QuasiHaltsSt` (one state quiet). So listB is NOT 100%
boardable to the census contract — it must re-pass the *QHBound* checker
(plain acyclicity or lex liveness). And the FIRST emitter reused
`sweep_qhbound_residue.wrapped_closure`, which does **not grow** the n-gram
sets (no `lset |= newl`) and so under-approximates the real Coq `ng_grow`
→ it closed for the holdouts but caught **0%** of listB. Fix = grow the
sets to a fixpoint (as `gen_residue_wrap.closure_sizes` does); `gen_provenqh`
now does this + full pattern-measure vocabulary. After the fix: holdouts
16/18 (= the known `provenqh_dropped` set; the 2 `provenqh_stay` genuinely
don't board), listB **~86%** caught (t<=1024<B_census, so the `S t -> 2000`
lift is sound; ~57% plain gate, ~43% lex).

**State at hand-off (FULL listB LANDED):** the tier boards **6,517
machines** = 16 holdouts + **6,501 of the 7,976 four-state listB residue
machines (81.5%)** -- 4,699 plain gate, 1,818 lex gate. `Deferred_*`
regenerated via `regen_residue.py --provenqh`: **D_census = 9,548** (27
holdouts + 9,521 residue), down from 16,065; base `make` green,
`Print Assumptions provenqh_all`/`decider_WF` = `functional_extensionality_dep`
only. The 1,475 uncaught listB (`tools/provenqh_uncaught.txt`) resist the
QHBound gates at n<=4, t<=1024 (t is capped at 1999 by B_census=2000, so
t=4096 is out; n=5,6 might recover a few -- low priority). Census re-cert
(the native walk re-certifying `census_decided` at D_census=9,548) is
PARKED for the box -- only the `Deferred_*` tables changed among census
`.v` inputs.

**Compile tax (measured, the key scaling constraint):** `QHB_XX.v` ~3s /
100 machines; `ProvenQH_XX.v` ~30s / 100 machines (the `Forall` assembly,
dominated by Coq elaborating 100 large hypotheses, NOT `lia`). Base `make`
itself is dominated by the unchanged IRules fuel-3e5 `vm_compute` batches
(~5.5 GB each, -j2 max per the OOM rule, ~30-40 min cold). So: the batch
layer builds ONCE (its `.vo` persist), then tier iterations are fast
incremental builds. Board listB in ~2k-machine chunks (~20 `ProvenQH`
files ≈ 10 min compile), commit each (chunk-commit discipline; the emitter
is deterministic so chunks are byte-stable and `make` skips built ones).
If full-scale-in-one-build is wanted, first speed up the `ProvenQH` Forall
(e.g. per-machine `census_qh` lemmas in the QHB file + one nested
`Forall_cons` term — untested).

**Next (steps 1+2+4 for provenQH are DONE; D_census 16,065 -> 9,548):**
to reach the ~6,200 target, the two remaining independent tracks:
(3) **re-root bridge** (`BRIDGE.md`; ~1,854 machines) -- the
`qhbound_reroot`/`neverqh_reroot` lemma family + the 680-core vm_compute
table + dedup + 107 cert-boards. Independent; good as a parallel Opus
agent. (4) **listC state-nQH** (~1,496 census) -- these get
`NeverQuasiHaltsSt` theorems via the EXISTING NGram-rank / irules
checkers and join the **proven (R_NeverQH) tier** (not provenQH): fork
the `gen_proven`/`gen_bulk_certs` path over the `neverqh_rank` /
`irules claim_qh_state F` reps (SWEEP.md §4-6), then extend
`proven_dropped.txt` + `regen_residue.py`. Both land the same
proven/provenqh-tier way (per-machine theorem -> drop at regen, zero walk
cost). Emitter uncaught list: `tools/provenqh_uncaught.txt`.

---

## wave-2 residue STAGED (2026-07-22, branch claude/coq-bbb4-residue-wave-2-5vnmxc)

**2,109 more machines proved + Coq-validated, STAGED but NOT wired** (the
census re-cert was running on the box at `D_census = 9,364`, so no census
`.v` input was touched and `regen_residue.py` was NOT run).  Full
wire+regen recipe: **`docs/REROOT_LISTC_STAGE.md`** (the batched box
FOLLOW-UP).  Both land the zero-walk-cost conveyor-belt way (per-machine
theorem → drop at regen).

- **Track 1 — re-root untapped cores → R_QH: 1,518 machines.**
  `tools/gen_reroot.py --staged` adds base-checker recipes (RankSearch
  `rank_tier` n=3 boards 1,437; `rw_tier` 77; `rank_tier` n=4 4) for the
  `qh_reroot` never-QH core premise the wave-1 `rw_tier`-only recipe missed
  (184/1,742 → +1,518).  Files `theories/Machines/RerootStage/RRStage_00..15.v`;
  corruption test `theories/Tests/RerootStage_Corruption.v`; manifest
  `tools/reroot_stage_manifest.tsv`; 80 residual in
  `tools/reroot_stage_uncaught.txt` (40 no-recipe + 40 no-`closed_b`-silent-state).
- **Track 2 — listC never-QH → R_NeverQH: 591 machines.**
  `tools/gen_listc_stage.py` (fork of `gen_bulk_certs`) over the 6,247 list-C
  residue; shuffled full sweep decided 599 (9.6%), **8 dropped by the Coq
  ngram-lex re-check**, 591 Coq-verified.  Files
  `theories/Machines/ListCStage/LCStage_00..11.v`; manifest
  `tools/listc_stage_manifest.tsv`; verified set `tools/listc_caught.tsv`.
  The IRules-only listC share (~1/3 of boardable, SWEEP §4) is a further
  follow-up (heavy fuel-3e5 batches).

Every file compiles under `coqc -Q theories BBB4`; `Print Assumptions` =
`functional_extensionality_dep` only.  After wiring+regen+re-cert:
`D_census 9,364 → ~7,255` (1,518 list-B ⊎ 591 list-C, disjoint, all in residue).

---

## wave-3 residue STAGED (2026-07-22, branch claude/coq-bbb4-wave-3-harvest-jha79p)

**The irules-QH corollary landed (SWEEP §6 step 3 — the single
highest-value new checker) + 2,053 more list-C machines proved and
Coq-validated, STAGED not wired** (census_cache --check reports the
pre-wave-2 hash mismatch: the wave-2 wire + re-cert had not landed on
this branch, so census inputs stayed FROZEN; wave-2's 2,109 staged
machines are also still unwired here).  Full recipe:
**`docs/IRULESQH_WAVE3.md`**; the wire follow-up is mechanized as
**`tools/wire_wave3.py --box`** (wires wave-2 AND wave-3, regen via
`regen_residue.py --wave3`, all set asserts there).

- **The new checker (the one new trust surface):** the dual extraction
  lemma over the landed IRules engines — from the same faithful
  forward-behavior model, a prefix-visited state with no transition in
  the meta-cycle's fired set is silent from the anchor on ⇒
  `QuasiHaltsSt`; F-states recur ⇒ never quiet; a score-window pass
  (`[min B anchor, anchor)` clean of non-F states) ⇒ `QHBound B`.
  Files `theories/Checkers/IRules/MetaQH.v` (v1) and
  `MetaBlkPfxQH.v` (v3/v5/v6/v7 — what the residue actually has; 0 of
  the harvest certs are v1).  Axiom footprint
  `functional_extensionality_dep` only.  Corruption tests
  `theories/Tests/IRulesQH_Corruption.v` (never-QH machine rejected for
  EVERY witness on both engines; halter rejected; live witness
  rejected; window gate load-bearing: B=2000 accepts / B=100 refuses a
  machine quieting at ~1459).
- **Track 1 — list-C state-QH → R_QH: 1,090 machines** (the SWEEP §5
  ~1,047 projection, beaten).  `bin/irules --max-steps 2e5` over the
  5,656 unboarded list-C residue; 1,090 certs show a quiet state
  (max last visit 1,459 < 2000 — ALL board `QHBound 2000`, zero
  skipped).  Emitter `tools/gen_irulesqh_certs.py` → files
  `theories/Machines/IRulesQHStage/IQHStage_00..10.v`, manifest
  `tools/irulesqh_manifest.tsv`.
- **Track 2 — list-C never-QH (IRules share) → R_NeverQH: 810
  machines** (the ~560 projection, beaten).  Same sweep's all-live
  certs through the LANDED `irulesblkpfx_check_neverqh_sound` (no new
  trust surface).  Emitter `tools/gen_irulesnqh_stage.py` → files
  `theories/Machines/ListCStage2/LCS2_00..08.v`, manifest
  `tools/irulesnqh_manifest.tsv`.  **NOTE the attrition:** the sweep
  produced 963 never-QH certs; a full Coq-oracle pass refused 152 (+1
  v7 validation stall) — `bin/verify` passes them but the landed
  Phase-2 rule replay doesn't cover their corner (mostly v5).  List:
  `tools/irulesnqh_refused.txt`; a future engine extension recovers
  them.  Kernel-refused = never boarded (wave-2 discipline).
- **Compile tax measured:** ~1 s/machine, ~80–170 s per 100-machine
  file, memory small — the "~8 GB, 10/file" rule was for the 50 deep
  Phase-2 holdout certs, NOT these shallow residue certs.
- **SWEEP step 4 RUN (same session): +199 more** — the ngram-rank
  ladder at n≤8/t=5e6 over the 3,756 unboarded caught 199 (ALL at
  n∈{5..8}, past wave-2's n≤4), staged `LCStage_12..15.v` via the
  landed NGram lex checker (zero new Coq).  irules at 1e6 steps
  found ZERO new machines — only re-certs of the engine-gap set, and
  the 18 rank didn't also catch were refused AGAIN: the v5
  rule-replay gap is structural, not budget-bound.  108 of the 153
  engine-gap machines board via rank; **45 remain**
  (`tools/irulesnqh_refused.txt`, annotated) — the cheapest next lever
  is the MetaBlkPfx v5 rule-replay extension (+45 guaranteed, certs
  in hand).
- **After the combined wave-2+3+step-4 wire + regen + re-cert:**
  `D_census 9,364 − 1,518 (RRStage) − 591+199 (LCStage) − 1,090
  (IQHStage) − 810 (LCS2) = 5,156`.  (The remaining list-C uncaught =
  3,557 incl. the 45 engine-gap + wrap-B remainder; fuel/drift
  variants and docs/groups.md abstractions are the step-4 leftovers;
  ~1,475 listB QHBound-uncaught in `tools/provenqh_uncaught.txt` stay
  the marginal n=5/6 item.)
- **Box ops note:** `make _census-walk` is now RESUMABLE (per-unit
  skip-if-`.vo`) and defaults to `WALK_JOBS=2` — `-P4 native_compute`
  OOM-killed a 16 GB box (signal 9) on the GG_1LC layer.
  `census-verify` remains the only destructive target (delete-first =
  the full from-source honesty pass).

---

## wave-7 NGramHist ORACLE-DRIVE LANDED (2026-07-24, branch claude/ngramhist-oracle-wave-7-yo7hub)

Continues wave-6 (PR #25).  Three moves + the TNF finding.

**THE TNF FINDING (corrects the wave-6 hand-off hypothesis).**  The hand-off
assumed the 3,594 residue machines that don't string-match
`BB4_verified_enumeration.csv` are "the same machines under a different TNF
relabeling".  MEASURED FALSE: mxdys' CSV has **ZERO full machines** -- every
row has >=1 undefined transition (bbchallenge cnt>=1 pruning; the enumeration
space is machines using <= 2n-1 = 7 of the 8 transitions).  A machine that uses
all 8 is OUTSIDE that space (its TNF ancestor is a HALT node), absent under all
48 state-perm x mirror symmetries.  So the residue splits **1,535 targetable**
(<=7 transitions, map to nonhalt NGRAM_CPS_* with exact params) vs **3,594
full-8** (no oracle row); holdouts split 114 vs 3,599.  Tooling:
`tools/nghist/tnf_canon.py` + `oracle_lookup.py` (`reached_canon`, `oracle_of`,
`params_for`) + `oracle_params.csv` (the 1,486 targetable residue machines).
Full writeup: **`docs/NGHIST_WAVE7.md`**.

**Move 1 -- oracle lookup: DONE, committed.**  Every <=7-transition machine
maps to mxdys' decider+params.  BUT the targetable machines mostly CLOSE at
oracle params yet FAIL liveness (they are the genuinely-hard never-QH tail);
yield came from the full-8 machines instead (see Move 2).

**Move 3 -- HPatt pattern measures + lex-tuple synthesis: DONE, committed.**
- Checker (`NGramHist.v`, funext-only): `HPatt (p rg K phi gate)` on `hcomp`
  (pattern measure over `hsym`, the `NgPattE` fork); the new obligation
  `pm_start_exact` (ng_start form of `NGram.pm_exact`) proved by self-seeding
  `ng_start_covers`.  `hcomp_denote` gained the `n` param (pm_ok guard); wrap
  threaded.  `NGramHist_Corruption.v`: `ctl_hpatt_boards` (pattern-ONLY cert
  boards) + `hpatt_mut_rejected` (MUST-fail: `[S1;S1]->[S0;S0]` => pm_ok false
  => no-op => rejected).  Both axiom-free.
- Untrusted prover (`nghist_prove.py`): `pm_delta` over the bit projection +
  greedy **lexicographic ranking** (`lex_synth`) combining count + pattern
  measures.  The wave-6 single-measure path is preserved (no regression); lex
  TUPLES are the actual unlock for the "liveness lags closure" tail (one state
  needing several measures in lex order).  Kernel-verified end to end.

**Move 2 -- oracle-drive + re-sweep: IN PROGRESS.**  `oracle_sweep.py`
(per-machine oracle params for targetable, escalation for full-8).  The
lex-tuple prover boards ~15-23% of the previously-stuck full-8 residue that
wave-6's single-measure sweep missed.  Continuing files NGH_05.. / NGHW_06..,
per-file `Forall`, coqc-validated, manifests extended.  [update on land]

**Stretch -- `theories/Census/Assembly.v`: scaffolded.**  App-chains the
NGHStage `Forall NeverQuasiHaltsSt` + NGHWStage `Forall iqh` into one
`Forall boarded boarded_all` (route A, no walk), via a common `boarded` =
never-QH \/ bounded-quasihalter.  Extend with wave-7 files + waves 2/3/4.

---

## wave-6 NGramHist LANDED (2026-07-24, branch claude/ngramhist-closeout-wave6-ci4h3w)

**The gap plain n-gram left: history augmentation.**  mxdys' BB4 pipeline
decides the whole (4,2) space; our residue tail is ~98% binary counters that
plain n-gram CANNOT close (the carry chain looks different each pass), but
mxdys' history-augmented `NGRAM_CPS_IMPL1` (cell = last-`k` `(state,read)`
records) closes them.  BBB4's `NGram.v` had no history — wave-6 adds it.
Full design + oracle provenance + pilot: **`docs/NGHIST_WAVE5.md`**.

**The one new trust surface (`theories/Checkers/NGramHist.v`, funext only):**
the history-augmented n-gram closure as a NEW INSTANCE of `Closure.v` over
the ORIGINAL machine.  `covers a c := exists hc, lift (hproj hc) = c /\
hng_covers a hc` (an existential over the augmented config `hcconf`); the
augmented step `hcstep` projects to `cstep` (`hcstep_proj`, the new
soundness); the far-cell branch is history-constrained via gram sets over
`hsym` windows (the closure refinement, `hng_succs_sound_some`).  The
`Closure.v` liveness gates are **reused verbatim** — never-QH comes from
`live_lex_ok` over the augmented closure, NOT from closure alone
(safety!=liveness; a quiet state's early firings sit in the closed set too).
Both gates landed: `ngramhist_check_neverqh_lex_sound` (never-QH, R_NeverQH)
and `NGramHistWrap.ngramhist_check_qhbound_lex_sound` (`NonHalt /\ QHBound
(S t) /\ QuasiHaltsSt`, R_QH).  Corruption tests all pass
(`theories/Tests/NGramHist_Corruption.v`): quasihalter closed-but-rejected
(the trap), halter rejected, mutated closure rejected, plain-misses/hist-
catches.

**Harvest — 964 residue machines boarded (both shapes, kernel-validated):**
UNTRUSTED prover `tools/nghist/*.py` grows the gram sets and emits phase-
dependent count/rank lex certs; the kernel re-checks every cert via
`vm_compute`.  100/file, per-file `Forall`, `coqc`-validated, committed on
landing.
- **never-QH: 434** (`theories/Machines/NGHStage/NGH_00..04.v`,
  `Forall NeverQuasiHaltsSt`, `tools/nghstage_manifest.tsv`).
- **R_QH: 530** (`theories/Machines/NGHWStage/NGHW_00..05.v`, `Forall iqh` =
  `NonHalt /\ QHBound 2000 /\ QuasiHaltsSt`, `tools/nghwstage_manifest.tsv`)
  via the wrap variant — the genuine quasihalters the never-QH gate rejects.
  Disjoint from never-QH (overlap 0).

**Next — full residue-completion plan in `docs/TERMINOLOGY.md`
§"Eliminating the residue".** In brief: (1) a `Census/Assembly.v` that
`app`-chains the NGHStage + NGHWStage (+ waves 2/3/4) `Forall`s into
`Forall boarded D_census` — no census walk (`docs/NGHIST_WAVE5.md` §5
route A); (2) `NgPattE` pattern measures for the "liveness lags closure"
tail both harvests miss; (3) history=6,8 escalation if the yield plateaus.
State now: **964 / 5,129 residue boarded, ~4,165 unboarded** — bounded port
work (every residue machine is mxdys-decided, so a witness exists). Try the
out-degree-vs-history "hammer" probe (`docs/TERMINOLOGY.md` §hammer) before
the per-machine measure grind.

---

# Next session: start here

State as of 2026-07-16 (branch `claude/easy-machines-bb5-strategy-8pz2fn`).
**THE CENSUS IS CERTIFIED**: `Census_Theorem.census_decided :
forall tm, QHBound B_census tm \/ Deferred D_census tm` is Qed through
the kernel, `Print Assumptions` = `functional_extensionality_dep`
only.  Scope B stands end-to-end: the BB5-style TNF census over the
full (4,2) space, refounded on quasihalting, generic tiers verified,
computation certified (see "The big compute" below for the layer
layout).  In parallel the holdout-porting session built + verified
the wrap/QHBound tiers and measured them over the census residue
(item 1 of the shrink plan below) -- the next census regeneration can
drop the 20,568 wrap-caught machines from `D_census`.

## Scoreboard

- **The census machinery is verified and compiles**
  (`theories/Census/`): TNF tree + SearchQueue with a quasihalting
  node invariant, the don't-care completion lemma, swap/mirror orbit
  transfer, the verified decider pipeline, and
  `census_from_empty : Nat.iter n q_suc q_0 = ([],[]) ->
   forall tm, QHBound 2000 tm \/ Deferred D_census tm`.
- **Measured over all 3,995,005 TNF nodes** (tools/census_ladder.c,
  gas 512, both A0=0RB/1RB subtrees, no cnt=1 pruning):
  halt 249,692 (max halting step 107 = BB(4), champion reproduced) /
  in-place cycles 1,029,749 (incl. 399,512 QH with exact scores) /
  translated cycles 2,286,534 (incl. 810,873 QH) /
  n-gram CPS ladder 196,595 / holdouts reached 3,708 of 3,713
  (the other 5 are ngram-easy and already have Bulk theorems here) /
  residue 228,726.
- **Deferred list** `D_census` = 3,713 holdouts + 52,326 residue =
  56,039 machines (generated tables `Census/Deferred_*.v`; the rank
  tier shrank the raw 228,726 tier residue by 77.1%).
- Previous sessions' 3,136 holdout theorems stand unchanged.

## What was built this session

1. `tools/census_ladder.c` — the measurement harness
   (NEXT_SESSION's "first move"): enumerates the exact tree the Coq
   census walks and runs the QH tier ladder.  Validations: BB(4)=107
   with the right champion; 3,708/3,713 holdouts reached as leaves
   (tree normalization confirmed); the 5 ngram-killed holdouts match
   existing Bulk_011/019/021/024/035 theorems.
2. `theories/Census/TNF_QH.v` — the Coq-BB5 port, quasihalting
   contract: `QHBound B tm` (every eventually-quiet state's last
   visit < B) replaces `HaltTimeUpperBound`; `Deferred D` is the
   swap/mirror/completion orbit of an explicit list; `NodeDecided`,
   `node_expand_spec` (unused-state pointer + swap argument),
   `SearchQueue_*` specs.  KEY DIFFERENCES from the halting census,
   both forced (SCOPING §7): no cnt=1 pruning (full machines are
   enumerated and decided), and leaves discharge by trace equality of
   completions (`qhbound_le`,`nonhalt_le` = the don't-care lemma).
3. `theories/Census/Decide.v` — the pipeline: verified `find_halt`,
   `cycle_leaf_check`/`tcycler_leaf_check` (NonHalt + QHBound n1 via
   the lap induction, reusing `tcycler_laps/_fold`), untrusted
   searches (rolling-hash in-place scan; record-pair TC candidates,
   2/side, left side via `mirror_tm` on the same record log),
   deferred lookup through a `PositiveMap` of `tm_enc` keys (map
   stores the machine, one `tm_eqb` per hit — no injectivity proof
   needed), `decide_easy` + `decide_easy_WF`.
4. `theories/Census/Deferred_Defs.v` + generated `Deferred_00..07.v`
   + `Deferred_Data.v` (`tools/gen_deferred.py`).
5. `theories/Census/Run.v` — root + mirror symmetrization (the 4
   first-move-left children covered by `node_decided_mirror`),
   `q_iter_WF`, `census_from_empty`.
6. `theories/Tests/Census_Corruption.v` — negative controls: tampered
   cycle/TC parameters rejected, ngram must reject a quasihalter and
   a halting machine, deferred lookup misses, pipeline classification
   on knowns.

## The big compute (DONE -- certified 2026-07-16)

`census_decided` is Qed with the expected axiom footprint.  The
certification layer under `theories/Census/Compute/`:

- 24 per-grandchild Qed files `G_*.v` (tools/gen_gsplit.py; the two
  xRB subtrees split at B0 into 12 each, composed by
  `Run_Split.child_from_grandchildren`), each Qed one native queue
  walk (`Nat.iter 700 q_suc ... = ([],[])`).
- The A0=1RB, B0=1LC grandchild is the largest single walk (>2.5 h;
  it outlived the remote container's reclaim window repeatedly), so
  it is split ONCE MORE: `Census/Run_Split2.v` expands its machine at
  the undefined C1 slot (index 2, pointer StD, all 16 fills
  admissible) and `tools/gen_ggsplit.py` emits the 16 `GG_1LC_*.v`
  walk units plus the assembling `G_1RB_1LC.v` (same lemma names as
  the monolithic version, so Census_Theorem.v is untouched).  Every
  unit lands in <= ~10 min, making certification robust to compute
  interruptions.
- `make census` drives the whole layer order (Run_Split, Run_Split2,
  GG units, G units, theorem); ~2-3 h wall on 4 cores under the
  native switch.

Re-running from scratch re-derives everything; the per-unit
logs/progress live in `census_probes/` (gitignored).  If a future
regeneration's log shows leftovers: decode the printed tm_enc keys
with `tools/dec_tm_enc.py`, classify with `tools/census_ladder.c
--machines`, fix the tier divergence or extend the residue, and
regenerate (this loop converged after one iteration -- the
false-record fix in `scan_records0`).

Environment: coq-native lives in the opam switch `census`
(`OPAMROOT=/root/.opam`, `eval $(opam env --switch=census)`); apt's
coqc has no native_compute.  Everything compiles under Coq 8.18.
The probe .v files are one-liners over `Run_Split.q_sub`; see
`census_probes/` logs for the exact form used.

## The rank tier (BUILT this session) and what remains

`Census/RankSearch.v` implements the rules-(a)/(b) search in-Coq
(untrusted: SCC decomposition, condensation ranks, Bellman-Ford
potentials over the three count-of-1s measures) feeding the EXISTING
verified `ngram_check_neverqh_lex`; wired as the pipeline's last
tier (rungs n=3, t in {0,64,256,1024}).  Validated per-machine
against bulk_prover.py -- which surfaced a real overclaim in the
PYTHON side: `bulk_prover.decide` demands liveness only for states
present in the closure, so machines whose quiet states vanish from
it (visited once, never again -- genuine quasihalters like
`1RB---_1LC1LD_1RB1LD_1LC0LC`) were wrongly "killed".  The Coq
checker requires prefix-visited states too and rejects; the v2
deferred sweep (`tools/sweep_rank_residue.py`, `decide_strict`)
mirrors the checker's exact premise.

Measured on the full 228,726 residue: **rank kills 176,400
(77.1%)**; the loose rate was ~86.6%, so ~21.7k of the remainder are
prefix-quiet QUASIHALTERS (wrap-class).  v2 deferred list D_census =
3,713 holdouts + 52,326 residue = **56,039 machines**.

## Next session: shrink the deferred list (52,326 residue + holdouts)

Work items in measured coverage-per-effort order.  The loop for each
tier is mechanized: add the tier to `decide_easy` + its WF case,
mirror it in the residue sweep tool, regenerate `Deferred_*`
(`tools/gen_deferred.py`; the current residue = the committed
Deferred rows minus the holdout list, or re-derive with
census_ladder + the sweep), re-validate with the 64k-pop probe
(expect `(32, 0, [])`), then `make census` (~2-3 h wall at the
grandchild split).  Batch tiers into ONE regeneration + one
certification.

1. **Wrap tier -- MEASURED: 20,568 of the 52,326 residue (39%) are
   prefix-quiet quasihalters** (`tools/sweep_wrap_residue.py`;
   confirms the ~21.7k estimate).  Each is a genuine quasihalter with
   a Coq-checked `NonHalt /\ QuietAfter q s /\ QuasiHaltsSt` via the
   EXISTING verified `ngram_check_quiet` (Wrap.v) -- validated on 414
   random machines through `vm_compute`, 0 failures, and
   `tools/gen_residue_wrap.py` regenerates the theorems from
   `tools/wrap_residue_caught.tsv` (`theories/Tests/Residue_Wrap_Probe.v`
   is a committed 120-machine sample).  **The 31,758 survivors
   (`tools/wrap_residue_survivors.txt`) are the residue's hard never-QH
   core -- the meat.**
   **The QHBound tier is now BUILT and verified** (`ngram_check_qhbound`
   / `ngram_check_qhbound_sound` in `Checkers/Wrap.v`, axiom footprint
   `functional_extensionality_dep`): the wrapped closure PLUS the
   engine's plain-acyclicity rank liveness (`Closure.live_ok` /
   `rank_reach` / `live_appears_recur`, added to `Closure.v`) gives the
   full census decision `NonHalt /\ QHBound (S t) /\ QuasiHaltsSt`.
   Measured (`tools/sweep_qhbound_residue.py`): the plain-acyclicity
   gate decides **~24% of the 20,568** wrap machines now (`n<=6`);
   `theories/Tests/QHB_Probe.v` verifies 150 through `vm_compute`.
   **The lex-gated variant is ALSO built** (`ngram_check_qhbound_lex`
   + `_sound`; `Closure.v` gains `lex_reach` / `closure_invariant_c` /
   `live_lex_ok` / `live_appears_recur_lex`): each appearing state is
   discharged by plain acyclicity OR an `NgRankE`/`NgPattE` measure
   certificate over the wrapped closure.  Tools:
   `tools/gen_qhbound_wrap.py` (plain, from `qhbound_caught.tsv`),
   `tools/gen_qhbound_lex.py` (lex, from `qhbound_survivors`);
   committed probes `Tests/QHB_Probe.v` (150 plain) and
   `Tests/QHB_Lex_Probe.v` (lex-only machines).
   **FULL MEASUREMENT (committed artifacts): of the 20,568 wrap-QH
   machines, 5,307 are QHBound-decidable by the plain gate NOW
   (`tools/qhbound_caught.tsv`; a 100-machine RANDOM sample verified
   through Coq, 0 failures) and 15,261 need the measure gate
   (`tools/qhbound_survivors.txt`; a small-sample lex sweep with just
   the count-of-1s measures lifts ~13% -- offer the digram/pattern
   candidates as `Bulk_R` did to push further).**
   REMAINING:
   (a) run gen_qhbound_wrap over the full `tools/qhbound_caught.tsv`
   and check the tables in as `Machines/Bulk/QHBWrap_*.v` (~90 files
   at 60/file; each compiles in seconds);
   (b) strengthen the lex sweep (pattern vocabulary, larger n) over
   `tools/qhbound_survivors.txt` and emit via gen_qhbound_lex;
   (c) wire `ngram_check_qhbound(_lex)_sound` into the census
   `decide_easy` as an `R_QH` tier, regenerate `Deferred_*` over what
   remains, and re-`make census` (needs the native switch).
2. **Pattern-vocabulary rank (cheap add-on, ~3-6k):** generalize
   RankSearch's candidate measures from the three `ngmeas` counts to
   the `NgPattE` pattern measures (pm_delta is verified; the search
   loop is measure-agnostic -- add candidate enumeration with
   `pm_ok` coverage limits) and add n=4 rungs.  Mirror in
   sweep_rank_residue (bulk_prover already speaks patterns).
3. **RepWL tier (the remaining ~25-30k are mostly this class):**
   port Coq-BB5's `Decider_RepWL.v` closure construction as a second
   instance of the `Closure.v` engine (SCOPING phase 2's rwl block),
   plain-acyclicity liveness first (the engine's `compute_ranks`
   works for any instance), rwlrank measures later.  This is the
   biggest single block and also the prerequisite for the 106
   rwlrank holdout certs.
4. **Holdout absorption** (independent track): upstream is down to
   ONE open machine (`1RB0RB_1LC1RC_0RA1LD_1RC0LD`, the residue-3
   nested/mixed tower; `check_coverage.py`, 2026-07-16).  The
   checker gaps that absorb the remaining certificate types: irules
   (352), rwlrank (106 incl. 9 rwlrank+wrapngram), fuel (62), drift
   (17), and ~42 counter machines (the BBB residue-3 sprint boarded
   many more counters than the old 22) -- SCOPING phases 2b-5.
   **The fuel checker (rule c2) is now BUILT and verified**, axiom
   footprint `functional_extensionality_dep`:
   - `theories/Records.v` -- record/extent substrate (side windows,
     growth <=1/step, toward-move shrinks, `run_right_exhausts`).
   - `theories/Closure.v` -- `runner_find` (the record argument as a
     per-state liveness lemma) + `closure_check_neverqh_fuel`
     (`lex_ok || runner_ok` per visited state) + soundness.
   - `theories/Checkers/FuelClass.v` -- capped sided-count lower-bound
     classes with `finc_sound`/`fdec_sound` (the beyond-window
     upgrade's delta core).
   - `theories/Checkers/Fuel.v` -- `ngram_check_neverqh_fuel` on the
     n-gram abstraction (reuses the full measure vocabulary; runner
     fuel read from the window), `Tests/Fuel_Examples.v` validates it
     end-to-end (subsumes the lex checker on a real bulk machine).
   REMAINING to land the 62 machines: the untrusted prover must emit
   runner-mode certs -- adapt `tools/bulk_prover.py` to detect the
   runner SCCs (states the rank measures leave undischarged, whose
   nodes all move one direction with in-window fuel), emit them as
   the runner-gated states, and `tools/gen_bulk_certs.py` to write
   `apply (ngram_check_neverqh_fuel_sound ...)`.  For beyond-window
   fuel machines, swap `cconf` for the `cconf * fclass * fclass`
   refined context (FuelClass) and read `rfuel_ge1` off the tracked
   class; the Closure-side soundness path is unchanged.  Then rule
   (c3) drift rides the same substrate (+17).  Each holdout theorem
   also lets its machine leave the deferred list
   at the NEXT regeneration (deferred entries with Coq theorems can
   be dropped once a "proven machines" tier exists -- a
   PositiveMap of the Bulk/Wrap theorem machines returning
   R_NeverQH/R_QH, trivially WF from the existing per-machine
   theorems).

Nothing from the certification run itself needs checking in beyond
what is committed: the G_*.vo/logs are gitignored artifacts
(re-derivable by `make census`), and the residue list is recoverable
from the committed Deferred tables minus the holdout file.

## Gotchas discovered (do not re-learn these)

- **BB5's cnt=1 pruning is unsound for quasihalting** -- full machines
  can still quasihalt.  The tree expands them; the C tool counts
  3,995,005 nodes vs BB4's 858,909.
- **Coq list literals**: >~5k elements per Definition stack-overflow
  the parser and typecheck superlinearly; the deferred tables use
  500-row sub-definitions + concat.  ~30s-4min per 1.1MB file is
  normal with the native compiler on.
- **`simpl`/`cbn` vs the pipeline**: never let simpl touch `decider`
  applications (it contains a 232k-entry map); root lemmas
  use a hand-built `q_0` and `node_expand_spec` directly, plus
  `cbn [explicit constants]` (include `t_head`! an unreduced
  `t_head {|...|}` blocks rewrites).
- **`Section` hypotheses capture per-lemma**: swap lemmas take
  explicit `u <> StA` args now; don't guess closed signatures.
- **In-place scan keys must be padding-blind** (ceqb ignores blank
  padding): the rolling hash tracks 1-cells relative to the head;
  side LENGTHS are not invariant.
- `repeat split` proves `forall`-wrapped equalities by constructor --
  count your goals.
- The BBB enumerator's A0->xxA exclusion is unnecessary here: 0RA is
  an in-place cycle at (0,1), 1RA a translated cycle at (1,1); both
  die in the loop tier.

## Hard rules (unchanged)

- Everything emitted by tools/ is UNTRUSTED; only the Coq checkers
  carry soundness.  Never weaken a checker to make a cert pass.
- Every new certificate feature gets corruption tests that MUST fail.
- `make` stays green; axiom footprint stays
  `functional_extensionality_dep` only (check with
  `Print Assumptions`).

---

# Counters track (individual proofs) -- session 2026-07-16

State of the SCOPING section 5 phase 5 "individual proofs" track
(branch `claude/coq-bbb4-counter-proofs-3yx9bj`).  Own files only:
`theories/Counters/`, `theories/Machines/Counters/`,
`theories/Tests/Counters_Corruption.v`, `tools/counters*`; the
`_CoqProject` block is marked `# --- counters track ---`.

## Boarded: 6 of 39 counter machines

| family | status |
|---|---|
| mono_counter (3) | **COMPLETE**: #10, #26, #31 (`Mono_10/26/31.v`) |
| spacer_counter (3) | **COMPLETE**: #16, #22, #23 (`Spacer_16/22/23.v`) |
| gray(1) double(4) blockdbl(3) mono2(2) interleave(2) exp(3) bounce(2) | not started, in that order (bounce needs the well-founded measure -- see its family notes upstream) |
| wave(6) wave4(1) tower(4) xd(3) fractal(2) | hard tail, budget separately |

Every theorem is `nqh_<bbchallenge text> : NeverQuasiHaltsSt tm_*`,
`Print Assumptions` = `functional_extensionality_dep` only, listed in
`tools/counters_manifest.tsv` (wired into `check_coverage.py`;
coverage now 3142/3713).

## The architecture that landed (native route -- decided over busycoq)

- `theories/Counters/WTape.v`: two-sided windowed runs (`wsteps`
  with per-side wall/blank-materialize modes), the transport lemma
  into `csteps`, repetition cycles `cycR`/`cycL`/`cycLW` (the last
  carries a fixed marker window -- spacer transcription), and the
  `rep` algebra (`rep_shift`, `rep_rot`, `rep_slide`, `rep_dbl`,
  `rep_add`).
- `theories/Counters/LapGlue.v`: `glue_neverqh` -- bootstrap +
  per-anchor lap (up to `lift`, for the overflow trailing blank) +
  per-anchor all-state visit witnesses => `NeverQuasiHaltsSt`.
- `theories/Counters/MonoCounter.v`: counter encodings over
  `positive` (`Wp` odd-cell, `Bp` contiguous), the carry view
  `cview` with decomposition lemmas for both encodings, and the
  mono-family comb-alignment/final-area rewrites.
- Per machine: ~15 unit runs (each `Proof. reflexivity. Qed.` on
  `wsteps`), transported phase lemmas in cons-normal form, and a
  linear `eapply csteps_chain` lap script with `rep`-algebra
  junction rewrites, split by `cview` case (interior carry j /
  overflow 2^j-1).

busycoq route rejected after the #10 prototype: it would add the
stream-world port PLUS a new quasihalting-aware translation (a fresh
trust surface) and the carry case analysis stays manual either way;
our unit runs are one-line reflexivity checks, so busycoq's Ltac
advantage evaporates.

## The per-machine recipe (tools/counters/, ~2-4h per machine)

1. `trace.py` the lap macro-structure (sweeps, turnarounds);
2. write `lapNN.py` against `executor.py` (combinators mirror the
   Coq lemmas 1:1; wall discipline asserted; units auto-derived);
3. `python3 lapNN.py 300` must print ALL OK (differential vs raw:
   step counts + configs + next-anchor, all carry shapes);
4. transcribe: unit dump -> unit lemmas; chain -> lap script; small
   probes give the bootstrap step count and visit offsets;
5. corruption tests (mutant machine breaks a unit, wall-discipline
   `= None` checks, wrong boot anchor `ceqb = false`);
6. manifest row + `_CoqProject` line + `make` + `Print Assumptions`.

## Next machine: #19 gray_counter (results/counter19.cert)

The only gray machine; read its cert + `verify_gray_counter` in
BBB/src/verify.c for the encoding, then run the recipe.  After it:
double_counter (#30 + 3 more per check_coverage), blockdbl, mono2,
interleave, exp, bounce (well-founded measure -- LapGlue may need a
second closer whose laps shrink a secondary quantity; design against
the C verifier's bounce obligations before coding).

Session-2 notes on the spacer twins (#22/#23, voff=-1): p0 = 1, the
lap runs from every positive (`Pos2Nat.is_pos` + one destruct level
instead of two); #23's separator rebuild is 8 steps exiting through
D and deposits its own spacer zero, so its final fold ends
`rewrite HBs, rep_slide` where #16/#22 use the [1]-shuttle +
`rep_add` fusion.  The twins CONVERGE after 8 steps -- a corruption
example claiming their 8-step runs differ is false (learned the
hard way); discriminate them at 7 steps.

## Trap catalog (do not re-learn)

- **Comb units are rotations**: the crossing consumes `[1;0;1]`
  even though the comb is written `(110)^a` -- pick the boundary
  where the 5-step excursion stays inside the unit and prove the
  `rot_*` fold by 3-line induction (`induction k; cbn [rep app];
  now rewrite IHk`).
- **Overflow laps may end one trailing blank long** (mono) or
  exactly (spacer #16): state the lap up to `lift` and use
  `lift_app_blank` only where the executor says so.
- **Evars vs case analysis**: `destruct j` must happen BEFORE
  `do 2 eexists` when the two carry branches produce different
  final configurations (Mono_31 lesson).
- **`cbn [rep app]` over-unfolds**: it will expand EVERY
  S-headed `rep` in the goal, wrecking later pattern matches; use
  definitional fold lemmas (`Proof. reflexivity. Qed.`) as targeted
  rewrites instead (`spacer_fold`, `ones_fold`, ... in Spacer_16).
- **`rewrite` needs app-forms**: a bare `rep [S1] j` tail won't
  match `... ++ X` patterns -- keep `_nil` fold variants around.
- **Anchor conventions**: the executor's `raw_lap` event detector
  IS the spec of `Cc` -- keep them in lockstep or the differential
  test lies to you.
- Step-count formulas are never needed in Coq (the lap `n` is an
  existential); do not waste time deriving them beyond executor
  sanity checks.

## Counters track, session A (2026-07-16): gray + mono2 boarded

(Marked append; supersedes the table above.)  Boarded: **9 of 39**.

| family | status |
|---|---|
| mono_counter (3) | COMPLETE: #10, #26, #31 |
| spacer_counter (3) | COMPLETE: #16, #22, #23 |
| gray_counter (1) | **COMPLETE: #19 (`Gray_19.v`)** |
| mono2_counter (2) | **COMPLETE: #38, #39 (`Mono2_38/39.v`)** |
| double(4) blockdbl(3) interleave(2) exp(3) bounce(2) | not started; session A scoped double+blockdbl, session B interleave/exp/bounce |
| wave(6) wave4(1) tower(4) xd(3) fractal(2) | hard tail, budget separately |

Coverage after this session: 3145/3713.  All three new theorems are
`nqh_<text>` with `Print Assumptions` = `functional_extensionality_dep`
only; negative controls live in `theories/Tests/CountersA_Corruption.v`
(new file, session A's own -- session B uses its own test file).

### What landed (all in the MonoCounter session-A appendix)

- Gray encoding `Wg` (3-cell slots of G(p) = p xor p>>1): the increment
  flips slot j = fst (cview p), so `Wg_some`/`Wg_none` follow the
  `cview_some_W` pattern verbatim.  #19's lap: FIVE flows (even
  set/clear, interior set/clear, overflow), one turnaround each.
- Interleaved-marker encoding `Wm2` (mono2): `Wm2_some/none`, again
  same skeleton.  #39 = one sweep/lap, #38 = two sweeps/lap (comb_step
  2); the twins share A/B/D rows, so their unit tables coincide up to
  the C-row units.
- New rep algebra: `rep_dblu`, `rep_trip`, `rep_snoc2/3`, `rot_cross2/3`,
  `rot_ret`, `ones2_slide`, `cross_ret/cross_ret2`, `comb_even/odd`,
  `comb_refold`, and definitional `rep011/101/110_expose` (targeted
  substitutes for `cbn [rep]`, per the over-unfolding trap).

### New traps (session A)

- **rewrite needs concrete rotations**: `rep_rot`'s `u ++ [x]` pattern
  never matches literal `rep [S0;S1] j` -- state the machine's exact
  rotation as its own induction lemma (`rot_ret` etc.), 3 lines each.
- **Evars vs side conditions**: in `split; [| split; [| lia]]` the
  `lia`/`reflexivity` fire BEFORE the csteps chain instantiates the
  evars -- prove the chain first, side goals after (Mono_10 bullet
  order, not inline brackets).
- **`destruct (cview p) eqn:` rewrites the IH too**: apply the IH via
  `eq_refl` (the file's established `cview_some_W` pattern), not via
  the destructed hypothesis.
- `injection` recurses through `S` -- `(S j', o) = (S j, Some q)`
  yields `j' = j` directly; a second injection is "Nothing to inject".
- Head-exposure hypotheses (`Wm2_head q = S1 :: wq`): rewrite them
  globally BEFORE starting the chain; mid-chain `rewrite <- Hwq`
  fails once deposits shadow the head.

### Doubling families (double #9/#30/#32/#37, blockdbl #11/#13/#28):
### reconnaissance done, NOT started -- read before coding

`tools/counters/trace_dbl.py` probes all seven: synthetic anchors are
validated (each reaches the next anchor with the cert recurrences).
Anchor cconfs (head-side per cert `acc_side`):

- #30: `(B, 1^t ++ (011)^k-rev ++ [0;1], 0, [])`, k=2^j-1, t=3j+4;
- #9:  gen comb (10), no prefix, kg=2^j-1, acc 3j (unary, side R);
- #32: gen comb (110), prefix 1, kg=2^j, spacer-acc 0^(3+2j) then 1;
- #37: side L (acc left), legacy comb, t=1+3j;
- #11/#13: solid 1^m 0 1^t, m=3*2^(j-1)+{1,0}, t=2j-1;
- #28: side L, 1 0^z 1^m, m=4*2^(j-1)-1, z=2j.

These laps are O(k^2): a NESTED loop of per-unit mini-sweeps (#30
j=2,3,4: 431/1447/5207 steps).  The toolkit handles every inner phase
(the #30 wiggle-clear is a textbook `cycLW` unit
`(B,([1;1],1,[])) -> (B,([1],1,[0]))`, collapse/spread are 3-step
cycL/cycR with u=[1;1;0], w=[1;0;1] and back), BUT:

- the OUTER loop needs a new closer: `creach tm c c' := exists n,
  csteps tm n c = Some c'` with refl/trans/csteps lemmas and
  `creach_iter : (forall i, i < k -> creach (f i) (f (S i))) ->
  creach (f 0) (f k)`; the lap lemma then chains boundary phases
  around `creach_iter` and recovers `0 < n` from a nonempty prefix
  phase.  The mid-config family `f i` must be read off the executor,
  not derived by hand: my hand-derived #30 step model was 2x short --
  the acc is re-shuttled EVERY mini-lap (the per-lap fill triples are
  re-cleared by the next wiggle), so wiggle counts grow ~3/lap.
- the executor needs a `cycLW` combinator (lap16.py inlined one
  manually; a reusable `cycLW(ex, cfg, lwlen, ulen, P, k, name)`
  helper that mirrors `WTape.cycLW` -- unit `(q,(lw++u,h,[])) ->
  (q,(lw,h,w))` -- was drafted and works; put it in executor.py or
  per-lap files).
- derive the mini-lap phase list with a DbgExec subclass that prints
  the cfg after every combinator (see the mono2 session: two dumps at
  consecutive j pin down every list shape and count).

**Next machine: #30** (canonical double_counter).  Known #30 phase
inventory (validated against the raw trace, counts NOT yet final):
`UTe (B,([],0,[]))->3,br=F->(B,([1],1,[1]))` edge turn block;
wiggle `cycLW` as above (mini-lap 1 clears the whole acc, t reps);
junction `UJ (B,([1;0],1,[]))->2->(D,([],0,[1;0]))`;
collapse `UC (D,([1;1;0],0,[]))->3->(D,([],0,[1;0;1]))` + an edge
variant eating into the old prefix; prefix turns `UP` (3 steps
mini-lap 1, 4-5 steps steady, shapes differ); spread
`US (B,([],0,[1;1;0]))->3->(B,([1;0;1],0,[]))`; per-lap fill triples
`(B0 w1, C0 w1, D1 keep)` = cycR u=[0;1;0]-ish, and a final fill
pass ending in a br=F edge unit.  Seeds: each mini-lap's UJ keeps a
1 (spaced 3), UTe's third 1 is the top seed.  After #30: #9 (gen
comb (10), fewest turns/lap: 2 per mini-lap), then #37, #32, then
blockdbl #13/#11 (solid blocks, (B1,D1)-conversion cycles), #28
(side L).  Budget one machine per ~2-3h; the creach scaffolding is
shared after the first.
---

# Counters track, session B (interleave/exp/bounce) -- 2026-07-16

Parallel to session A (gray/double/blockdbl/mono2), own files only:
`theories/Counters/{ILCounter,ExpCounter,BounceCounter,MeasureGlue}.v`,
`theories/Machines/Counters/{Interleave_18,Interleave_35,Exp_2,Exp_4,
Exp_12,Bounce_8,Bounce_33}.v`, `theories/Tests/CountersB_Corruption.v`,
`tools/counters/lap{18,35,2,4,12,8,33}.py`; the `_CoqProject` block is
marked `# --- counters track: session B ---`.

## Boarded: 7 machines (16 of 39 total with session A's 9 -- see its section above)

| family | status |
|---|---|
| interleave_counter (2) | **COMPLETE**: #18, #35 (`Interleave_18/35.v`) |
| exp_counter (3) | **COMPLETE**: #2, #4, #12 (`Exp_2/4/12.v`) |
| bounce_counter (2) | **COMPLETE**: #8, #33 (`Bounce_8/33.v`, via MeasureGlue) |

All `nqh_<bbchallenge text> : NeverQuasiHaltsSt`, `Print Assumptions`
= `functional_extensionality_dep` only, manifest rows appended.

## What was built

- `ILCounter.v`: the interleaved counter encoding `Ip` (rev of E(n),
  LSB-first, one `S1` pad per bit), cview decomposition lemmas, and
  `pair_fold`.  #18/#35 share the anchor
  `D(n) = E(n) (110)^(2n) 1` and a two-sweep lap through the mid
  shape `E(n+1) 010 (110)^(2n) 1`; the increment carries on sweep 1,
  sweep 2 rewrites `010` locally.  Laps end exactly (no lift slack).
- `ExpCounter.v`: the stride-3 marker encodings -- zeros-first `Tp`
  and marker-first `Gp` -- with cview lemmas emitting the exact
  `rep`-block shapes the stride cycles and zeroing runs consume, plus
  `rep1_fold`/`ones_fold_S`/`rep_tpl`.  #2 (side R, moff 1: the two
  sides carry on ALTERNATE laps -- case over both cview's), #4
  (side L, moff 0: one cview drives both sides), #12 (sym: markers
  both sides).
- `MeasureGlue.v` -- THE NEW CLOSER (bounce): `mrun` composes a
  measure-decreasing abstract recurrence of EXACT micro laps
  (invariant-guarded; terminal up to lift) into one csteps run by
  strong induction on the measure.  The macro family then steps
  p -> succ p and plain LapGlue closes never-QH: unboundedness from
  the macro index, per-lap finiteness from the measure.
- `BounceCounter.v`: digit words `Dw` (00/11 pairs), carry view
  `bview`, measure `cval` (value of the complement, LSB-first;
  `cval_step`: each increment decrements it by EXACTLY 1),
  comb rotations `comb_rot0/1`, run folds.
- `Bounce_8/33.v`: macro anchors `D(k) = 1^m 0^z`; macro lap =
  boot-in half sweep + `mrun` over the double-sweeps + terminal
  settle from the all-ones word.  KEY DISCOVERY: the double-sweep is
  a CELL-UNIFORM binary increment
  `Sc a (1^j 0 x) -> Sc (a+1) (0^j 1 x)` -- the C verifier's
  interior/overflow split is pure decode (the flipped top digit
  merges with the accumulator AS CELLS), so a fixed-length bool word
  carries the whole macro lap with no case analysis, and the
  invariant is just the conservation law
  `S (fst x) + cval (snd x) = const(k)`.  Validated k=2..9 (#8, 510
  double-sweeps) and k=2..8 (#33) against raw.

## Trap catalog additions (session B)

- **The `apply`-unification unfolds double-`S` reps**: `apply phU1`
  against `S1 :: rep u (S (S a)) ++ X` leaves the residual evar in a
  half-unfolded `fix`-form that later `rewrite`s can't match.  Insert
  an explicit `change` exposing the cons cells
  (`S1 :: S0 :: S1 :: rep u (S a) ++ X`) BEFORE the apply; folds like
  `ones_fold3` also want their explicit instance (`rewrite
  (ones_fold3 a)`).
- **`rewrite <- rep_dbl` is ambiguous** when both `rep [S0] (2*t)`
  and `rep [S1] (2*P)` are present -- give the instance explicitly.
- **exp #2's two sides carry on alternate laps** (moff 1): destruct
  BOTH `cview p` and `cview (Pos.succ p)`; the impossible
  overflow+overflow branch still closes (the algebra composes, no
  contradiction needed).
- **Bounce sweep-B entry is comb-rotated**: the collapse absorbs the
  mid marker `0` + first block `1` as one more `[S0;S1]` unit
  (`comb_rot1`); the executor frames catch this automatically.

## Next machine

The counters residue after both sessions: session A's remaining
queue (double(4) starting at #30, then blockdbl(3) -- see its
section above) and then the hard tail wave(6) wave4(1) tower(4)
xd(3) fractal(2).  For the
tail, start with **wave**: read `results/counter*.cert` types `wave_counter`
and `verify_wave_counter` in BBB/src/verify.c; expect LapGlue to
suffice (parameter -> infinity liveness) with wider unit tables.  The
bounce-style MeasureGlue composition is now available for any family
whose macro lap chains an inner counter (tower is the likely
customer: its cert type suggests nested doubling).

<!-- --- irules mass-board --- -->

## IRules mass-board (this session)

Boarded **250** of the 352 irules-typed holdouts:
`theories/Machines/IRules_Batch_00.v` .. `IRules_Batch_08.v`, each
machine = TM + `IRCert` literal + `_never_quasihalts` (via
`irules_check_neverqh_sound`, fuel 300000, `vm_compute`) +
`_nonhalt` corollary.  Manifest: `tools/irules_manifest.tsv` (250
rows), wired into `tools/check_coverage.py`.  Negative controls:
`theories/Tests/IRulesBatch_Corruption.v` (mutant TM -> `false`;
perturbed meta map / wrong anchor -> `<> true`; meta-map control at
fuel 2000 with the genuine cert shown passing at that same fuel,
because a corrupted map burns unbounded memory at fuel 300000).
`Print Assumptions` on 5 sampled theorems across batches:
`functional_extensionality_dep` only.

**Coverage: 3152 -> 3402 Coq-proven (+250).**

### Deferred: 102 machines the v1 Coq engine cannot board

Full list with per-machine reasons: `tools/irules_deferred.tsv`.
None are the anticipated >10M-step-anchor cases -- all 352 anchors
fit the flat checker.  Instead these certs use post-v1 format
features the verified engine does not model:

- 44: v6 certs needing `blk`,`rulepfx` (block-encoded rules)
- 38: v3 certs with decrement delta -2 (v1 supports -1 only)
-  6: v7 certs needing `rulepfx`,`rulerunm`
-  6: v3 certs needing `blk`
-  4: v3 certs with decrement delta -3
-  3: v3, d=-1 only, but v1 bound reasoning fails (probed incl.
  kmin/lb bumps)
-  1: v4 cert needing `mmrow`,`nvar`,`tplrunmv`

Next session: extend the engine (multi-decrement first -- 42
machines for one feature) or port the v6 block-rule layer.
Machine strings:

```
1RB---_0LC0LB_1RC0RD_1LB1LA
1RB---_0RC0RB_1LD0LA_1LD1LB
1RB0LA_0RC0RB_1LC1LD_0RA0RB
1RB0LC_0LC0LB_1RC1RD_1LA0LB
1RB0LC_0LC0LB_1RC1RD_1LA0LD
1RB0LC_1LA0LD_1RC1RB_0LC0LD
1RB0LD_0LC0LB_0LD1LC_1RD1RA
1RB0LD_1LC0LB_0RA0LD_1RD1RB
1RB0LD_1LC0LB_0RA1LC_1RD1RB
1RB0RA_0RC1LD_1LC0LA_0RC0RD
1RB0RA_0RC1LD_1LC0LA_0RD0RB
1RB0RB_0RC1LD_1LC0LD_1RB0RA
1RB0RC_0LC0LB_0LD1LC_1RD1RA
1RB0RC_0RC0RB_1LC1LD_1RA0RB
1RB0RC_0RC1RB_0RD0RC_1LD1LA
1RB0RD_0LC0RC_1LC1LA_0RC0RD
1RB0RD_0RC0RB_1LC0LA_0RA0RB
1RB0RD_0RC0RB_1LC0LA_0RB---
1RB0RD_0RC0RB_1LC0LA_0RD0RB
1RB0RD_0RC0RB_1LC0LA_1RD1LB
1RB0RD_0RC0RC_1LC1LA_0RC0RD
1RB0RD_0RC1LA_1LC0LA_0RA0RB
1RB0RD_0RC1LA_1LC0LA_0RB0RB
1RB0RD_0RC1LA_1LC0LA_0RD0RB
1RB0RD_0RC1LA_1LC0LA_1LA0RB
1RB0RD_0RC1LA_1LC0LA_1RB0RB
1RB0RD_0RC1LD_1LC0LA_0RD0RB
1RB0RD_1LB0RC_1LC1LA_0RC0RD
1RB0RD_1LC0LB_1RA1LC_1LC0LC
1RB0RD_1RC0RB_0LA0RD_1LD1LB
1RB0RD_1RC0RB_0LA1RC_1LD1LB
1RB1LA_0LC0LB_1RC1RD_1LA0LB
1RB1LA_0LC0LB_1RC1RD_1LA0LD
1RB1LA_1LA0LC_0LD0LC_1RD1RB
1RB1LC_0RC0RB_1LD0LA_0RA1LB
1RB1LD_0RC1RB_1LC1LA_0RB0RD
1RB1RA_0RC0RB_1LC1LD_1RA0RB
1RB1RA_0RC0RB_1LD0RA_1LD1LB
1RB1RA_0RC1LD_1LC0LA_0RD0RB
1RB1RB_0LC0LB_0LD1LC_1RD1RA
1RB1RD_0RC0RB_1LC0LA_1LA1LB
1RB1RD_0RC0RB_1LC0LA_1LB---
1RB1RD_0RC0RB_1LC0LA_1LD0RB
1RB1RD_0RC0RD_1LC0LA_0RB1LD
1RB1RD_0RC1LD_1LC0LA_0RD0RB
1RB---_1RC1RA_1LD0RB_1LB0LC
1RB0LC_0LA1RA_1LA0RD_1LD1RC
1RB0LC_1LA1RA_1LA0RD_1LD1RC
1RB0LC_1RC0RA_1LA1LD_1LC---
1RB0LD_0LC1RA_1LC1RD_1LA0RC
1RB0LD_0LC1RD_0RD1LC_1RB1LA
1RB0LD_0LC1RD_1LA1LC_1RB1LA
1RB0LD_0LC1RD_1LD1LC_1RB1LA
1RB0LD_0LC1RD_1RA1LC_1RB1LA
1RB0LD_0LC1RD_1RB1LC_1RB1LA
1RB0LD_0RC1RA_1LC1RD_1LA0RC
1RB0LD_1LC0RA_0LD1LB_1RD1LA
1RB0LD_1LC0RA_0RA0LB_1RD1RC
1RB0LD_1LC0RA_0RB1LB_1RD1LA
1RB0LD_1LC0RA_0RD1LB_1RD1LA
1RB0LD_1LC0RA_1RB1LB_1RD1LA
1RB0LD_1LC0RA_1RD1LB_1RD1LA
1RB0LD_1LC1RA_1LC1RD_1LA0RC
1RB0LD_1LC1RD_0RD1LC_1RB1LA
1RB0LD_1LC1RD_1LA1LC_1RB1LA
1RB0LD_1LC1RD_1LD1LC_1RB1LA
1RB0LD_1LC1RD_1RA1LC_1RB1LA
1RB0LD_1LC1RD_1RB1LC_1RB1LA
1RB0RC_1LC1LD_1RA0LB_1LB---
1RB0RD_1LC1LB_1RD0LB_0RD1RA
1RB1LA_0LA1RC_1RB1LD_1RB0LC
1RB1LA_1LA1RC_1RB1LD_1RB0LC
1RB1LA_1RC0LD_0LA1RD_1RC1LB
1RB1LA_1RC0LD_1LA1RD_1RC1LB
1RB1LB_1LA0RC_1RB0LD_1RD1LC
1RB1LC_0LC1RB_1LA1RD_1LA0RC
1RB1LC_1LA1RB_1LA1RD_1LA0RC
1RB1LC_1RC1RB_1LA1RD_1LA0RC
1RB1LD_0LC1RA_0RA1LC_1RB0LA
1RB1LD_0LC1RA_1LA1LC_1RB0LA
1RB1LD_0LC1RA_1LD1LC_1RB0LA
1RB1LD_0LC1RA_1RB1LC_1RB0LA
1RB1LD_0LC1RA_1RD1LC_1RB0LA
1RB1LD_1LC1RA_0RA1LC_1RB0LA
1RB1LD_1LC1RA_1LA1LC_1RB0LA
1RB1LD_1LC1RA_1LD1LC_1RB0LA
1RB1LD_1LC1RA_1RB1LC_1RB0LA
1RB1LD_1LC1RA_1RD1LC_1RB0LA
1RB1LD_1LC1RB_1LA0RD_1LA1RC
1RB1LD_1RC1RB_1LA0RD_1LA1RC
1RB1RA_0RC0RB_1LC1LD_0RA0LA
1RB1RA_1LC0RB_1LB1LD_0RA1RB
1RB1RA_1LC0RB_1LB1LD_1RA1RB
1RB1RA_1LC0RD_0RA1LD_1LC1RB
1RB1RA_1LC0RD_1RA1LD_1LC1RB
1RB1RA_1LC1RD_0RA1LB_1LC0RB
1RB1RA_1LC1RD_1RA1LB_1LC0RB
1RB1RC_0LA1RB_1LD0RC_1LC1LA
1RB1RC_1RC1RB_1LD0RC_1LC1LA
1RB1RD_1LC0RA_1LA0LB_1RA---
1RB1RD_1LC1RB_1LD1LA_1LC0RD
1RB1RD_1RC1RB_1LD1LA_1LC0RD
```

## Fuel track: DONE (62/62 boarded)

The scoping above was executed in the follow-up session: the class
refinement AND the per-SCC gate both landed as new files
(`Checkers/FuelSCC.v`, `Checkers/FuelWide.v`; Fuel.v / FuelClass.v /
Closure.v untouched), and all 62 `neverqh_fuel` holdouts are proved
(`Machines/Fuel_Batch_{01,02,03}.v`, manifest
`tools/fuel_manifest.tsv`, coverage 3152 -> 3214).  Key design notes
for reuse:

- **The runner rule as a lex disjunct, not a peeling stage.**
  [fscc_edge_ok] = lex-good OR gate-internal-with-every-component-
  non-increasing.  The emitted certificates keep gate edges
  "equal" at every component (rank components are computed over the
  peeling graph PLUS gate edges; rule-(a) components have delta <= 0
  on residue edges by construction; later measure gates never touch
  gate nodes since a gate is a full SCC).  The descent proof then
  needs no peeling-sequence induction: outer well-founded induction
  on the lex tuple, inner induction on the right-window bound.
- **Lower-bound classes suffice.**  The C verifier's exact capped
  counts (with the disjunctive cap split) were not needed: FuelClass
  F0/F1/F2 lower bounds with deterministic finc/fdec transitions
  catch all 62, because the runner SCCs cross only window-blank
  cells (classes constant around the cycles).
- **The refined instance is plumbing, not proofs.**  fw_succs pairs
  the base ng_succs branches with ONE class update read off the
  window; finc_sound/fdec_sound close the covering obligations.
  Anyone adding another context refinement should copy that shape.

Possible next customer of FuelSCC: the 17 `neverqh_drift` holdouts
(rule (c3), net-drift SCCs with fuel on the drift side, verify.c
~4300).  The gate check would swap "every node moves right" for a
per-SCC Bellman-Ford drift certificate; the record argument changes
(records via strictly-positive net displacement instead of monotone
motion), so [runner_find]'s window induction needs a drift variant,
but the FuelSCC edge-gate/descent skeleton and the FuelWide class
plumbing should carry over.

## RepWL session 1: DONE (106/106 boarded)

`Checkers/RepWL.v` is complete and sound (`rw_check_neverqh_sound`,
functional_extensionality_dep only) and all 106 `neverqh_rwlrank`
holdouts are proved (`Machines/RepWL_Batch_{01..04}.v`,
`tools/repwl_manifest.tsv`; coverage 3464 -> 3570 of 3713, the
rwlrank family cleared).  What remains of the original two-session
plan is SESSION 2 ONLY: wire `rw_check_neverqh` into the census
`decide_easy` as a tier (plus the wrap/QHBound tier), sweep the
31,758 wrap-survivor residue with `tools/repwl_prover.py` to measure
the kill rate, regenerate `Deferred_*`, and re-run `make census`
once for both tiers.  Remaining holdout families after this board:
102 irules-deferred, 17 neverqh_drift (FuelSCC gate + a (c3) drift
descent variant), the counters tail (wave 6, tower 4, xd 3, ...),
and the 1 upstream-open machine.

## Next: the RepWL port (two sessions)

Highest-leverage block left, paying on both ledgers: the 106
`neverqh_rwlrank` holdouts AND the ~25-30k RepWL-class machines that
dominate the 52,326-machine census residue.  Derisked by three
existing artifacts: Coq-BB5 ships a BB4-flavored `Decider_RepWL.v`
(1,320 lines, `../Coq-BB5/CoqBB5/BB4/Deciders/`, with the
`RepW_match`/`RepWL_match` concretization relations and the closed-set
construction proved); the `Closure.v` engine is generic over the
abstraction (plug in context type + injective enc + `succs`/`covers`
and ranks, the lex gate, and the FuelSCC runner gate all come free);
and the rwlrank measure vocabulary is small and documented
(`../BBB/docs/neverqh.md`: `N/A,N/L,N/R` block counts + `0/l,0/r`
interior blank counts, with exact per-node deltas -- the `comp_exact`
contract).

- **Session 1** (fuel-session shape): `Checkers/RepWL.v` instance +
  measure vocabulary + exactness lemmas, Python mirror forked from
  the fuel generator, differential-validate the 106 certs
  (`../BBB/results/certs_rwlrank`, params `block`/`threshold` per
  cert), board as `Machines/RepWL_Batch_*.v` with corruption tests.
  Two design risks to settle on day one: the tape-model impedance
  (Coq-BB5 is directional head-between-cells; BBB4 is head-on-cell
  `nat -> Sym` sides -- re-derive `covers`/`succs_sound` locally, do
  not transcribe), and the single-step contract (`succs_sound` is one
  concrete step to one covered successor, so the RepWL step relation
  must peel the front word at symbol granularity, no macro-jumps).

  **SESSION 1 STARTED -- design validated, prover built, 106/106
  catch-rate measured.**  `tools/repwl_prover.py` is the executable
  design spec for `Checkers/RepWL.v` (its docstring pins the context
  shape, step, and normalization): head-on-cell configs
  `(q, hp, buf, litems, ritems)` with whole-block buffers
  (|buf| in {L, 2L, 3L}), symmetric nearest-first item lists (left
  words stored mirror-image so both sides run one code path),
  fold-on-|buf|=3L with RLE merge saturating at T, cap-branch on pop
  (mirror of verify.c `wg_succ`, re-expressed symmetrically), the
  five documented measures with per-node deltas (`rdelta` /
  `arrival_info` implement the exactness argument's witness bits).
  Rules (a)/(b) with the cert measures discharge EVERY state of all
  106 rwlrank holdouts at t=0; largest closure 13,994 abstract
  configs (fine for vm_compute).  Coq progress (all Qed, committed): denotation
  (items_den/side_den), the symmetric step, rw_succs_sound,
  injective encoding (rconf_enc_inj), seed (chunk/rle +
  rw_seed_covers), and the wf layer (item_wf, rw_covers',
  rw_succs_sound').  REMAINING, with the design pinned:

  1. STRENGTHEN item_wf to [w <> [] /\ 1 <= c /\ (cap -> 2 <= c)]
     with [2 <= T] threaded through the checker (certs all have
     T in {2,3}).  Reason: the interior measures' "nonblank beyond"
     bit counts a first item's word when [2 <= c || cap]; a
     c=1-capped item admits k=1 vs k>=2 expansions that differ in
     the bit, so no per-node delta is exact -- cap must imply >= 2.
     Preservation: merge gives c1 = min (S c0) T >= 2 when c1 = T
     or cap0 (c0 >= 2); new items are (w,1,false) since T >= 2.
  2. Measures: values on cconf -- countnb (1s) and ibc (interior
     blanks: cell = S0 with a nonblank strictly farther in the
     list); rwmeas := RwNA|RwNL|RwNR|RwZL|RwZR.  Deltas on the node
     via arr_s2 (arrival cell: buffer head, else first item word's
     head, else S0), arr_nbb (beyond-arrival bit: rest-of-buffer ||
     items_nb, else tl w0 || (2<=c||cap)&&nonblank w0 || items_nb
     rest), dep_nbb (departed side: whole old side).  Exactness
     correspondences: arr_s2 = chd of the concrete side (wf: k >= 1
     and w0 nonempty make expansions start with w0); blankness of a
     side <-> word_blank buffer && ~items_nb items (wf makes every
     item contribute >= 1 copy, so items_nb is exact both ways);
     ibc equations ibc(w::l) and ibc(ctl l) are definitional.
  3. Checker: rwcomp := RwRankE (phi : list (positive*nat)) |
     RwMeasE (m : rwmeas) (K : nat) phi (gate : list positive),
     denote to LexMeas rconf (rw_mval m) (fun a _ => rw_delta tm m a)
     with rconf_enc keys; instantiate closure_check_neverqh_lex with
     rw_succs/rw_covers'/rconf_enc/rw_state, seed rw_seed L T at
     csteps t; params (L T t fuel).  Gate 1 <= L, 2 <= T.
  4. Python: align repwl_prover.py's seed to the Coq chunk/rle of
     the CTAPE lists (sim with explicit (l,h,r) lists, not a tape
     dict), mirror rw_delta/arr_* exactly, re-run the 106 survey,
     then fork the emitter (gen_repwl_certs.py) emitting
     RwRankE/RwMeasE tables keyed by rconf_enc + the
     `apply (rw_check_neverqh_sound ...)` theorems, batch as
     Machines/RepWL_Batch_*.v, corruption tests, manifest
     repwl_manifest.tsv wired into check_coverage.
- **Session 2**: wire the checker into the census `decide_easy` as a
  tier, sweep the 31,758 wrap-survivor residue with the Python
  mirror to measure the kill rate, regenerate `Deferred_*`, re-run
  `make census` (native switch, 2-3h wall).  Kept separate so
  session 1 never blocks on the census rebuild loop.

<!-- --- census verified-tiers wiring session (2026-07-18) --- -->

# Census verified-tiers session: D_census 56,039 -> 19,735

**CERTIFIED 2026-07-18**: `census_decided : forall tm, QHBound B_census
tm \/ Deferred D_census tm` is Qed through the kernel with the new
tiers and the 19,735-machine deferred list; `Print Assumptions` =
`functional_extensionality_dep` only.  Merged with main (disjoint
drift/irules tracks; only NEXT_SESSION needed a keep-both resolve).

Wired the two new verified tiers into the census `decide_easy` and
regenerated the deferred list.  Branch `claude/census-verified-tiers-
wire-e51w4e` (PR #11).

## What shrank the deferred list

The 52,326-machine residue was cut by 36,304 at census-walk time by
three parameter-closed tiers (no per-machine certs in the walk):

- **wrapped QHBound, plain acyclicity** (`ngram_check_qhbound`, tier Q):
  5,307 prefix-quiet quasihalters -> R_QH.
- **wrapped QHBound, lex gate** (`ngram_check_qhbound_lex` + in-Coq
  RankSearch certs): 5,486 more -> R_QH.
- **RepWL** (`rw_tier` in `Census/RepWLSearch.v` -> the verified
  `rw_check_neverqh`, tier W): 25,511 never-QH core machines -> R_NeverQH.
  Ladder (`rw_rungs_census`) is t=0 only, (L,T) in {(2,2),(3,2),(4,2),
  (2,3)}, `rw_fuel` 8192 (the 16-rung grid measured ZERO catches at t>0;
  closure sizes p50 185 / p99 1,010 / max 3,963, all under the fuel).

New residue 16,022 = 9,775 wrap-QH survivors (need a stronger measure/
pattern QHBound gate) + 6,247 never-QH survivors (need rwlrank measures
or bigger rungs).  D_census = 3,713 holdouts + 16,022 = **19,735**.

Sweep mirrors / artifacts (untrusted): `tools/sweep_qhbound_lex.py`,
`tools/sweep_repwl_residue.py`, `tools/finish_repwl_sweep.py`,
`tools/regen_residue.py` (reproduces Deferred_* from the committed
`*_caught.tsv` + `wrap_residue_survivors.txt`); validation probes
`tools/gen_tier_probe.py` (94/94 qhb + 40/40 rw machines pass through
the Coq checkers via vm_compute); corruption tests in
`Tests/Census_Corruption.v`.

## GOTCHA: the tiers made the census walk ~100x slower per machine

Newly-undeferred machines now run the full ngram->rank->qhb->rw ladder
(~46ms/pop vs ~0.1ms with the old fat deferred list).  The residue-heavy
1RB/0RB grandchild subtrees became **>2.5h single native_compute walks**
-- longer than the remote container's ~2h preemption window, so they
never certified monolithically (watched it restart 5x).

FIX (this session): generalize Run_Split2 to a **great-grandchild
split** of the 7 heavy grandchildren (1RB_0LC/0RC/1LA/1LB/1RC,
0RB_1LC/1RC).  `tools/gen_gsplit_heavy.py` expands each grandchild's
first undefined transition into its 12/16 fills (node_expand_spec),
emitting `Census/Run_Split_<tag>.v` + 104 `Compute/GGH_<tag>_*.v`
sub-walks (few min each) + replacement `Compute/G_<tag>.v`.  `make
census` order updated.  Result: every walk unit fits the window and is
resumable (skips done .vo), so restarts cost only in-flight sub-walks.

If splitting a future regeneration's heavies: add rows to
`gen_gsplit_heavy.HEAVY` (the (A0,B0,w,w2,d2,nx2) tuples), regenerate,
wire the Makefile globs.  If a sub-walk itself exceeds the window, split
it again (same tool, one level deeper).
<!-- --- drift track --- -->
## Drift track (this session): the 17 neverqh_drift holdouts are boarded

Rule (c3) is formalized (`theories/Checkers/Drift.v`,
`ngram_check_neverqh_driftw_sound`) and all 17 upstream
`neverqh_drift` machines have theorems in
`theories/Machines/Drift_Batch_01.v` (coverage 3,570 -> 3,587; the
`neverqh_drift` line is gone from `check_coverage.py`'s remaining
table).  Key facts for future sessions:

- The descent generalizes FuelSCC's window induction to the measure
  `W * R + phi a` with untrusted Bellman-Ford potentials; fuel is
  needed only at TOWARD-moving gate nodes (weaker than verify.c's
  all-intra-active premise), and the record argument is not used
  directly -- the window bound of Records.v already carries it.
- Two disjoint per-state gates (R and L drift) are REQUIRED: two of
  the 17 have a single state with opposite-drifting stuck SCCs, so
  the FuelSCC mirror-orientation trick cannot work.  Disjointness
  makes at most one budget live per node (`dbudget`), keeping the
  descent one nat induction.
- `tools/drift_prover.py` mirrors the checker (dw_procedure +
  dw_state_check); `tools/gen_drift_certs.py --dry-run` re-measures
  the catch.  All 17 land at n=2 t=0 in seconds; deferral mechanism
  (tools/drift_deferred.tsv) exists but is empty.
- The drift gate strictly subsumes the (c2) runner gate (a uniform
  fueled right-mover SCC has trivially feasible potentials), so new
  fuel-shaped SCCs can also be discharged by this checker if a
  future track wants one engine instead of two.

<!-- --- irules multi-decrement track --- -->
## IRules multi-decrement track (general step-size decrements)

Boarded ALL 42 of the `certs_modclass` v3 irules holdouts tagged
"decrement delta(s) [-2]/[-3] (v1 engine supports -1 only)"
(`tools/irules_deferred.tsv`).  Coverage 3587 -> 3629
(`irulesk_manifest.tsv` wired into `check_coverage.py`).  Checker
`theories/Checkers/IRules/RulesK.v` + `MetaK.v`, both
`functional_extensionality_dep` only; the v1 `Engine`/`RLE`/`Expr`/
`Rules`/`Meta` are untouched.  Build the batches at `-j1`/`-j2` (this
container OOMs compiling IRules batches at `-j4`); each machine's
`vm_compute` runs a ~1-2.8M-step concrete anchor re-simulation (~4 s).

Two mechanisms, both reusing the same applier:

1. General step-size decrements.  `find_binding` (the binding-run
   selection) is UNTRUSTED.  Soundness comes only from the guard
   `expr_ge lo Rex 1` plus `appK_side`'s per-decrement survival re-check
   `e + d*Rex >= lb + d` (the run's minimum over the R rounds is its
   last-round value).  So the R-fold application is sound for ANY `Rex`;
   the division/binding search only has to produce the `Rex` that lands
   the drained run exactly, and the proof never mentions it.  This kept
   `ruleK_apply_sound` a line-for-line generalisation of
   `Rules.rule_apply_sound` (same induction on R, reusing `vvals` /
   `rstart` / `rend` / `rule_sem`).

2. Rule-in-rule application (one level).  Ten of the 42 have a rule
   whose proof applies an already-validated lower-index rule; without it
   the replay ratchets over a symbolic-count run (the head crosses it
   via a multi-step maneuver the engine peels cell-by-cell -- verified
   by instrumenting the C verifier: rule 2 of
   `1RB0RA_0RC1LD_1LC0LA_0RD0RB` applies rule 1 at op 5).  This is NOT a
   new engine op: `check_rulesK` validates rules in index order and
   threads the already-validated ones into each rule's replay via
   `ruleK_check`, reusing `ruleK_apply`; `check_rulesK_sound` discharges
   `replayK_sound`'s per-rule Reach obligation with `ruleK_apply_sound`,
   so the dependency (strictly lower index) is well-founded.  The
   corruption tests show it is load-bearing (a dependent rule validated
   before/without its dependency fails).

Differentially confirmed against the C verifier: `bin/verify` accepts
all 42; `tools/irulesk_prover.py` (faithful mirror: engine port +
binding-run applier + rule-in-rule) accepts the same 42 and validates
all 504 rules across the 428 v1 certs -- no false positives.

UPDATE (this session): the 3 `d=-1 only, but v1 engine bound reasoning
fails` rows are NOT actually out of scope -- that note was about the v1
`Rules`/`Meta` engine.  The general-delta `RulesK` engine's per-decrement
survival re-check discharges all three (`1RB1RD_0RC0RD_1LC0LA_0RB1LD`,
`1RB1RD_0RC1LD_1LC0LA_0RD0RB`, `1RB1RA_0RC1LD_1LC0LA_0RD0RB`); the mirror
passes them and the Coq checker closes each by `vm_compute` (~24 s anchor
re-sim).  Boarded as `Machines/IRulesK_Batch_07.v` (no checker change --
same `irulesk_check_neverqh_sound`), manifest rows appended.  Coverage
3635 -> 3638.  The only remaining irules blockers are the 44 v6 `rulepfx`
+ 6 v7 (`rulepfx`,`rulerunm`) and the 1 v4 `certs_geom` machine.

<!-- --- irules block-run track (added by the block/rule-prefix session) --- -->
## irules BLOCK-RUN track -- Phase 1 LANDED (6 boarded, 3629 -> 3634)

Target: the 50 irules holdouts whose certs use block runs -- the 6 tagged
`v3 cert, needs blk` (Phase 1) and the 44 tagged `v6 cert, needs
blk,rulepfx` (Phase 2).  A run's symbol may be a BLOCK id `>= 2`
(`blk <id> <cells>`); a run `(B, e)` denotes `e` copies of `B`'s cell
sequence, not `e` copies of one symbol -- the CRUX.

### Landed this session (all green, `functional_extensionality_dep` only)

The full block checker vertical is built, sound, and BOARDS 5 of the 6
v3-blk holdouts through the actual Coq checker (`vm_compute`):

- **`theories/Checkers/IRules/EngineK.v`** -- the block symbolic engine
  against `bdside tbl` (parametric in the UNTRUSTED table): `bdside` /
  push / merge / trim; `beng_step` = concrete step + chain hops + block
  PEEL + block HOP, `beng_step_sound` a `Reach`.  Block-HOP crux:
  `hop_sim` (one-copy zipper replay, each step one `cstep`) ->
  `hop_one_reach` -> `hop_copies` -> `bhop_result` (replay + primitive-
  root reduce + table lookup + re-verify) -> `bhop_reach`.
- **`theories/Checkers/IRules/RulesBlk.v`** -- `ruleBlk_apply` +
  `ruleBlk_apply_sound`, rule-in-rule `check_rulesBlk`, driver
  `breplayK`, sound cell-stream end-equality `bstreams_eq` (expand
  constant block runs + `merge_adj` + structural compare -> exact
  `bdside` equality), and the driver canonicalization `bcanon` =
  re-block (`breblock_side`, untrusted greedy re-encode VERIFIED by
  `bstreams_eq`) + whole-copy `babsorb` (proven denotation-preserving).
- **`theories/Checkers/IRules/MetaBlk.v`** -- `irulesblk_check_neverqh`
  (block table via `mk_tbl`, `raw_ok` by construction; templates,
  anchor re-sim, state coverage; end-match strict-or-`bstreams_eq`) and
  `irulesblk_check_neverqh_sound : ... -> NeverQuasiHaltsSt`.
- **`theories/Machines/IRulesBlk_Batch_01.v`** -- 5 boarded machines;
  **`theories/Tests/IRulesBlkBatch_Corruption.v`** -- negative controls
  (honest true; transition / block-table / rule-delta / meta-a / meta-b
  mutants all `false`).  `tools/gen_irulesblk_certs.py`,
  `tools/irulesblk_manifest.tsv`, one `check_coverage.py` tuple,
  marked `_CoqProject` block.  (`tools/irulesblk_prover.py` was the
  de-risking scaffold: it measured the minimal mechanism set and diffed
  against `bin/verify`; the ground truth is `bin/verify` + the Coq
  checker.)

### LANDED: the 6th v3-blk (partial absorb) -- 3633 -> 3634

`1RB0RD_1LC1LB_1RD0LB_0RD1RA` (14 blocks, 6 rules, anchor 9,999,528) is
now boarded.  Its `iv_absorb_side` does PARTIAL (symbolic-remainder)
absorbs -- a single-cell run contributes only PART of its cells (`need+1`)
to complete a block copy and stays, decremented, rather than the whole
copy sitting as separate count-1 runs.  Instrumenting `bin/verify`
(`DBG_ABSORB`) showed this machine's partials are on CONST runs
(e.g. block 7 `10111`: a `1x3` run gives 1 leading cell, leaving `1x2`).

Formalized in `RulesBlk.v` with an UNTRUSTED-candidate + re-verify design
(same philosophy as `breblock_side`), so the peel logic never enters the
trust surface:

- `bpeel_rev tbl budget rrs` -- untrusted: peel `budget = length (tbl s)`
  concrete cells off the RIGHT of `acc` (= FRONT of `rev acc`), consuming
  single-cell const runs, decrementing the leftmost touched run.
- `babsorb_partial lo tbl acc s e rest` -- proposes `new_acc := rev (bpeel_rev ...)`,
  then GATES on `expr_ge lo e 0 && bstreams_eq tbl lo acc (new_acc ++ peel_cells tbl s)`
  (i.e. `acc` denotes `new_acc` followed by exactly one block copy), and
  returns `new_acc ++ (s, e+1) :: rest`.
- `babsorb_partial_den` -- soundness: `bstreams_eq_sound` gives
  `bdside acc = bdside new_acc ++ tbl s`; the symbolic block-run `+1`
  rides the same `cnt_succ` + `nreps_S` fold as the whole-copy case.
  A wrong peel just fails the `bstreams_eq` re-check -> no absorb (sound).
- Wired as the `else` branch of `babsorb_go` at a block run (whole-copy
  fast path unchanged, so the other 5 machines are untouched); `bcanon`,
  `babsorb_iter`, the driver, and `MetaBlk` need no change.

Negative control: `theories/Tests/IRulesBlkPartial_Corruption.v` (block-7
cells mutated -> checker `= false` at rule validation, 1.3 s).  Axiom
footprint `functional_extensionality_dep` only; `check_coverage` now 3634.
All 6 v3-blk holdouts boarded; Phase 2 (44 v6 `rulepfx`) is the next block.

### Phase 2 (rulepfx, the 44 v6) -- deferred, on top of Phase 1

Add prefix matching to the applier (a `rulepfx` side matches only the
first `r->nl` near-head runs and splices the untouched rest back; a
non-prefix side keeps exact-count matching and must not be a sentinel
side) + sentinel sides to the engine (a prefix rule's OWN validation
treats its prefix sides as opaque; `beng_step`'s `[] ->` branch must fail
when `sent[side]`, so the proof reads only the declared runs).  Check
whether the 44 need v6 `rmdok` (a binding drain leaving remainder
`rmd = (e-lb) mod d`, ending at `lb+rmd-d`); the survival check already
covers it, only the drop-to-0 condition changes in a forked
`find_binding`/`appBlk_side`.  Fork `RulesBlkPfx.v` / `MetaBlkPfx.v` +
`IRulesBlkPfx_Batch_*.v` + corruption tests; differential-validate the 44
vs `bin/verify` first.  Machines whose certs ALSO need
`rulerunm`/`mmrow`/`nvar` are out of scope (re-check per cert).
<!-- --- irules block-prefix track (phase 2) --- -->
## irules Phase 2 LANDED (2026-07-21): all 50 boarded, coverage 3,688, D_census 16,065

The 44 v6 (`rulepfx`+`rmdok`) + 6 v7 (`rulerunm`) holdouts are boarded
through a verified checker; only the 1 v4 `mmrow` machine remains of the
irules family. Files (all `functional_extensionality_dep` only):

- **`Checkers/IRules/EngineKS.v`** — sentinel-aware fork of the block
  engine ([EngineK] untouched). THE design idea: soundness is stated
  against the SUFFIX-EXTENDED semantics `bsemX` (each side denotes its
  runs ++ an arbitrary opaque cell suffix, `[]` forced on non-sentinel
  sides), so a validated prefix rule's `Reach` holds for EVERY
  continuation of its opaque sides — exactly what splice-back
  application needs. `bpushS` keeps a blank pushed onto an empty
  sentinel side as CONTENT (mirror of `iv_rebuild_side`); the
  app-exhausted branch hard-fails on sentinels.
- **`Checkers/IRules/RulesBlkPfx.v`** — `BRuleP` prefix rules over
  `BC/BV/BVm` run counts. `appBlkPfx_side` decomposes (proved:
  `appBlkPfx_decomp`) into an EXACT application on the matched
  near-head runs + spliced rest, so the Phase-1 denotation-lemma
  structure carries over; the `BVm` residue-lattice case rides a
  `latt_ok` guard checked in the applier (exact division available by
  inversion). `rmdok` needed ONLY an untrusted `find_bindingP` fork —
  the applier's per-decrement survival re-check makes any `Rex` sound,
  so the remainder logic carries zero proof weight. The whole-rule-on-
  sentinel-side guard (`pfx || ~sent`) is enforced and load-bearing in
  `ruleBlkPfx_apply_sound` (the `YL/YR` instantiation needs it).
- **`Checkers/IRules/MetaBlkPfx.v`** — the checker; scalar meta layer
  identical to MetaBlk; meta replay runs sentinel-free with `bsemX_nil`
  recovering `bsem`.
- **`Machines/IRulesBlkPfx_Batch_01..05.v`** (10/file, emitter
  `tools/gen_irulesblkpfx_certs.py`, manifest
  `tools/irulesblkpfx_manifest.tsv`, wired into check_coverage) and
  **`Tests/IRulesBlkPfxBatch_Corruption.v`** (honest controls pass at
  fuel 3000; REJECTED at the same fuel: pfx flag flip, rmdok lb shift,
  block-table cell, meta map v6+v7, sentinel read-past = deleting a
  LOAD-BEARING drain run from a prefix side, lattice delta).

### Measured lenience classes (soundness-preserving; document, don't "fix")
- Tampers that make the lattice run STRUCTURALLY dead (`res`/`mod`
  violating the parse-time constraints verify.c enforces) are ACCEPTED:
  the dead rule self-validates or the meta replay routes around it with
  cheap symbolic engine steps, and everything actually verified stays
  true. Same class as PHASE2_DESIGN §6's non-minimal-`lb` gap.
- Deleting a trailing NON-load-bearing prefix run yields a valid
  GENERALIZED rule (its content joins the opaque rest) — accepted.

### Conveyor-belt step done (proven tier) -- base `make` GREEN with the new tables
`tools/proven_map.tsv` is now COMMITTED (reconstructed from the
manifests; reproduction test: its 3,620-row subset regenerates the
committed `Proven_*.v` byte-identically — the audit's file/theorem
picks and (file, theorem) sort are exactly recoverable). Regenerated at
3,670; `proven_dropped.txt` extended; `regen_residue.py --proven-only`
asserts now 3670/43/16065. `Deferred_*` regenerated: **D_census =
16,065**. Census re-cert = stable-hardware (`make census-verify` +
`tools/census_cache.py --update`).

### Environment note (2 preemptions this session)
The container was FULLY re-provisioned twice (repo re-cloned at origin,
/root and /tmp wiped, uncommitted work LOST). Rules that saved the
session: commit+push after EVERY artifact; and **apt now ships Coq
8.18.0 on Ubuntu 24.04 (`apt-get install coq`, ~2 min)** — exactly our
pin, vm_compute-capable (no native_compute, fine for everything except
the census walk). Use apt coq for container sessions; the opam census
switch is only needed on the stable box.
<!-- --- end irules block-prefix track --- -->

<!-- --- end irules block-run track --- -->

<!-- --- census D-shrink session (2026-07-19/20): proven tier + B/C grind post-mortem --- -->

# Census D_census shrink (2026-07-19/20): proven tier LANDED; B/C in-walk grind ABANDONED

## TL;DR / the one lesson
**Shrink D_census by PROVING machines (they drop out via the zero-cost proven
tier), NOT by un-deferring machines into expensive in-walk tiers.** The latter
makes the census native_compute walk hours-long per subtree, which CANNOT
certify in a container that preempts every few min-30min. Measure the per-unit
walk time BEFORE committing to any lever that un-defers into an in-walk tier.

## What worked and is banked (committed + pushed)
- **Proven-machines tier (lever A): -3,620, ZERO walk cost.** `Census/Proven_00..07.v`
  + `Proven_Data.v` (tools/gen_proven.py), `proven_lookup` in Decide.v before the
  deferred tier, WF via `Forall NeverQuasiHaltsSt` over the batch theorems. This is
  the compounding conveyor belt: any machine that ever gets an individual Coq
  theorem drops out of D_census for free at the next regen.
- **Measurement of all three levers** (parallel opus sweeps): A proven audit
  (3,620 usable), B qhb-lex over 9,775 wrap-QH survivors (2,533 catch, larger
  prefix rungs), C RepWL over 6,247 never-QH survivors (592 catch, (5/6/7,2,0)).
- **Recon roadmap** (tools/recon_20260719/): FAR post-mortem (SKIP -- safety-only,
  liveness-dead despite 100% nonhalt coverage), re-root normalization bridge
  (~1,300 more via one small lemma; residue is 9,917 distinct upstream-solved
  machines), irules Phase 2 differentially validated (-50 holdouts).
- **Deep-split tooling** (tools/gen_gsplit_deeper.py, tools/census_grind.sh):
  recursive great-great-grandchild splitter + self-splitting resumable grinder.
  Correct and reusable IF a STABLE long-lived compute env is ever available.

## The wild goose chase -- DO NOT REPEAT here
Levers B (qhb-lex, +2,533) and C (RepWL, +592) un-defer machines that then run the
full ngram->rank->qhb->rw ladder DURING the census walk (~46ms+/pop, vs ~0.1ms for
a deferred-lookup skip). This made the residue-heavy grandchild subtrees
(1RB_1LC, 0RB_1LC, ...) into MULTI-HOUR single native_compute walks. Deep-splitting
them (recursive node_expand) makes units smaller, but those subtrees are so large
(GG_1LC_0LB alone: 331+ sub-walks, not done after 8h; est. 6,000-10,000 total
sub-walks) that the full 12,974 grind is **1-2 WEEKS**. And the container preempts
every few min-30min, so hours-long units NEVER complete -- confirmed stalled
(+5 .vo in 1.5h). Structurally impossible in this environment.
The SCOPING instructions warned exactly this ("a lever that recovers few machines
at high walk-cost may not be worth the cert-time tax"). B/C were that.

## THE RIGHT WAY to shrink D_census (do this going forward)
1. **Keep the census walk LIGHT.** Deferred list stays fat enough that every
   subtree walk is "few min" and fits a container window (the 19,735 cert had this;
   it certified in 2-3h with the great-grandchild split, units "few min each").
2. **Shrink only via per-machine PROOFS + the proven tier.** Prove a machine
   (holdout cert or residue cert), add it to the proven table, regen Deferred to
   drop it. Walk cost unchanged (fast proven lookup). This is the sustainable loop.
3. **Next levers, all proof-producing (proven-tier-cheap):**
   - Re-root bridge (~1,300): `neverqh_reroot`/`qhbound_reroot` (~20-30 line
     StA-variant of visits_swap/quiet_swap) + a reroot table. tools/recon_20260719/
     BRIDGE.md + reroot_mapping.tsv. Also gives free de-dup (12,897 rows = 9,917
     distinct) and ~1,295 <=3-state-core reductions.
   - irules Phase 2 (-50 holdouts): fork RulesBlkPfx/MetaBlkPfx. PHASE2_DESIGN.md.
   - Bouncer/segment checker (residue mass lever): verified checker over upstream
     certs_bouncer period_records+segments -> per-machine certs -> proven tier.
     (Bouncers are common here; reference in bbchallenge-deciders + BB5 project.)
4. **Do NOT re-enable the qhb-lex/RepWL in-walk tiers (B/C)** unless a stable,
   long-lived native_compute environment is available. Their tables (Deferred at
   12,974, sweeps, gen_gsplit_deeper) are committed for that scenario only.

## This session's actual deliverable: proven-only cert (D_census 16,115)
Pivoted from 12,974 (abandoned) to proven-only: **D_census = 16,115 = 93 holdouts
+ 16,022 residue** -- drop ONLY the 3,620 proven-nqh machines; B/C residue and the
16 provenQH stay deferred. Walk is LIGHT (B/C deferred, monolith units "few min
each"), so it certifies within container windows via .vo-skip resume. The B/C
rungs stay wired in Run.v but are dead code (their machines are deferred, caught
before the rungs fire). [status filled at cert completion]

## Env note (container instability, 2026-07-20)
The container preempted every few min to ~30min during this session (vs stable
1.5h+ earlier). Any long native_compute (the census walk, or heavy grind units)
must be resumable and window-sized. The census `all`/`census-resume` path with
monolith units is resumable (.vo-skip). Native switch: OPAMROOT=/root/.opam,
eval $(opam env --switch=census) -- rebuild from apt if the switch is missing
(~1h; the switch survived this session's restarts on /home persistent disk).
<!-- --- end census D-shrink session --- -->

## ✅ CERTIFIED 2026-07-21
`make census` completed **GREEN on a stable WSL2 host (16 cores / 56 GB)**:
all 144 walk units + `Census_Theorem.vo` built, and `Print Assumptions
census_decided = functional_extensionality_dep` only. **D_census = 16,115 is
certified** — `census_decided : forall tm, QHBound 2000 tm \/ Deferred
D_census tm` closes through the kernel, axiom-clean. Every unit compiling also
confirms the 16,115 deferred list is COMPLETE (no machine escapes the bound
and the list). The "verification pending / DO NOT MERGE" caveat below is
RESOLVED; PR #16 is mergeable. (Original closeout retained for history.)

## FINAL CLOSEOUT (2026-07-20, session end)
Decision: **stop the census walk; close out the sound, committed work; do NOT
merge as a certified shrink.** After days wedged on the native_compute walk under
a container that preempts every few-to-30 min, the ~7h walk (16 GG_1LC heavies +
~5 heavy GGH units, ~25-30 min EACH even at the light 19,735 rungs -- confirmed
this session) could not be driven to a green `Census_Theorem.vo` here. This is an
ENVIRONMENT limit, not a proof problem.

### What IS done, verified, and committed (HEAD aac7c1b)
- `make` (base build): **GREEN**, exit 0. Builds Run.v, the 16,115 Deferred
  tables, Proven_Data (proven tier + `proven_all` certificate), Decide.v, and the
  corruption test suite `theories/Tests/Census_Corruption.v` (negative tests pass
  -> the checkers correctly REJECT tampered certs).
- `Print Assumptions` = `functional_extensionality_dep` ONLY for all three
  soundness lemmas: `proven_all` (the 3,620 dropped machines genuinely never
  quasi-halt), `decider_WF` (decider soundness), `census_from_empty` (IF the walk
  empties the queue THEN the census theorem holds).
- The shrink 19,735 -> 16,115 is **sound by construction**: the 3,620 machines
  leave `D_census` *because* the proven tier now decides them R_NeverQH, justified
  by the axiom-clean `proven_all` certificate. The corruption tests guard the
  checker against being weakened to fake this.

### What is NOT done
- `make census` (the native_compute walk producing `Census_Theorem.vo`) did NOT
  complete. So the unconditional `census_decided` theorem at D_census = 16,115 is
  **not established on this branch**. The branch proves the setup is sound and the
  theorem follows IF the walk closes; it does not (here) demonstrate closure.

### DO NOT MERGE until verified
Merging now would present an unverified shrink as certified. To finish: run
`make census` on a STABLE host with native_compute (real Linux / WSL2, >=16GB RAM,
no preemption; ~7h at -P4, faster at higher -j). When it is green with
`Print Assumptions Census_Theorem.census_decided = functional_extensionality_dep`
only, it is a certified 16,115 census and can merge. No .v file needs to change --
it is purely a compute run on the already-committed tree.

### Why it wedged (for the record)
Walk cost ~ (machines per subtree) x (per-machine pipeline incl. ~19,735-entry map
lookups). Heavy subtrees are inherently ~25-30 min single-threaded (NORMAL: the
original 19,735 census was documented "~7h at -P4"). The blocker was purely that
no reliable ~30-min window was available, and parallelism OOMs on the 16GB/4-core
container (2 heavy units ~13GB, 4 >16GB). A 64GB / higher-core host removes both
constraints at once and would finish in 1-2h.
<!-- --- end final closeout --- -->

<!-- wave track -->
# Counters wave track (2026-07-21): recon + closer landed; per-pass proof is the open work

Files (own): `theories/Counters/WaveCounter.v` (closer, COMPILES, axiom-clean),
`tools/counters/trace_wave.py` (recon tracer, validated). `_CoqProject`
block `# --- counters track: wave ---`. Targets: 6 wave_counter certs
(counter6/7/17/24/27/36) + 1 wave4_counter (#15).

## KEY FINDING: the playbook's "LapGlue suffices" is WRONG for wave.

The wave machines are PARITY-WAVE ODOMETERS, not single `positive`
counters. The event config is a variable-length BLOCK WORD

    1^{B_0} 0 1^{B_1} 0 ... 0 1^{B_m}   (single-0 separators),

head one cell past the frontier at the edge state (side R; mirror for
side L). `B_0` = lead, `B_m` = frontier. One pass = one event-to-event
run, rule (parities only, exactly verify.c `wc_expected`):
  - `out = B; out[m] += 1` (frontier increments EVERY pass);
  - scan `i = m-1 .. 0`, `par = B[i+1] + (poff if i==m-1 else 0)`;
    first ODD -> `out[i] += 1`, class `t = m-i` (wave depth), or `t=0`
    (LEAD-STOP) if `i==0`;
  - if no odd interior block and `B_0==1`: SPAWN (insert length-1 block
    after the lead), class -1; if `B_0 != 1`: UNDEFINED (-2).

The vector GROWS in length (spawns) and values (unbounded), and the
carry depth is unbounded, so a pass is a NESTED translated cycle -- NOT
one parametric run. `LapGlue` (positive + `Pos.succ`) cannot index it.

## The closer that IS right: `WaveCounter.wglue_neverqh` (LANDED).

Generalizes `LapGlue` to anchors indexed by an arbitrary state type `A`
advanced by a TOTAL successor `nextA` under a PRESERVED invariant `Inv`:
  - `Inv a0`, `Inv a -> Inv (nextA a)`;
  - `Hboot`: blank ->* `lift (Cf a0)`;
  - `Hlap`: `Inv a -> Cf a ->^{>=1} Cf (nextA a)` (up to `lift`);
  - `Hvis`: `Inv a -> every state reachable from Cf a`.
Then `NeverQuasiHaltsSt`. Proof = `LapGlue.glue_reach` with
`Nat.iter k nextA a0` as the k-th anchor. Compiles; `Print Assumptions`
= `functional_extensionality_dep` only. This is the whole outer layer;
it is DONE. The three hypotheses are the remaining work.

## The abstract state and the three proof obligations.

Take `A := list positive` (block vector, all entries >= 1, LSB=lead...
actually lead-first). `nextA := wc_expected` (parity odometer). `Cf B` =
the block-word tape above. `a0` = the boot vector (per cert
`boot_vector`, e.g. `[1;1;2;4]`). Then:

- **P2 (Inv preserved; MACHINE-INDEPENDENT, hard math).** `Inv` must
  exclude LEAD-STOP (t=0) and bad SPAWN (-2) so `nextA` stays in the
  event family. This IS verify.c `wc_parity_schema` + `wc_bootstrap`'s
  abstract chain: the parity word `e_i = B_i mod 2` evolves as an
  odometer `R` (flip `e_m`; flip `e_{i*-1}`, `i*` = highest set), and
  the safety is a RECURSIVE identity `R;R = R'` one level down (verify.c
  lines ~9544-9712). Candidate `Inv`: "B_0 = 1 AND the parity word is
  reachable from a canonical spawn word", proved preserved by the
  R;R=R' pairing induction. This is the single hardest sub-proof and is
  SHARED by all 6 machines -- do it once. (Alternatively: a weaker `Inv`
  that is obviously preserved and obviously forbids i*=1 -- OPEN whether
  one exists; the parities genuinely require the odometer argument.)

- **P1 (Hlap; PER-MACHINE, hard).** From `Cf B` reach `Cf (nextA B)`.
  Decomposition (validated for all 6 via `trace_wave.py`, and per-machine
  micro-gadgets extracted -- see table): FRONTIER-TURNAROUND (fixed ~2-3
  steps, frontier += 1, reverse to inward sweep) ++ LEFTWARD WAVE (cross
  blocks m, m-1, ... as translated cycles until the parity STOP) ++
  DEPOSIT+turnaround ++ RIGHTWARD RETURN (cross blocks back to frontier).
  The leftward wave is a FOLD over a variable-length sublist of the block
  vector, each block crossed by a 2-state (clean tier) or 4-state (hard
  tier) alternating cycle = a `WTape.cycL`/`cycR` application over the
  1-run; the SEPARATOR arrival STATE encodes the running parity and
  selects continue-vs-deposit. Needs: a `creach_iter`-style induction
  over the crossed blocks (cf. MonoCounter `creach`), plus the
  block-length translated cycles. This is the double/blockdbl nested-loop
  pattern one level richer.

- **P3 (Hvis; PER-MACHINE, easy).** Every state visited each pass:
  finite `wsteps` reflexivity witnesses off `Cf B`, as in Spacer_16
  `vis_16`. From the fired-transition traces every pass fires >=7 of 8
  transitions; a single class-1 + class-2 pass covers all 8.

## Per-machine gadget tables (from validated micro-traces, transitions
## written `state sym / write dir > next`).

Difficulty tiers by the leftward cross-cycle:

- **#17** `1RB0RD_0LB1LC_1RA1LB_1RA1RD` edge D, side R, poff 0, boot
  [1;1;2;3]. EASIEST. FT=`D0/1R>A A0/1R>B B0/0L>B`; cross-pair=`B1/1L>C
  C1/1L>B` (cycL unit u=[1;1], state B); sep-continue=`B0/0L>B`;
  deposit=`C0/1R>A`; return unit=`D1/1R>D` (D-sweep), sep-on-return=
  `D0/1R>A A1/0R>D`. Arrive-at-sep in C => DEPOSIT (odd run), in B =>
  CONTINUE (even). Start here.
- **#27** `1RB1LC_1LC0RD_0LC1LA_1RB1RD` edge D, side R, poff 1, boot
  [1;1;2;4]. FT=`D0/1R>B B0/1L>C`; cross-pair=`C1/1L>A A1/1L>C`;
  sep-continue=`C0/0L>C`; deposit=`A0/1R>B`; return=`B1/0R>D`/`D1/1R>D`,
  sep=`D0/1R>B B1/0R>D`.
- **#36** `1RB1RA_1LC0RA_0LC1LD_1RB1LC` edge A, side R, poff 1, boot
  [1;1;2;4]. FT=`A0/1R>B B0/1L>C`; cross-pair=`C1/1L>D D1/1L>C`;
  sep=`C0/0L>C`; deposit=`D0/1R>B`; return=`B1/0R>A`/`A1/1R>A`,
  sep=`A0/1R>B B1/0R>A`.
- **#7** `1RB0LC_1LA1RD_1LA1LC_0RD1RB` edge A, side L, poff 1, boot
  [1;1;2;4]. MIRROR (frontier on the LEFT, inward = rightward).
  FT=`A0/1R>B B1/1R>D`; cross-pair=`D1/1R>B B1/1R>D`; sep=`D0/0R>D`;
  deposit=`B0/1L>A A1/0L>C`; return=`C1/1L>C`, sep=`C0/1L>A A1/0L>C`.
- **#6** `1RB0LB_0LB0RC_1LD1RC_1LA1RB` edge C, side R, poff 1, boot
  [1;1;2;4]. HARD: 4-step cross cycle `C0/1L>D D0/1L>A A1/0L>B B1/0R>C`
  that WRITES 0s (the run is re-encoded during the cross); return is a
  `C1/1R>C` sweep. Budget separately.
- **#24** `1RB1LA_1RC1LD_1LD0RD_0RD0LA` edge A, side L, poff 1, boot
  [1;1;2;4]. HARD (mirror of the #6-class): 3-4 step cross cycle
  `A0/1R>B B0/1R>C C1/0R>D D1/0L>A` writing 0s. Budget separately.

## #15 wave4_counter `1RB0RC_0LC1LB_0LD1LC_1RD0RA` (edge C, boot [1;4;2]):
separate `verify_wave4_counter` (verify.c ~10462) -- read it before
coding; likely a base-4 variant of the same odometer. Do last.

## Recommended plan for the next wave session.
1. Build `tools/counters/lapwave17.py` (fork lap16.py): symbolic pass for
   #17 via `Exec.cycL`/`cycR` combinators + explicit FT/deposit/return
   `conc` units + a Python fold over the crossed blocks; `python3
   lapwave17.py 40` must match raw (differential over classes 1/2/3/spawn
   and depths to ~6). This pins the exact unit windows/walls for Coq.
2. `theories/Counters/WaveCounter.v`: add the block encoding `Wv : list
   positive -> list Sym` + decomposition lemmas (cross-fold, parity
   split). Keep machine-independent parts here.
3. P2 once (parity-safety `Inv`), P1+P3 per machine starting at #17.
4. Corruption tests `theories/Tests/CountersWave_Corruption.v` (NEW).
   Manifest rows in `tools/counters_manifest.tsv` (append only).

Budget: P2 is ~1 session (the recursive parity induction); #17 P1 ~1
session; #27/#36/#7 faster once #17's fold is generic; #6/#24/#15 hard,
budget separately. The abstract odometer is IDENTICAL across all 6
(same boot orbit) -- only the micro-gadget tables differ, so P2 and the
fold skeleton are shared.
<!-- end wave track -->

## #17 units CONFIRMED in Coq (2026-07-21, via `Compute` on `tm17`).

The block encoding is FRONTIER-FIRST: `Cf B = (edge, (l, S0, []))` with
`l = 1^{B_m} ++ 0 :: 1^{B_{m-1}} ++ 0 :: ... ++ 0 :: 1^{B_0}` (nearest
block = frontier), head on the trailing separator, right blank (side R).
Every intended unit run computes cleanly as `wsteps ... = Some ...`
(direct `Proof. reflexivity. Qed.` transcription), and the whole cls1
pass is ONE windowed run landing EXACTLY on the next event (no lift
slack). tm17 = `1RB0RD_0LB1LC_1RA1LB_1RA1RD`. Confirmed:

  - FT (br=false, 3): `(D,(1^n, S0, [])) -> (B,(1^(n+1), S1, [S0]))`
    (D0/1R>A A0/1R>B B0/0L>B; frontier + scratch, turns to left B-sweep).
  - cross-pair cycL unit (2): `(B,([S1;S1], S1, [])) -> (B,([], S1,
    [S1;S1]))`  (u=[S1;S1], w=[S1;S1]; use `WTape.cycL`).
  - odd-tail (1): `(B,([S1], S1, [])) -> (C,([], S1, [S1]))`.
  - sep-continue B0 (1): `(B,([S1], S0, R)) -> (B,([], S1, S0::R))`
    (even parity: push sep right, enter next block still in B).
  - deposit C0;A1 (2): `(C,([S0], S0, [S1;S1])) -> (D,([S0;S1;S0], S1,
    []))` (odd parity STOP: write 1 at sep, turn to rightward D-sweep).
  - D-return sep (2): `(D,([], S0, [S1;S1])) -> (D,([S0;S1], S1, []))`.
  - D-return over ones: `D1/1R>D`, one step per cell.
  - FULL cls1 pass (br=false, 14): `Cf([1,1,2,3]) -> Cf([1,1,3,4])`,
    exact -- `wsteps true false tm17 14 (D,([S1;S1;S1;S0;S1;S1;S0;S1;S0;
    S1],S0,[])) = Some (D,([S1;S1;S1;S1;S0;S1;S1;S1;S0;S1;S0;S1],S0,[]))`.

So P1 for #17 is: state these as unit lemmas, then a lap lemma that
(a) FT, (b) folds cross-pair over even blocks to the parity stop
(the arrival-state B/C = block-length parity is the whole selector),
(c) deposits, (d) folds the D-return back to the frontier event. The
fold is over the block sublist crossed = `creach_iter`/cycL induction.
The ONLY genuinely hard piece left is P2 (the shared parity-safety
`Inv`). #27/#36/#7 have the identical shape with their own unit tables
(design appendix above); #6/#24 have 4-step 0-writing cross cycles.
<!-- end wave track confirmed units -->

<!-- double track -->

# Counters track, DOUBLE session (2026-07-21): #30 recon complete, CReach landed

Own files: `theories/Counters/CReach.v` (+ planned `DblCounter.v`,
`theories/Machines/Counters/Double_*.v`, `theories/Tests/CountersDbl_Corruption.v`,
`tools/counters/{recon30,probe30,lap30}.py`); `_CoqProject` block
`# --- counters track: double ---` (appended at the very end, after wave).

## LANDED this session

- **`CReach.v`** -- the required new closer, axiom-clean (`Print
  Assumptions creach_iter` = *Closed under the global context*, no
  functional_extensionality even). `creach`/`creach_refl`/
  `creach_csteps`/`creach_trans`/`creach_iter` EXACTLY as the recon
  specified, plus two glue helpers the double laps will want:
  `creach_pos` (recover `0 < n` from a positive prefix run) and
  `creach_lap` (package the whole thing into the `LapGlue.Hlap`
  existential up to `lift`). **creach_iter's shape matched the recon's
  expectation verbatim** -- it is byte-identical to the copy session A
  already appended to `MonoCounter.v` (lines 473-521). The double
  machine files should import `CReach`, NOT `MonoCounter`, to avoid a
  duplicate-`creach` ambiguity (keep the rep-algebra they need --
  `rep011/101/110_expose` etc. -- local to `DblCounter.v`).
- **`recon30.py`** (lap segmenter, RLE at every turnaround) and
  **`probe30.py`** (unit prober). Both validated: step counts
  **431 / 1447 / 5207** for j=2/3/4 reproduce the recon's numbers
  EXACTLY; DONE decodes as D(j+1) = `1 0 (110)^(2k+1) 1^(t+3)` for
  j=2,3.

## #30 fully reconnoitred (NOT yet transcribed to Coq)

Anchor (confirmed against `verify.c` `dc_build_D`, side R):
`D(j) = (StB, (rep [S1] t ++ rep [S0;S1;S1] k ++ [S0;S1], S0, []))`,
head on the blank one cell right of the frontier, k=2^j-1, t=3j+4.
Index it for LapGlue via `Cf p := D30 (S (Pos.to_nat p))`, p0=1 -> j=2.

**Unit inventory CONFIRMED** (probe30.py, all against the real tm_30
`1RB1LD_1RC0LA_1RD0RD_1LB1RB`):
- `UTe` edge turn, br=F: `(B,([],0,[])) -3-> (B,([1],1,[1]))`.
- `wig` wiggle = **`cycL(u=[S1], rw=[], w=[S0], P=3)`**: the unit is
  `(A,([S1],1,[])) -3-> (A,([],1,[S0]))` -- one accumulator 1 becomes
  one 0 shuttled right. (The recon's `(B,([1;1],1,[]))` guess WALLS;
  the real wiggle is this A-state cycL.)
- `UJ` junction: `(B,([S1;S0],1,[])) -2-> (D,([],0,[S1;S0]))`.
- `UC` collapse: `(D,([S1;S1;S0],0,[])) -3-> (D,([],0,[S1;S0;S1]))`
  (leftward comb cycle, |delta|=3).
- `US` spread: `(B,([],0,[S1;S1;S0])) -3-> (B,([S1;S0;S1],0,[]))`
  (rightward comb cycle, |delta|=3).

**THE CRUX -- the right region is a base-4 mixed-radix counter with
carries that CHANGE LENGTH.** This is why the hand model was 2x short
and why a flat `cycR`/`cycL` lap does NOT close it. After the initial
wiggle the accumulator is `0^(t+1) 1` (a **conserved budget of t+2
cells**). The outer loop then does k+1 comb-doubling steps; between
left-edge turnarounds the right region is partitioned into chunks
`0^z 1` with **z in {2,5,8,11} = 2 + 3*digit, digit in {0,1,2,3}**,
`#chunks = m-2` where the comb is `(110)^m 11`. Chronological left-edge
turns for j=2 (comb m, digit list LSB-at-left):

```
 A@-1  m=3  [3]         B@-3  m=4  [0,2]
 A@-4  m=4  [1,1]       B@-6  m=5  [0,0,1]
 A@-7  m=5  [2,0]       B@-9  m=6  [0,1,0]
 A@-10 m=6  [1,0,0]     B@-12 m=7  [0,0,0,0]  <- overflow
```

The FINAL B-turn is the clean overflow `(0^2 1)^(k+1)` (all digits 0),
which the closing spread collapses into the new accumulator `1^(t+3)`
and re-emits the `1 0` frontier prefix -- giving D(j+1) exactly (no
lift slack observed; DONE ends on a blank with r=[]). The digit
transitions are NOT plain binary increment (lengths change: `[1,1]`->
`[0,0,1]`, `[0,0,1]`->`[2,0]`); they must be **read off the executor**,
not derived (mission's warning). This counter is richer than the
`cview` binary carry the mono/spacer families use.

## Transcription plan for the next session (the real work, ~1 full session)

1. Finish **`lap30.py`**: an OUTER python loop over the k+1 doubling
   steps, each = collapse `cycL`(UC) over the comb + a spread `cycR`
   handling ONE digit increment on the right + the A/B edge turns +
   the re-wiggle. The differential (`python3 lap30.py 300` = ALL OK
   across j and both parities) is the gate; use a DbgExec dumping the
   cfg after every combinator to pin the per-digit mid-config.
2. `DblCounter.v`: the anchor `D30`, a `positive`- or `nat`-indexed
   right-region counter type (base-4 digits `0^2 1`.. with the carry
   rule from step 1), its cview-analogue decomposition lemmas, and
   the comb rep-algebra (`rep [S0;S1;S1]` rotations).
3. `Double_30.v`: units as `wsteps` reflexivity lemmas, transported
   phases, the OUTER lap via `creach_iter` over the digit-counter
   family (likely a NESTED creach_iter: outer over comb units, inner
   over the digit carry), boundary phases (`UTe` prefix -> gives the
   `0<n` via `creach_pos`; overflow-collapse suffix), then
   `creach_lap` -> `glue_neverqh`. Boot (~vm_compute to D(2)) + visits.
4. Corruption tests in `CountersDbl_Corruption.v` (new file), manifest
   row, compile, `Print Assumptions` = functional_extensionality_dep.

**Assessment:** #30 is a genuinely hard parametric proof -- larger
than any landed counter machine -- because its "doubling" is a
length-changing mixed-radix counter, not a fixed-unit translated
cycle (the C verifier sidesteps this by only raw-checking j=2..8;
Coq cannot). The closer + full recon are done and de-risk it; the
counter-carry modeling is the remaining multi-hour piece. #9 (recon
says "fewest turns/lap: 2 per mini-lap", gen comb (10)) is likely a
gentler first FULL board than #30 -- consider reordering to #9 first
to validate the creach_iter lap shape on an easier counter, then
return to #30.
<!-- end double track -->

## Wave P2 LANDED + #17 P1 in progress (2026-07-21 cont.)

**P2 DONE, axiom-clean** (`theories/Counters/WaveCounter.v`): the abstract
parity odometer `nextf`/`carry` (= verify.c `wc_expected`, Compute-validated),
`WInv poff front := fp poff front = false /\ Forall (>=1) front /\ front<>[]`
(even popcount of the effective parity word), `WInv_preserved` and
`WInv_no_leadstop` (both "Closed under the global context" -- ZERO axioms).
Key math: each pass flips exactly 2 parity bits so even-popcount is invariant;
lead-stop needs the odd word `0..01`, excluded. Unifies both poff via the
effective frontier bit; lead is dropped (implicit 1) so bad-spawn is impossible.
Also added to WaveCounter: `wreach`/`wreach_iter`/`wreach_lap` (reachability
closer for the nested folds).

**#17 P1 crux DONE** (`theories/Machines/Counters/Wave_17.v`): `tm_17` +
`cross_run` -- crossing a run of ones leftward, `csteps tm_17 (S k)
(StB,(rep[S1]k++S0::rest,S1,R)) = Some (stB k,(rest,S0,rep[S1](S k)++R))`,
`stB k = if even k then StC else StB` (exit state = run parity: C=deposit,
B=continue). Well-founded 2-step induction. Compiles axiom-clean.

**Remaining for #17 (the two folds).** Confirmed phase units (all `wsteps`/
`csteps` reflexivity, from Compute on tm_17):
  - FT (br=false, 3): `csteps 3 (StD,(L,S0,[])) = Some(StB,(S1::L,S1,[S0]))`
    -- generic in L (never reads left); prove via `wsteps_frame_r` of the
    empty-window unit `wsteps true false tm_17 3 (StD,([],S0,[])) =
    Some(StB,([S1],S1,[S0]))`.
  - sep-continue B0 (1): `(StB,([S1],S0,R)) -> (StB,([],S1,S0::R))` -- wait,
    at a separator head=S0 in state B: `csteps 1 (StB,(rest,S0,R)) =
    Some(StB,(?,hd rest,S0::R))`; actually the head after cross_run is S0 and
    state B => step B0/0L>B moves left onto next block: `(StB,(S1::rest,S0,R))
    -> (StB,(rest,S1,S0::R))` then cross the next run in state B head S1.
  - deposit C0 (1): `(StC,(X,S0,S1::R)) -> (StA,(S1::X,S1,R))`.
  - return: A1/0R>D (1) then D-sweep. D over a one: `(StD,(L,S1,R))->
    (StD,(S1::L,chd R,ctl R))`; return separator D0;A1: at a swept 0
    `(StD,(L,S0,S1::R)) -> ...`. The rightward return re-lays each block; it
    is a `cycR`-style fold over the swept region (state D), mirroring the
    leftward fold.
  - deposit turnaround (cls1 example, front [3;2;1]->[4;3;1]): the leftward
    wave = FT ++ cross_run(S b0) at the frontier; if exit StC (odd b0) deposit
    immediately; else B0-continue then cross_run(a-1) per block until StC.
    Full cls1 = 14 steps, cls2 = 24 steps, both land EXACTLY on Cf(nextf).

Structure to finish: a recursive `wave_L` (mirrors `carry`: cross frontier,
then while exit=B do B0-continue+cross_run, until exit=C deposit; produces the
deposit-turnaround config with crossed blocks mirrored onto r) via `wreach`,
then a recursive `return_R` (state-D rightward fold consuming r, re-laying the
event) via `wreach_iter`/`cycR`; the lap cases on `WInv_no_leadstop`. Then
`boot_17` (Compute, ~? steps to Cf [3;2;1] i.e. boot front [3;2;1]),
`vis_17` (finite wsteps witnesses per state), instantiate `wglue_neverqh` with
`A := list nat`, `nextA := nextf 0`, `Inv := WInv 0`, `Cf := Cf17`, `a0 :=
[3;2;1]`. #27/#36/#7 reuse the same skeleton with their gadget tables; #6/#24
have 4-step 0-writing cross cycles (harder cross_run).
<!-- end wave P2+P1 note -->

## UPDATE (2026-07-21, same session): #9 is a GRAY-CODE double_counter -- lap9.py ALL OK

`#9` (1RB0LC_1RC0RD_1LA0LC_1RD0RA, edge D) was reconnoitred fully and
its mid-config family VALIDATED (`tools/counters/lap9.py 90` = ALL OK,
j=2..6; totals 125/445/1661/6397/25085 match raw).

Anchor `D9(j) = (10)^kg 1^acc`, head on the rightmost 1, state D;
kg=2^j-1, acc=3j.  cconf:
`(StD, (rep [S1] (acc-1) ++ rep [S0;S1] kg, S1, []))`.
Doubling kg->2kg+1, acc->acc+3.

**KEY: the doubling drives a GRAY-CODE counter** (NOT a base-4
mixed-radix odometer like #30 -- #9 is genuinely gentler).  The i-th
left-edge turnaround config (state A, head on the new left blank) is

  f_i = (StA, ([], S0, rep [S1;S0] (kg+1+i) ++ gray_region(kg-i, j)))
  gray_region(v,j) = [S0] ++ concat_{s<j} [bit_s(G(v)); S0; S0] ++ [S1]
  G(v) = v xor (v>>1)  (reflected Gray code)

Consecutive f_i differ by EXACTLY ONE gray-bit flip (verified Gray
property: for j=3 the counter is G(7..0) = 4,5,7,6,2,3,1,0, each a
single-bit change).  The comb grows one unit per step (kg+1+i), the
Gray counter counts DOWN from G(kg) to G(0)=0 over kg steps, and the
final all-zero state's spread reforms `D9(j+1)` exactly.

**This is STRUCTURALLY the landed gray_counter #19 (`Gray_19.v`).**
#19's anchor `(StC,([],S0, rep [S1;S0](p+2) ++ S0::Wg p))` is the same
shape as f_i (comb `rep [S1;S0]` + `S0::`gray-slots).  Differences to
handle in `Double_9.v`:
  1. #9's mini-lap is one gray-code step but the MACRO lap chains `kg`
     of them -> `CReach.creach_iter` over the mini-lap (this is why
     #9 needs the closer; #19 is a single parametric lap).
  2. #9 DECREMENTS the Gray counter (Wg(w) -> Wg(w-1)); the flip bit
     for w->w-1 is `fst (cview (w-1))` (trailing 1s of w-1 = trailing
     0s of w).  Use `Wg_some`/`Wg_none` with before=Wg(succ p),
     after=Wg(p) (roles swapped vs #19).
  3. Fixed width j: the high zero-slots above the flip are INERT
     context R in each mini-lap (head turns at the flip), so no
     fixed-width machinery is needed -- frame them as R.
  4. Comb-doubling boundaries: a poke prefix D9(j) -> f_0 (the
     nonempty `0<n` prefix for `creach_lap`) and a final spread
     f_kg -> D9(j+1).

CONFIRMED unit runs (probe9.py; all vs the real tm_9):
  - collapse (leftward): `cycL(u=[S0;S1], w=[S1;S0], P=2)`:
    `(A,([S0;S1],1,[])) -2-> (A,([],1,[S1;S0]))`.
  - spread (rightward): `cycR(u=[S0;S1;S0;S1], w=[S1;S0;S1;S0], P=4)`:
    `(B,([],1,[S0;S1;S0;S1])) -4-> (B,([S1;S0;S1;S0],1,[]))`
    (2 comb units per cycle -> comb-parity split like #19's
    comb_even/comb_odd + Gray_19's U2).
  - poke edge unit: `(D,([],1,[])) ...` (D1=0RA, the doubling start).
  - gray flip: the cview-slot flip, a bounded C/A/B push exactly as
    Gray_19's phU3e/phU4s/phU5s family (different write table).

Transcription is a Gray_19-scale proof wrapped in one `creach_iter`.
Files staged: `tools/counters/{recon9,probe9,lap9}.py` (committed).
Recommended next: build `theories/Counters/DblCounter.v` (fixed-width
gray decomposition OR reuse `MonoCounter.Wg` with inert high context)
+ `theories/Machines/Counters/Double_9.v` per the Gray_19 template,
importing `CReach` (qualified, to avoid the MonoCounter creach clash)
+ `MonoCounter` (for Wg/cview) + `WTape`/`LapGlue`.  #37 (side L,
t=1+3j) is the likely next Gray-code sibling; #30/#32 are the harder
base-4 odometers.

### #9 foundation LANDED (compiling): theories/Machines/Counters/Double_9.v

A machine-checked WIP foundation compiles standalone
(`coqc -Q theories BBB4 theories/Machines/Counters/Double_9.v`, EXIT 0;
NOT yet in _CoqProject / manifest -- no theorem yet):
  - `tm_9`, anchor `D9(j) = (StD,(rep[S1](3j-1)++rep[S0;S1](2^j-1),S1,[]))`;
  - comb units `Ucol` (collapse cycL u=[S0;S1] w=[S1;S0] P=2) and
    `Uspr` (spread cycR u=[S0;S1;S0;S1] w=[S1;S0;S1;S0] P=4) + their
    transported phases `phUcol`/`phUspr`;
  - right-edge visit units `UvA/UvB/UvC` + `phUv*`, and `vis_9`
    (every state reached from any D9(j) at offset 0/1/2/3) -- DONE;
  - `boot_9` (blank -> D9(2) in 47 steps, vm_compute) -- DONE.
Only `lap_9` (the creach_iter over the gray mini-laps + poke prefix +
final spread) and the `nqh_1RB0LC_1RC0RD_1LA0LC_1RD0RA` theorem remain;
`vis_9`+`boot_9` already satisfy two of the three `glue_neverqh`
premises.  Next session: build the gray decomposition (fixed-width
`WgF` or `MonoCounter.Wg` with inert high context), prove one mini-lap
(Gray_19.v lap_19 template, decrement direction), wrap in creach_iter,
add poke/final, then wire into _CoqProject/manifest.

## Wave #17: wave_L LANDED; return_R fully mapped (2026-07-21 cont. 2)

`Wave_17.v` now has (all compile, axiom-clean): tm_17, cross_run, wbody/Cf17,
ph_FT/ph_sepB/ph_dep/ph_spawn, and **wave_L** -- the leftward carry-wave fold
(mirrors `carry`): crosses even blocks (run onto r via cross_run), deposits at
the first odd block (ph_dep), or spawns past the lead (ph_spawn); `outL`/`outR`
give the deposit-turnaround `(StA, (outL po blocks, S1, outR po blocks R))`.
Threads `carry_ok` (no lead-stop, from P2) + Forall>=1 + R-starts-S1.

**return_R -- the ONLY remaining proof piece, fully mapped.** From the
deposit-turnaround sweep RIGHT (state D) to `Cf17 (nextf 0 front)`. Trajectory
verified by Compute (front [4;3;1] -> [5;3;2], deposit-turnaround `(StA, (1^2 0
1, S1, 1^2 0 1^6 0))` -> 10 steps -> `Cf17 [5;3;2] = (StD, (1^5 0 1^3 0 1^2 0 1,
S0, []))`). Per-block units:
  - start: `A1/0R>D` -- the deposit-block top S1 becomes a separator (StA->StD).
  - run cross: `cycR` D unit `(StD,([],S1,[S1])) -> (StD,([S1],S1,[]))` re-lays
    a swept run (head stays S1).
  - separator BORROW gadget `D0/1R>A ; A1/0R>D` at each swept 0: `(StD,(L,S0,
    S1::R)) -> ... -> (StD,(S0::S1::L, ?, R))`, moving one 1 across the boundary.
The net re-lay: the frontier mirror `1^{S(S b0)}` becomes the correct new
frontier `1^{S b0}` (the FT scratch is removed) and each crossed block's mirror
is restored to its value; cls1 (deposit right after frontier) is just
`A1 + cycR` (no interior seps), so start there. Then glue:
`lap_17 := FT + cross_run(S b0) + wave_L + return_R`, and
`nqh_1RB0RD_0LB1LC_1RA1LB_1RA1RD` via wglue_neverqh (A:=list nat, nextA:=nextf
0, Inv:=WInv 0, Cf:=Cf17, a0:=[3;2;1]). boot: `csteps ~? c0 = Cf17 [3;2;1]`
(Compute); vis: finite wsteps per state. #27/#36/#7 clone the skeleton.
<!-- end wave #17 wave_L note -->

### #9 progress (2026-07-21 cont.): gray decomposition layer COMPLETE, axiom-clean

`theories/Counters/DblCounter.v` now fully carries the gray algebra the
mini-lap consumes (chunks 1/1b/1c, all `Closed under the global
context`, in `_CoqProject` double block):
  - encoding `gbn`/`slotsf`/`grr` (validated vs lap9.py gray_region);
  - head bits `gbn_even_hd`/`gbn_odd_hd`;
  - odd flip `grr_odd` (w odd: flip at slot 0, tail shared with w-1);
  - even marker+flip `grr_even_marker`/`grr_even_flip` (value side) and
    `gbn_pred_marker`/`grr_even_pred` (predecessor side): for w even
    = 2^(S r)*u (u odd), BOTH grr(w) and grr(w-1) =
    `S0 :: rep[S0;S0;S0] r ++ S1::S0::S0 :: FLIP::S0::S0 :: TAIL`, same
    marker run + TAIL, only FLIP toggles -- the reflected-Gray
    one-bit-change, proven structurally (no xor algebra);
  - `factor2`: every 0<w = 2^r*u (u odd) -- bridges the family index
    kg-i into the two cases.

**REMAINING to land #9** (the mini-lap phase assembly + wrapper --
NOT the gray algebra, which is done):
1. Extract the tm_9 phase units for the gray region (Double_9.v already
   has the comb units Ucol/Uspr): the odd-flip 3-step push
   (A0;B0;C0 over slot0 `0,0,0`, turning left), the even D-fill cycR
   over `rep[S0;S0;S0] r` up to the marker, the marker-clear + flip
   push (2 sub-cases on `Nat.odd(Nat.div2 u)` = clear/set flip), and
   the collapse cycL + edge-materialize.  Build a combinator mini-lap
   (lap9.py-style `conc`/`cycR`/`cycL`) to emit them, differential
   against raw.  Traced phase order (w=7, odd): edge-turn(1) ->
   spread cycR(comb) -> flip push(3) -> collapse cycL(comb) ->
   edge-materialize.  The flip writes `1,1,1` into slot0 and the
   COLLAPSE rewrites the extra cells back (slot0 -> `1,0,0`) -- the
   flip/collapse interaction is the one delicate bit to get exact.
2. The mini-lap `creach (f i) (f (S i))`: f i = the framed anchor
   `(StA, ([], S0, rep [S1;S0] (kg+1+i) ++ grr (kg-i) j))`.  Case
   `w = kg-i` via `factor2`: r=0 -> grr_odd; r=S _ -> grr_even_flip
   /grr_even_pred, sub-case `Nat.odd(Nat.div2 u)`.  Chain
   phUspr(cycR) + D-fill + flip + phUcol(cycL) with rep-algebra
   junctions (comb parity split like Gray_19 comb_even/comb_odd).
3. `CReach.creach_iter` over i<kg -> creach (f 0)(f kg); poke prefix
   `creach (D9 j) (f 0)` (gives 0<n via `CReach.creach_pos`), final
   spread `creach (f kg)(D9(S j))`; `CReach.creach_lap` -> the
   `LapGlue.Hlap` shape -> `lap_9`.  Then
   `glue_neverqh tm_9 (fun p => D9 (S (Pos.to_nat p))) 1` with
   `boot_9`/`vis_9` -> `nqh_1RB0LC_1RC0RD_1LA0LC_1RD0RA`.
4. Corruption test + manifest row + wire Double_9.v into _CoqProject.

The hard conceptual piece (the fixed-width reflected-Gray decrement
decomposition) is DONE and reusable for #37.  What's left is the
Gray_19-style mechanical phase transcription for tm_9's unit table.

## Wave #17 FULLY BOARDED (2026-07-21 cont. 3) -- first wave theorem

`nqh_1RB0RD_0LB1LC_1RA1LB_1RA1RD : NeverQuasiHaltsSt tm_17` is landed,
axiom-clean (functional_extensionality_dep only), with corruption tests
(`theories/Tests/CountersWave_Corruption.v`), manifest row, and _CoqProject
entry. The full proof stack (all in `Wave_17.v` + machine-independent
`WaveCounter.v`):
  - P2: `WInv`/`WInv_preserved`/`WInv_no_leadstop` (even-popcount parity safety).
  - closer: `wglue_neverqh` (nextA-indexed) + `wreach`/`wreach_iter`/`wreach_lap`.
  - `cross_run` (parity-alternating leftward run cross), phase units
    `ph_FT`/`ph_sepB`/`ph_dep`/`ph_spawn`.
  - `wave_L` (leftward carry-wave fold, mirrors `carry`; outputs `outL`/`outR`).
  - `Dsweep`/`run_to_sep`/`return_R` (rightward reconstruction; `relaid` with
    the odometer borrow via the borrow-accumulator `relaid_b`).
  - bridge: `bcs`/`dsuffix` (outR = sw(bcs), outL = wbody(dsuffix)) + the
    telescoping `bridge_l` identity, landing exactly on `Cf17(nextf 0 front)`.
  - `boot_17` (Compute, 49 steps), `vis_17` (finite wsteps witnesses).

### Recipe for #27/#36/#7 (clean tier) -- clone Wave_17.v
The machinery is now a template. Per machine: swap `tm_NN`, the poff (WInv poff,
nextf poff, a0), and the per-machine gadget tables (design appendix above):
  - #27 D/R/poff1: FT=`D0/1R>B B0/1L>C`, cross-pair=`C1/1L>A A1/1L>C`,
    sep=`C0/0L>C`, deposit=`A0/1R>B`, return=`B1/0R>D`/`D1/1R>D`, retsep=`D0/1R>B B1/0R>D`.
  - #36 A/R/poff1, #7 A/L/poff1 (mirror): tables in the design appendix.
KEY poff=1 deltas from #17 (poff=0): the frontier-cross exit parity uses
`odd(b0+1)` (the FT already flips it), so `cross_run`'s [stB] and the wave_L
entry `po := Nat.odd (b0 + poff)` change; `WInv_no_leadstop`'s `Nat.add_0_r`
becomes a general `poff`. The 2-state cross cycle (C<->A for #27, C<->D for
#36) replaces #17's B<->C but proves identically. #6/#24 (4-step 0-writing
cross) are the hard pair -- budget separately. wave4 #15: separate verifier.
<!-- end wave #17 boarded note -->

## Wave #27 + #36 BOARDED; #7 fully reconnoitred (2026-07-21 cont. 4, CLEAN tier)

Two more wave theorems landed, axiom-clean (functional_extensionality_dep
only), each with corruption tests (`CountersWave_Corruption.v`), manifest
row, `_CoqProject` entry:
  - **#27** `nqh_1RB1LC_1LC0RD_0LC1LA_1RB1RD : NeverQuasiHaltsSt tm_27`
    (`theories/Machines/Counters/Wave_27.v`), edge D, poff 1, a0=[4;2;1],
    boot 50.
  - **#36** `nqh_1RB1RA_1LC0RA_0LC1LD_1RB1LC : NeverQuasiHaltsSt tm_36`
    (`Wave_36.v`), edge A, poff 1, a0=[4;2;1], boot 50.
Recon/probe scripts: `tools/counters/probe27.py` (step-level cconf
simulator; `trace_wave.py` already validates all 6 orbits).
`WaveCounter.v` needed **NO change** -- `WInv_no_leadstop` is already
poff-general; do NOT `rewrite Nat.add_0_r`, just apply it with poff=1.

### Template deltas actually discovered (beyond the design-appendix guess)
- **poff=1 frontier parity.** After the FT crosses the frontier run, the
  exit state selects deposit/continue by `Nat.odd (b0+poff)`. In Coq:
  `stC k := if Nat.even k then <deposit> else <continue>`, and the frontier
  cross uses `cross_run k` with `k = b0` (NOT `S b0` -- see FT below); then
  `stC b0 = if Nat.odd(b0+1) then <deposit> else <continue>` via
  `unfold stC; replace (b0+1) with (S b0) by lia; rewrite Nat.odd_succ`.
  wave_L is entered with `po := Nat.odd (b0+1)`, and `WInv_no_leadstop 1 b0
  r0` gives `carry_ok (Nat.odd(b0+1)) r0 = true` directly.
- **FT scratch = 1 (not 0) => the frontier-swept run has NO trailing
  separator.** #17's FT (3 steps, B0/0L>B) writes a `S0` scratch, so its
  swept frontier is `sw [S(S b0)] = rep[S1](S(S b0)) ++ [S0]`. #27's FT is
  **2 steps** `D0/1R>B B0/1L>C`, generic in L (D0's written 1 becomes the
  head, B0 lays a `S1` scratch): `ph_FT27 : csteps tm 2 (StD,(L,S0,[])) =
  Some (StC,(L,S1,[S1]))`. After `cross_run27 k=b0`, the right is
  `rep[S1](S b0) ++ [S1] = rep[S1](S(S b0))` -- a bare run, no `[S0]`. So
  #17's `sw` is replaced by **`sw27`** (last run bare):
    `sw27 [] = [] | sw27 [c] = rep[S1] c | sw27 (c::rest) = rep[S1] c ++ S0::sw27 rest`
  with the one-line helper `sw27_slide : sw27 (S c::rest) = S1 :: sw27 (c::rest)`
  (proof `intros c [|c2 rest]; reflexivity`). The return needs a terminal
  **`run_to_end27`** (walk the deepest run off into the blank via
  `Dsweep_blank27`) alongside `run_to_sep27` (interior runs). Everything
  else -- `relaid`/`relaid_b`/`dec1`/`bcs`/`dsuffix`/`bridge_l`/`outR_sw27`
  (a trivially adapted `outR_sw`, needs `base<>[]`) -- is byte-identical to
  #17. The full lap lands EXACTLY on `Cf27(nextf 1 front)` (no lift slack);
  cls1=14 steps, cls2=24, spawn(cls-1)=40, all Compute-checked.
- **#36 = #27 under the state relabelling A<->D.** #36's gadget table is
  #27's with StA and StD exchanged (edge D->A, deposit A->D, sweep D->A,
  cross C/A->C/D). `Wave_36.v` is literally `Wave_27.v` run through
  `sed -e s/StA/@X@/ -e s/StD/StA/ -e s/@X@/StD/` then `s/27/36/`, with the
  header/theorem-name/spec-string fixed by hand and **vis offsets swapped**
  (StA<->StD branches of `destruct q`: #36 is StA->0, StB->1, StC->2,
  StD->3). tm and all proofs transcribe verbatim; boot is still 50. This is
  the cheapest kind of sibling -- look for A<->D (or other 2-cycle)
  relabellings before writing a machine from scratch.

### #7 BOARDED (2026-07-21 cont. 5) `nqh_1RB0LC_1LA1RD_1LA1LC_0RD1RB`
`Wave_7.v`, axiom-clean (functional_extensionality_dep only), corruption
tests + manifest + _CoqProject landed. Boarded through the side-R mirror as
planned below; boot=42. The reverse-encode bridge was NOT a fight -- it is
`bridge_l` verbatim with `relaid -> relaid7` (only `relaid7_b`'s `[c]` base
case bumps to `rep[S1](S(c-b))`). Two extra findings beyond the recon:
(1) the FT lands in the DEPOSIT-state B, but interior blocks are entered in
the CONTINUE-state D, so there are TWO cross lemmas `cross_run7B`/`cross_run7`
(start B / start D). (2) state C never appears in the frontier gadget (the
FT is a single `A0/1L>B`), so `vis`'s C-witness cannot be shallow -- reach it
via the deposit turnaround (`reach_C7 = FT + cross + wave_L7 + one A1/0R>C`).
All 6 clean-tier wave machines (#17/#27/#36/#7 here; #6/#24 remain the hard
4-step-0-writing pair; #15 wave4) -- FOUR now boarded.

### (original #7 recon, retained) board via `Mirror.mirror_never_qh`.
Side L, so use `theories/Mirror.v`: prove `NeverQuasiHaltsSt (mirror_tm
tm_7)` then `apply mirror_never_qh`. The side-R machine to board is
  **`mirror_tm tm_7 = 1LB0RC_1RA1LD_1RA1RC_0LD1LB`** (flip every dir L<->R;
  keep write+next). It IS a side-R wave odometer, edge A, poff 1,
  a0=[4;2;1], SAME abstract orbit (`nextf 1`/`WInv 1`), Compute-validated:
  cls1=12 steps, cls2=22, spawn=38, all land on `Cf(nextf 1 front)` exactly
  (probe: `scratchpad/probe7m.py`, reproduce it). Gadget table (side R):
    - FT **1 step** `A0/1L>B` (writes the +1 increment, moves straight onto
      the frontier top in B, scratch `[S1]` on the right). Swept frontier
      after the cross is `rep[S1](S b0)` -- i.e. `S b0`, **one less than #27's
      `S(S b0)`**, because this FT adds only the increment.
    - cross-pair `B1/1L>D D1/1L>B` (states B/D, start B); `stB7 k = if even k
      then StA else StB`... i.e. deposit exit A, continue exit B.
    - sep-continue `B0/0L>B`? -- recheck; the cross is leftward like #27.
    - deposit `B0/1R>A` (leaves head `S1`, state A -- like #27's extra head).
    - return: sweep `C1/1R>C`, start `A1/0R>C`, retsep `C0/1R>A A1/0R>C`,
      **terminal `C0/1R>A` WRITES A ONE** (materialise-and-write) landing in
      the edge state A -- so the deepest run GAINS one at the walk-off.
- **THE DIVERGENCE (why #7 is not a #27 sed):** #27's return DECREMENTS the
  deepest (frontier) run by 1 (removing the FT's extra scratch: swept
  `S(S b0)` -> new frontier `S b0`, via `relaid`'s `relaid_b` borrow whose
  net is deepest-1/nearest+1). #7's FT adds only 1, so the swept frontier is
  already `S b0` = the correct new frontier, AND the terminal `C0` writes the
  cell back -- so **#7's return conserves every run count**. Its `relaid7`
  is a clean REVERSE-and-encode (frontier becomes nearest, all values
  unchanged): `relaid7 [c0;..;cn] = rep[S1] cn ++ S0 :: .. ++ S0 :: rep[S1] c0`.
  The concrete return still SHIFTS separators (retsep `C0/1R>A A1/0R>C`
  borrows one from the next run), but nearest+1 (deposit head) and deepest-0
  (no scratch) net to no change. So `return_R7` + its bridge must be
  RE-DERIVED (not the `relaid_b`/`bridge_l` copy): sw7=sw27 (last bare) is
  reusable, but `bcs7`/`relaid7`/`bridge7` differ (no `dec1` on the base;
  the base is `[S b0]` not `[S(S b0)]`). Est. ~1/2 the #27 effort once the
  reverse-encode bridge identity is stated. cross_run7 (B/D), ph_FT7 (1
  step), the units, wave_L7, and vis (edge A: A->0,B->1,...) transcribe like
  #27/#36. Then wrap: `Theorem nqh_1RB0LC_1LA1RD_1LA1LC_0RD1RB : ... := 
  mirror_never_qh tm_7 <proof of NeverQuasiHaltsSt (mirror_tm tm_7)>` (note
  `mirror_tm tm_7` must be DEFINITIONALLY the boarded machine; state its TM
  literally and prove `mirror_tm tm_7 = tm_7m` by `reflexivity`, or board
  `tm_7m` and show `mirror_tm tm_7 = tm_7m`).

### New traps for the catalog (wave clean tier)
- **`repeat constructor; lia` OVER-APPLIES** on `Forall (>=1) [S(S b0)]`: it
  runs `constructor` into the `le` goal and mangles it. Use
  `constructor; [lia | constructor]` (Forall_cons then Forall_nil), exactly
  as #17 does. Bit me on the first #27 compile.
- **FT genericity depends on the scratch not being read.** #27's 2-step FT
  is generic in `L` ONLY because B0 pops the very `S1` that D0 pushed (never
  reaches into L). Prove it with `wsteps_frame_r ... reflexivity` with
  `l=l'=[]` (so `l'++L = L`, left literally unchanged). If a machine's FT
  reads L, this breaks -- check by Compute first.
- **`vis` reflexivity survives stuck `chd/ctl`.** For symbolic `p=b0::r0`,
  `csteps k (Cf p)` reduces to `Some (q, <stuck tape>)`; `eexists; split;
  reflexivity` still closes `fst c = q` because `fst (q,_) = q`. Max useful
  depth is 3 (all four states appear in the first frontier gadget).
- **Mirror machines: swept-frontier count = `S b0` when the FT is 1-step
  (scratch-1), `S(S b0)` when 2/3-step.** Determines whether `relaid`
  decrements. Always Compute the full cls1+cls2 pass to pin it; do not
  assume the #27 dec applies.
<!-- end wave #27/#36 boarded, #7 recon note -->

### #9 COMPLETE (2026-07-21 cont.): nqh_1RB0LC_1RC0RD_1LA0LC_1RD0RA landed

`theories/Machines/Counters/Double_9.v` now carries the full proof
(`Print Assumptions nqh_1RB0LC_1RC0RD_1LA0LC_1RD0RA` =
`functional_extensionality_dep` ONLY).  Wired into `_CoqProject`
(double block) + `tools/counters_manifest.tsv`;
`theories/Tests/CountersDbl_Corruption.v` is the negative-control file.
double_counter family: **#9 done (1 of 4)**; #30/#32/#37 remain.

Structure that landed (all phase counts read off an executor
decomposition validated j=2..7, both parities, all sub-cases -- the
minilap/poke/final decomposers, never hand-counted):
  - `minilap9 : creach tm_9 (g9 j n w) (g9 j (S n) (w-1))` -- the gray
    decrement.  Cases via `DblCounter.factor2`: **odd w** (r=0) is a
    slot-0 flip (`phFlipO0/1`, cased on the slot bit); **even w**
    (r=S _) is a D-fill to the marker (`phDf9`), a flip approach
    (`phFapp0/1`), and a period-3 "dirty collapse" that clears the
    D-fill 1-run (`phdA1` + `phDclr9 (drun-1)` + `phdC1C0`), cased on
    `Nat.odd (Nat.div2 u)` (SET fb=0 / CLEAR fb=1; both 3R+4 steps,
    shared tail).  Then the flat comb collapse (`phUcol`) + `phMat9`.
  - macro lap: `poke9` (D9 j -> f_0, the 0<n prefix; reuses
    phdA1/phDclr9/phdC1C0/phUcol/phMat9 + new phPokein/phPseed),
    `iter9` (`CReach.creach_iter` over the kg mini-laps), `final9`
    (f_kg -> D9(S j) via phSpr9/phEnter9/phDf9/phFin, gray value 0),
    `macro9` (`CReach.creach_pos` assembles it with 0<m).
  - helpers: `grr_kg`/`grr_zero` (gray region of 2^j-1 / of 0),
    `gbn_allones`, `even_fold`/`poke_fold` (comb regroup + rep_shift),
    `rep4_10/01`, `rep000`, `rep_snoc`.

New traps for the catalog:
  - **`replace X at 1` mis-targets when X's SUBTERMS recur** (poke9):
    `replace (2^S j') with (S(S(2^S j'-2)))` clobbered the `2^S j'`
    inside the sibling `2^S j'-2`.  Fix: `set (b := 2^S j'-2)` FIRST
    (opaque), prove `2^S j' = S(S b)`, then folds can't leak.
  - **Last phase: `apply phMat9` directly, NOT via `csteps_chain`.**
    Wrapping the final phase in `eapply csteps_chain` leaves a second
    goal `csteps ?n2 out = Some target` whose `?n2` reflexivity can't
    instantiate (the fix is stuck on the evar).  Close the chain by
    applying the terminal phase lemma so it unifies `?n := 2`.
  - **`cbn [gbn]` leaves `Nat.div2 0` stuck** (div2 not in the delta
    set) -> the recursive `gbn (Nat.div2 0) j` won't match `gbn 0 j`
    for a rewrite; use `simpl` for the all-zero/all-one gbn folds.
  - **`cycL` takes 7 explicit args before the unit** (tm P q h u rw w);
    `cycL _ _ _ _ _ _ Ucol` (6 underscores) errors "expected list Sym".
  - **The even leftward collapse is a period-3 cycle** over the
    D-fill/marker/flip 3-cell slots (`[A1,C1,C0]`), distinct from the
    period-2 comb collapse (`phUcol`); the D-fill 1-run is the only
    length-varying part -> `cycL(u=[S1], C h1, k=drun-1)` sandwiched by
    fixed concs.  Both flip sub-cases are 3R+4 steps, shared tail.
  - **executor `conc` with `lwin=None` captures the whole L**, so
    `record` reports "unit varies" across j even when the decomposition
    is correct -- a recording artifact; the raw differential is the
    real gate.

#37 (side L Gray sibling) reuses the DblCounter gray algebra + this
mini-lap skeleton verbatim (decrement direction, inert high context).

# Cleanup + residue-recon session (2026-07-29): build fix, issue #61 burndown, emitter findings

Community-facing pass after the public announcement, plus recon over the
167-core residue.  No Coq toolchain in this container, so everything here
is either docs/tooling or a measurement handed to the next proof session.

## Landed (branch claude/coq-bbb4-cleanup-kmtd7g, PR #69)

- **BUILD FIX: `_CoqProject` was missing `theories/Counters/RegGlue.v`** --
  the four REG_* boards (7613cb9) import it, so a fresh `make` died with
  "No rule to make target RegGlue.vo".  One line added.  CI now runs
  `make -f Makefile.coq -n all` (dry run, seconds) so a board whose dep
  never made it into `_CoqProject` fails fast instead of on a user's box.
- Docs freshened to the live counts (167 core + 80 shadows, audit OK):
  README, CLAIMS, RESIDUE_MAP (family table regenerated over the live
  list; newcomer section now leads with the 25 cycR-gap/lift rows).
- Pruned 24 orphan .v never wired into any build (15 ILS4F_*, 7 LAPC_*,
  PQHS_00, Census/Assembly.v) -- all their machines settled elsewhere;
  recoverable from git history.
- **Issue #61 now carries the full burndown list**: all 167 core rows
  grouped by blocker, cycR-gap/lift rows tagged, champion flagged;
  verified programmatically against core_rows.txt (exact match) and
  intgap51.json (all 51 verdicts).  Lesson re-learned: NEVER retype
  machine lists into a post -- generate, paste verbatim, then diff the
  posted content against the row file.  The first attempt fabricated
  ~100 rows and only the diff caught it.

## Emitter recon over the 167 (dry pass, per-row 30s cap)

- **`1RB1LC_0LC0RB_1LA1RD_1RC0RD` (core row 131, filed "no boot chain")
  NOW DERIVES: `OK Alph_00_10_1 4*j+4 4*j+13`.**  The cascade wave
  taught the engine what this row needed and nobody re-swept.  On a box
  with Coq: `emit_lapcert.py --spec 1RB1LC_0LC0RB_1LA1RD_1RC0RD --emit`,
  then the closeout regen.  A free board.
- **`emit_lapcert.py` OOM-dies on `1RB0RD_1LB1LC_1RC0RA_0LB1RD`** (core
  row 78): `nestcert.derive_offset` -> `phase_mid` at K=7 accumulates
  every blank-head config of a phase that never closes (400k-step cap,
  no memory cap) until the OOM killer takes the process -- exit 137, and
  a full-list run dies SILENTLY partway.  Nine rows total exceeded 30s
  (rows 34-36, 47-50, 78, 167 of core_rows.txt).  Any "run the emitter
  over the WHOLE residue" step (wave-30 acceptance) must shard around
  them or bound phase_mid's `mid` list.  NOT fixed here on purpose: an
  emitter change can shift candidate ordering, and the byte-identical
  re-render regression that guards that needs coqc.
- Everything else: 157 rows report "no" with unchanged blocker labels.

## John's readings this session (recorded for the next design pass)

- `0RB1LA_0LC1RD_0LD1LD_1RB0LA` (Gray-ish up/down read): it is a SHADOW
  of core `1RB0LD_0LC1RA_0LA1LA_0RB1LD` (shadow_rows.tsv row 29), which
  tailcert already reads as a two-form family stopping at
  "no interior j=0 chain at octave parity 0" -- i.e. wave-30 §3's double
  peel is the designed unblock, not a new decode.
- `0RB0RD_1LC1RB_1RA0LC_1LB0LC` "is a bouncer counter" -- CONFIRMED
  read, matches WAVE29_BOUNCER_FINDINGS §7c verbatim (envelope 2^k+7);
  waiting on the MeasureGlue/mrun build, family indexed by the wall.
- `0RB1LC_1LC1RD_1LA0LC_0RD1RB` "bouncer counter, reminds me of
  1RB1LD_1RC0RB_1LA0RC_0LD0LA" -- the analogy points at the Double_32
  ROUTE: abandon the macro anchor, re-sample at the record, transcribe
  the rewriting system on the comb word (here `1^11 0 (110)^k`, blocks
  2,4,7,9,15,17), close with WaveCounter.wglue_neverqh (no closed form
  needed).  comb_probe.py says NOCOMB but its template demands an Ip/Jp
  tail and short prefix, so that negative does not test this read.

# 2026-07-31 — the ladder's two knobs, the quasihalt closer, nineteen rows

_Full record in `docs/LADDER_PLAN.md` §4l.  This is the short version plus the
traps._

- **`LadderCheck` now carries ONE arm-indexing scheme and both class arms use
  it** — flat below a threshold `N0`, `N0 + (n-N0) mod st` at or above it,
  block count `(n-N0)/st`.  `arm_index` is the one lemma (`Nat.div_mod_eq` +
  `lia`).  4i's `off = n mod st` is this at `N0 = 0`, and that is why it left
  four rows short: an arm whose materialisation offset is at or above the
  stride cannot be a residue.
- **The trap that cost the most, and it is a SHAPE not a count.**  With
  `stride = 0` there is no repeated block for the engine's steps to walk
  around: `SWin` moves inside `s_pre`, no step carries a cell from `s_post`
  across the block boundary, and `srot 0` is the identity.  So a flat arm
  written `mkS pre [] 1 0 post` has **no chain at any depth or stride**, and
  the first emitter run refused all 21 rows on it.  `LadderCheck.blk` is the
  normalisation (empty block ⇒ whole side concrete in `s_pre`) and `blk_den`
  says the denotation is unchanged.  The failure reads exactly like "the
  carry ripple is not affine in the run length" and is not.
- **`LapGlueQuiet.glue_qh_quiet` ported** (`glue_qh_quietN`): `nat`-indexed,
  weak visit premise for every `q <> qa`.  The new obligation is `AvoidRun`
  on the lap; `base_chain : list rstep -> option (list lstep)` plus
  `base_chain_run` bridges to `LapAvoid.srun_avoid_sound`, which is stated on
  `srun`.  No new certificate data — the avoidance is recomputed from the
  same chain the kernel already replays.
- **`board_lap` became `board_arm`, parameterised by what the closer wants of
  the arm.**  `board_neverqh` at `RuleSound`, `board_iqh` at
  `RuleSound /\ RuleAvoid`.  The case split — which arm serves a state, at
  what index, at what block count — is stated once.  Duplicating it is how
  two closers drift apart.
- **Numbers.**  21 rows the closure applies to, 15 boarded (6 never-QH, 9
  quasihalting), 6 blocked on the arms — matching
  `tools/ladder/core61_armshapes.txt` row for row.  Then the six `0RB` rows
  that the boards promoted out of the shadow list certified and boarded too.
  Nineteen boards; on this branch's base, core undecided 59 → 46.
- **Nine of the nineteen were boarded concurrently by PR #91** (the
  three-state ternary-counter wave) while this session ran — every `1RB---`
  row here is also a `KS_`/`KA_`/`T3_` board on main, same `iqh` triple.
  Merged, it is **ten rows net**: remaining 68 → 58, core undecided
  47 → 43.  4k warned about exactly this ("a candidate that sits unboarded
  decays") and the guard is one diff: check
  `git show origin/main:tools/closeout/core_rows.txt` BEFORE picking a
  bucket, not after building for it.
- **Bookkeeping lesson.**  "core undecided" is a BUCKET, not a count of
  machines: boarding a core row can promote a `0RB` shadow into the core, so
  13 boards took 59 → 52, not 59 → 46.  Quote `settled by a board` when the
  claim is about rows decided.
- **Build note.**  The full tree is ~2 h at `-j3` and
  `theories/Machines/IRules_Batch_*.v` are ~16 CPU-minutes EACH at the very
  end, so the last quarter looks stalled and is not.  A single `valfam.py`
  row (~25 s) alongside a build is fine; the 61-row sweep is not.
- **`IRules_Batch_*` OOM-kill each other at `-j3`** on the 15 GB box —
  "Killed", `Error 137`.  The sources are a few KB; the `vm_compute` is not.
  Build those nine SERIALLY and the rest at `-j3`.  A `-j3` run that lands
  three of them together throws away ~40 minutes.
- **`board_ladder.py` rewrites `_CoqProject` under a running `make` and the
  build then LIES**: `Makefile.coq` is generated from `_CoqProject`, so
  changing it mid-build invalidates the makefile and `make` can exit 0 with
  hundreds of files unbuilt.  Board first, then build.
