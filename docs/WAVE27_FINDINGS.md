# Wave-27: the SKIP counters boarded, and the QUAD route built

_Branch `claude/residue-reduction-4-2-cont-frgu3x`, 2026-07-29.  Wave-26
spent the cascade route and re-ranked the 211-row "no overflow phase" bucket
to the top after John's decode (WAVE26 section 8: the SKIP counter — an
ordinary binary counter that never rests at a power of two).  This wave
builds that route end to end and boards the bucket's skip-`s` regime, then
builds the QUAD/QUAD route (WAVE26 section 7f) and boards its single-class
Kp cluster._

## 1. The one-line result

**104 new boards, all first render except three, all funext-only.**
`D_remaining` **427 → 323**.  Two new library files
(`Counters/SkipGlue.v`, `Counters/QuadGlue.v` — the second is
`Tests/QuadMGShape.v` moved under `Counters/` so boards can import it), two
new emitters (`tools/counters/skipcert.py`, `tools/counters/quad_emit.py`),
one new scan (`tools/counters/restscan.py`).  `LapDecider` untouched; no new
axiom anywhere (`Print Assumptions` on every board:
`functional_extensionality_dep` only).

## 2. The SKIP route (RESIDUE_PROMPT item 3): 98 of the 211

Exactly the build order the prompt asked for:

* **`phase_skip`** (skipcert.py) is `phase_mid` with the closure reading the
  skip OFF THE MACHINE: the phase from `E(fill(2^K-1))` ends at the first
  `E(2^K + s)`, `s = 0..3`.  Measured at two K and required to agree.
* **The VIRT extractor**: candidate virtual anchors are configuration pairs
  from two ADJACENT phases (K and K+1) that align as one sside family
  (`pre ++ rep u (j+b) ++ post`, then normalized to `b = 0`).  No form is
  assumed; the phase-END configuration is aligned the same way, so machines
  that land with extra written blanks or a rewritten far wall still close
  (that fix recovered 3 boards).
* **`Counters/SkipGlue.v`**: the power-of-two view `pexp` (`pexpi` for the
  second skip-2 anchor) with the successor lemmas the case analysis needs,
  and the reach/vis plumbing: `reach_ovf_skip` / `vis_via_skip` are
  `LapCertGlue`'s inductions with the interior-lap hypothesis GUARDED by
  "not a virtual anchor" and everything fenced by `p0 <= p` — so the
  degenerate small-p anchors (2, 3, 4, 5 are all virtual on a skip-2
  machine) carry no laps at all, and the fences discharge by `vm_compute`
  against the concrete `p0`.
* **The board** (`SKIP_*`): `Cc p = match pexp p with Some (S k) => VIRT k
  | _ => E p ++ tail end` (skip-2 adds the `pexpi` arm), three/four lap
  branches, all ordinary affine chains: interior (exact), fill → VIRT
  (exact, onto the measured transient form), VIRT (→ VIRT2) → `E(2^k+s)`
  (up to lift).  Closed by `glue_neverqh` directly — Bounce_8's pattern, as
  §8 predicted.  The exemplar `0RB0LC_1LC1RB_0RD1LA_1LB1LA`: interior
  `4j+4`; the extractor split the `4j+7` overflow phase as fill `0j+1` +
  virt `4k+10` -- it takes the FIRST split that derives and validates,
  and any valid split is sound (the kernel re-runs both chains).

Scoreboard on the 211: **98 boarded** (41 skip-1, 57 skip-2,
under `Alph_10_11_11`, direct and mirrored), each differentially validated
against the raw simulator (~198 anchors per machine: exact step counts,
exact virtual-anchor configurations, lift-equal landings) before rendering.

**What did not board, measured:**

* **113 rows** are the alternate-octave / register×counter regime
  (WAVE26 8b) or deeper skips — see §4.
* **4 rows** (`Jp` alphabet) close the phase at `s = 1` but with a ~`8j`
  phase whose middle no single V→E chain crosses (a second turnaround);
  they need a 2-segment virtual pipeline nobody has needed yet.
* **skip-4 exists** (`0RB1LD_1LC1RB_1LA1RC_0RC0LA`, WAVE26 8b): the
  template stops at `s = 2`; wiring `s <= 4` is mechanical (`pexpii`/
  `pexpiii` views, the same fences).

## 3. The QUAD route (RESIDUE_PROMPT item 1, WAVE26 7f): 6 of the 41

The build §7e/7f specified, all of it:

* **`Counters/QuadGlue.v`**: `quad_lap` — `MeasureGlue.mrun` at abstract
  state (probe depth k, unprobed count m), `mu = snd`, invariant
  `k + m = j`.  Axiom-free.
* **The two-index denotation** `Cq W k m` (the cascade's `Dc l m` pattern):
  k probed digits right of the head, m unprobed behind it, the deep word W
  OPAQUE — `W = E q0 ++ tail` on the interior branch, the measured
  overflow word on the overflow branch, so BOTH branches are one family.
* **Hterm first**, as §7e ordered: the terminal chain's count is the FINAL
  k; `term_*` states it for every k with the k = 0 case a separate concrete
  chain, and `qrun_*` ties it to the anchor's carry index through
  `quad_lap`'s `k + 0 = j`.
* **Nine chains per board** (`QMG_*`): three boots (interior j ≥ 1 /
  interior j = 0 / overflow), four micro hops (landing on a digit / on the
  stop cell, at k = 0 / k ≥ 1 — the peeled framing again), two terminals.
  The micro-hop and terminal lemmas are `cden` bridges (`assert` +
  `replace (1*k'+0) with k'`), and the whole lap is ONE `csteps` run.
* **The close**: interior laps compose through `mrun`, so they close up to
  `lift`; the closer is `glue_neverqh_lift` with `vis_via_ovf_lift`
  (the LAPC lift route, unchanged).

Scoreboard on the 41: **6 boarded** — the single-class anchor-pivot
Kp cluster.  The measured misses, in order of size:

* **16 parity-class**: micro chains differ in LETTERS by k-parity; the
  emitter needs per-parity chain pairs and the `k = 2i+r` reindex
  (`a = 2` ssides — the checker already expresses them, plus one
  `rep (u ++ u) i = rep u (2*i)` doubling lemma);
* **12 double-ladder** (named in 7f): term counts fit no affine law under
  the plain reader — expected, they need recursive terminal segmentation;
* **4 whose right sides are not `rep RU k ++ RPOST`** (2-cell stride
  variants);
* **3 deep-pivot** (mode `(1, True)`), whose boot is a j-dependent law.

None of these is new theory; all four are emitter extensions.

## 4. The tolerant rest scan (WAVE26 8b/8c incorporated): the remaining
   113 of the 211, split

`tools/counters/restscan.py` closes `anchors()`'s SECOND gap (8c): it
decodes every blank-head rest of a long run against EVERY alphabet × tail
split and classifies the best key's value coverage (plain / skip-s /
other), with a floor for the run's own transient.  At this
document's commit the sweep had covered 31 of the 113: **30 "other"** —
the register×counter regime — and 1 classified plain whose laps the flat
route still rejects (one of the `Jp` long-phase rows).  John's 8b read
held on every sampled row (the tape is `[register][1b-pairs]`; the
family alternates forms by octave, with register steps at measured
mid-octave points); the completed sweep's json is the next session's
starting split.

**The register×counter build is the next wave's biggest bite**: the same
piecewise-`Cc` + `glue_neverqh` device, one register dimension richer — a
FINITE union of anchor forms (register state × counter) with register-step
laps at `2^(k+1)-2`-style measured points.  Everything this wave built
composes with it: the virtual-anchor fences (`SkipGlue`), the tolerant
reader, and the same affine chains.

## 4b. John's five reads during the wave (hand-inspection now 31-for-31)

Given live during the wave's close, and the first is verified mechanically:

* **`0RB0LB_1LC1RD_0RD0LC_1RB1LA`** (from the `no inner family` 32):
  "a regular counter with a 0 to the left of every bit, and the carry has
  to alternate states to cross these 0s."  CONFIRMED, and it opens a
  class: `alphabet_infer` returns `A=[0,0] B=[0,1] C=[1]` — the
  ALREADY-WIRED `Alph_00_01_1` — and under it the interior is exact
  affine `4j+4` and the overflow `4j+6` for j >= 2 with ONE CONCRETE
  EXCEPTION at j = 1 (8 steps, not 10; the state-alternating carry at
  the smallest width).  That single exception is the whole mis-filing:
  the flat validate rejects at the j = 1 anchor and `degree()` reads
  HIGHER.  The boarding device already exists — state the overflow lap
  at `j = S j''` and discharge j = 1 as a concrete vm_compute lap, the
  offset route's j = 0 device one octave up.  MEASURE the `no inner
  family` and `no anchor` buckets for this affine-with-small-j-exception
  shape before designing anything new.
* **`0RB1LA_1LC1RD_0RB1LD_1RB0LA`** (the 4 `Jp` long-phase skip rows):
  "like a grey code where it counts up and down" — matches the measured
  inner countdown inside the exponential overflow phase (the blank-head
  rests step `111111011 -> 111011011 -> 101011011 -> ...`).  So these
  are skip + a GRAY-CODE inner induction, not a third chain.
* **`0RB0LD_1LA1LC_0LD0LC_1RD1RB`** and **`0RB1LA_1LA1LC_0LD0LC_1RD1RB`**
  (from the `no anchor` 24): "just a bouncer" — the two differ only in
  the A row, one class.  **`0RB0RD_1LC1RB_1RA0LC_1LB0LC`**: "a bouncer
  counter."  Bouncer machinery exists in the tree (`BounceCounter.v`,
  Bounce_8's MeasureGlue composition), and `QuadGlue` was JUST built for
  exactly the measure-composed micro-lap shape — the `no anchor` bucket
  should be probed with a bouncer-flavored quad reader before anything
  else.

## 5. Do-not-retry, extended

* The 4 `Jp` skip rows with a single V→E chain — 0 through 32+ extracted
  candidates and both landing families; the middle has a second turnaround
  and needs a 2-segment pipeline.
* `restscan` keys ranked by coverage alone — measured: alias families
  (`Ip` reading octave-shifted forms) out-score the true key; rank by
  regularity class FIRST (plain > skip > other), coverage second.
* Reading WAVE26 8c's "plain-full" rows as literally one-form: measured on
  `0RB0LC_1LC1RB_1RD1LA_1LD1LB`, the StA form covers only alternating
  octave bands and values 32..47 rest at StB with a GROWING far of ones —
  the register dimension again.  The flat route does not take them; the
  register build will.

## 6. Standing lessons, confirmed again

* **Peel before anything else** (three waves running, now four): the QUAD
  micro hops and terminals derive ONLY in the peeled framing (one unit
  copy in the prefix) plus a concrete k = 0 chain — the exact split-mode
  device of wave-13, at the micro level.
* The kernel re-checks everything: every board this wave compiled in-line
  at emission, and the three SKIP recoveries came from reading the
  LANDING off the machine instead of assuming its padding.
