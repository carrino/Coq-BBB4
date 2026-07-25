# The 708-machine residue — full diagnosis (wave-8, big-block RepWL track)

_Written 2026-07-25.  These are the 708 of `tools/counters/wave8_unrecognized.txt`
that the big-block RepWL sweep did NOT board (see
`docs/REPWL_BIGBLOCK_WAVE8.md`; 36 of the 742 were boarded there).  Method:
structural fingerprinting of all 708 (growth law, state-visit profile, blank
events, translated-cycle detection) + a wider-parameter RepWL probe of all 708
+ six parallel per-cluster deep-dives with two adversarial verification passes.
Everything here is untrusted analysis EXCEPT the boards, which the kernel
checked._

## TL;DR

**Nothing in this set is hard; almost nothing in it is open.** The residue is
dominated by binary counters — structurally the most *regular* machines in the
space — and the reason every generic decider bounces off is that they all use a
**lossy abstraction**, while a counter needs its forward behaviour modelled
**exactly**. (mxdys's inductive decider decides this whole set, and states the
condition plainly: *"my inductive decider can only decide a TM when it can
model the forward behavior exactly."* That is the one-line explanation of this
entire residue.)

| cluster | count | structure | route | boardable today |
|---|---|---|---|---|
| translated cyclers | 10 | linear extent; exact pattern recurs every `P` steps with constant head drift (`P` = 67…2215) | **existing `Checkers/TCycler.v`** | **YES — 8 boarded here, 2 already boarded via RepWL L=30** |
| √-growth wave/bounce counters | 15 | growing wall + bouncing digit region, extent ∝ √steps | `WaveCounter.v` / `BounceCounter.v` templates, per-machine | template exists, per-machine Coq needed |
| the champion | 1 | blanks at step 32,779,478 then spins out | `exists B, QHBound B` (quasihalter, not never-QH) | known route, heavy prefix |
| clean binary counters (1 rare state) | 166 | interleaved binary counter, one log-rare overflow state | wave-8 interleave emitter (`Jp`/`Ip` + `LapGlue`) | emitter owned by another session |
| carry-woven binary counters (0 rare states) | 515 | same, but the carry rides the main cycle so no rare state exists | same emitter, with the stride `k` from §"Counter encodings" | same |
| spinout | 1 | state-D spinout after blank re-entry at step 66,344 | trivially never-QH / `TCycler` degenerate period-1 | yes, needs the period-1 anchor convention |
| **genuinely open** | **0** | — see §"Zero open machines" — the last candidate was decoded | — | — |

> **UPDATE 2026-07-25 (human reads).** Three machine-by-machine reads from a
> human on bbchallenge overturned three of this document's conclusions,
> including the "1 genuinely open" claim — **the residue has ZERO known-open
> machines.** The corrections are in §"Zero open machines" and
> §"Counter encodings"; the mechanized form of the insight is
> `tools/kcopy_classify.py`.  This is the wave-8 lesson for the fourth,
> fifth and sixth time.

Boarded during this debug: **8 new translated-cycler boards** (`TCyc8_01..08`),
each `coqc -native-compiler no` compiled with `Print Assumptions` =
`functional_extensionality_dep` only, through the **existing** TCycler decider —
zero new soundness surface.

## The clean result that pins it down

The wider-parameter RepWL probe (`L ≤ 40`, `T ≤ 4`, with warmup, 12 000-node
cap) over all 708 returned:

- **CAUGHT 2** (boarded at `L=30`),
- **NOCLOSE 706**,
- **CLOSED_NOCERT 0**.

Zero finitize-but-no-certificate cases is the load-bearing number: **the
measure/rank vocabulary is never the bottleneck** for this residue — a richer
measure set cannot help. The wall is *finitization itself*. A binary counter's
tape word is literally the base-2 expansion of `n`, so it differs on **every
single increment**; no finite block set, n-gram set, or window closes it, and
every closure method instead manufactures a spurious carry-free cycle. This
matches `COUNTER_EMITTER_WAVE8.md` §4b ("RepWL over the counter core: DEAD")
and now *explains* it rather than just recording it. It is also exactly the
complement of mxdys's condition: an exact forward model decides these; a lossy
abstraction cannot.

## Per-cluster diagnosis

### 1. Translated cyclers — 10 machines — **BOARDED (8 new)**

Linear extent growth; after a short transient the exact `(state, local window)`
signature recurs every `P` steps with a constant head shift. Verified genuine by
persistence: each holds the cycle for **≥ 5,000,000 absolute steps** (adversarial
re-check at a longer budget than the original detection; 0 of 10 refuted).

Periods/shifts: side-R `167/+13`, `318/+18`, `337/+15`, `597/+39`, `2215/+23`;
side-L `67/−13`, `67/−13`, `170/−22`, `170/−22`, `337/−15`.

They are `NOCLOSE` under RepWL because a *drifting* cycler never finitizes under
a counted-block abstraction — but a translated cycler's natural decider already
exists in the repo. **Why they sat in the residue: a budget/coverage gap.** No
TCycler pass was ever run over this residue, and periods up to 2215 (plus
transient) exceed the cycle-search budget of the census light tier. The windowed
fingerprint already held the *correct* `(period, shift)` for 10/11 lin machines;
that certificate was simply never handed to the sound checker.

Boarded: `TCyc8_01..08` via `tcycler_check_neverqh_sound` (side R) and
`tcycler_check_neverqh_sound_L` (side L, via `Mirror`), params in
`tools/tcyc8_manifest.tsv`. The other 2 were already boarded by RepWL at `L=30`.

**Beware the detector.** 17 of the 27 windowed-detector "translated cycler"
flags are FALSE POSITIVES: a bouncer's sweep interior looks like a period-1
translation for `O(sweep length)` steps, and a counter's carry-free run looks
periodic until a carry propagates. They break after 4–230 confirmed steps at
tiny periods (`P = 1..5`) and are all √-growth. Growth law disambiguates
cleanly: genuine ⇒ linear, spurious ⇒ sqrt.

### 2. √-growth wave/bounce counters — 15 machines

Extent doubles when steps quadruple (measured ratio ≈ 2.00). A wall that grows
without bound plus a bounded/slowly-growing bouncing digit region ⇒
extent ∝ counter value ∝ √steps. Three sub-shapes:

- **parity-wave block-word odometer** (5): left-edge word `1^{B0} 0 1^{B1} 0 …`
  with unbounded depth; each pass carries a parity wave leftward and spawns a
  new length-1 block — exactly the `WaveCounter.v` invariant.
- **single unary wall, geometric ×3** (3): pure `1^n` with `n = 28, 82, 244,
  730, 2188` at ×9 step intervals ⇒ `BounceCounter.v`.
- **growing 0-gap + bounded carry** (5) and **doubling right block** (2): a
  `1^k` block bouncing in a `0^m` gap that grows +2/pass, ones flat.

Route: per-machine instantiation of the landed `WaveCounter`/`BounceCounter`
glue (as `Wave_7/17/27/36.v`, `Bounce_8/33.v` already do). No generic decider
applies — RepWL/TCycler/Cycle are all dead here. Several are behavioural
twins/relabelings (≥5 twin pairs), so one template board can cover multiple
machines. This is `COUNTER_EMITTER_WAVE8.md` WAVE-3 ("route the √/Gray tail
OUT").

### 3. Binary counters — 681 machines (166 clean + 515 carry-woven)

Both clusters are the same object; they differ only in whether an overflow state
is visible to a fingerprinter.

- **166 with exactly one rare state** — textbook single-track interleaved binary
  counters. The rare state is the carry/overflow state at the growth edge, so it
  fires `O(log N)` times. Verified on the canonical
  `0RB---_1RC1LD_0LD0RC_1LB1LA`: overflow fires at steps 3, 17, 47, 109, 235,
  489, … with consecutive deltas `14, 30, 62, 126, 254, …` = `2^(k+1) − 2`
  (exactly one overflow per power of two). De-interleaving the digit region
  yields the consecutive integers 0, 1, 2, 3, … incrementing by exactly 1 per
  lap. Growth side splits ~evenly (~80 left / ~82 right); a handful are
  wide-stride base-4 (`2^(2k)`).
- **515 with zero rare states** — identical counters whose carry is **woven into
  the main increment cycle**, so all four states fire ~25% each and there is no
  low-frequency state to hang a rank/measure on. That is *precisely* why they
  are the "resistant" variety. Extent law is uniform and diagnostic: **`3k`
  cells per 8× steps** for stride `k` — `+6` for the stride-2 majority, `+9` for
  a stride-3 machine. They differ only in ENCODING, along the stride axis
  measured in §"Counter encodings" (`SEP2` 51, `KCOPY1` 31, `KCOPY2` 28, `SEP3`
  3 out of a 120-machine sample); all of them are interleave-emitter targets
  with `k` as the stride parameter. A few show a small fixed companion block on
  the far side (mild two-sided).
  (An earlier revision of this document split off ~120 "sparse
  run-length/spacer" machines whose value supposedly lived in gap lengths — that
  subclass was an artifact of misreading oscillating popcount; see Correction 1.)

All 681 are never-quasihalting (the overflow/edge event keeps recurring;
`blank_reentry` is `None`), and all are `NOCLOSE` for RepWL at every parameter
tried (spot-checked to `L=60, T=6`). Route: the wave-8 interleaved-counter
emitter (`Jp`/`Ip` + `JpCounter.v` + `LapGlue.glue_neverqh`, template
`Interleave_TGT.v` proven end-to-end) — **owned by another session**, and this
residue is its un-emitted remainder. Per-machine lap-proof codegen, not a
runnable generic decider.

### 4. The champion and the spinout — 2 machines

- `1RB1LD_1RC1RB_1LC1LA_0RC0RD` — the 32M champion: blanks at step 32,779,478
  then spins out. A genuine **quasihalter**, so it needs `exists B, QHBound B`
  (`COUNTER_EMITTER_WAVE8.md` §7), not never-QH. Its fingerprint reads as
  sqrt/period-1 — a false positive in both directions; don't let it pollute the
  √-counter cluster.
- `1RB0LD_1LC0LA_1LA0LC_1RD1RC` — a pure state-D spinout (write 1, move right
  forever) beginning at step 66,348 after a blank re-entry at 66,344. Trivially
  never-QH. Note: the default `warm=60000` in the verifier lands *before* the
  onset and mislabels it — a warmup artifact, not machine behaviour.

## Counter encodings — the stride axis (and three corrections)

A human read of three individual machines produced the classification axis this
document was missing. **A residue counter is a binary counter in one of a small
family of encodings**, parameterized by a stride `k` and whether the `k` cells of
a digit are identical copies or one data cell plus a constant separator:

| encoding | meaning | example |
|---|---|---|
| `KCOPY1` | plain binary, one cell per bit | 31/120 of the 515 sample |
| `KCOPY2` | each bit stored **twice** | 28/120 |
| `KCOPY3` | each bit stored **three times** ("3× wider counter") | `1RB1RC_1LA1RA_0RC1LD_1LB0LD` |
| `SEP2` | data cell + one constant separator ("counter with **0 between bits**") | 51/120 |
| `SEP3` | data cell + two separators | 3/120 |

Mechanized as `tools/kcopy_classify.py`: it decodes wall-anchored snapshots and
requires the decoded integers to be **consecutive**, then re-confirms in a
**late window at large counter values** (a decode that works at value 6 but
breaks at 10³ is not a decode). On a 120-machine sample of the 515 cluster:
**113/120 (94 %) decode as counters** — `SEP2` 51, `KCOPY1` 31, `KCOPY2` 28,
`SEP3` 3 — every one late-confirmed; 5 `MIXED` + 2 no-wall remain (tool
limitation, not machine hardness). All of them are therefore the interleave
emitter's target, with `k` feeding the stride parameter
`COUNTER_EMITTER_WAVE8.md` §3 WAVE-2 already anticipates.

**Correction 1 — the "sparse run-length / spacer" subclass does not exist.**
This document previously claimed ~120 of the 515 hold their value in *gap
lengths* (routing them to the `Spacer` template). Wrong. The exemplar
`1RB0LD_1LC0RD_0LC1LD_0RB1RA` and its twin `1RB1RC_0LB1LA_0RD1RC_1LB0RC` are
ordinary counters with a `0` between bits: `SEP2` decodes them to
497,498,…,502 and 3007,…,3012 respectively. **The analytical error is worth
recording: popcount OSCILLATES on a counter** (7 = `111` → 3 ones, 8 = `1000` →
1 one), so the "ones frozen at 8 while a 0-gap grows" observation is exactly
what a counter looks like — it is not evidence that the value lives in the gaps.

**Correction 2 — stride ≠ 1 is a real and common variant**, not an exotic ~2 %
tail: 28 + 3 of 120 sampled machines need `k ≥ 2`, plus a confirmed `KCOPY3`.
Verified independently by the extent law: a stride-`k` counter grows **`3k`
cells per 8× steps** (`+9` measured for the `KCOPY3` machine vs `+6` for the
stride-2 bulk).

## Zero open machines

**Correction 3, the big one: `1RB1RC_0LA1LC_0RD0LB_1LB1RD` is NOT open.** It is a
plain `SEP2` interleaved counter. A *fixed* decode (`k=2`, `off=2`, data cell
first, LSB nearest the wall, **anchor state A**) yields consecutive integers both
early (0,1,2,…,7) and in a late window at large values
(**959,960,961,962,963,964**, and 1959…1964 at a longer horizon — 15/15 unit
increments with ~11 digits). So the field does **not** shift: the earlier
"the high bit is whether the data sits in even or odd cells, so the whole field
shifts" reading (`MACHINE_NOTES_WAVE8.md`, "no route yet") was an artifact of
decoding at the wrong **anchor**, not a property of the machine. Route: the
ordinary interleave emitter.

Two things made the old reading stick, both now fixed in the classifier:
the anchor cell is **not** the tape extreme (the extreme is visited *once*, while
the real per-lap turnaround sits one or two cells inward — the "wall activity" on
low-bit increments), and the anchor **state** matters (only state A decodes; the
most-frequent state at that cell does not).

So **every one of the 708 has a known route.** What remains is codegen and
per-machine Coq, not open mathematics — consistent with the fact that mxdys's
inductive decider decides this whole set.

Caveat, stated honestly: 395 of the 515 were not individually decoded (a
120-machine sample was), and 7 of the 120 sampled did not decode with this crude
tool. Those 7 + the unsampled remainder are where an undiscovered odd shape
could still hide.

## EYEBALL THESE

Prioritized for a human on bbchallenge. The top group is where a human read is
most likely to pay off.

**RESOLVED by human reads — kept as the worked examples (no longer questions)**
```
1RB1RC_0LA1LC_0RD0LB_1LB1RD   was "confirmed open"; is SEP2, fixed decode, late values 959..964 => NOT open
1RB1RC_1LA1RA_0RC1LD_1LB0LD   KCOPY3: each bit in 3 copies, 3x wider counter, right wall (+9 cells / 8x steps)
1RB1RC_1LA0LB_1LD0RC_0RA1LB   SEP2/KCOPY2: clean duplicated-bit counter, values 4..13 consecutive
1RB0LD_1LC0RD_0LC1LD_0RB1RA   SEP2: "counter with 0 between bits", wall activity on low-bit increments, late 497..502
1RB1RC_0LB1LA_0RD1RC_1LB0RC   SEP2: same wall+counter structure, late 3007..3012
```

**Carry-woven counters — still worth a check**
```
1RB0LB_1LC1RD_0RB0LC_1RA1LD   canonical dense interleaved counter (de-interleaves to 0,1,2,3 with carry reset)
1RB0RB_0LC0RA_1LC0LD_1RA1LD   mild two-sided: fixed left block + active right counter (widened-anchor path)
1RB0LB_1LC1RD_0RD0LC_1RA1LD   which stride/encoding? (was mislabeled "value in 0-run lengths")
```
**The 7 the classifier could not read (best remaining places to look)**
```
0RB1LC_1LC0LC_0RD1LA_1RD1RB   MIXED (wall=L)
1RB0LB_1LA0LC_0LB0RD_1RD0RC   MIXED (wall=R)
1RB0LB_1LA0LC_0LB0RD_1RD1LA   MIXED (wall=R)
1RB0LB_1LA0LC_1LC1RD_0RD1RA   MIXED (wall=L)
1RB0LB_1LB0LC_0RD1LC_1RD1RA   MIXED (wall=L)
1RB0LB_1LC1RD_0RB0LC_1RA1LD   no fixed wall found (grows both ways?)
1RB0LB_1LC1RD_0RD0LC_1RA1LD   no fixed wall found
```
These are almost certainly counters in an encoding the reader does not cover
(a wall of width > 1, a two-sided anchor, or a stride/offset outside the grid) —
they are listed because a human read has now corrected this analysis six times.

**Clean counters — orientation/stride variants for the emitter**
```
0RB---_1RC1LD_0LD0RC_1LB1LA   canonical clean overflow counter, deltas exactly 2^(k+1)-2
0RB0LC_1LC1RB_1RD1LA_0LB0RC   reference "this IS the emitter route" (value 3,7,15..511, power-of-two carries)
1RB0LD_1RC1RA_1LA0RC_0RA1LD   wide-stride base-4: extends once per TWO binary digits (2^(2k)) — WAVE-2 stride
0RB1LA_1RC0LA_0RD1RB_1LD0LB   carry-ripple variant: rare state fires per set bit => log^2-rare, not log-rare
```

**√-growth wave/bounce (template targets)**
```
0RB0LB_1LC1RA_0LD0LC_1RD1LB   canonical parity-wave block word 1^{B0} 0 1^{B1} 0 ... (WaveCounter shape)
0RB0LD_1LA1LC_0LD0LC_1RD1RB   pure unary wall tripling 28->82->244->730->2188 (BounceCounter shape)
0RB0RD_1LC1RB_1RA0LC_1LB0LC   textbook bounce: 1^k block in a growing 0^m gap, ones flat ~118
0RB0LC_1LC0RC_1RD1LB_1LA0RD   doubling right block 24->48->96->192 (geometric field variant)
```

**Boarded here — sanity-check the diagnosis**
```
1RB0RD_1LC0LD_0RB0LB_1RD0RA   translated cycler P=167 shift+13, boarded TCyc8_01
1RB1LB_1RC0LA_0RD0RC_1LD1LA   translated cycler P=2215 shift+23 (largest), boarded TCyc8_03
1RB1LD_1RC1RB_1LC1LA_0RC0RD   the 32M champion: blanks at 32,779,478 then spins out (QHBound route)
1RB0LD_1LC0LA_1LA0LC_1RD1RC   state-D spinout from step 66,348 (fingerprint + default verifier both mislabel it)
```

## Method / reproduce

```sh
# structural fingerprint of all 708 (growth law, visits, blank events, tcycle)
python3 <scratch>/sim708.py <708-list> fp708.jsonl
# wider-parameter RepWL probe: CAUGHT / CLOSED_NOCERT / NOCLOSE per machine
python3 <scratch>/repwl_wider.py <708-list> wider.jsonl
# translated-cycle persistence check (rejects bouncer/carry-free false positives)
python3 -c "import dbg; print(dbg.verify_tcycler('<machine>', conf_steps=5_000_000))"
# board a genuine translated cycler through the EXISTING decider
#   tcycler_check_neverqh_sound  tm anchor period reach     (side R)
#   tcycler_check_neverqh_sound_L tm anchor period reach    (side L, via Mirror)
```

Scope: no committed file outside the big-block RepWL track was modified; the
counter emitters, `theories/Machines/Counters/`, `theories/Counters/ILC*` and
`theories/Census/` were not touched (`census_cache.py --check` = MATCH).
