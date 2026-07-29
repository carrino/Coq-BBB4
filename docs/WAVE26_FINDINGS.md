# Wave-26: the cascade bucket, closed out — and the 41 QUAD/QUAD, characterised

_Branch `claude/residue-reduction-4-2-dpb65q`, 2026-07-29.  Wave-25 boarded
the 57 gated cascade machines and 8 of the 12 octave-down rows, and named the
remaining 4 precisely (`docs/WAVE25_FINDINGS.md` §7): the same octave-down
shape except the closing count **enters one value in**.  This wave boards
those 4, re-measures the 17 one/two-count rows the bucket has left (§3-4),
and then takes the design pass `RESIDUE_PROMPT.md` item (1) asks for on the
41 `QUAD`/`QUAD` rows — the largest never-designed population in the residue.
**§7 is that pass, and it is the most reusable thing in this document:** the
41 are ONE shape, measured with no exceptions, and the composition theorem
they need is already in the tree._

## 1. The one-line result

**All 4 board, first render, funext-only.**  `D_remaining` **431 → 427**
(4,729 of the frozen 5,156 settled, 91.7%).  The cascade route is now
**spent**: `cascade_probe.py --gate` over the whole 87-machine bucket reports
**69 GATED** — and all 69 are boarded (`CASB_*`) — against 17 one/two-count
rows and 1 main-count-at-4..7.  Nothing in `theories/` outside the four new
board files was touched; no new library Coq, no new checker surface, no new
axiom.

`make closeout` regenerated the stages; `audit.py` OK (exact partition);
`Closeout.vo` and every stage file recompiled in-container, with
`Print Assumptions closeout_partial` = `functional_extensionality_dep` only;
`census_cache --check` MATCH throughout (nothing under `theories/Census/`
touched).

## 2. The 4: what "enters one value in" actually cost

Wave-25's §7 reading was exactly right, including the size of the fix.  At
outer index `S j'` the closing count runs `2^(j'+2)+1 .. 2^(j'+3)-1`, i.e.
it starts at `xI (pow2 (S j'))` and not at `pow2 (S (S j'))`.  Three
consequences, and only three:

* **the word.**  `E (xI (pow2 n)) = uS ++ rep uD n ++ soD` — the octave's own
  word with the odd digit peeled off the front and ONE FEWER unit copy behind
  it.  (`docs/WAVE25_FINDINGS.md` §7 wrote this as `sS ++ …`; the digit-1
  word is `uS` in `ENCDATA` terms — `sS` is the interior lap's start `post`
  and equals `uD` in every row of the table, inferred rows included, so it is
  the wrong name for this position.)  Proved by `rewrite <- epow2_; reflexivity`
  — it is the encoding fixpoint's own `xI` clause.
* **the fill twin.**  `E (fill (xI (pow2 n))) = rep uS (S n) ++ soS`, proved
  `exact (efill_ (S n))`: `fill (xI (pow2 n))` and `fill (pow2 (S n))` both
  reduce to `xI (fill (pow2 n))`, so the two are convertible and the existing
  `efill_` discharges it as-is.
* **nothing else.**  The way OUT is untouched — both values share a fill, so
  `CLOSEB`, `gclbx_` and `geo_` are byte-identical to the `big_in = 0` render.
  `fill_hop` needed no generalisation (`inner_to_fill_lift` is arbitrary-`v0`
  already), and `cascade_overflow` never sees the value.

Mechanically: `nestcert.cascade_law` reads the entry offset off the run
instead of demanding it be zero (`law['big_in']` ∈ {0, 1});
`cascade_transitions` gives `CLOSEA`'s destination the peeled prefix and one
fewer unit; `cascade_validate` replays the closing count from `2^(j+1)+big_in`;
and `cascade_emit.reps_low` swaps the landing-shape gate, the rendered word
and the index `replace`.  The `LOW_*` templates carry the count's value in
four holes (`@BIGV@`/`@BIGVP@`/`@BIGVE@`/`@BIGVF@`) plus an `@EXISEC@` block
that is EMPTY at `big_in = 0`.

**Regression:** all 65 previously committed `CASB_*` boards and the gated
`--proto` render come out **byte-identical** to the pre-change emitter
(checked mechanically, all 65 + proto).  The committed
`theories/Tests/CASC_*.v` differs from BOTH renders only in its doc header,
which was hand-edited when it was committed in wave-24 — pre-existing, not
this wave.

## 3. The 17 one/two-count rows, re-measured

Wave-25 §6 said "nothing about them is a cascade" and asked for a
re-measurement before any design.  Here it is.  **All 17 are `no boot chain`
rows**, and they fall into exactly three sub-families:

| n | shape | what the phase is |
|---|---|---|
| **10** | `2^(j-1)` count, then `2^j` count | TWO counts, one octave apart, **under two different alphabets** (`Alph_01_11_011` tail `11`, then `Alph_10_11_1` tail `1`) |
| **4** | one 5-value count `12..16` | a slow count spanning ~the whole phase with a GROWING far side (`far = 0…01`); profile `2^7:x6 2^6:x4` |
| **3** | one span, decoded at 5 octaves | every segment is a nested SHADOW of one span (`64..127`, `32..63`, … `4..7`, far growing by `11` per level) — one count, not five |

The 10 are the interesting ones and §4 is about them.  The 4 and the 3 are
each a distinct unsolved shape; note two of the 3 measure overflow **HIGHER**,
not `EXP2`, so they are not in the exponential-counter model at all.

## 4. The 10: two of the three pieces derive, and the third is not a search

The 10 are a two-count overflow whose **first count sits one octave DOWN**.
That is why they are `no boot chain` and not `no exit chain`:
`nestcert.families()` searches octaves `0 .. MAXOCT` only, so the
`2^(j-1) .. 2^j-1` count is never returned as a candidate; the boot is
searched into the `2^j` count instead, which begins ~130 configurations into
the phase behind a whole other count, and no chain reaches it.

Three things were measured this wave, in order, and the third is the one that
matters.

**(a) The octave floor is real but not the whole blocker.**  With `families()`
restricted to `oct = -1` the octave-down family is found on all 10 —
`Alph_01_11_011@…` tail `11`, unambiguous, top-scoring — and then the boot
chain into it **still does not derive** under the plain `_chain`
(`derive_chain`, no peel and no split).

**(b) Under the FRAMING search it derives on all 10.**  Wave-24's own lesson
had never been applied here — *"when a transition is known to exist by trace
and does not derive, the framing search space is (peel, split) before it is
anything else"* (`WAVE24_FINDINGS.md` §2), and B→A had NO chain at peel 0 at
any split.  Running `_frame_pair` on this boot: **10 of 10 derive**, all at
the identical framing —

    peel = (1, 0)   post = 6   cost = 4*i + 6   EXACT (no lift), 7 steps

One peeled unit copy, again.  So these rows are **not** an identification
failure and **not** a boot-chain failure; both pieces exist.

**(c) The remaining blocker is the SHIFT chain**, from the octave-down count's
fill to the octave-0 count's start — and it is NOT a bounds problem.  It does
not derive at `(peel ≤ CASC_PEEL = 3, split ≤ CASC_POST = 14)` on any of the
10, and widening to `(peel ≤ 8, split ≤ 30)` — **378 framings per machine** —
finds nothing either (checked on 3 of the 10; the 10 are structurally
identical everywhere else, all deriving at the same framing with the same
cost).  The second family is identified without ambiguity (`families()`
returns `Ip@…` tail `1`, the same three words as the `Alph_10_11_1` the
segment scan names — the known alphabet-aliasing that `cascade_runs`'
`prefer` exists for), so this is not a decode question either.

What the shift actually has to do is the thing no route here has: **re-encode
a `j`-length word from one digit alphabet into another** (`Alph_01_11_011`'s
`uD`/`uS` into `Ip`'s), across ~66 configurations.  That is a pass over the
whole word, not a turnaround at its head, and a single-index window chain is
the wrong shape for it however it is framed.  The exit chain is untested
behind it.

Note the other half of the cost if the shift lands: an octave-DOWN count is
`j - 1` blocks, which is not an sside count over `nat` without a reindex at
`j = S j'` plus a concrete `j = 0` case — exactly the reindex the octave-down
cascade route already builds (`cview_none_shape` + `lapz_`/`visz_`), so the
device exists and is not new theory.

## 5. Machines with a halt transition: a real effect, already spent

Worth recording because it is a natural thing to try next and the answer is
"no":

| | with a `---` halt | full 4×2 |
|---|---|---|
| in the frozen 5,156 | 1,537 (29.8%) | 3,619 |
| boarded | 1,492 | 3,237 |
| **settled** | **97.1%** | **89.4%** |
| still open | **45** | 382 |

One fewer reachable transition does make a machine easier for this
machinery — by 7.7 points — but that is why only **45** are left, 10.5% of
the residue against 29.8% of the frozen set.  The 45 sit in the same buckets
as everything else (26 `no interior chain`, 12 `no overflow phase`, 3 `no
inner family`, 3 `no anchor`, 1 `no boot chain`) and share no sub-route.
**They are not a batch.**

## 6. Do-not-retry, extended

Everything in `WAVE25_FINDINGS.md` §6 and `WAVE24_FINDINGS.md` §7 stands.
Add:

* Searching the 10 two-count rows' boot chain with the UNFRAMED `_chain` —
  measured, 0 of 10; with `_frame_pair` it is 10 of 10 at peel (1,0), post 6.
  This is the third bucket in a row where one peeled unit copy was the whole
  difference (B→A in wave-24, the octave-down boot in wave-25, this).  **Peel
  before anything else** is now the standing first move on any transition
  that traces but does not derive.
* WIDENING the 10's SHIFT-chain framing bounds — measured 0 at
  `(peel ≤ 3, split ≤ 14)` and 0 again at `(peel ≤ 8, split ≤ 30)`, 378
  framings per machine.  Do not widen further and do not go back to
  alphabets (the second family is identified unambiguously).  The shift
  re-encodes a `j`-length word between two different digit alphabets; that
  is a pass over the whole word and a single-index window chain cannot be
  it at any framing.  Whatever takes these 10 is a NEW piece, and naming it
  is the design question — not a search-budget question.
* Reading the 3 shadow-only rows as a one-count-per-level cascade — the five
  descending segments are nested re-decodings of ONE span, not five counts,
  and two of the three measure overflow `HIGHER`.

## 7. Same session: the 41 QUAD/QUAD, characterised — one shape, all of them

`RESIDUE_PROMPT.md` item (1) calls the 41 `QUAD`/`QUAD` rows of the
`no interior chain` bucket "the largest population in the whole residue that
has never had a design pass".  This is that pass.  It is measurement only —
nothing is boarded — but the class turns out to be **completely uniform**, and
the composition theorem it needs **already exists**.

### 7a. What they are

A binary increment whose **carry is done by linear search**: to find the first
zero digit the head makes ONE ROUND TRIP PER DIGIT, out to the digit and back
to the anchor, before probing one digit deeper.  `Θ(j)` excursions of length
`Θ(k)` gives `Θ(j²)` — the measured quadratic, on the nose.

Here is one whole interior lap, `p = 47 → 48` at carry index `j = 4`, of
`0RB1LA_1LC1RD_1RD1LD_1RB0LA`'s cluster-mate
`0RB0LA_1LA0LC_0RD1LC_1RB1RD` (mirrored spec `0LB0RA_1RA0RC_0LD1RC_1LB1LD`,
`Kp@A`, `tools/counters/spacetime.py --t0 324 --t1 355 --lo -7 --hi 4`).  The
counter word reads leftward from the head, LSB nearest: `47 = 111101` in `Kp`.

```
         col  -7........4      head
324  A p=0    010111100000     at the anchor, word = 1 1 1 1 0 1
326  C p=0    010111000000     probe depth 1: clear it ...
328  B p=-2   010111100000     ... restored, one deeper
329  C p=-1   010110100000     probe depth 2 ...
333  B p=-3   010111100000     ... restored, one deeper
334  C p=-2   010101100000     probe depth 3 ...
340  B p=-4   010111100000     ... restored, one deeper
341  C p=-3   010011100000     probe depth 4 ...
349  B p=-5   010111100000     ... restored, one deeper
350  A p=-4   011111100000     depth 5 is the first ZERO digit -> SET it
351  A p=-3   011011100000     and sweep back right, clearing the ones
354  A p=0    011000000000     lap done: 48 = 000011
```

Cost `2+4+6+8+10 = 30`, exactly the measured `(j+1)(j+2)` at `j = 4`.

### 7b. Three measurements, all 41 machines, no exceptions

| measurement | result |
|---|---|
| interior lap polynomial fits an exact integer quadratic | **41 / 41** |
| **overflow polynomial is the SAME polynomial** as the interior | **41 / 41** |
| head-direction **reversals per lap affine in `j`, slope exactly 2** | **41 / 41** |
| micro-lap (one excursion) run-length-encodes to a fixed letter pattern with counts affine in the probe index `k` | 33 / 41 directly; the other 8 alternate between two increments — the parity pattern — and all 8 are `Bp` |
| **the micro-lap's `(state, read, write, move)` sequence — i.e. a CHAIN — is a fixed list with counts affine in `k`** | **41 / 41**: 37 uniform in `k`, 4 after the standard `k = 2i+r` re-index.  **The chain bodies are 2–3 window steps.** |

That last row is the decisive one and it is worth stating plainly: **the
micro-lap is not merely chain-*like*, it is literally a chain** — a fixed list
of two or three `(state, read, write, move)` window steps with counted
repeats, which is exactly what `LapDecider` expresses and what `srun` costs at
`ca*k + cb`.  Nothing about the micro-lap is outside the certificate model.
What is outside the model is only that there are `Θ(j)` of them.

The leading coefficient is the alphabet's word stride: `1·j²` for the 25 `Kp`
rows (1-cell digits), `2·j²` for the 10 `Bp` and 6 `Alph_00_10_1` rows (2-cell
digits).  Example micro-lap bodies: `B·Cᵏ·Dᵏ`, `CD`, `AB`, `DAB`, `AC` — a
handful of shapes, each a fixed letter pattern with counted runs.

That overflow and interior are the *same polynomial* says the machine does not
treat overflow specially at all: the carry search simply runs one digit
further.  A route that takes the interior branch takes the overflow branch for
free, which is why this bucket is `no interior chain` and not
`no interior chain` + something else.

### 7c. Why no chain search can ever reach them

A `LapDecider` chain is a fixed list of window steps, so it sweeps a **bounded**
number of times and `srun` returns `ca*i + cb`.  These laps make `Θ(j)`
excursions — reversal count affine in `j` with slope 2, measured on all 41.
**No `derive_chain` widening reaches them at any peel, split, or budget**, and
this is a proof from the shape rather than a failed search.  It is consistent
with `WAVE16_FINDINGS.md` §5's do-not-retry list and explains it.

### 7d. The route: `MeasureGlue`, which already exists

`theories/Counters/MeasureGlue.v` was built for exactly this and its docstring
describes this class almost word for word — *"a bounce macro-lap `D(k) → D(k+1)`
is not one parametric run: it chains an unbounded number of micro laps … and
only a measure bounds how many"*.  `mrun` composes a measure-decreasing
recurrence of exact micro laps into one `csteps` run, and costs are
existentially quantified throughout, so a quadratic total is no obstruction at
all — only the *structure* has to be uniform, and it is.

The instantiation the 41 want:

| `MeasureGlue` variable | here |
|---|---|
| `A` (abstract micro state) | the probe depth `k` |
| `stepA k` | `Some (k+1)` while digit `k` is set; `None` at the first clear digit |
| `mu k` | `j + 1 - k` |
| `Cf k` | head at the `k`-th digit, word unchanged — the tape at `t = 328/333/340/349` above is literally identical |
| `Hstep` | the micro-lap chain, uniform in `k` |
| `Hterm` | the carry write plus the clearing sweep (`t = 350..354`) |

The micro-lap's endpoints are both plain ssides: the region left of the deepest
probe is never touched, so it is an **arbitrary opaque tail** exactly like the
cascade's `Cin T v`; the region right of the head is the `k-1` already-probed
digits plus the anchor tail, a count of `k-1` with `a = 1`.  One digit crosses
from the opaque region to the counted one per step, which is precisely the
`Xs`-shaped opaque region `nestcert._xterm` already reads off a framing.

### 7e. What is NOT done — and what is no longer in doubt

**No board and no emitter route.**  That is the whole of what is missing, and
it is engineering rather than discovery, because both halves of the route are
now confirmed rather than conjectured:

* the **micro-lap is a chain** — §7b's last row, 41 / 41, bodies of 2–3 window
  steps.  It does not need `_frame_pair` or any widening; it is already in the
  certificate model.
* the **composition is `MeasureGlue.mrun`**, which exists, is funext-clean,
  and quantifies costs existentially.

So the build the 41 want is:

1. an extractor that reads `(probe chain body, stride, parity)` off one
   measured interior lap — the same shape of reader as `cascade_law`;
2. a board template instantiating `MeasureGlue` with `A = k`, `mu = j+1-k`,
   `Cf k` the head-at-digit-`k` denotation, `Hstep` the micro-lap chain and
   `Hterm` the set-and-clear sweep;
3. the `k = 2i+r` re-index for the 4 parity rows;
4. the differential validator, replaying whole laps at several `j` against the
   raw simulator — wave-18's discipline, unchanged.

**No new library Coq is predicted.**  The one thing to check early, because it
is the only piece with no precedent in this tree, is `Hterm`: the terminal
sweep writes the carry and then clears the probed digits, so it is a chain
whose count is the *final* `k` rather than a running one, and the board has to
tie that `k` to the anchor's carry index.  Everything else is assembly.

Reproduce every number here with the scripts named in this section plus
`tools/counters/ovfshape.py --spec SPEC -v`.


### 7f. Same session: the extractor and the skeleton, BUILT

§7e's items 1 (extractor) and part of 2 (the composition) are no longer
pending; the fable leg of this session built and validated both.

**`tools/counters/quad_probe.py`** reads the whole law off measured laps —
boot, micro and terminal as folded step-patterns with affine count laws —
and validates it differentially: exact restore-point times, exact totals,
exact successor tape, `j = 2..11`, interior AND overflow.  **29 of 41 gate**
(13 `Kp`, 10 `Bp`, 6 `Alph_00_10_1`; 13 single-class, 16 with parity
classes; every one from `j = 2` with no concrete exceptions).  Generalising
the reader over the class forced four findings the design pass had not seen:

* **anchor-pivot vs DEEP-PIVOT.**  3 of the 29 (`mode=(1, True)`, all `Kp`)
  walk out once and do their round trips pivoting on the DEEP end, so their
  boot is `j`-dependent — a law, not a fixed step list.  The reader tries
  four skeleton modes: records left/right, tracked from the start or from
  the opposite side's global extreme.
* **two-cell alphabets set TWO depth records per digit** — the mark count is
  an affine law `a*j + b`, not `j + const`.
* **the parity classes differ in LETTERS, not just counts** — per-class
  templates, with counts fit in the class ORDINAL (a slope of ½ in `k` is
  no integer fit in `k`).
* **the terminal folds as `prefix + (2-step block)^(affine) + suffix`** —
  §7b's "pattern varies" was the flat RLE not folding repeated pairs, not a
  real irregularity.

**`theories/Tests/QuadMGShape.v`** pins the composition, kernel-checked and
**axiom-free** (`Print Assumptions quad_lap`: closed under the global
context): `MeasureGlue.mrun` at abstract state `(k, m)`, `stepA` a PURE pair
function, `mu = snd`, `P x = fst x + snd x = j` — exactly §7d's table.
Given a micro hop `Cf k (S m) → Cf (S k) m` and a terminal at `m = 0`, the
whole quadratic lap is one `csteps` run.  The `(0, j)` entry point needs one
`change` to eta-pin the pair; that is in the file.

**The 12 that do not gate** are one further shape, the DOUBLE LADDER:
ascending probe trips, then a DESCENDING ladder of clearing trips inside
what the reader calls the terminal (visible as block counts descending
`…5,1,5 … 4,1,4 … 3,1,3…` in the failure prints).  In Coq that is two
`mrun` compositions back to back — nothing new — but the reader needs to
segment the terminal recursively before they gate:

    0RB0LA_1LA0RC_0LD1RC_1RB1LD   0RB0LA_1LA1RC_0LD0RC_1LD1RB
    0RB0LA_1RC1LB_1LA0RD_0LB1RD   0RB1LA_1LC1RB_1RD0LA_0LB0RD
    0RB1LA_1LC1RB_1RD0LA_0LC0RD   0RB1LC_1LA1RB_0RD0LC_1RD0LA
    1RB0LC_0LA0RB_0RD1LC_1LA1RD   1RB0LD_0LC0RB_1LA1RC_0RC1LD
    1RB1LA_0LA1RC_0LD0RC_1LD0RB   1RB1LA_1LC0RD_0RA0LC_0LA1RD
    1RB1LA_1LC0RD_0RB0LC_0LA1RD   1RB1LC_0LA0RB_0RD0LC_1RD1LA

What remains for a board is §7e items 1'-6: the two-index denotation
`Cf k m` (the cascade's `Dc l m` pattern), the micro chain and `Hterm` in
sside form with their `cden` bridges, the standard wrapping, and the
emitter.  Hand-board the exemplar `0RB0LA_1LA0LC_0RD1LC_1RB1RD` first —
micro `B1R0 (C1R1)^i C0L0 (D1L1)^i D0L1`, term `B0R1 (A1R0)^(j+4)`, boot
`A0L0`, everything validated to `j = 11`.

## 8. John's decode of the no-anchor bucket: the SKIP counter (verified)

_Added after the wave closed, same branch.  John read
`0RB0LC_1LC1RB_0RD1LA_1LB1LA` off its tape dump: **"just a counter with 1
to the left of every bit."**  Hand-inspection is now 23-for-23._

Verified mechanically, and the reading opens the whole bucket:

* **The decode is right and the anchor EXISTS.**  Pairs `1b`, LSB at the
  left edge, head resting AT the left edge in `StA`: 2,492 consecutive
  values decode over a 20k-step replay.  Better: `emit_lapcert.anchors`
  ALREADY finds this family on the mirrored spec — `Alph_10_11_11@A`,
  `tail=[0]`, `far=()`, an alphabet that has been wired since wave-14.
* **Why every wave still reported `no anchor`:** the machine **never rests
  at a power of two.**  `anchor_times` to p = 300 hits every value EXCEPT
  {2, 4, 8, …, 256} — at the fill the overflow sweep runs straight
  through, writing the LSB pair's data cell LAST and already incremented,
  so `E(2^k)` exists only half-written and the overflow lap is
  `fill(2^k − 1) → 2^k + 1`: **it enters one value in, at the OUTER
  anchor** — the same phenomenon as the octave-down 4's closing count
  (`xI (pow2 j)`, §2), one level up.  `phase_mid` waits for `E(2^K)`
  exactly, which never comes; that single test is the entire bucket.
* **With the anchor in hand the machine is AFFINE everywhere**: interior
  lap `4j + 4`, double-step overflow `4j + 7`.  No cascade, no measure —
  ordinary chains.

**The boarding route** (no checker extension needed): define the family in
plain Coq as

    Cc p = if is_pow2 p then VIRT p else E p ++ tail

with `VIRT (2^k)` the machine's real transient form (`E(2^k)` with the LSB
pair half-written, at a measured head position), and close with
`LapGlue.glue_neverqh` DIRECTLY — Bounce_8's pattern, which takes an
arbitrary `Cc : positive -> cconf` and only needs boot + laps + visits.
Three lap branches, all affine chains: interior (`cview Some`), fill →
`VIRT`, `VIRT → E(2^k + 1)`.  `LapDecider` is not touched.

**The taxonomy, full scan** (`anchor_times` to p = 300 over all 211; the
skip set is the machine's, read not assumed): **104 of the 211 find the
anchor family immediately** -- 21 missing exactly the 8 powers of two
(skip-1), 9+12 missing the powers plus/minus a small-p concrete case
(skip-1 with p=1 noise), 31+17 missing `{2^k} ∪ {2^k+1}` (skip-2, with and
without the noise), 3+2 with slightly deeper skip sets to name.  **107
report `no anchor family`** -- the alternate-octave shape below, or another
tail/edge.  Per-shape:

* **skip-1**: missing exactly `{2^k}` — `fill → 2^k + 1`, one virtual
  anchor.  The exemplar above.
* **skip-2**: missing exactly `{2^k} ∪ {2^k + 1}` (plus small-`p` concrete
  noise) — `fill → 2^k + 2`, two virtual anchors; measured on
  `0RB0LC_1LC1RB_0RD1LA_1LB1RB` and `0RB0LC_1LC1RB_1RD1LA_1LB0LA`.  The
  `+2` entry is the offset route's device one level up.
* **alternate-octave**: the form appears only on ODD octaves (present 2-3,
  8-15, 32-63, 128-255, 512-1023; measured on
  `0RB0LC_1LC1RB_1LD1LA_1RD0RC`) — the machine rests in a SECOND syntactic
  form on the even octaves, so the family is two-formed the way skip-k
  families are virtual-pointed.  These are the scan's 107 `no anchor
  family` rows; the decode itself held on the sampled ones, so the miss is
  the FORM enumeration, not the reading.

**Ranking consequence**: 104 rows with an anchor in hand and affine costs
is a bigger and cheaper bite than the QUAD 29 — the skip-counter route
(virtual anchor + `glue_neverqh`) should go FIRST in the next wave.
