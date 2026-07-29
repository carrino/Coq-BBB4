# Wave-29 (register route): the composition BUILT, and the bucket is one family

_Branch `claude/register-counter-4-2-tus108`, cut from
`claude/residue-reduction-4-2-ao95wq`, 2026-07-29.  Wave-28 measured the
`no overflow phase at K=6` bucket, split it seven ways, and asked for the
composition that did not exist: a piecewise `Cc` (virtual arm + framed arm)
crossed with a NESTED branch.  This wave builds it — and then re-measures
the split, which turns out to have been mostly the READER._

## 1. The one-line result

**4 new boards, all funext-only.**  `D_remaining` **269 → 265**.  One new
library file (`theories/Counters/RegGlue.v`, axiom-free, 3 lemmas), one new
emitter (`tools/counters/regcert.py`), one new probe
(`tools/counters/regprobe.py`).

And four measurements that change the bucket's shape:

| what wave-28 filed | what this wave measures |
|---|---|
| `period-2+virt` (4) | **BOARDED**, all four (§2) |
| `drift` (24) | **not a class**: 22 of 24 are `grow-11` once the reader's 8-cell far cap is lifted and the lowest octave is held out (§4a) |
| `short` (36) | **not a class**: the chase's `TAILMAX = 2` was the whole blocker; with a 3- or 4-cell tail **34 of 36** walk 60-139 anchors and read a growing wall (§4b) |
| `grow-11` (35, +8 `+virt`) | **there is no wall.**  John's read (§5c), confirmed: it is a PLAIN counter under the already-wired `Mp` alphabet whose anchor family alternates its TAIL by octave parity — `Mp@C` tail `[S1]` / `[S0;S1;S1]`, gap-free over 8..255, interior lap exact `4j+2`.  The "growing `[S1;S1]`" is the counter's own leading zero-pairs, and every exponential measurement of the class (§5a) is what you get chasing a `sqrt` subsequence of it |

So the bucket is not seven classes.  Counted exactly:

| n | class |
|---:|---|
| **99** | ONE family -- a counter with a wall that gains `[S1;S1]` (a few `[S1^4]`) per octave: 35 `grow-11` + 8 `grow-11+virt` + 22 of the `drift` + 34 of the `short` |
| 10 | constant-frame: **4 boarded** here, the 4 `Jp` gray-code rows (§6), 2 `plain` |
| 4 | still unread: 2 `drift` whose walk is short at `pmax = 300`, 2 `short` |

Nothing under `theories/Census/` was touched; `census_cache --check` stayed
MATCH throughout.  `SkipGlue`, `NestedLapLift`, `LapDecider`, `LapCertGlue`,
`LapGlue*` are **untouched**.  Nothing owned by the concurrent QUAD session
(`quad_*.py`, `QuadGlue.v`, `QMG_*`, the `no interior chain` bucket) was
edited; every board added here is named `REG_*`.

## 2. The composition (prompt item 1): piecewise `Cc` x a NESTED branch

It exists, and it needed **nothing new in `theories/` beyond the octave
parity**.  That is the finding: `NestedLapLift.nested_overflow_lift` takes
its outer anchor `p` and inner start `v0` as ORDINARY ARGUMENTS, so it does
not care that `Cc` is piecewise; and `SkipGlue`'s `reach_ovf_skip` /
`vis_via_skip` already fence the virtual anchors.  The two just compose.

The board (`REG_*`) is

    virt p = match pexp p with Some (S _) => <parity selector> | _ => false end
    frm  p = if podd p then far1 else far0          (the octave's frame)
    frmv p = if podd p then farv1 else farv0        (the virtual frame)
    Cc   p = if virt p then (qv, E p ++ tail, S0, frmv p)
                       else (qf, E p ++ tail, S0, frm  p)

with `RegGlue.podd` the octave parity, and

| branch | law | route |
|---|---|---|
| interior, `virt p = false` | `4j+4` / `4j+8`, exact | one chain PER PARITY |
| overflow, `cview p = (S j, None)` | `4j+7` (odd octave) / `4j+9` (even) | one chain per parity |
| register step, `virt p = true` | `4*2^k + 11` | **boot + inner counter + exit** |

`RegGlue.v` is three lemmas and a `Fixpoint`:

* `podd_succ_int` — an interior increment stays in its octave, so the frame
  does not move under it;
* `podd_succ_fill` — an overflow increment crosses into the next octave, so
  the frame flips;
* `podd_succ_pexp` — `2^k` and `2^k + 1` are in the SAME octave, which is
  why a virtual anchor and the ordinary anchor just above it share a frame.

`Print Assumptions` on all three: **closed under the global context**.

### 2a. The measurement that made it statable

`regscan.lap_law` fits the two laps a virtual anchor carries (`vin`, the
overflow into it; `vout`, the register step out) with ONE affine law over all
`k`, and reported "both virt laps exponential" on 2 of the 4 rows.  On a
period-2 frame that is the wrong fit: the frame at octave `k` is
`forms[k mod 2]`, so the laps depend on `k mod 2` too and a single fit over
consecutive `k` mixes two laws.  `tools/counters/regprobe.py` fits PER OCTAVE
CLASS, and on the exemplar `0RB0LC_1LC1RB_1LD1LA_1RD0RC`:

    vin    k = 3,5 -> 19, 27      4k+7          k = 4,6 -> 25, 33   4k+9
    vout   k = 3,5,7 -> 4         flat          k = 4,6 -> 75, 267  4*2^k+11
    int    4j+4 at BOTH parities

**Three of the four branches are ordinary chains.**  Only the register step
is exponential.  That is a one-nested build, not a two-nested one.

### 2b. What the register step actually is

`nestcert.families` over the phase from `E(2^k)` to `E(2^k + 1)` finds a
consecutive inner family running `2^(k-1) .. 2^k - 1`, at the SAME alphabet,
with far `[S1;S1]` — the machine **re-counts the whole counter** to move the
register mark one place.  That is why the mark cannot be moved by a chain,
and it is exactly `NestedLapLift`'s shape at the inner index `k-1`.

### 2c. Two standing lessons, paid again

* **PEEL BEFORE ANYTHING ELSE.**  The register step's boot derives only from
  the PEELED virtual anchor (`uD ++ rep uD k ++ soD` rather than
  `rep uD (S k) ++ soD`): the step's first move is onto the counter's own top
  block, and the unpeeled form denies the head a concrete cell to step onto.
  Unpeeled: 0 chains.  Peeled: first try, `0*k+6`.
* **READ THE LANDING, NOT ITS PADDING.**  On two of the four rows the
  interior lap landed one written blank past the anchor and closed only up to
  `lift` — which `SkipGlue.reach_ovf_skip` cannot use, since it needs the
  interior lap EXACT.  The cause is that the chase strips trailing blanks off
  the far side, so a frame the machine leaves as `[S0]` is reported as `[]`.
  The emitter now recovers it by trying the padding: whichever far makes the
  interior chain land exactly IS the frame, and the whole board is stated
  against it.  That fix is the difference between 2 boards and 4.

### 2d. Two virtual parities, not one

On two of the four rows the machine rests at EVERY power of two in a
transient frame, and that frame ALTERNATES as well (`C@[S1]` on odd octaves,
`C@[]` on even).  So `virt` is not "one parity of the powers of two" and the
register step needs ONE ARM PER PARITY — here one FLAT (`0*k+10`) and one
NESTED.  The emitter reads both the frame and the virtual frame as functions
of the octave parity and emits per-parity interior, overflow and register
arms; a parity with no virtual anchor discharges its case from
`virt p = true` and `podd p = b` directly.

## 3. What is in the tree

| file | role |
|---|---|
| `theories/Counters/RegGlue.v` | **new**, axiom-free: `podd` and its three lemmas |
| `tools/counters/regcert.py` | **new**, UNTRUSTED: chase -> frames by octave parity -> per-parity chains -> the nested register step -> differential validation -> board |
| `tools/counters/regprobe.py` | **new**: the per-octave-class lap fit (§2a) and the growing-far fit (§4a) |
| `tools/counters/spacetime.py` | `--rests` (blank-head rows only) and `--mark` (the state letter AT the head cell), for the head-anywhere reads |

`regcert.validate` replays EVERY branch against the raw simulator before a
board is written: exact step counts, exact configurations, `lift`-equal
landings, and every inner lap of every register step (119 anchors, 2-4
register steps, 38 inner laps per board).  The kernel then re-runs `srun` on
every chain.

## 4. The bucket, re-measured: `drift` and `short` were the READER

### 4a. `drift` is `grow-11` (22 of 24)

`regscan.frame_law` fits a growing far from `ks[0]` and requires the unit to
be APPENDED.  Two things break that and both are cosmetic:

* the LOWEST octave is often exceptional (a different state, or a shorter
  far) — hold it out and the rest fit;
* the chase caps the far side at `FARMAX = 8` cells, which a growing far
  outruns after three octaves — so the walk stopped and the frames looked
  lawless.

`regprobe.py --grow` (hold out the lowest `d` octaves, allow the unit to be
prepended, `FARMAX = 40`) over the 24:

| n | fit |
|---:|---|
| 15 | `grow-11`, appended, no octave held out |
| 3 | `grow-11`, appended, lowest octave held out |
| 2 | `grow-11`, PREPENDED |
| 1 | `grow-1111` |
| 3 | walk still too short at `pmax = 300` |

The exemplar the prompt names, `0RB0LC_1LC1RB_1RD1LA_0LD1LB`, is one of
them: frames `A@[]`, `B@[S1]`, `B@[S1;S1;S1]`, `B@[S1^5]`, `B@[S1^7]` — the
first octave exceptional, `[S1;S1]` per octave after it.  That is John's read
("a counter with 1 to the left of each bit, msb on the right, 2 1s to the
right of the msb") plus `restscan`'s "the gap starts at 128 = 2^7 because the
far grows", and the two agree.

### 4b. `short` is `grow-11` too: the blocker was `TAILMAX = 2`

`regscan._tails()` enumerates tails of at most **2** cells.  John's live read
of the `short` exemplar `0RB1LA_0LC1RD_0LD1LD_1RB0LA` — "a fixed `01` two
cells right of the frame that the head keeps returning to" — is a **3-cell
tail**, and that is the whole of it.  An absolute-coordinate rest dump
(`spacetime.py --rests --mark --lo -12 --hi 5`) shows the frame ending at
column 1 with `0` at column 2 and a fixed `1` at column 3, and the head
returning to the left end of the word:

    col  890123456789012345
    435  D p=1    0000111111111d0100
    436  B p=2    00001111111111b100
    447  A p=-9   000a11111111010100

With `TAILMAX = 4` the chase on that row runs to **n = 137** anchors and
reads `Jp@tail=[1;0;1;0]` mirrored, frames `A@[]`, `D@[S1]`, `D@[S1^3]`,
`D@[S1^5]`, `D@[S1^7]` — §4a's shape exactly.  The whole bucket, re-chased at
`TAILMAX = 4`, `FARMAX = 40` (`regprobe.py --wide`) and then refitted by §4a:

| n | fit |
|---:|---|
| 20 | `grow-11`, appended, lowest octave held out |
| 4 | `grow-11` outright |
| 2 | `grow-11`, PREPENDED |
| 4 + 2 + 2 | `grow-1111` (with and without a held-out octave, 2 of them `+virt`) |
| **2** | still `short` |

**34 of the 36 walk, 60 to 139 anchors each, and every one of them reads a
growing wall.**  The answer to "which cell is home" is the blank at the LEFT
END OF THE WORD, and the `01` is not a landmark to anchor on but a tail the
enumeration never offered.

`TAILMAX` is left at 2 in `regscan.py` so that `reg113.json` still
reproduces; the wide scan is a separate run.

## 5. The `grow-11` family (prompt item 2): three readings, and the third
   one is a PLAIN COUNTER

The prompt asked to check EARLY whether `rep u (Pos.size_nat p - c)` survives
the lap glue.  It does, structurally, and it does not, dynamically.

**Structurally it survives.**  On the exemplar `0RB0RC_1LC1RB_0LD1RA_1RC1LD`
(`Alph_10_11_11@D`, tail `[S1;S1]`) the frames are exactly

    octave 3  far = [S1;S1]        octave 5  far = [S1^6]
    octave 4  far = [S1;S1;S1;S1]  octave 6  far = [S1^8]

i.e. `rep [S1;S1] (size_nat p - 3)`, state constant.  The interior lap does
not change `size_nat p` and the overflow lap raises it by exactly one, so the
two obligations the prompt names hold.  And the index problem is solvable:
`sden` uses ONE index for both sides, and on the overflow branch the far's
count `m = j - c` is linked to the carry index, so REINDEXING at `j = j' + c`
puts both sides on `j'` (`pre = rep uS c` on the left, `rep u j'` on the
right).  On the interior branch the two indices are independent, but there
the far is untouched and can ride as the RIGHT OPAQUE TAIL — the same device
this wave's interior chain already uses.

**Dynamically it does not — at the frame the chase reads.**  Measured over
6 rows of the class, at the growing-far frames above:

| row | interior lap at octave `k` | overflow lap |
|---|---|---|
| `0RB0RC_1LC1RB_0LD1RA_1RC1LD` | `4j + 3*2^k - 4` (20, 44, 92, 188 at k=3..6) | 803, 3147, 12439 — `Theta(4^k)` |
| `0RB0RD_1LA1RC_1RD1LC_0LC1RA` | 44, 92, 188, 380 | 1619, 6303, 24883 |
| `0RB1LA_1RC0LA_1LD1RB_1LB1LD` | 44, 92, 188, 380, 764 | 102, 202, 398, 786 — `Theta(2^k)` |

Not one branch is affine, **including the interior one** — and an interior
increment cannot cost `2^k` steps on a tape of `O(k)` cells unless something
else is counting.  It is.

### 5b. The chased counter is a SUBSEQUENCE of the machine's own

Decode the blank-head rests INSIDE one of those "interior laps" and they are
a consecutive run in the SAME alphabet at the SAME state with the SAME far:

    chased anchor p = 16 -> 17     inner rests decode   97 ..   98
    chased anchor p = 32 -> 33     inner rests decode  386 ..  389
    chased anchor p = 64 -> 65     inner rests decode 1540 .. 1547

with `real ~ 0.376 * p^2`.  The chase's `p` is not the machine's counter: it
is the subsequence of values whose word happens to match `E p ++ [S1;S1]`
with a short far.  **The tail was taken from the wrong split.**

### 5c. John's read, mechanised: there is no wall.  It is a PLAIN counter

Given live during the wave's close, on `0RB0RC_1LC1RB_0LD1RA_1RC1LD`:

> "a pure counter with a 1 to the left of each bit, msb on the left" …
> "2 ones to the left of the msb"

**CONFIRMED, and it dissolves the class.**  Read in ABSOLUTE coordinates,
pairs `(1, b)` with the marker to the LEFT of its bit and the MSB leftmost,
the whole tape decodes at **15,630 consecutive steps out of 15,645 rests**.
The leading `[1;1]` is the constant John names.  And the alphabet
`bit b -> (b, 1)`, terminator `[S1;S1]` is **`Mp`, wired since wave-13** —
nothing new was needed at all.

The anchor family is `Mp@C`, far `[]`, with a **period-2 TAIL**:

| octave | tail | coverage |
|---|---|---:|
| 3, 5, 7 (odd) | `[S1]` | 8/8, 32/32, 128/128 |
| 4, 6 (even) | `[S0;S1;S1]` | 16/16, 64/64 |

The union covers **8..255 with no gaps at all** — no skip, no virtual
anchor, no register mark — and the interior lap is exact **`4j + 2`**.

So every earlier reading of this bucket was wrong in the same way.  The
"growing `[S1;S1]` wall" is the counter's own **leading zero-pairs**: the
word is fixed-width and widens one pair per octave, and under an alphabet
whose terminator is `[S1;S1]` those pairs read as a wall past the end.  The
`Theta(2^k)` interior and `Theta(4^k)` overflow of section 5a are what you
measure when you chase a `~sqrt` subsequence of a plain counter.

`tools/counters/regprobe.py two_form()` mechanises the read: collect every
blank-head rest keyed by `(alphabet, state, tail, far)`, and look for a PAIR
of keys whose union is gap-free and which splits by octave parity.  On the
exemplar it returns `Mp@C tail=[S1]` and `Mp@C tail=[S0;S1;S1]` directly.

### 5d. The build, specified — and how far it gets today

`tools/counters/tailcert.py` (new) is the route: `two_form()` reads the pair
of keys off the machine (collect every blank-head rest keyed by
`(alphabet, state, tail, far)`, keep a PAIR whose union is gap-free and which
splits by octave parity), and `_derive` builds the certificate.  Swept over
the 113, `two_form` finds a gap-free family on **95 of them** — 28 `Mp`,
22 `Ip`, 35 `Alph_10_11_11`, 6 one-form, plus a few others; 18 find none.

The board is

    Cc p = if podd p then (q1, E p ++ t1, S0, f1)
                     else (q0, E p ++ t0, S0, f0)

and both peels are needed, measured on the exemplar:

* the anchor's prefix is EMPTY on both sides, so at `j = 0` the head has no
  concrete cell to step onto and NO window step exists — `derive_chain`
  returns nothing at every framing.  The interior branch therefore SPLITS
  (`j = 0` concrete: `SWin 2`, cost 2; `j = S j'` with one unit peeled into
  the prefix: cost `4j'+6`), which is `emit_lapcert`'s split mode;
* the overflow branch is likewise stated at `j = S j'` with one unit peeled,
  and `cview p = (1, None)` (that is, `p = 1`) is fenced below `p0`.  Cost
  `4j'+10` out of an even octave, exact.

With those, **three of the four branches derive and validate**.  The fourth —
the overflow out of an ODD octave, `Theta(2^j)` — does not, and the reason is
worth recording because it is a NEW inner shape:

    K = 5 (p = 63 -> 64):  inner rests run 132 .. 191  =  2^7+4 .. 2^7+2^6-1
    K = 7 (p = 255 -> 256): inner rests run 516 .. 767  =  2^9+4 .. 2^9+2^8-1

The inner counter runs a **PARTIAL octave** — it starts at an offset and
stops HALFWAY, not at the all-ones fill.  `nestcert.families` wants a full
`2^(K-1) .. 2^K - 1`, `nestcert.derive_offset` wants `2^(K+1)+c .. 2^(K+2)-1`,
and `NestedLapLift.inner_to_fill_lift` runs to `fill v0`.  None of the three
covers "from `v0` to `v0 + 2^k - 1`".

So the missing piece is a **bounded inner carrier**: the same well-founded
induction on `JpCounter.tovf`, stopped at a measured endpoint instead of at
the fill.  That is one lemma next to `inner_to_fill_lift`.

### 5e. Swept: where the 113 actually stop

`tailcert.py --list` over all 113 (`tools/counters/tail113.json`), reporting
the FURTHEST gate either orientation reached:

| n | gate |
|---:|---|
| **66** | `no interior j=0 chain` — the split's concrete `j = 0` lap does not derive; a THIRD framing, not a theory gap |
| 22 | `no inner family at pow2 j` — the partial-octave inner counter of §5d |
| 18 | `no gap-free two-form family` — the reader still misses these |
| 4 | `no interior j=0 chain` at the other parity |
| 1 | `no boot chain` |
| **2** | fully derive and validate (192 anchors, 2 nested overflows, 18 inner laps) — and both are rows this wave already boarded through `regcert.py`, so they add nothing |

So the two-form route as it stands boards **zero new machines**: the reader
reaches 95 rows, but 70 of them stop at a `j = 0` framing gate before any of
the exponential machinery is reached.  That gate is the cheap thing to attack
next — it is the PEEL question one notch further in, and it stands in front of
70 rows.  The two rows that DO derive end-to-end are the proof that the rest
of the route is sound.

## 6. The 4 `plain+virt`: they are the four `Jp` gray-code rows

`0RB1LA_1LC1RD_0RB1LD_1RB0LA` and its three siblings have a constant frame
(`A@[]` or `D@[]`), a virtual anchor at EVERY power of two (state `C`, all
ones), a flat `0*k+4` register step OUT of it, and an overflow INTO it
costing `2^(k+4) - 2k - 8` — exponential.  The phase's blank-head rests
decode DOWNWARD (`15, 14, …, 8`), which is John's wave-27 read ("like a grey
code where it counts up and down") and is why `nestcert.families` — which
wants a consecutive UPWARD run `2^(K-1) .. 2^K - 1` — finds nothing.  These
are the same 4 rows WAVE27 section 2 filed as "the `Jp` long-phase rows"; a
descending inner induction is a different carrier from
`inner_to_fill_lift` and neither exists yet.

## 7. DO NOT RETRY (measured this wave)

* **Fitting a virtual anchor's laps with one affine law when the frame has
  period P.**  Measured: on all 4 `period-2+virt` rows the single fit reports
  "exponential" on branches that are `4k+7` / `4k+9` per parity.  Fit per
  octave class first; you may be looking at one nested branch, not four.
* **Believing ANY reading of the `grow-11` family that has a wall in it.**
  Two were measured this wave (wall in the tail, wall on the far side) and
  both are artifacts: the machine is a plain counter and the "wall" is its
  own leading zero-pairs (§5c).  A reading whose laps come out exponential
  on a bucket whose neighbours are affine is a reading to distrust, not a
  branch to budget for.
* **`regscan.chase` on a family whose wall grows.**  It takes the FIRST rest
  whose word matches, which on this bucket is measured to be a rest of a
  LATER pass with a longer wall.  Collect every rest and keep the frames that
  cover a whole octave (`regcert.frame_probe`) instead.
* **`nestcert.families` on a phase whose inner rests DESCEND.**  The 4
  `plain+virt` rows: the run is there, `15..8`, and `families` requires
  `2^(K-1)..2^K-1` ascending, so it reports nothing at any tail.  Needs a
  descending carrier, not a wider search.
* **Calling a row `drift` or `short` before widening the reader.**  `drift`
  was `FARMAX = 8` plus an exceptional lowest octave; `short` was
  `TAILMAX = 2`.  22 of 24 and (sampled) most of 36.
* Standing: everything in WAVE28 section 4, WAVE27 section 5, WAVE26
  section 6, WAVE25 section 6, WAVE24 section 7, WAVE18 section 5, WAVE16
  section 5.

## 8. What the next wave should build

1. **A BOUNDED inner carrier** (§5d), and then the two-form board.
   `tailcert.py` already reads the family (95 of the 113) and derives three
   of its four branches; the fourth needs `inner_to_fill_lift` stopped at a
   measured endpoint rather than at the all-ones fill, because the inner
   counter of the exponential arm runs a PARTIAL octave.  One lemma next to
   `inner_to_fill_lift`, then the board template (split interior + peeled
   overflow + the nested arm), and the 95 follow.
2. **A descending inner carrier** for the 4 `Jp` gray-code rows (§6):
   `inner_to_fill_lift` run from `fill v0` down to `v0`, which is the same
   well-founded induction on `JpCounter.tovf` in the other direction.
3. The 2 `plain` rows: an exponential overflow whose inner family starts at
   `2^(j+1) + 4`, i.e. `nestcert.derive_offset` with `OFFSETS` extended past
   3.  Two boards, one constant.

## 9. Standing lessons, confirmed again

* **Peel before anything else** — seventh wave running (§2c).
* **Read the landing off the machine instead of assuming its padding** — the
  difference between 2 boards and 4 (§2c).
* **Measure the bucket before designing for it** — and measure the READER
  too.  Four of wave-28's seven classes were the reader's caps, not the
  machines' (§4, §5b).
* **Ask with a TAPE, in absolute coordinates.**  The `short` decode fell out
  of one `spacetime.py --rests --mark` dump with fixed `--lo/--hi`: John's
  "fixed `01` two cells right of the frame" is a 3-cell tail, and the
  question "which cell is home" answers itself once the columns line up.
