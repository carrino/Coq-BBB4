# Wave-30: seven boards, two headline builds measured dead, and a bit-polarity inversion that empties the interior gate

_Branch `claude/residue-reduction-4-2-counters-p8kmdk`, cut from `main`,
2026-07-29.  The wave-30 prompt sized three builds — a missing `WTape`
primitive (§1, 17 rows), a template combination (§2, 8 rows), and a deeper peel
(§3, 70 rows) — and said "nothing below needs new mathematics".  §2 is right and
is built.  §1 and §3 are not: each rests on a diagnostic that turns out to
select a NECESSARY shape rather than a sufficient one, and measuring the
machines instead of the labels re-scopes 87 rows.

Then John's live reads on two machines — "msb on the left", "like a grey counter
where it goes up then down" — turned out to name the same defect in the reader
(§6b), and fixing it takes the `no interior j=0 chain` bucket from 70 rows to
ZERO (§6d).  The wave's real output is 7 boards and a residue whose next gate
has moved, in one step, from the interior branch to the exponential overflow
arm._

## 1. The one-line result

**7 new boards, all funext-only**, and one hand read that re-reads a 51-row
class.  Settled **4,901 → 4,908** by this branch's own boards; with `main`'s
cascade wave merged in the tree stands at **4,916 of 5,156 (95.3%)**, core
undecided **172 → 162**, `0RB` shadows 83 → 78.  Two emitter changes
(`GLUE_SPLIT_LIFT`, the offset close), one library lemma
(`LapCertGlue.lift_app_blank_l`, funext-only), two generated alphabets,
`theories/Census/` untouched, `census_cache --check` MATCH.

| what the prompt asked for | what this wave measures |
|---|---|
| §1 `cycRW` + `SCycR2`, "expect ~17 boards" | **0 boards.** Every SOUND instance of the mirror derives zero new chains; the variant that does fire is unsound. The dead ends are blocked by the crossing's STATE PERIOD (§2) |
| §2 split × lift, "expect ~8 boards" | **built; 4 board.** The other 4 are blocked on the OVERFLOW branch, not the interior (§3) |
| §3 the double peel, 70 rows | **the peel is irrelevant.** 51 of the 70 have a family the machine walks DOWNWARD; the other 19 are the SAME lift gap as §2, one level up (§4) |
| §5 measure the 26 `unreachable` first | done — every anchor family, both mirrors, plus the tolerant and parity-split readers. **All 26 survive it** (§5) |

And one hand read converted: John's `1RB0LC_0LA0RB_0RD1LC_1LA1RD` (§6).
Hand-inspection goes to **36-for-36**.

## 2. §1: the `cycR` gap is not a gap in the step language

Wave-29 §10a read the `no interior chain` bucket's dead ends as a missing
primitive: `WTape.cycL` deposits past a concrete right window and `cycLW`
generalises it on both sides, but `cycR` demands the left window be EMPTY on
entry and `SCycR n` has no offset, so "a lap that walks the block back
rightward past a concrete left prefix cannot be written down."  17 rows
dead-end at that shape (`intgap._cycr_gap`).

The shape is real.  The inference is not.

### 2a. The honest mirror fires nowhere

`cycRW`, the mirror of `cycLW`, is

    wsteps true true tm P (q, (lw, h, rw ++ u)) = Some (q, (lw ++ w, h, rw))
    ==> csteps tm (P*k) (q, (lw ++ L, h, rw ++ rep u k ++ R))
          = Some (q, (lw ++ rep w k ++ L, h, rw ++ R))

— the deposit lands BELOW the left window, which is what `cycLW`'s own
induction forces (the window has to be re-established on top for the next
unit), and it degenerates to `cycR` at `lw = rw = []`.  Wired into
`lapcert.py` in its FULL generality — both windows, every split of both
prefixes, i.e. every sound instance, not just the prompt's `SCycR2 n m`
(which is the `rw = []` case) — over all 51 `no interior chain` rows:

| | |
|---|---:|
| rows offering a sound `cycRW` step anywhere in the closure | **5 of 17** |
| rows gaining a new chain at any framing | **0 of 17** |

`emit_lapcert --list` over the 51 boards 0 before and 0 after.

### 2b. The variant that fires is unsound, and fails exactly at the induction step

The other orientation — deposit ABOVE the window, `(q,(lw,h,u)) -> (q,(w++lw,h,[]))`
— does fire, and turns the `j = S j'` frame exact on 3 rows.  It is also
wrong, and it is worth recording HOW wrong, because the shape is seductive:

    1RB1LA_0LA0LC_1LC1RD_0RB0RD, conf D L=1 h=0 R=[1]^(1j+0)0
      SCycR2 n=5 m=1 lw=1 w=0     plain SCycR unavailable
      k=0 OK   k=1 OK   k=2 MISMATCH

`k = 1` holds — that is just `wsteps_frame`.  `k = 2` fails because the second
unit run starts with `w` sitting on top of `lw`, so the hypothesis no longer
applies.  A window the deposit buries is not a window.  Checked against the raw
simulator on every row where it fires; the failure is at `k = 2` every time.

**So the trusted checker gets nothing.**  A lemma plus a constructor plus a
soundness case in `Checkers/LapDecider.v`, for zero boards, is not a trade to
make, and the prompt's own gate ("if you get 0, the deposit orientation is
mirrored wrong — check it against the dead-end state") is what closed it: both
orientations were checked against the dead-end state, and the dead-end state is
the thing that says no.

### 2c. What actually blocks them: the crossing's STATE PERIOD

Read off the machine at each dead end — how many units of the right block does
it take to return to the state and head the crossing entered with?  That is
exactly `cycR`'s induction hypothesis.

| period | rows | what it means |
|---:|---:|---|
| **2** | **8** | the state ALTERNATES over single-cell units.  No `cycR`-shaped lemma at unit size 1 can close; the block's count has to be made EVEN first — a parity device, not a cycle lemma |
| 1 | 1 | one unit closes, but only with the window buried (§2b) — not expressible |
| none in 8 units | 8 | the crossing DRIFTS.  The lap is not affine at all |

On the prompt's own exemplar `1RB---_0LC1RD_0LB1RD_1LB0RD` (`Kp@D`, tail
`[S0]`, far `[S1]`) the interior lap read off the machine is

    D -(2j+6)-> D      leftward carry across 1^(j+1), state D constant,
                       then a turn, then a rightward return across the
                       deposited 0^(j+1) alternating B > C > B > C ...

The return is one step per cell and two cells per state cycle, so the block
must be re-unitised from `rep [S0] (j+1)` to `rep [S0;S0] k`, and `j+1` has no
known parity.  The parity cancels only in the lap's LAST TWO steps, which is
why the total cost is affine (`2j+6`) while no affine CHAIN exists.

### 2d. It splits the bucket exactly along `ovfshape`

The period measurement and `residue_map.tsv`'s independently-derived shape
column agree row for row:

| `intgap` verdict | AFFINE | PARITY-AFFINE | HIGHER | EXP3 | EXP4 | QUAD | total |
|---|---:|---:|---:|---:|---:|---:|---:|
| `cycR-gap` | 3 | 5 | 5 | 2 | 0 | 2 | **17** |
| `lift` | **8** | 0 | 0 | 0 | 0 | 0 | **8** |
| `unreachable` | 5 | 2 | 7 | 6 | 4 | 2 | **26** |
| total | 16 | 7 | 12 | 8 | 4 | 4 | 51 |

All 5 PARITY-AFFINE rows and all 3 AFFINE rows measure period 2.  All 5 HIGHER,
both EXP3 and both QUAD measure never-returns.  And all 8 `lift` rows are
AFFINE — which is why §2 boards and §1 does not.

`intgap.py` now reports the period rather than the shape (`parity-cross` /
`drift-cross`), and `_cycr_gap` carries a comment saying what it is and is not,
so the next wave is not sent after the same lemma.

## 3. §2: split × lift, built — and what it does and does not reach

`emit_lapcert.derive` derived the SPLIT interior chains (`Z0 -> Z1` at `j = 0`,
`P0 -> P1` at `j = S j'`) **exactly only**.  The `lift = True` last resort was
reached on the ONE-chain path alone, and `GLUE_SPLIT` proves exact `cden`
equalities — strictly more than `LapDecider.lap_of_run` and `LapGlue`'s `Hlap`
ask for, both of which want a `lift` equality, and `CTape.lift_side` cannot see
a trailing blank.

`GLUE_SPLIT_LIFT` is the same fallback for the split.  No new theory:

* `gz_`/`gp_` state their second conjunct as a `lift` equality;
* `lapi_` returns `exists n c'`, which `@LAPICASE@`, `@VISCONC@`, `@VISHI@` and
  `NQH_CLOSE_LIFT` already consume — wave-16 built all of them;
* `@ZPEEL@`/`@PPEEL@` are per-half blank-peeling tactics, EMPTY when that half
  lands exactly, so a mixed split renders correctly rather than silently.

One thing had to be got right that the one-chain template gets for free: the
count `a * j + b` must be REDUCED before `rewrite !lift_app_blank`, because
`rewrite` does not compute and the far side is otherwise
`pre ++ rep u (0 * 0 + 0) ++ post`.  The exact templates finish by
`reflexivity`, which is up to conversion, and so never noticed.  Hence
`cbn [rep app Nat.mul Nat.add]` in the peel.

Ordering: tried LAST, after exact-one-chain, exact-split and one-chain-lift.

### 3a. 4 of the 8, and the other 4 are a different gate

All 8 rows wave-29 §10b measured do derive both split halves under `lift`, with
the slack exactly one trailing blank on a rep-free far side, and the exemplar
reproduces the prompt's numbers exactly (`1RB0RB_1LC1RA_0LC0LD_0RA0RD` under
`Alph_000_100_1@A`: `j = 0` cost 4, `j = S j'` cost `10j' + 14`).

4 board.  The other 4 — all `Alph_01_11_011` — fail at
`no overflow chain (nested: no boot chain)`: the INTERIOR gate is now open and
the OVERFLOW branch is what stops them.  That is a different build, and filing
them as `lift` rows overstated what the interior fix could reach.

Two `0RB` shadows (`0RB0RC_1RC0LA_1LD1RB_0LD1LA`,
`0RB1LD_1LA1RC_1RB0RC_0LD0LA`) were promoted to core rows when their cores
boarded — the shadow re-root does not carry a shadow whose core is settled by a
board — and both board through the same route here.

### 3b. The byte-identical regression, and why it has to be run as an A/B

The prompt's acceptance is "every committed board re-renders BYTE-IDENTICAL —
emit to a scratch dir and diff against `theories/Machines/`".  Run literally,
that test **cannot pass at `main`**: 717 of the 863 boards in
`frozen_map.tsv` that `emit_lapcert` owns already differ from what today's
templates render, because the templates have moved across ~20 waves (the
`first [ ... | ... ]` glue fallbacks, the `LapGlueAbs` import, the `lapi_`
lemma) while the boards in the tree were rendered by older ones.  9 no longer
derive at all.  None of that is this wave's doing.

The test that measures the intent — did the candidate ordering shift? — is the
same render run TWICE, once from a pristine `HEAD` worktree and once from the
patched tree, diffed against each other:

    863 boards rendered both ways      diff -rq: EMPTY
    717 DIFFERS / 146 IDENTICAL / 9 no longer derives   in BOTH runs
    failure sets identical, row for row

`tools/counters/rerender_check.py` is that harness, and its docstring says
which form to run and why.  This is the check the standing move asks for after
any change to `derive` or to the step language; it should be run as an A/B from
here on.

## 4. §3: the double peel is irrelevant, because 51 of the 70 count DOWN

`tailcert.py`'s two-form reader finds a gap-free family on 95 of the 113 rows,
and 70 of them stop at `no interior j=0 chain at octave parity b`.  Wave-29
read the `j = 0` frame as too SHORT — the lap leaves the concrete `sS` and runs
into the opaque `XL = E q0 ++ tail` — and the prompt asked for one more peeled
digit, splitting the interior branch three ways with concrete prefixes
`sS ++ dig(0)` and `sS ++ dig(1)`.

Measured on the prompt's own exemplar `0RB1LA_0LC1RD_1LD0RB_1RB0LA` (`Ip@A`,
tail `[S0;S1;S0]`) first, per the prompt's "MEASURE FIRST": the double peel
derives nothing — and neither does the `j = S j'` branch, which the `j = 0`
label hides because `_derive` checks `j = 0` first and raises.

Then the reason, read off the machine.  Walk the real run and keep every rest
matching either key, in VISIT ORDER:

    t=220 p=31 A   t=224 p=30 A   t=226 p=15 D   t=232 p=29 A
    t=236 p=28 A   t=238 p=14 D   t=248 p=27 A   t=252 p=26 A   ...

**The family counts DOWN.**  `two_form` accepts a pair of keys whose value sets
UNION to a gap-free range and split by octave parity — a condition on the SET,
which says nothing about the order the machine visits them in.  Every
derivation downstream assumes `E p -> E (Pos.succ p)`, so a descending family
has no interior lap at ANY framing and no peel of any depth can make one.  (The
two keys here are also reading ONE tape word at two tail splits — `p = 30` under
frame `A` and `p = 15` under frame `D` at adjacent steps — so the "gap-free
union" is partly the reader pairing a value with its own half.)

Over all 70 (`tools/counters/twoform_dir.py`):

| n | direction |
|---:|---|
| **51** | DESCENDING — 243 down / 3 up, `p -> p+1` realised NOWHERE |
| 19 | ASCENDING — `p -> p+1` realised 243 times |

And there is no mirror rescue: for all 51, the family exists in exactly ONE
mirror and descends there, while the other mirror has no family at all.

### 4a. The 19 ascending rows are §2's gap, one level up

On those 19, with both split halves tested exactly and up to `lift`:

| frames | interior split |
|---:|---|
| 29 | both halves derive up to `lift` |
| 9 | both halves derive EXACTLY |
| 0 | blocked |

**All 19 rows derive both interior halves at both parities.**  `tailcert`
requires the reached configuration to equal the target syntactically
(`rz[0] != Z1` raises), so 29 frames that close one written blank out are
reported as "no chain".  That is precisely the gap §2 closes for
`emit_lapcert`, and the double peel changes nothing: the peeled `j = 0` frames
return the same `lift` verdict as the unpeeled one, digit by digit.

So the properly-sized build for these 19 is **`lift` in `tailcert`'s interior
split** — the same plumbing as §2 plus a lift-capable interior glue in the
two-form board's per-parity arms — not a third framing.  What it reaches
downstream is §5b below.

## 5. §5: the 26 `unreachable`, at EVERY anchor family

`intgap.probe` only ever looked at the FIRST family `emit_lapcert.anchors`
offers, so `unreachable` was a statement about one family.  `intgap.py --every`
now probes, for both mirrors: every family the flat enumeration offers,
`restscan.best_key`'s TOLERANT key (which reads the family off the machine's own
rests and finds tails the enumeration never offers), and
`tailcert.two_form`'s parity-split pair.

Over all 26 (`intgap.py --every --list`):

| n | result |
|---:|---|
| **26** | `unreachable at every family` |

So nothing dissolves.  Unlike wave-29, where four of seven sub-classes fell to
exactly this move, these 26 are not a framing or a reader gap: the interior
target is in no form at any family either mirror offers.  §6's shape table says
why for 19 of them (EXP3 6, EXP4 4, HIGHER 7, QUAD 2 -- the lap is not affine);
the remaining 7 (5 AFFINE, 2 PARITY-AFFINE) are the ones worth a tape.

## 6. John's read: the carry is a BOUNCER, and that is what `no interior chain`
   means on a QUAD row

Given live during the wave, on `1RB0LC_0LA0RB_0RD1LC_1LA1RD`:

> "appears to be just a regular counter, but it does a carry bit using
> bouncing, so if it needs to carry across x 1's it does x bounces"

**Confirmed exactly.**  Under `Kp@B`, tail `[S0]`, far `[]`, the interior lap
from `E p` to `E (p+1)` at carry index `j`:

| j | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|--:|--:|--:|--:|--:|--:|--:|--:|
| lap | 6 | 12 | 20 | 30 | 42 | 56 | 72 | 90 |
| head reversals | 3 | 5 | 7 | 9 | 11 | 13 | 15 | 17 |

Reversals `= 2j + 1`, i.e. **`j` bounces to carry across `j` ones**, and the lap
is exactly **`(j+1)(j+2)`** — quadratic.  `residue_map.tsv` files the row `QUAD`
independently.

The consequence is general and it is why §1 was mis-scoped: **`no interior
chain` on a QUAD/HIGHER/EXP row is not a missing step, it is a lap that is not
affine.**  The lap language's cost model is `a*j + b`; a bouncing carry costs
`Theta(j^2)` and no chain of any length can express it.  That is the QUAD
route's business (`QuadGlue.quad_reach`), not the lap chain's — and of the 51
`no interior chain` rows, 28 are HIGHER/EXP3/EXP4/QUAD.

## 6b. BIT-POLARITY INVERSION: John's read re-reads all 51 descending rows

Given live, on `1RB1LC_0LC0RB_1LA1RD_1RC0RD` ("behaves very similar with msb on
the left") and on `0RB1LA_0LC1RD_0LD1LD_1RB0LA` ("like a grey counter where it
goes up then down?  adding one to alternating bits produces a rollover").

Both are the same fact, and it is the cause of §4's descending families: the
reader matched the tape under an alphabet whose two DIGIT WORDS are the wrong
way round, so the decoded value is the octave-wise complement of the machine's.
Measured on `0RB1LA_0LC1RD_0LD1LD_1RB0LA` under `Alph_10_11_11`:

| decode | longest consecutive `+1` run | up / down |
|---|---:|---|
| plain | 0 | 13 / 12,915 |
| Gray-to-binary | 1 | 6,465 / 6,463 |
| **complement within the width** | **4,095** | **12,915 / 12** |

It is an ordinary ascending counter read backwards.  ("Up then down" is what a
reflected reading looks like from outside; the complement is the reflection.)

The alphabet that reads it directly swaps `dig(0)` and `dig(1)` and KEEPS the
terminator.  `Jp` and `Alph_11_10_1` have the swapped digits but a ONE-cell
terminator, so they match nothing; the partner of `Alph_10_11_11` is
`Alph_11_10_11`, which did not exist.  Both new modules come straight out of
`gen_alphabet.py --abc <dig0>,<dig1>,<term>`, which PROVES the two
decomposition lemmas rather than asserting them, and both compile first try.

Registered in `ENCDATA` and in `tailcert.TRY` but deliberately **not in
`ENCS`**: verified that `ENCS` is unchanged (25 rows before and after importing
`tailcert`), that no `ENCS` row's data or `ENC` function is mutated, and that no
generator of `reg113.json` / `quad35.json` / `jexc80.json` imports `tailcert`.

With the two alphabets registered, **all 51 descending rows read ASCENDING** --
43 under `Alph_11_10_11`, 8 under `Alph_11_01_11`, consecutive `+1` runs of
127-247.

### 6c. And the reader now REFUSES a descending family

The alphabets alone are not enough: `two_form` scores candidate pairs by
coverage, so it kept preferring the descending reading it already had.  It now
records the ARRIVAL ORDER of each key's first sightings and rejects any pair
that does not count up — the invariant every route downstream assumes
(`E p -> E (Pos.succ p)`) and the one thing the old "gap-free union" test could
not see.  That change alone rescues rows for which an ascending family already
existed under a stock alphabet (the exemplar of §4 now reads `Jp`).

Re-measured over the whole 70:

| | before | after |
|---|---:|---:|
| ASCENDING | 19 | **67** |
| DESCENDING | 51 | 0 |
| no family at all | 0 | 3 |

### 6d. Consequence: the interior gate is EMPTY

With the reader fixed and `lift` allowed on the interior split (§4a), the gate
the whole wave-30 prompt was built around is gone.  Over all 70:

| n | furthest gate now |
|---:|---|
| 27 | `register step does not close` |
| 22 | `no boot chain` |
| 8 | `no inner family at pow2 j` |
| 8 | inner fill lands off the measured endpoint |
| 3 | no gap-free two-form family |
| 1 | `no exit chain` |
| 1 | `no inner interior chain` |

**Zero rows stop at `no interior j=0 chain`** — down from 70.  Nothing boards
from this yet: every one of the 67 now dies on the EXPONENTIAL OVERFLOW arm,
which is §4 of the prompt (the bounded inner carrier) and was parked while
`claude/cascade-twocount-4-2-r82mvf` was live.  That branch has since merged, so
it is unparked, and it is now the single gate in front of 67 rows.

## 6e. The census closure is a real constraint on where a lemma may live

`WTape.lift_app_blank` strips a trailing blank from the RIGHT of a
configuration; `CTape.lift_tape` is symmetric in the two sides, so the LEFT
twin is the same one-line proof.  The offset route's boot needs it (its boot
lands one written blank past the anchor's left end), and that is the whole of
the free board below.

Putting it beside its twin in `WTape.v` **breaks `census_cache --check`**:
`WTape.v` is one of the 526 `.v` files in the committed census input closure, so
editing it invalidates the committed census `.vo` and forces the ~7h re-walk the
prompt defers to stable hardware.  Measured, not guessed — the hash moved.

`lift_app_blank_l` therefore lives in `Counters/LapCertGlue.v`, which is OUTSIDE
the closure and which all 370 `NLAP_*` boards already import.  `Print
Assumptions`: funext only.  Worth recording as a standing constraint: **before
adding a lemma to a library file, check `census_cache.closure_v_files()`.**
`LapCertGlue`, `LapCertGlueLift`, `NestedLapLift`, `LapDecider`, `RegGlue` are
outside; `WTape` and `LapGlue` are inside.

The board it unblocks, `1RB1LC_0LC0RB_1LA1RD_1RC0RD` (`Alph_00_10_1`, `4j+4` /
`4j+13`), derives identically at `HEAD` and here — the cascade wave unblocked
its derivation and nobody re-swept.  The `?lift_app_blank_l` rewrite has to run
BEFORE the close's `cbn [app]`, which flattens `w ++ [S0]` into one literal and
destroys the shape it matches on.

## 6f. The 27 `register step does not close` rows: NOT a digit-width mismatch

John, on `1RB1RD_1LC1RA_0RB0LC_1LA0RD` (one of the 27): *"just a counter with 0s
to the left of each bit with a wall on the right, msb on the right, when the msb
overflows the wall moves over 4"*.

**Confirmed**: the wall is real and it is not misread high bits.  The row reads
under `Alph_00_01_0` — `dig(0) = 00`, `dig(1) = 01`, terminator `0` — so a `1`
only ever occurs as the SECOND cell of a digit and **two adjacent `1`s cannot be
counter digits at all**.  The `11` on the far side is therefore a genuine wall,
which is what distinguishes this from the `grow-11` artefact wave-29 §5c retired
(there the "wall" WAS the counter's own leading pairs).  An unfiltered
absolute-coordinate dump also confirms the geometry: the counter grows away from
a fixed 2-cell object on the far side, msb nearest it.

**Not confirmed, and this is the useful part**: the wall does not move 4 cells
per overflow.  `tools/counters/digitwidth.py` measures the length of the matched
word at the first pass through each octave and differences it.  Over all 27:

| n | result |
|---:|---|
| **27** | word grows **exactly 2 cells per octave**, matching a 2-cell digit |

Every row, every octave, no exceptions.  The `+4` visible in a raw dump spans
TWO octaves, not one.

That is worth recording because of what it rules out.  A wall moving 4 cells per
overflow under a 2-cell alphabet would have meant the reader was matching a
SUBSEQUENCE — one reader-digit per two machine digits — which is exactly the
wave-29 §5b failure mode, and it would have meant the register step fails because
it tries to move the mark one digit where the machine moves it two.  The fix
would have been a 4-cell alphabet.  **Measured: no row in the category has that
problem.**  The 27 are being read at the right width, on a genuine consecutive
family (243 `p -> p+1` transitions realised), and their blocker is in the arm
itself, not in the reading of the word.

So for wave-31 item (3): the digit-width hypothesis is closed.  What remains
un-measured there is the per-octave-class lap fit and whether the INNER family
is ascending under the inverted alphabets.

## 6g. …and the wall DOES move: the overflow phase is Theta(4^k), not Theta(2^k)

§6f measured the WORD and found no wall motion.  John's follow-up says why that
was the wrong object: *"the msb butts up against the wall but doesn't include
it."*  The wall is a SEPARATE object just beyond the top of the word, so a
word-length measurement can never see it move.

`tools/counters/wallstep.py` tracks the wall itself — the first run of `>= 2`
ones outward from the head, which under a `dig0 = 00` / `dig1 = 01` alphabet
cannot be counter digits — and records its absolute column and the time between
displacements.  On the exemplar `1RB1RD_1LC1RA_0RB0LC_1LA0RD`:

    wall start column   0    4    8    12    16    20    24
    first seen at t     6   42  168   654  2580 10266 40992
    displacement           +4   +4    +4    +4    +4    +4
    phase ratio               7.0  4.0   3.9   4.0   4.0   4.0

**`wall +4 per overflow, phase ratio ~3.99`** — the read, mechanised, exactly.

And that second column is the finding.  Over the 27 `register step does not
close` rows, on the 8 where a MONOTONE wall is detected:

| phase ratio per octave | rows | wall step |
|---|---:|---|
| ~4 | 5 | 2 or 4 cells |
| ~6 | 3 | 2 cells |
| **~2** | **0** | — |

Not one row has a phase that doubles.

_(Corrected: the first run of this measurement reported 14 rows with ratios
~4/~6/~3.  It ordered each wall's sightings by COLUMN rather than by
first-sighting TIME, and on a side the counter grows into those two orders
differ — which produced negative gaps and meaningless ratios on 6 of the 14.
`wallstep.py` now orders by time and requires the displacement to be monotone,
which drops those 6 and turns the other 13 from a spurious `+1 / ratio ~0` into
an honest "no wall found".  The 8 that survive are the trustworthy ones, and
the conclusion is unchanged: 4 and 6, never 2.)_  `nestcert`'s register step is built for
an inner counter that RE-COUNTS the counter once to move the mark — that is
`Theta(2^k)`, and `NestedLapLift.nested_overflow_lift` is stated against it.  A
phase growing `4^k` means the inner counter itself runs a full octave per step:
a DOUBLE nesting, not a single one.  A search for a `2^k`-shaped inner family
will not find a `4^k` phase, and from the outside that is precisely
`register step does not close`.

So the 27 are not a carrier-endpoint problem (§6d item 2) and not a width
problem (§6f).  They need one more level of nesting, and the exponent is
measured rather than guessed on the 8; the remaining 19 have no monotone wall
under this detector, which is a fact about the DETECTOR and the next thing to
sharpen — not evidence that they are a different shape.  The wall displacement (1, 2 or 4 cells) is the
per-row constant that the arm's landing has to be stated with.

**Consequence for wave-31's ranking:** item (2), the bounded inner carrier, is
the right build for the 16 inner-fill rows but will NOT reach the 27.  Item (3)
is a bigger build than the prompt assumed, and it now has a measured shape.

## 7. What is in the tree

| file | role |
|---|---|
| `tools/counters/emit_lapcert.py` | `GLUE_SPLIT_LIFT` + the split-lift route in `derive` (§3) |
| `tools/counters/intgap.py` | `_cross_period` and the `parity-cross`/`drift-cross` verdicts; `--every` (§5) |
| `tools/counters/rerender_check.py` | **new**: the byte-identical regression, as an A/B (§3b) |
| `tools/counters/cycrprobe.py` | **new**: dumps the `cycR-gap` dead ends and their closing unit runs (§2) |
| `tools/counters/twoform_dir.py` | **new**: which WAY a two-form family counts (§4) |
| `tools/counters/dblpeel_probe.py` | **new**: the double peel, measured before any template (§4) |
| `tools/counters/digitwidth.py` | **new**: word growth per octave vs the alphabet's digit width (§6f) |
| `tools/counters/wallstep.py` | **new**: the wall's displacement per overflow and the phase growth ratio (§6g) |
| `tools/counters/tailcert.py` | the two INVERTED alphabet rows + `two_form` refuses a descending family (§6b, §6c) |
| `theories/Counters/Alph_11_10_11.v`, `Alph_11_01_11.v` | **new**, generated and proved by `gen_alphabet.py` (§6b) |
| `theories/Counters/LapCertGlue.v` | `lift_app_blank_l`, funext-only (§6e) |
| `tools/counters/nestcert.py` | the offset close strips a LEFT trailing blank (§6e) |

Everything under `tools/` is untrusted; the kernel re-runs `srun` on every
chain.  `theories/` gains only the 6 boards — no library file was touched, so
`LapDecider`, `WTape`, `SkipGlue`, `NestedLapLift`, `LapCertGlue*`, `RegGlue`
are bit-for-bit unchanged and stay axiom-free / funext-only.

Nothing owned by the concurrent `claude/cascade-twocount-4-2-r82mvf` branch was
edited: `nestcert.py`'s cascade section, `cascade_probe.py`, `cascade_emit.py`,
`NestedLapCascade.v` and every `CASB_*`/`CASC_*` board are untouched.  §4 (the
bounded inner carrier) was NOT taken, as that branch's prompt requires.  And
because §1 was not built, the step language is unchanged — so that branch's
`_inner_lap_split` cannot have re-routed, and the byte-identical A/B (§3b)
confirms it over all 863 boards.

## 8. DO NOT RETRY (measured this wave)

* **`WTape.cycRW` / an `SCycR` with a left-prefix offset.**  Every SOUND
  instance derives 0 new chains on all 17 rows the shape selects (§2a).  The
  deposit-ABOVE orientation that does fire is unsound and fails at `k = 2`
  (§2b).  Do not re-open this without first changing the CROSSING PERIOD
  measurement, which is the actual obstruction.
* **Reading `intgap._cycr_gap`'s shape as a missing primitive.**  The shape is
  necessary for such a step and nowhere near sufficient; use `_cross_period`.
* **A deeper peel on the `no interior j=0 chain` bucket.**  51 of the 70 count
  DOWN (§4) — no peel of any depth can produce a `p -> p+1` lap — and on the
  other 19 the peeled `j = 0` frames return the same `lift` verdict as the
  unpeeled one (§4a).
* **Looking for the other mirror to rescue a descending two-form family.**
  Measured on all 51: the family exists in one mirror only and descends there.
* **`two_form`'s "gap-free union split by octave parity" as evidence of an
  ascending counter.**  It is a condition on the value SET.  Check the visit
  order (`twoform_dir.py`) before deriving anything from it -- `two_form` now
  refuses a descending pair outright (§6c).
* **Designing a DESCENDING carrier for a family the reader sees counting
  down.**  Measured on all 51: it is a bit-polarity inversion, and the
  inverted alphabet reads the same tape as an ordinary ascending counter
  (§6b).  Try the swapped digit words FIRST.
* **Adding a lemma to `WTape.v` or `LapGlue.v`.**  Both are inside the census
  input closure; the hash moves and `census_cache --check` fails (§6e).
* **The literal "re-renders byte-identical against `theories/Machines/`"
  test.**  717 of 863 already differ at `main` from template drift; run it as a
  patched-vs-pristine A/B instead (§3b).
* Standing: WAVE29 §7, WAVE28 §4, WAVE27 §5, WAVE26 §6, WAVE25 §6, WAVE24 §7,
  WAVE18 §5, WAVE16 §5.

## 9. What the next wave should build

Ranked by measured rows behind each piece.

1. **The BOUNDED INNER CARRIER** (prompt §4, wave-29 §5d) — now the single gate
   in front of **67 rows** (§6d), and unparked since the cascade branch merged.
   One lemma next to `NestedLapLift.inner_to_fill_lift`: the same well-founded
   induction on `JpCounter.tovf` stopped at a MEASURED endpoint instead of at
   `fill v0`, because the inner counter of the exponential arm runs a PARTIAL
   octave (`2^(K+1)+4 .. 2^(K+1)+2^K-1`).  Then `tailcert`'s two-form board.
2. **`lift` in `tailcert`'s interior split**, for real (§4a, §6d) — measured to
   open the interior gate on all 67; the work is the two-form board's per-parity
   interior glue, and it is a prerequisite for item 1 boarding anything.
3. **The overflow branch of the 4 `Alph_01_11_011` rows** (§3a) —
   `nested: no boot chain` with the interior gate now open.
4. **A parity device for the 8 period-2 rows** (§2c): a `cycR` whose unit run
   returns after TWO units, plus an interior branch stated at `j = 2k` /
   `j = 2k+1` so the block count is even.  This is a real build — a `WTape`
   lemma, a checker arm AND an emitter split — and it is worth 8 rows, so size
   it honestly before starting.  It is NOT §1's lemma.
5. ~~A descending anchor family for the 51~~ — **not needed**: they were an
   inverted digit order, and §6b/§6c settles them.  Note that wave-29 §7's
   do-not-retry on descending INNER rests is very likely the same fact one
   level in, and worth re-testing under the inverted alphabet before anyone
   builds a descending carrier for the 4 `Jp` gray-code rows.
6. **The 28 non-affine `no interior chain` rows** (HIGHER/EXP/QUAD, §6) belong
   to the QUAD and bouncer routes, not the lap chain.  John's read gives the
   shape for the QUAD ones: `j` bounces per carry, lap `(j+1)(j+2)`.

## 10. Standing lessons, paid again

* **MEASURE THE BUCKET — AND THE READER — BEFORE DESIGNING FOR IT.**  Twice in
  one wave, and both times the reader was a predicate that selected a necessary
  condition: `_cycr_gap`'s dead-end shape (§2) and `two_form`'s gap-free union
  (§4).  Four of wave-29's seven sub-classes were reader caps; two of wave-30's
  three builds were reader inferences.
* **READ THE LANDING OFF THE MACHINE.**  The `2j+6` lap of §2c and the
  descending walk of §4 are both one dump away, and both were invisible in the
  label.
* **A SOUNDNESS ARGUMENT IS A MEASUREMENT.**  §2b's `k = 2` check took one
  script and killed a lemma that would otherwise have been written, proved
  against the wrong statement, and found not to fire.  Test the induction STEP
  against the simulator before writing the induction.
* **Ask with a TAPE, and cross-check the hand read against the shape column.**
  John's bouncing-carry read (§6) and `residue_map`'s QUAD label are
  independent, and together they explain why a third of the `no interior chain`
  bucket was never a chain problem.
