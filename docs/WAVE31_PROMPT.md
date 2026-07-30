# Wave-31 prompt: the EXPONENTIAL OVERFLOW ARM — one gate, 67 rows

Continue the (4,2) residue reduction in `carrino/Coq-BBB4`, on branch
`claude/inner-carrier-4-2-<yourid>`, cut from `main` (wave-30 is merged).

## STATE

`make closeout-status`, or `python3 tools/closeout/audit.py`:

    4,916 of the frozen 5,156 settled (95.3%)
    162 core undecided + 78 0RB shadows (the shadows resolve with their cores)

**Read this first, because it is the whole shape of the wave: the FLAT route is
exhausted.**  Wave-30 swept `emit_lapcert --list` over 249 of the 255 then-open
rows (core + shadows).  It found **5**, and all 5 are boarded — plus 2 shadows
that the boards promoted, which is the wave's 7.  There is no low-hanging fruit
left in `emit_lapcert`: every remaining board comes from a route piece that does
not exist yet, and wave-30 measured exactly which one stands in front of the
most rows.  (Re-run the sweep over the current 162 to confirm before you trust
this; it is the cheapest sanity check in the document.)

## THE ONE GATE

Wave-30 fixed the reader (`docs/WAVE30_FINDINGS.md` §6b–§6d): the two-form
counter class was being read under an alphabet with its two digit words the
wrong way round, so 51 of 70 rows looked like DESCENDING counters.  With the
inverted alphabets registered and `two_form` refusing a descending family, **67
of the 70 read ascending**, and with `lift` allowed on the interior split
**every one of them clears the interior gate**.

They then all stop in the same place.  Measured over the 70 **with (1)'s `lift`
patch applied** — this is the table you get AFTER item (1), not before:

|   n | furthest gate, with `lift` on the interior split |
|----:|---|
|  27 | `register step does not close` |
|  22 | `no boot chain` |
|   8 | `no inner family at pow2 j` |
|   8 | inner fill lands off the measured endpoint |
|   3 | no gap-free two-form family |
|   1 | `no exit chain` |
|   1 | `no inner interior chain` |
|   0 | `no interior j=0 chain` — **was 70** |

**AS COMMITTED, the interior gate is still shut.**  Item (1) was measured with a
patched copy of `tailcert` and never landed, so `tailcert.py --list` over the 162
open core rows on today's `main` reports:

|   n | furthest gate, as committed |
|----:|---|
|  38 | `no interior j=S j chain` at octave parity 0 |
|  30 | `no inner family at pow2 j` |
|  26 | `no gap-free two-form family` |
|  26 | `no interior j=0 chain` at octave parity 0 |
|  **12** | **OK — fully derived, see §(0)** |
|  11 | `no boot chain` |
|  10 | `no interior j=0 chain` at octave parity 1 |
|   6 | inner fill lands off the measured endpoint |
|   3 | one each: no visit witness for StA, no inner interior chain, register step |

So **74 rows (38 + 26 + 10) are still behind the exactness assertion** that item
(1) removes.  That is the single largest gate in the residue, it is two lines of
plumbing plus a per-parity glue template, and it is measured to open all of them.
Do not read the first table as work already done.

**YOUR TASK IS THE EXPONENTIAL OVERFLOW ARM — after (0), which is free.**  Five
builds, in this order.  **(0) is 12 rows that already derive and validate and
have nowhere to be written; do it first and do not be talked out of it.**
(1) is a prerequisite for anything else boarding and is pure plumbing.  (2) is
the lemma wave-29 §5d specified and wave-30 could not take (it was parked while
`claude/cascade-twocount-4-2-r82mvf` held `NestedLapLift`; that branch has
merged, so it is unparked).  (3) and (4) are the two largest sub-buckets and
each needs a measurement before a design.

## READ FIRST, in this order

* `docs/WAVE30_FINDINGS.md` — **§6d is your task list**; §6b/§6c are the reader
  fix you are building on; §6e is where a lemma may and may not live; §8 is
  do-not-retry.
* `docs/WAVE29_REGISTER_FINDINGS.md` §5d — the partial-octave inner counter,
  measured, with the numbers you are going to state the carrier against.
* `theories/Counters/NestedLapLift.v` lines 72–95 — `inner_to_fill_lift`, the
  lemma you are writing the bounded twin of.  Read the induction twice.
* `tools/counters/tailcert.py` — `two_form` (the fixed reader) and `_derive`
  (the exactness assertions you are relaxing in (1)).
* `docs/WAVE28_FINDINGS.md` §2 (the PEEL) and `docs/WAVE16_FINDINGS.md` §§5–6
  (do-not-retry).

## (0) THE TWO-FORM BOARD RENDERER — 12 rows ALREADY DERIVED.  DO THIS FIRST.

`tools/counters/tailcert.py` reads the family, derives every branch, and
**differentially validates each one against the raw simulator** — and then stops,
because it has no renderer.  Its docstring advertises `--emit`; `main()` never
implemented it.  `PREFIX = 'REG'`, `OUTDIR`, and the imports of `coqc` and
`mirrorize` are all there, unused.  The route's last mile was never built.

Measured with wave-30's fixed reader, `tailcert.py --list` over the 162 open core
rows:

    12 / 162 fully derived

Twelve rows whose certificate exists, validates, and cannot be written down.
The list is `tools/counters/tailcert_derived12.txt`, and it splits cleanly:

| n | alphabet | overflow arms | validation |
|--:|---|---|---|
| **6** | `Alph_00_01_1` | **FLAT** — 0 nested overflows | 192 anchors |
| 6 | `Alph_10_11_11` | nested — 4 nested overflows, 56 inner laps | 192 anchors |

**Take the 6 FLAT ones first.**  They have no nesting anywhere: a per-parity
split interior and a per-parity flat overflow, every branch replayed against the
raw simulator.  Two of them (`1RB0RD_0RC0LD_1LD1RC_0LA1LB`,
`1RB1LA_0RC1RD_1LD0LB_0LA0RB`) are rows wave-30 §3a filed as blocked on the
overflow branch through the FLAT route — the two-form framing reaches what
`emit_lapcert` could not.

**This is ahead of everything else in this document.**  It needs no new
mathematics, no new lemma, and no new measurement: the certificates are in hand.

### What to build

`tools/counters/regcert.py` already renders a piecewise-`Cc` board that
alternates its frame by octave parity (`render` at l. 1100, `process` at l. 1209,
plus the `_arm_reps` / `_fill` template helpers), and `tailcert` already imports
`regcert`'s `RegError`, `F`, `octave`, `_chain`, `_phase`, `_denc` and even uses
the same `REG_*` prefix.  Start from that renderer.

Two structural differences to handle — check them against `_derive` before
writing a template:

* the interior branch is a SPLIT (`Z0 -> Z1` at `j = 0`, `P0 -> P1` at
  `j = S j'`) **per octave parity** — four chains, not two.  `emit_lapcert`'s
  `GLUE_SPLIT` is the shape for each half; what is new is the per-parity pair;
* the overflow arm CROSSES parities: `_derive` states it as

      B0 = (st[b],  (uS, uS, 1, 0, soS ++ tl[b]),  S0, far[b])
      B1 = (st[nb], ((), uD, 1, 2, soD ++ tl[nb]), S0, far[nb])

  — destination state `st[nb]`, count `1*j+2`, source PEELED.  That framing is
  why these rows derive here and NOT through `emit_lapcert.derive`, which was
  tried on the exemplar's key and fails at `no overflow chain` on both parities.
  Do not try to shortcut through the flat route; the framing is the point.

`D` carries `spec`, `orig`, `mirror`, `enc`, `st`, `tl`, `fr`, `ks`, `p0`,
`ints` (`Z0 Z1 P0 P1 chz chp cz cp` per parity), `ovf` (per parity: `kind B0 B1`
plus `ch c` when `kind == 'flat'`, or the boot/inner/exit triple when
`kind == 'nested'`), `vis`, `boot`, `val`.

### Acceptance

Every board compiles and `Print Assumptions nqh_<ID>` is funext-only.  Nothing
under `theories/` needs to change for the 12 flat rows — if a board wants a new
library lemma, check the census closure first (see NON-NEGOTIABLE).  Run the
A/B re-render check afterwards: adding a renderer cannot re-route
`emit_lapcert`, but `tailcert` shares `regcert`'s helpers, so prove it.

**Expect 6 boards from the flat arms and 6 more once the nested arm renders, then
re-run `tailcert --list` over the residue** — the
reader fix moved 67 rows and only 12 were checked for end-to-end derivation
against the CURRENT open list.

## (1) `lift` IN `tailcert`'s INTERIOR SPLIT — plumbing, prerequisite, 0 new Coq

`tailcert._derive` requires the reached configuration to equal the target
SYNTACTICALLY:

    if chz is None or rz[0] != Z1 or rz[2] == 0:
        raise RegError('no interior j=0 chain at octave parity %d' % b)

Measured on the 19 rows that already read ascending before the reader fix: both
split halves derive at both parities — **29 frames up to `lift`, 9 exactly, 0
blocked**.  So this assertion, not the machines, is what filed 70 rows as
`no interior j=0 chain`.

`emit_lapcert.GLUE_SPLIT_LIFT` (wave-30) is the template to copy: `gz_`/`gp_`
state their second conjunct as a `lift` equality, `lapi_` returns
`exists n c'`, and `LapCertGlueLift`'s closers consume it unchanged.  The work
here is the two-form board's PER-PARITY interior glue, which `GLUE_SPLIT_LIFT`
does not have (it is one arm, not two).

Reference implementation of the measurement, so you can reproduce the numbers
before touching a template: fall back to `_chain(..., lift=True)` and weaken
both assertions to `LC._match(rz[0], Z1, False, True, True)`.

**Expect 0 boards from (1) alone** — it opens the gate, it does not close a
branch.  Do it first anyway; nothing below can board without it.

## (2) THE BOUNDED INNER CARRIER — the lemma, 16 rows directly

Wave-29 §5d, measured: on the exponential arm the inner counter runs a PARTIAL
octave and stops HALFWAY, not at the all-ones fill.

    K = 5 (p = 63 -> 64):  inner rests run 132 .. 191  =  2^7+4 .. 2^7+2^6-1
    K = 7 (p = 255 -> 256): inner rests run 516 .. 767  =  2^9+4 .. 2^9+2^8-1

`NestedLapLift.inner_to_fill_lift` runs to `fill v`, `nestcert.families` wants a
full `2^(K-1)..2^K-1`, and `derive_offset` wants `2^(K+1)+c..2^(K+2)-1`.  None
covers "from `v0` to `v0 + 2^k - 1`".

### The lemma, and why it is SIMPLER than its twin

`inner_to_fill_lift` needs well-founded induction on `tovf` because it must
reach the fill.  A bounded carrier does not: it takes `k` increments and stops,
so it is a PLAIN induction on `k`.

    Lemma inner_to_add_lift : forall k v, k <= tovf v ->
      exists n, stepn tm n (lift (Cin v)) = Some (lift (Cin (Pos.iter Pos.succ v k))).

`k <= tovf v` is the whole side condition — it says the run stops at or before
the fill, which is exactly what makes every intermediate anchor INTERIOR, which
is what `Hin` needs.  `tovf_succ` (already in `JpCounter`) carries the premise
through the step.  Do NOT state the side condition as
`forall m < k, exists i q0, cview (v + m) = (i, Some q0)`: `k` is `2^K - 4`,
exponential in the board's symbolic index, so a per-`m` premise cannot be
discharged by `vm_compute` and the board cannot state it.

`NestedLapLift.v` is OUTSIDE the census input closure (checked), so it is a
legal home.  It is funext-only — **keep it that way**.

Then the board template: `nestcert`'s inner-family section states the endpoint
against `fill v0`; it needs to state it against the measured `k`.  Read the
endpoint off the machine, do not assume `2^K - 4`.

**Expect ~16 boards** (the 8 `no inner family at pow2 j` + 8 whose fill lands
off the endpoint), and re-check whether the same carrier moves any of the 27 in
(3).

## (3) `register step does not close` — 27 rows.  MEASURED: it is a DOUBLE nesting

The largest sub-bucket.  Wave-30 §6g measured it after John's read of
`1RB1RD_1LC1RA_0RB0LC_1LA0RD` ("a wall on the right, msb on the right, when the
msb overflows the wall moves over 4"; "the msb butts up against the wall but
doesn't include it").

    wall start column   0    4    8    12    16    20    24
    first seen at t     6   42  168   654  2580 10266 40992

The wall moves a FIXED number of cells (2 or 4, per row) per overflow, and the
phase between displacements grows by a factor of **4 or 6** — over the 8 of 27
rows where `tools/counters/wallstep.py` detects a MONOTONE wall: ratio ~4 on 5,
~6 on 3, and **~2 on none**.  The other 19 report "no wall found": that is a
statement about the detector, not about those machines.

`nestcert`'s register step is built for an inner counter that RE-COUNTS the
counter once, which is `Theta(2^k)`, and `nested_overflow_lift` is stated against
that.  A `Theta(4^k)` phase means the inner counter itself runs a full octave per
step — a DOUBLE nesting.  A search for a `2^k` inner family cannot find a `4^k`
phase, and from outside that is exactly `register step does not close`.

So (2)'s bounded carrier will NOT reach these 27, and this item is bigger than a
carrier fix.  Two things to do before designing:

* sharpen `wallstep.py` for the 19 rows with no monotone wall.  Two policies
  (innermost / outermost run of `>= 2` ones, each side) and a monotonicity
  requirement get 8; what is missing is a way to tell the wall from the
  counter's own incidental `11` pairs when both move.  Candidate: a run whose
  LENGTH is constant across sightings, since a wall does not grow while the
  word does.  Get the exponent on all 27 before designing the nesting;
* then decide whether the shape is a double nesting or one nesting over a
  SQUARED index — the measured constants (wall displacement per row, phase
  ratio) are what the arm's landing must be stated with.

Also still unmeasured:

* dump the phase with `tools/counters/spacetime.py --rests --mark --ruler` and
  FIXED `--lo/--hi` (without fixed columns the frame shifts row to row and the
  dump is unreadable);
* fit the arm's laps PER OCTAVE CLASS, not with one affine law — wave-29 §7,
  a period-P frame makes a single fit report "exponential" on branches that are
  `4k+7`/`4k+9` per parity;
* the DIGIT-WIDTH hypothesis is closed: `tools/counters/digitwidth.py`
  measures the word growing exactly 2 cells per octave against a 2-cell digit on
  **all 27**, so no row is being read as a subsequence and none needs a wider
  alphabet (`docs/WAVE30_FINDINGS.md` §6f).  Do not re-open it;
* check whether the inner family is ASCENDING under the INVERTED alphabets
  (`tailcert.INVERTED`).  Wave-30's whole result is that this was wrong at the
  outer level for 51 rows; the inner level has not been re-checked and
  wave-29 §7's do-not-retry on descending INNER rests is very possibly the
  same fact one level in.

That last bullet is the cheapest experiment in this document and it may retire
the sub-bucket outright.  Do it before writing a line of Coq.

## (4) `no boot chain` — 22 rows.  RE-RUN BEFORE BUILDING

`main` merged a SOLO CASCADE route for exactly the `no boot chain` label
(`nestcert.py`'s cascade section, `cascade_emit.py`,
`docs/WAVE29_CASCADE_FINDINGS.md`).  These 22 rows acquired that label only
AFTER wave-30's reader fix, so the cascade route has never been run against
them.  Run it first.  If it boards some, that is free.

## NON-NEGOTIABLE

* Never edit `theories/Census/`.  `python3 tools/census_cache.py --check` must
  stay **MATCH**.
* **Check the census closure before adding a lemma to a library file.**
  `python3 -c "import sys;sys.path.insert(0,'tools');import census_cache as C;print('theories/Counters/X.v' in set(C.closure_v_files()))"`.
  INSIDE (do not edit): `WTape.v`, `LapGlue.v`.  OUTSIDE (fine):
  `LapCertGlue.v`, `LapCertGlueLift.v`, `NestedLapLift.v`, `NestedLap.v`,
  `LapDecider.v`, `RegGlue.v`, `JpCounter.v`.  Wave-30 lost a build cycle
  putting a one-line lemma next to its twin in `WTape.v`; the hash moved and
  `--check` failed.
* A board counts only when its file compiles AND
  `Print Assumptions nqh_<ID>` shows `functional_extensionality_dep` only.
* `SkipGlue`, `NestedLapLift`, `LapDecider`, `LapCertGlue`, `LapCertGlueLift`,
  `LapGlue*`, `RegGlue`, `WTape` are axiom-free or funext-only — keep them so.
  (2) touches one of them; prove, do not assume.
* Everything under `tools/` is UNTRUSTED; the kernel re-checks every board.
* **Do not add a row to `alphabets_gen.ENCROWS`/`ENCS`** without checking that
  `reg113.json`, `quad35.json` and `jexc80.json` still reproduce.  Register a
  private `ENCDATA` row instead — see `tailcert.INVERTED` for the pattern, and
  assert that `ENCS` is unchanged after import.
* **The byte-identical regression is an A/B, not a comparison against the
  tree.**  `tools/counters/rerender_check.py` run twice — once from a pristine
  worktree at your merge base, once from the patched tree — then
  `diff -rq` the two output dirs.  717 of 863 boards already differ from what
  today's templates render (20 waves of template drift), so the literal test
  cannot pass and will drown a real re-route in noise.  If a diff appears,
  confirm hunk by hunk that it is the change you intended and recompile every
  board that moved.

## ENV

`apt-get install -y coq` (8.18.0), then
`coq_makefile -f _CoqProject -o Makefile.coq`.

**Build the Counters/Checkers closure ONCE, up front:**

    make -f Makefile.coq $(ls theories/Counters/*.v theories/Checkers/*.v \
      | sed 's/\.v$/.vo/' | tr '\n' ' ')

Wave-30 lost real time to this: `emit_lapcert --emit` runs `coqc`, and a board
whose alphabet `.vo` is missing fails with "Cannot find a physical path bound
to logical path", which `process` reports as an ordinary derivation failure and
then deletes the file.  It looks exactly like "the row does not board".  Build
first.  **DO NOT run `make all`.**

After any change to a library file, rebuild BOTH `theories/Counters` and
`theories/Checkers` — a stale `LapDecider.vo` gives "makes inconsistent
assumptions over library BBB4.Counters.WTape", which also looks like a proof
failure and is not.

## DO NOT RETRY (measured)

* **`WTape.cycRW` / an `SCycR` with a left-prefix offset.**  Wave-30 §2: every
  SOUND instance derives 0 new chains on all 17 rows the shape selects, and the
  deposit-ABOVE orientation that does fire is unsound — `k=0` and `k=1` hold,
  `k=2` fails, because the window is buried under its own deposit.
* **Reading `intgap._cycr_gap`'s dead-end shape as a missing primitive.**  Use
  `_cross_period`: period 2 on 8 rows (needs an even block count — a parity
  device), never-returns on 8 (the lap is not affine).
* **A deeper peel on the two-form interior branch.**  The peeled `j = 0` frames
  return the same `lift` verdict as the unpeeled one, digit by digit.
* **Designing a DESCENDING carrier for a family the reader sees counting
  down.**  Measured on all 51: bit-polarity inversion.  Try the swapped digit
  words first (`tailcert.INVERTED`, `gen_alphabet.py --abc dig0,dig1,term`).
* **`two_form`'s "gap-free union" as evidence of an ascending counter.**  It is
  a condition on the value SET.  `two_form` now refuses a descending pair; if
  you write a new reader, carry that check.
* **Widening `derive_chain`'s depth on `no interior chain`.**  The reachable
  set is CLOSED at 7–89 states.
* **Any reading of the wave-29 register bucket with a WALL in it**; **decoding
  the whole tape as one word**; **one affine fit across a period-P frame**.
* Standing: WAVE30 §8, WAVE29 §7, WAVE28 §4, WAVE27 §5, WAVE26 §6, WAVE25 §6,
  WAVE24 §7, WAVE18 §5, WAVE16 §5.

## STANDING MOVES

* **MEASURE THE BUCKET — AND THE READER — BEFORE DESIGNING FOR IT.**  Wave-30
  killed two of its own three builds this way, and both diagnostics had
  selected a NECESSARY condition and been read as a sufficient one.  Ask of any
  gate label: is this a fact about the machine, or about the predicate?
* **PEEL BEFORE ANYTHING ELSE.**  Eight waves.
* **READ THE LANDING OFF THE MACHINE** instead of assuming its padding.
* **A SOUNDNESS ARGUMENT IS A MEASUREMENT.**  Before writing an induction,
  test its STEP against the raw simulator at `k = 0, 1, 2`.  Wave-30 killed a
  lemma in one script that way.
* **After ANY change to `derive`, to a reader, or to the step language, re-run
  `emit_lapcert --list`, `restscan.py --emit`, `regcert.py` and `tailcert.py`
  over the open buckets.**  Each is a DIFFERENT gate and it costs nothing but
  the run.  Wave-30 changed a reader and re-ran only one of the four.
* **WHEN STUCK ON A CLASS, ask John with an ABSOLUTE-COORDINATE TAPE DUMP**
  (`spacetime.py --rests --mark --lo/--hi` FIXED).  Hand-inspection is
  **38-for-38** across waves 8–30.  In wave-30 two sentences — "msb on the
  left" and "like a grey counter where it goes up then down" — named a reader
  defect that had cost 51 rows and three waves of wrong designs.  Ask EARLY,
  ask with a TAPE, ask about a CLASS not a machine.

## PER BATCH

    python3 tools/closeout/inventory.py && python3 tools/closeout/gen_stages.py \
      && python3 tools/closeout/audit.py && python3 tools/census_cache.py --check
    git push -u origin <branch>          # retry on network error

Merge conflicts with `main` are routine and always in GENERATED tables
(`_CoqProject`, `theories/Closeout/*`, `tools/closeout/*`): take main's side on
every one, then re-run the four commands above.

Write `docs/WAVE31_FINDINGS.md`.

## DEFERRED TO STABLE HARDWARE

Census fold-in, `CloseoutFinal.v`, the champion
`1RB1LD_1RC1RB_1LC1LA_0RC0RD`, and `0RB1LC_1LC0LC_0RD1LA_1RD1RB`.
