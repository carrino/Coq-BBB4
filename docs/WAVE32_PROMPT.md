# Wave-32 prompt: the BOUNDED INNER CARRIER, and the 40-row interior wall

Continue the (4,2) residue reduction in `carrino/Coq-BBB4`, on branch
`claude/inner-carrier-4-2-<yourid>`, cut from `main` (wave-31 is merged).

## STATE — measured 2026-07-30 at `f4467cc`, with the code that measured it IN that commit

`make closeout-status`, or `python3 tools/closeout/audit.py`:

    4,930 of the frozen 5,156 settled (95.6%)
    150 core undecided + 76 0RB shadows (the shadows resolve with their cores)

**Read §11 of `docs/WAVE31_FINDINGS.md` before you trust any other number in
this document, including the ones below.**  Wave-30 §6d published a bucket table
measured against a working tree whose patch never landed, and wave-31 spent a
build re-deriving it.  Every table here was produced by code that is committed;
the row lists are in the tree so you do not have to re-derive them at all:

    tools/counters/buckets31/*.txt          one file per gate label
    tools/counters/tailcert_innerfam33.txt  item (1)'s 33 rows
    tools/counters/tailcert_filloff6.txt    item (1)'s other 6

Re-run `tailcert --list tools/closeout/core_rows.txt` before you trust them
anyway — it is the cheapest sanity check in this document and the residue moves
under you.

## THE GATE TABLE

`tailcert --list` over the 150 open core rows, with wave-31's `lift` fallback in:

    0 / 150 fully derived

|   n | furthest gate |
|----:|---|
|  40 | `no interior j=S j chain` |
|  33 | `no inner family at pow2 j` |
|  26 | `no gap-free two-form family` |
|  20 | `no boot chain` |
|  17 | `register step does not close` |
|   6 | inner fill lands off the measured endpoint |
|   4 | `no interior j=0 chain` |
|   2 | `no inner interior chain` |
|   1 | `no visit witness for state A` |
|   1 | `no exit chain` |

**Two items, in this order.  (1) is the only route piece in the wave-31 prompt
whose stated size survived contact with the data, and it is the only one that
needs new Coq.  (2) is the largest bucket in the residue and has never had an
item written for it.**

## READ FIRST, in this order

* `docs/WAVE31_FINDINGS.md` — **§10 is the table, §11 is why you must not trust a
  table without a commit, §8 is the interior split as it now stands**; §9 is
  do-not-retry; §3 is what the wave-31 boards do and do not demonstrate.
* `docs/WAVE29_REGISTER_FINDINGS.md` §5d — the partial-octave inner counter,
  measured, with the numbers you are going to state the carrier against.
* `theories/Counters/NestedLapLift.v` lines 72–95 — `inner_to_fill_lift`, the
  lemma you are writing the bounded twin of.  Read the induction twice.
* `tools/counters/tailcert.py` — `_int_chain` and `_far_peel` (wave-31's item
  (1), the shape any new interior framing has to fit), `_nested_ovf` (where (1)
  below lands), and `render`.
* `tools/counters/nestcert.py` — `families` / `endpoints`, whose `oct` shift is
  the only index flexibility the inner family currently has.
* `docs/WAVE28_FINDINGS.md` §2 (the PEEL) and `docs/WAVE16_FINDINGS.md` §§5–6
  (do-not-retry).

## (1) THE BOUNDED INNER CARRIER — the lemma, 39 rows

`tools/counters/tailcert_innerfam33.txt` (33 rows, `no inner family at pow2 j`)
and `tools/counters/tailcert_filloff6.txt` (6 rows, the fill lands off the
endpoint).  Wave-29 §5d, measured: on the exponential arm the inner counter runs
a PARTIAL octave and stops HALFWAY, not at the all-ones fill.

    K = 5 (p = 63 -> 64):  inner rests run 132 .. 191  =  2^7+4 .. 2^7+2^6-1
    K = 7 (p = 255 -> 256): inner rests run 516 .. 767  =  2^9+4 .. 2^9+2^8-1

`NestedLapLift.inner_to_fill_lift` runs to `fill v`, `nestcert.families` wants a
full `2^(K-1)..2^K-1`, and `derive_offset` wants `2^(K+1)+c..2^(K+2)-1`.  None
covers "from `v0` to `v0 + 2^k - 1`".

The 6 fill-off-endpoint rows are the same defect seen from one gate later, and
their diagnostic is already concrete — `tailcert.validate` prints the reached and
wanted configuration:

    p=15 inner fill -> (3, (1,0,1,0,1,1,1,0,0,1), 0, ())
                  want (3, (1,0,1,0,1,0,1,0,0,1), 0, ())
    p=31 inner fill -> (3, (1,0,1,0,1,0,1,1,1,0,0,1), 0, ())
                  want (3, (1,0,1,0,1,0,1,0,1,0,0,1), 0, ())

Two adjacent digits differ and the difference moves one block per octave.  **Read
the endpoint off that dump before you state the lemma** — it says the run stops
short by a fixed amount, which is what a bounded carrier is for, and it says by
how much.

### The lemma, and why it is SIMPLER than its twin

`inner_to_fill_lift` needs well-founded induction on `tovf` because it must reach
the fill.  A bounded carrier does not: it takes `k` increments and stops, so it
is a PLAIN induction on `k`.

    Lemma inner_to_add_lift : forall k v, k <= tovf v ->
      exists n, stepn tm n (lift (Cin v)) = Some (lift (Cin (Pos.iter Pos.succ v k))).

`k <= tovf v` is the whole side condition — it says the run stops at or before
the fill, which is exactly what makes every intermediate anchor INTERIOR, which
is what `Hin` needs.  `tovf_succ` (already in `JpCounter`) carries the premise
through the step.  Do NOT state the side condition as
`forall m < k, exists i q0, cview (v + m) = (i, Some q0)`: `k` is `2^K - 4`,
exponential in the board's symbolic index, so a per-`m` premise cannot be
discharged by `vm_compute` and the board cannot state it.

`NestedLapLift.v` is OUTSIDE the census input closure (re-check it yourself —
`census_cache.closure_v_files()`), so it is a legal home.  It is funext-only —
**keep it that way**.

### Then the emitter, and this is where wave-31 says the work actually is

`tailcert._nested_ovf` is the caller, not `nestcert`: the 39 rows are on the
two-form route.  It currently asks `NC.families(mid, ENCDATA, ENCS, K=K)` for a
family whose values run exactly `2^(K-1+o)..2^(K+o)-1` and gets nothing on 33
rows.  A bounded family needs `families` to accept a run
`v0 .. v0 + 2^k - 1` — which is a change to a function `regcert` and `nestcert`
both call, so **run the A/B re-render check on it** (see NON-NEGOTIABLE), unlike
wave-31's renderer which touched nothing shared.

`endpoints`'s `oct` shift (`a = 1`, `b = oct`) is the only index flexibility the
sside carries today.  A bounded endpoint needs the `b` of a DIFFERENT count;
check whether it is still an sside before designing the glue, because
wave-29 measured the offset form `pow2 j + 1` at 0/12 (the index-shift trap).

**Expect ~39 rows to move and fewer to board** — 33 of them are gated at the
inner family and will hit the arm's next gate the moment it is found, exactly as
wave-31's item (1) moved 30 rows and boarded none.  Sweep after, not before.

## (2) `no interior j=S j chain` — 40 rows.  NO ITEM HAS EVER BEEN WRITTEN FOR THIS

`tools/counters/buckets31/no_interior_jS_j_chain_at_octave_parity_0.txt`.  The
largest bucket in the residue, and wave-31 is what exposed it: with the `lift`
fallback in, 44 rows still fail the interior split, and **38 of them have the
`j = S j'` half dead at BOTH parities while the `j = 0` half derives exactly**
(`WAVE31_FINDINGS.md` §8).

That asymmetry is the whole clue and it has not been chased.  `_derive` states
the peeled half as

    P0 = (st[b], (uS, uS, 1, 0, sS), 0, F(fr[b]))
    P1 = (st[b], (uD, uD, 1, 0, sD), 0, F(fr[b]))

— ONE unit copy in the prefix, on the LEFT, at both endpoints.  Three things to
measure before designing anything, cheapest first:

* **is the step count affine in `j` at all?**  Fit the interior lap PER OCTAVE
  CLASS, not with one affine law — wave-29 §7: a period-P frame makes a single
  fit report "exponential" on branches that are `4k+7`/`4k+9` per parity.  If it
  is not affine, no chain of any depth expresses it and the bucket is not a
  framing problem;
* **a deeper peel on the `j = S j'` half specifically.**  Read the standing
  do-not-retry carefully before you dismiss this: WAVE31 §8 / WAVE30 §8's entry
  is *"a deeper peel on the two-form interior branch — the peeled `j = 0` frames
  return the same `lift` verdict as the unpeeled one"*.  That is about the
  **`j = 0`** half.  The `j = S j'` half at depth 2 is **not** covered and has
  not been tried.  Try it, and if it fails, write the do-not-retry entry that
  actually covers it;
* **which side needs the concrete cell.**  Both `P0`/`P1` peel on the LEFT.  The
  interior chain is derived with `el=False, er=True` — the far side is walled —
  so a machine whose head steps RIGHT out of the anchor has no concrete cell
  there.  `emit_lapcert`'s `GLUE_SPLIT` has the same left-only assumption, so
  this is untested across two emitters, not one.

**Ask John with an ABSOLUTE-COORDINATE TAPE DUMP before designing.**  38 rows
sharing one asymmetry is exactly the shape hand-inspection has been 38-for-38 on.
Dump a few with `spacetime.py --rests --mark --ruler` and FIXED `--lo/--hi`, and
ask about the CLASS: *why does the increment out of `j = 0` chain and the
increment out of `j = 1` not?*

## ALSO OPEN, not items

* **26 `no gap-free two-form family`.**  Reader-level, not a route.  Wave-30's
  whole result was that the reader was wrong for 51 rows; this is the bucket that
  says it is still wrong for 26.  Check the INVERTED alphabets and the two-cell
  terminator partners before assuming these need new mathematics.
* **20 `no boot chain` / 17 `register step does not close`.**  Both re-appeared
  when wave-31 opened the interior gate.  The solo cascade is measured dead
  against the first (see DO NOT RETRY); the second is wave-30 §6g's double
  nesting, whose phase ratio (~4 on 5 rows, ~6 on 3, ~2 on none) is measured but
  whose exponent is still unknown on 19 of the 27 `wallstep.py` cannot see a
  monotone wall in.  Neither is the best use of a wave while (1) and (2) are open.

## NON-NEGOTIABLE

* Never edit `theories/Census/`.  `python3 tools/census_cache.py --check` must
  stay **MATCH**.
* **Check the census closure before adding a lemma to a library file.**
  `python3 -c "import sys;sys.path.insert(0,'tools');import census_cache as C;print('theories/Counters/X.v' in set(C.closure_v_files()))"`.
  INSIDE (do not edit): `WTape.v`, `LapGlue.v`.  OUTSIDE (fine):
  `LapCertGlue.v`, `LapCertGlueLift.v`, `NestedLapLift.v`, `NestedLap.v`,
  `LapDecider.v`, `RegGlue.v`, `JpCounter.v`.
* A board counts only when its file compiles AND
  `Print Assumptions nqh_<ID>` shows `functional_extensionality_dep` only.
* `SkipGlue`, `NestedLapLift`, `LapDecider`, `LapCertGlue`, `LapCertGlueLift`,
  `LapGlue*`, `RegGlue`, `WTape` are axiom-free or funext-only — keep them so.
  (1) touches one of them; prove, do not assume.
* Everything under `tools/` is UNTRUSTED; the kernel re-checks every board.
* **Do not add a row to `alphabets_gen.ENCROWS`/`ENCS`** without checking that
  `reg113.json`, `quad35.json` and `jexc80.json` still reproduce.  Register a
  private `ENCDATA` row instead — see `tailcert.INVERTED` for the pattern.
* **The byte-identical regression is an A/B, not a comparison against the tree.**
  `tools/counters/rerender_check.py` run twice — once from a pristine worktree at
  your merge base, once from the patched tree — then `diff -rq` the two output
  dirs.  717 of 870 boards already differ from what today's templates render, so
  the literal test cannot pass and will drown a real re-route in noise.  Wave-31
  ran this and it came back clean because it touched nothing shared; **(1)
  changes `nestcert.families`, which `regcert` also calls, so expect this one to
  matter.**
* **Publish no bucket size without the commit it was measured at, and make sure
  the code that measured it is IN that commit.**  Wave-30 §6d cost wave-31 a
  build; see `WAVE31_FINDINGS.md` §11.

## ENV

`apt-get install -y coq` (8.18.0), then
`coq_makefile -f _CoqProject -o Makefile.coq`.

**Build the Counters/Checkers closure ONCE, up front:**

    make -f Makefile.coq $(ls theories/Counters/*.v theories/Checkers/*.v \
      | sed 's/\.v$/.vo/' | tr '\n' ' ')

A board whose alphabet `.vo` is missing fails with "Cannot find a physical path
bound to logical path", which `process` reports as an ordinary derivation failure
and then deletes the file.  It looks exactly like "the row does not board".
Build first.  **DO NOT run `make all`.**

After any change to a library file, rebuild BOTH `theories/Counters` and
`theories/Checkers` — a stale `LapDecider.vo` gives "makes inconsistent
assumptions over library BBB4.Counters.WTape", which also looks like a proof
failure and is not.

`cascade_probe` needs a couple of GB per row.  Run the probes one row at a time
under `ulimit -v` rather than trusting a `--solos`-style batch to survive; four
concurrent sweeps OOM-killed wave-31's at row 4 of 11 with exit 137.

## DO NOT RETRY (measured)

* **The SOLO CASCADE against `no boot chain`.**  Wave-31 §9: 0 of 11, with FIVE
  distinct causes (5 `no overflow phase at K=7`, 2 `the main count does not
  follow the descent`, 2 `no interior chain`, 1 `solo level 4: S is not in the
  phase`, 1 `no count below octave 6`).  That is the route not fitting the
  bucket, not one missing piece.
* **The `lift` fallback in the interior split as a way to BOARD rows.**  Wave-31
  §8b: it moves 30 rows and boards 0.  It is built and committed; do not rebuild
  it, and do not expect boards from opening a gate.
* **`WTape.cycRW` / an `SCycR` with a left-prefix offset.**  Wave-30 §2: every
  SOUND instance derives 0 new chains on all 17 rows the shape selects, and the
  deposit-ABOVE orientation that does fire is unsound at `k=2`.
* **Reading `intgap._cycr_gap`'s dead-end shape as a missing primitive.**  Use
  `_cross_period`: period 2 on 8 rows, never-returns on 8.
* **A deeper peel on the two-form interior branch at `j = 0`.**  The peeled
  `j = 0` frames return the same `lift` verdict as the unpeeled one, digit by
  digit.  (The `j = S j'` half is NOT covered — see item (2).)
* **Designing a DESCENDING carrier for a family the reader sees counting down.**
  Measured on all 51: bit-polarity inversion.  Try the swapped digit words first.
* **`two_form`'s "gap-free union" as evidence of an ascending counter.**  It is a
  condition on the value SET; `two_form` now refuses a descending pair.
* **Widening `derive_chain`'s depth on `no interior chain`.**  The reachable set
  is CLOSED at 7–89 states.
* **The DIGIT-WIDTH hypothesis on the register bucket.**  `digitwidth.py`
  measures the word growing exactly 2 cells per octave against a 2-cell digit on
  all 27 (WAVE30 §6f).
* Standing: WAVE31 §9, WAVE30 §8, WAVE29 §7, WAVE28 §4, WAVE27 §5, WAVE26 §6,
  WAVE25 §6, WAVE24 §7, WAVE18 §5, WAVE16 §5.

## STANDING MOVES

* **MEASURE THE BUCKET — AND THE READER — BEFORE DESIGNING FOR IT.**  Ask of any
  gate label: is this a fact about the machine, or about the predicate?  Wave-31
  asked it of the interior assertion and the answer was measurably **both**,
  30/44.
* **AND MEASURE IT AT A COMMIT.**  A bucket size without one is not a
  measurement; §11.
* **RE-RUN THE SWEEP OVER THE CURRENT OPEN LIST**, not the list the last wave
  left behind.  Wave-31 §7: that alone was +2 boards.
* **PEEL BEFORE ANYTHING ELSE.**  Nine waves.
* **READ THE LANDING OFF THE MACHINE** instead of assuming its padding.
* **A SOUNDNESS ARGUMENT IS A MEASUREMENT.**  Before writing an induction, test
  its STEP against the raw simulator at `k = 0, 1, 2`.
* **After ANY change to `derive`, to a reader, or to the step language, re-run
  `emit_lapcert --list`, `restscan.py --emit`, `regcert.py` and `tailcert.py`
  over the open buckets.**  Each is a DIFFERENT gate and it costs nothing but
  the run.
* **WHEN STUCK ON A CLASS, ask John with an ABSOLUTE-COORDINATE TAPE DUMP**
  (`spacetime.py --rests --mark --lo/--hi` FIXED).  Hand-inspection is
  **38-for-38** across waves 8–31.  Ask EARLY, ask with a TAPE, ask about a CLASS
  not a machine.  Item (2) is the place to do it this wave.

## PER BATCH

    python3 tools/closeout/inventory.py && python3 tools/closeout/gen_stages.py \
      && python3 tools/closeout/audit.py && python3 tools/census_cache.py --check
    git push -u origin <branch>          # retry on network error

Merge conflicts with `main` are routine and always in GENERATED tables
(`_CoqProject`, `theories/Closeout/*`, `tools/closeout/*`): take main's side on
every one, then re-run the four commands above.

Write `docs/WAVE32_FINDINGS.md`.

## DEFERRED TO STABLE HARDWARE

Census fold-in, `CloseoutFinal.v`, the champion
`1RB1LD_1RC1RB_1LC1LA_0RC0RD`, and `0RB1LC_1LC0LC_0RD1LA_1RD1RB`.
