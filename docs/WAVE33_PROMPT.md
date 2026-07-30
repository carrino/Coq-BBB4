# Wave-33 prompt: the NESTED INTERIOR LAP, and the bounded carrier's real 26

Continue the (4,2) residue reduction in `carrino/Coq-BBB4`, on branch
`claude/nested-interior-4-2-<yourid>`, cut from `main` (wave-32 is merged).

## STATE — measured 2026-07-30 at `5ffdebb`, with the code that measured it IN that commit

`make closeout-status`, or `python3 tools/closeout/audit.py`:

    4,939 of the frozen 5,156 settled (95.8%)
    143 core undecided + 74 0RB shadows (the shadows resolve with their cores)

**Read §5 and §8 of `docs/WAVE32_FINDINGS.md` before anything else.**  The
largest bucket in the residue was measured DEAD to every framing this wave, and
the item that the wave-32 prompt called the only one whose size survived contact
with the data turned out to be 19 rows of emitter bug.  Both of those are now
do-not-retry entries and both were cheap measurements.  The lesson is in §9 and
it is the same one every wave since 29 has paid for.

Row lists are in the tree; regenerate them rather than trusting them:

    python3 tools/counters/tailcert.py --list tools/closeout/core_rows.txt \
      --out /tmp/scan.json
    python3 tools/counters/buckets.py --json /tmp/scan.json \
      --out tools/counters/buckets33

`tools/counters/buckets32/` is wave-32's, with `GATETABLE.md` beside it.  Note
that a `--list` run without `--emit` reports the FURTHEST gate of the two
orientations (`scan`) while `--emit` reports the LAST orientation's error
(`derive`); **the two label sets are not comparable** and wave-32 lost half an
hour to that.

**And run the closeout regeneration then sweep AGAIN.**  Boarding a row re-roots
the 0RB shadow table, and wave-32's first 6 boards PROMOTED two shadows into the
core list — rows that had never been swept, both of which boarded on sight
(WAVE32 §3b).  That is +2 free boards for one extra pass, and it is the second
wave in a row it has paid.  Iterate until the open list stops changing.

## THE GATE TABLE

See `docs/WAVE32_FINDINGS.md` §10 and `tools/counters/buckets32/GATETABLE.md`.
The three things standing in front of everything else:

* **38 rows: the interior lap is a NESTED lap, and a DOUBLE one.**  Item (1).
* **26 nested arms: the inner family runs a PARTIAL octave.**  Item (2) — the
  bounded carrier, correctly sized at last.
* **25 rows: `no gap-free two-form family`.**  Reader-level, still unopened.

## READ FIRST, in this order

* `docs/WAVE32_FINDINGS.md` — **§5 is item (1)'s whole basis, §4 is item (2)'s,
  §8 is do-not-retry, §6 is why the A/B was free this time and will not be next
  time.**
* `theories/Counters/NestedLapLift.v` — `inner_to_fill_lift`,
  `nested_overflow_lift`, `vis_via_fill`.  This is the shape item (1) moves onto
  the interior arm.  Read all three; wave-32 found `vis_via_fill` sitting unused
  by `tailcert` after six waves.
* `theories/Counters/NestedLap2.v` and `NestedLapCascade.v` — whether
  `boot_via_fill` composing with itself is enough for a DOUBLE nesting, or
  whether the cascade is what item (1) actually wants.  Wave-31 §9 measured the
  SOLO cascade dead against `no boot chain`; that is not a verdict on the
  cascade against this bucket.
* `tools/counters/tailcert.py` — `_derive` (the interior split is `_int_chain`
  twice, and item (1) replaces one of those calls with a nested arm),
  `_nested_ovf` (the shape to copy), `render`'s `OVF_NEST_*` templates (already
  parameterized by an octave shift — item (2) may need the same for a bounded
  endpoint).
* `tools/counters/intnest.py`, `intnest2.py`, `intfit.py` — the three probes item
  (1) is stated from.  Re-run them; they are minutes, not hours.
* `docs/WAVE29_REGISTER_FINDINGS.md` §5d and `docs/WAVE30_FINDINGS.md` §6g (the
  double nesting, phase ratio ~4 — the SAME signature this bucket shows).

## (1) THE NESTED INTERIOR LAP — 38 rows, and it is the largest thing in the residue

`tools/counters/buckets32/no_interior_jS_j_chain_at_octave_parity_0.txt`.
Measured this wave, at `105db12`, three ways:

* `intfit.py`: the interior lap is **NOT affine in `j`, 40 rows of 40, at both
  octave parities**, growing by a factor of 3 (8 rows) or 4 (13 rows) per octave.
  Controlled against the 12 boarded rows, which measure affine at exactly the
  laws their boards state.  **So no peel and no framing will ever board these**
  — see §8, and do not spend the wave rediscovering it;
* `jspeel.py`: 0 of 40 for every deepening of the `j = S j'` half (prefix depth 2
  and 3, `q0`'s low digit in the post, and combinations), exact and up to `lift`;
* `intnest.py`: **38 of the 40 carry a FULL inner counter family at BOTH
  parities** inside ONE interior lap — values exactly `2^(j-1)..2^j-1`, octave
  shift 0.  Two rows carry none and are not part of this item.

So the interior branch wants the treatment the OVERFLOW branch already has.
`nested_overflow_lift` is generic in `(Cc, Cin, p, v0)` — it does not know the
arm it sits on — and `tailcert`'s overflow arm is the worked example, complete
with the boot/inner/exit chain triple, `vis_via_fill` for exit-only states, and
(as of this wave) an octave shift.

**The catch, and read it before designing.**  A single nesting predicts a growth
ratio of **2**: an affine inner cost `a*i + b` summed over `2^(j-1)` inner laps
is `Theta(2^j)`.  The measurement says 3 and 4.  `intnest2.py` measures the
INNER lap directly and it is **not affine either** — on the exemplar
`1RB---_0LB1RC_1LB0RD_1LC0RD` it runs `22, 42, 88, 202, 494` at `i = 0..4`.
There is a third level.  So:

1. `intnest2.py` measures the inner lap directly and it comes back **NOT AFFINE
   on 76 arms of 76** (every inner anchor located), with bases ~2.4 to ~4.  So
   the third level is real, not an artefact.  Always read its `anchors n/N`
   denominator: the first run of that measurement located none on 20 rows and
   still printed "not affine", which was right by luck (WAVE32 §5d);
2. decide between `NestedLap2.boot_via_fill` composed with itself (which
   `nestcert` already chains up to `MAXCOUNTS = 4`) and `NestedLapCascade`;
3. **what does NOT exist at any depth is an interior arm that accepts a nested
   lap at all.**  `_int_chain` returns a chain or raises.  That plumbing — an
   interior branch whose `j = S j'` half is boot + inner + exit rather than one
   chain — is the item, and it is worth building even if the inner level below
   it needs a second pass, because 38 rows are behind it and nothing else is.

**Ask John with an ABSOLUTE-COORDINATE TAPE DUMP before designing the third
level.**  Hand-inspection is 38-for-38 across waves 8–32.  Dump the exemplar with
`spacetime.py --rests --mark --ruler` and FIXED `--lo/--hi`, and ask about the
CLASS: *the interior lap runs a counter, and each lap of THAT counter runs
something exponential too — what is the innermost thing?*  Ask early; this is
the place for it.

## (2) THE BOUNDED INNER CARRIER — 26 nested arms, not 39 rows

Wave-32 §4.  Of the 60 nested arms across the old 39-row target, 26 have **no
full-octave inner family under any alphabet in `TRY`** and only partial runs.
The other 34 are done: 8 already worked, and 26 were opened by handing the inner
search `TRY` instead of `ENCS`.

The shapes, measured with `tools/counters/innerrun.py` (which takes `families`'s
exact-octave requirement out, so a partial run is reported instead of dropped):

| shape | run |
|---|---|
| `hi-64` / `hi-128` | `pow2 m .. pow2 m + 2^(m-1) - 1` — stops HALFWAY |
| `lo+1`, `lo+3`, `lo+4`, `lo+5` | starts a small constant above `pow2 m` |
| both | `132 .. 191` = `2^7+4 .. 2^7+2^6-1` (wave-29 §5d, reproduced exactly) |

**Two designs, and pick between them by measurement, not by taste.**

**(a) The bounded carrier**, as the wave-32 prompt stated it:

    Lemma inner_to_add_lift : forall k v, k <= tovf v ->
      exists n, stepn tm n (lift (Cin v)) = Some (lift (Cin (Pos.iter Pos.succ v k))).

`k <= tovf v` is the whole side condition and it is what makes every intermediate
anchor INTERIOR, which is what `Hin` needs; `tovf_succ` carries it through the
step.  Plain induction on `k`, not the well-founded one `inner_to_fill_lift`
needs.  Do NOT state the side condition per-`m`
(`forall m < k, exists i q0, cview (v + m) = (i, Some q0)`): `k` is exponential
in the board's symbolic index, so `vm_compute` cannot discharge it and the board
cannot state it.  The cost is that the emitter must then write `k` and
`Pos.iter Pos.succ v k` down symbolically, and `Pos.iter` is not an sside.

**(b) Reframe the family so the run IS a full octave.**  This is what the shape
argues for and wave-32 did not test it.  Strip the leading `10` from `132..191`
and the low six bits run `4 .. 63` — a full sub-counter run under a FIXED high
prefix.  If those high blocks can be absorbed into the key's `tail`, the run
becomes `pow2 2 .. fill (pow2 2)` and `inner_to_fill_lift` covers it with **no
new Coq at all**.  What stands in the way is that `nestcert.decode` requires the
word to END at the terminator `C`, so a word whose high part is
`dig(0) ++ term` cannot be split that way today — which is a change to
`decode`/`families`, i.e. to code `regcert` also calls, so **run the A/B**
(`rerender_check.py` AND `rerender_tail.py`, both as A/Bs; see NON-NEGOTIABLE).

**Measure (b) first.**  It is a Python question with a yes/no answer and it may
cost nothing; (a) is a Coq lemma plus an emitter that has to name an exponential
index.

## THE RESIDUE IS ALL NEVER-QH CANDIDATES — that is now measured, not assumed

Wave-32 §3c boarded `1RB1RD_1RC0LD_1LB0RA_1LC0LC` as a QUASIHALTER
(`QHBound 2401`) after John read it by hand: it diverges right using every state
but B after 2331 steps.  It had carried the label `no gap-free two-form family`
for three waves, which was TRUE and useless -- it has no two-form family because
it is not a counter.

Every emitter under `tools/counters/` assumes never-quasihalting, so none of
them could ever have said so.  `tools/sweep_qhbound_deep.py` then asked the
question properly over the whole open list, with `t` read off each machine
instead of from a fixed candidate list: **0 of 143**, with a positive control
that reproduces the one row that fired.  So the remaining 143 really are
never-quasihalting candidates and item (1)/(2) are the right shape of work.
**Do not re-run that sweep** (§8).

## ALSO OPEN, not items

* **25 `no gap-free two-form family`.**  Untouched for three waves and now the
  largest bucket after item (1) and `no boot chain`.  Reader-level: wave-30's whole result was the
  reader being wrong for 51 rows, and this is the bucket saying it is still wrong
  for 26.  Check the INVERTED alphabets and the two-cell terminator partners
  before assuming new mathematics.  Wave-32's §9 lesson applies directly — the
  predicate includes the SEARCH SPACE, and `two_form` and `_nested_ovf` were
  searching different ones for six waves.
* **29 `no boot chain` / 5 `no exit chain`.**  Both grew this wave, by exactly
  the 13 rows the alphabet fix moved into them (+9 and +4).  Those 13 have an
  inner family now and fail one gate later, so `no boot chain` is the SECOND
  largest bucket in the residue and 9 of it is brand new.  Nothing about the new
  9 has been measured — that makes them the cheapest thing here, and the wave-31
  §9 do-not-retry (the SOLO CASCADE, 0 of 11) was measured against the OLD 11
  rows, not these.
* **17 `register step does not close`.**  Wave-30 §6g's double nesting, whose
  phase ratio (~4) is now measured on a SECOND bucket (item (1)).  If item (1)
  builds a double nesting, come back here with it — that is the strongest reason
  to do item (1) first.

## NON-NEGOTIABLE

* Never edit `theories/Census/`.  `python3 tools/census_cache.py --check` must
  stay **MATCH**.
* **Check the census closure before adding a lemma to a library file.**
  `python3 -c "import sys;sys.path.insert(0,'tools');import census_cache as C;print('theories/Counters/X.v' in set(C.closure_v_files()))"`.
  INSIDE (do not edit): `WTape.v`, `LapGlue.v`.  OUTSIDE (fine):
  `LapCertGlue.v`, `LapCertGlueLift.v`, `NestedLapLift.v`, `NestedLap.v`,
  `NestedLap2.v`, `LapDecider.v`, `RegGlue.v`, `JpCounter.v`.
* A board counts only when its file compiles AND
  `Print Assumptions nqh_<ID>` shows `functional_extensionality_dep` only.
* `SkipGlue`, `NestedLapLift`, `NestedLap2`, `LapDecider`, `LapCertGlue`,
  `LapCertGlueLift`, `LapGlue*`, `RegGlue`, `WTape` are axiom-free or funext-only
  — keep them so.  Both items touch one; prove, do not assume.
* Everything under `tools/` is UNTRUSTED; the kernel re-checks every board.
* **Do not add a row to `alphabets_gen.ENCROWS`/`ENCS`** without checking that
  `reg113.json`, `quad35.json` and `jexc80.json` still reproduce.  Register a
  private `ENCDATA` row instead — see `tailcert.INVERTED`.  **And if you do,
  check every call that searches an alphabet list, not just the one you are
  editing**: `ENCDATA` had `Alph_01_11_11` for three waves while
  `_nested_ovf` searched `ENCS` and could not see it (wave-32 §2).
* **The byte-identical regression is an A/B, not a comparison against the tree.**
  Run `tools/counters/rerender_check.py` (emit_lapcert's prefixes) AND
  `tools/counters/rerender_tail.py` (the `REG_*` boards — new this wave, because
  the first cannot see them) twice each: once from a pristine worktree at your
  merge base, once from the patched tree, then `diff -rq`.  717 of 870 boards
  already differ from what today's templates render, so a literal comparison
  against the tree cannot pass.  Wave-32's A/B was clean because it changed
  nothing shared; item (2) design (b) changes `nestcert.decode`, so **that one
  will matter**.
* **Publish no bucket size without the commit it was measured at, and make sure
  the code that measured it is IN that commit.**  And publish the PROBE: wave-32
  added `buckets.py` so the row lists themselves are regenerable, not just the
  counts.
* **A CONTROL IS PART OF A MEASUREMENT.**  Wave-32 §9: "not affine on 40 rows" is
  worth nothing without "affine on the 12 that boarded, at the laws they state".
  Any verdict about a class of machines needs the same.

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

`tailcert.py --list` over the 143 takes **over an hour** — start the sweep first
and work while it runs.  (The row that never finished for wave-32,
`1RB1RD_1RC0LD_1LB0RA_1LC0LC`, is boarded and gone.)  `cascade_probe` needs a couple of GB per row; run
probes one row at a time under `ulimit -v`.

## DO NOT RETRY (measured)

* **Any framing, peel or chain depth against the 40 `no interior j=S j chain`
  rows.**  WAVE32 §5a/§5b: NOT affine on 40 of 40 at both parities (factor 3 or
  4 per octave), and 0 of 40 for every deepening.  A `srun` chain costs `a*j+b`.
  Build the nested arm (item (1)) or leave them.
* **A deeper peel on the two-form interior branch at `j = S j'`.**  WAVE32 §5b,
  `jspeel.py`, 0/40.  (The `j = 0` half was already covered by WAVE30 §8.)
* **Reading a fill-off-endpoint diagnostic as a partial inner run.**  WAVE32 §3:
  all 6 ran a FULL octave and the replay bound was wrong.
* **Looking for more residue QUASIHALTERS by widening the QHBound sweep's `t`.**
  WAVE32 §3c: `sweep_qhbound_deep.py` reads `t` off each machine and gets 0 of
  143, with a positive control.
* **The SOLO CASCADE against `no boot chain`.**  Wave-31 §9: 0 of 11 with five
  distinct causes.
* **The `lift` fallback in the interior split as a way to BOARD rows.**
  Wave-31 §8b: moves 30, boards 0.  Built and committed; do not rebuild.
* **`WTape.cycRW` / an `SCycR` with a left-prefix offset.**  Wave-30 §2.
* **Reading `intgap._cycr_gap`'s dead-end shape as a missing primitive.**
  Use `_cross_period`.
* **Designing a DESCENDING carrier for a family the reader sees counting down.**
  Measured on all 51: bit-polarity inversion.  Try the swapped digit words.
* **`two_form`'s "gap-free union" as evidence of an ascending counter.**
* **Widening `derive_chain`'s depth on `no interior chain`.**  The reachable set
  is CLOSED at 7–89 states.
* **The DIGIT-WIDTH hypothesis on the register bucket.**  WAVE30 §6f, all 27.
* Standing: WAVE32 §8, WAVE31 §9, WAVE30 §8, WAVE29 §7, WAVE28 §4, WAVE27 §5,
  WAVE26 §6, WAVE25 §6, WAVE24 §7, WAVE18 §5, WAVE16 §5.

## STANDING MOVES

* **MEASURE THE BUCKET — AND THE READER — BEFORE DESIGNING FOR IT.**  Wave-32
  paid this twice in one wave: item (1) as stated was 19 rows of emitter bug, and
  item (2) as stated was impossible.  Both measurements were under an hour.
* **THE PREDICATE INCLUDES THE SEARCH SPACE.**  Grep for every place a list of
  alphabets, tails or framings is passed in, and check they agree.
* **A CONTROL IS PART OF A MEASUREMENT.**
* **AND MEASURE IT AT A COMMIT, WITH A COMMITTED PROBE.**
* **RE-RUN THE SWEEP OVER THE CURRENT OPEN LIST**, not the list the last wave
  left behind.
* **PEEL BEFORE ANYTHING ELSE** — except when the cost is measured non-affine,
  in which case do not peel at all.
* **READ THE LANDING OFF THE MACHINE** instead of assuming its padding.
* **A SOUNDNESS ARGUMENT IS A MEASUREMENT.**  Before writing an induction, test
  its STEP against the raw simulator at `k = 0, 1, 2`.
* **After ANY change to `derive`, to a reader, or to the step language, re-run
  `emit_lapcert --list`, `restscan.py --emit`, `regcert.py` and `tailcert.py`
  over the open buckets.**  Each is a DIFFERENT gate.
* **WHEN STUCK ON A CLASS, ask John with an ABSOLUTE-COORDINATE TAPE DUMP**
  (`spacetime.py --rests --mark --lo/--hi` FIXED).  **38-for-38** across waves
  8–32.  Item (1)'s third level is the place to do it this wave.

## PER BATCH

    python3 tools/closeout/inventory.py && python3 tools/closeout/gen_stages.py \
      && python3 tools/closeout/audit.py && python3 tools/census_cache.py --check
    git push -u origin <branch>          # retry on network error

Merge conflicts with `main` are routine and always in GENERATED tables
(`_CoqProject`, `theories/Closeout/*`, `tools/closeout/*`): take main's side on
every one, then re-run the four commands above.

Write `docs/WAVE33_FINDINGS.md`.

## DEFERRED TO STABLE HARDWARE

Census fold-in, `CloseoutFinal.v`, the champion
`1RB1LD_1RC1RB_1LC1LA_0RC0RD`, and `0RB1LC_1LC0LC_0RD1LA_1RD1RB`.
