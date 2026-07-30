# Wave-33 findings: nickdrozd's "easy" 24, and the three gates it opened

_Branch `claude/nick-drozd-easy-problems-mj74al`, cut from `main` at
`53cec48`.  The wave started from a community list rather than from a gate
bucket: nickdrozd posted 24 machines he called easy.  One was already
boarded; the other 23 are all in the core residue, and working them turned
into three small builds that boarded 14 rows in total (9 core + 5 shadows)._

## 0. The scoreboard

    before   4,939 settled / 143 core + 74 shadows      (main, 53cec48)
    after    4,953 settled / 134 core + 69 shadows      (96.1%)

nickdrozd's list: **5 of 24 settled**, all `Print Assumptions` funext-only.

| machine | furthest gate today |
|---|---|
| `1RB0LD_1RC1RA_1LA1RC_0RB1LD` | BOARDED |
| `1RB0LD_1RC1RB_1LD1RC_0RC1LA` | no boot chain |
| `1RB0RB_0LC0LD_1LC1LD_1RA0RA` | no interior j=S j chain at octave parity 0 |
| `1RB0RB_0RC1RC_0LD1LA_1LD0LA` | no interior j=S j chain at octave parity 0 |
| `1RB0RB_1LC1LD_0LC1RA_0LD0RA` | no gap-free two-form family |
| `1RB0RC_0LA1LC_0RD0LB_1LB1RD` | no inner interior chain |
| `1RB0RC_0RC1LD_1LB1RC_0LA0LB` | no inner interior chain |
| `1RB0RC_1LC1RA_1RD1LB_0LC0RD` | no inner family at pow2 j |
| `1RB0RD_1LB1LC_1RC0RA_0LB1RD` | no inner interior chain |
| `1RB0RD_1LC0LB_1LD0LB_1RD0RA` | no gap-free two-form family |
| `1RB0RD_1LC0LC_1LD0LB_1RD0RA` | no gap-free two-form family |
| `1RB0RD_1LC1RA_0RB0LC_1LD0LA` | no boot chain |
| `1RB0RD_1RC---_1RD1LC_0LC1RA` | BOARDED |
| `1RB1LA_0LA0LC_1LC1RD_0RB0RD` | no interior j=S j chain at octave parity 0 |
| `1RB1LA_0LA0RC_0LD0RB_1LD1RC` | no interior j=S j chain at octave parity 0 |
| `1RB1LA_0LA1RC_0LD0RC_1LD0RB` | no interior j=S j chain at octave parity 0 |
| `1RB1LA_0LA1RC_0RD0RB_1LB0LA` | no inner interior chain |
| `1RB1LA_0LA1RC_0RD0RB_1LB0RA` | BOARDED |
| `1RB1LA_0LA1RC_0RD0RB_1LB1RA` | BOARDED |
| `1RB1LA_0LA1RC_0RD0RB_1LC1RA` | register step does not close |
| `1RB1LA_0LA1RC_0RD0RB_1RA---` | register step does not close |
| `1RB1LA_0LA1RC_1LD0RB_1LA1LD` | no boot chain |
| `1RB1LA_0LA1RC_1LD0RB_1RA1LD` | no boot chain |
| `1RB1LA_0LA1RC_1LD0RB_1RA1RD` | BOARDED |

The 19 that remain are spread over six gates and none of them is a
one-line fix; §5 says what each still needs.

## 1. What the list actually is

Every one of the 24 is a **binary counter**: 1M steps move the head over
~35 cells, and the states that look rare in a step trace (`C` at 873,786,
`D` at 262,194 = 2^18) are the OVERFLOW states, visited once per octave.
That is the shape this repository's `tailcert` two-form route is built
for, which is why the list maps cleanly onto the gate table instead of
needing a new reading.

Nothing in the list is a quasihalter: the wave-32 `sweep_qhbound_deep.py`
verdict (0 of 143) holds for all 24.

Two orientation notes, both paid for once:

* `1RB0LD_1RC1RA_1LA1RC_0RB1LD` was already boarded before this branch
  (`REG_1RB0LD_1RC1RA_1LA1RC_0RB1LD.v`, the wave-31 two-form renderer).
* every OTHER emitter in the tree was run over the 23 first --
  `emit_lapcert`, `restscan`, `emit_graycert`, `emit_wall`, `emit_wallj`,
  `emit_ixp`, `emit_ip`, `emit_kp`, `emit_shape1`, `emit_shape4` -- and
  scored **0 of 23**.  They are the residue; there were no free boards.

## 2. Build one: a visit witnessed at ONE octave parity is enough

`theories/Counters/LapCertGluePar.v` (commit `7c6c59c`).

A two-form board has two overflow arms, one per octave parity, and they
are different runs -- so a live state can have a prefix witness in one and
none in the other.  `visits()` demanded both, and filed the row
`no visit witness for state <q> at octave parity <b>`.

It never needed both, because the overflow anchors ALTERNATE:

* `reach_ovf_lift` only ever takes INTERIOR laps, and
  `RegGlue.podd_succ_int` says an interior increment never leaves its
  octave -- so the overflow anchor it lands on carries the parity it
  started from (`reach_ovf_par_lift`, the same induction with the parity
  and the anchor index carried along);
* if that is the wrong parity, ONE more lap crosses into the next octave
  (`RegGlue.podd_succ_fill` flips it) and the anchor after it carries the
  parity we want.

`vis_via_ovf_par_lift` is that argument.  It costs the OVERFLOW lap
(`lapo_*`, which every board already proves) and is stated at
`cview p = (S (S j), None)` with `2 <= p` -- the peel's leftover `p = 1`
is out of range on both sides and `ovf_index_pos` keeps it there.

Measured over the three rows the gate held: 2 of 3 move past it.  The
third, `1RB---_1LC1RD_0LB1RD_1LB0RD`, does not and never will: **state A
is not a transition target at all**, so it is visited exactly once, at
step 0.  That row is a QUASIHALTER with A quiet after step 0 and needs the
QH closer (`LapGlueQH`/`LapGlueQuiet`), not `glue_neverqh`.  It is the
only row left in that bucket and it is mislabelled by every never-QH
emitter in the tree, all of which assume never-quasihalting.

## 3. Build two: the HALFWAY nested arm gets a board

`theories/Counters/NestedLapHalf.v` (commit `f286524`).

Wave-32 proved the bounded inner carrier (`inner_to_add_lift`) and wrote
no board around it, because the emitter had no way to NAME the endpoint:
the lemma states it as `Nat.iter k Pos.succ v`, and `Nat.iter` is not an
sside.

It does not have to be.  The halfway value has a name:

    2^m + 2^(m-1) - 1  =  1 0 1^(m-1)  in binary  =  half2 (m-1)

and `half2 n` is an ordinary digit family -- `cview (half2 n) = (n, Some xH)`,
and its encoded word is one `rep`, emitted per board exactly like `iepow`.
What was missing was only the arithmetic joining the two spellings:
`iter_succ_to` (iterating `Pos.succ` by the numeric difference lands on
the named target) and `half_step_le` (the run stays inside its octave, so
`k <= tovf v` is free from `tovf (pow2 n) = 2^n - 1`).

## 4. Build three: the inner interior lap, and the OFFSET start

Commit `373b81e`.  Two measurements first, and the first one is the wave's
main result about a bucket:

**The `no inner interior chain` label was never about the machine.**
Measured over all 17 rows (the probe is in `_inner_chain`'s docstring):
the inner family's own interior lap is **affine at `4*i + b` on 21 of the
22 arms**.  The single genuine exception is
`1RB1LC_0LC0RB_1LA1RD_0LA0RD`, at `4, 16, 36, 72, 140` -- second
differences `8, 16, 32`, so that one is a third level and stays.  What
stopped the other 21 is the LANDING: 9 of the 17 rows close as soon as ONE
trailing blank on the far side is allowed, which is exactly the slack the
OUTER interior has tolerated since wave-31 and the inner one never got.
`_inner_chain` is `_int_chain`'s fallback moved onto that arm, with the
same discipline (the left side carries the opaque `E q0 ++ tail`, so it
must still land exactly), and `INNER_GLUE_LIFT` states the landing up to
`lift` with the usual peel.  The bucket went 17 -> 8.

**Then the arms that reached the renderer start at an OFFSET.**  Their
inner run is `2^m + c .. 2^m + 2^(m-1) - 1` with `c` 1 or 2.
`NestedLapHalf` gains the generic closer for that, with both endpoints
NAMED by the board and the side conditions in pure `Pos.to_nat`/`tovf`
form: `tovf_size` (`tovf v = 2^size v - 1 - v`) is what turns `tovf` of a
built-up start into `lia`, and `inner_to_named_lift` /
`nested_overflow_named_lift` / `vis_via_named` do the rest.  The emitter
names the start as `c`'s bits, LSB outermost, on top of
`pow2 (j + oct - w)`, and discharges the two premises from its own
`iloN`/`iloS`.

The offset is bounded by `lo <= hi` AT `j = 0`, because the arm is stated
for every `j`.  That is `c <= 2^(oct-1) - 1` -- except on a **parity-0**
arm, which never sees `j = 0` at all: `cview p = (S (S j), None)` makes
`podd p = true` exactly when `j` is even, so `j = 0` is `p = 3` and the
parity refutes it.  `OFF_LAPO_PEEL` states that arm one peel deeper and
buys a doubling of headroom for free.  One row is still refused on this
(`1RB1LC_0RC1LD_1LB1RC_0LA0LB`, parity 1, offset 2); it needs the `j = 0`
case proved concretely from `Cc 3`.

## 5. Measured negatives -- DO NOT RETRY

* **Widening `_nested_ovf`'s candidate cap** from 24 to 200: identical
  labels on all 22 open rows of the list.  The cap is not a gate.
* **Any other emitter against this list**: 0 of 23, all ten of them (§1).
* **A deeper inner chain, or a different framing, for
  `1RB1LC_0LC0RB_1LA1RD_0LA0RD`**: its inner interior lap is measured
  NON-affine (`4, 16, 36, 72, 140`).  That one is a third level.
* The standing lists still apply: WAVE32 section 8, WAVE31 section 9,
  WAVE30 section 8, WAVE29 section 7, and back.

## 6. The one thing that caught a real regression

The byte-identical A/B (`rerender_tail.py`, pristine worktree at the merge
base vs the patched tree) came back CLEAN three times and DIRTY on the
fourth: six boards rendered as `FAILED: negative shift count`, because the
new render gate computed `1 << (oct - 1)` before checking `oct >= 1` and
those six arms carry `oct = 0`.  The rows involved are all already
boarded, so nothing in the tree was wrong -- but a later `--force`
re-render would have deleted them.  **The A/B is the only check that
looks at boards the open list no longer contains.**

## 7. The gate table after this wave

Measured at this commit with the probe in it:

    python3 tools/counters/tailcert.py --list tools/closeout/core_rows.txt --out /tmp/scan.json
    python3 tools/counters/buckets.py --json /tmp/scan.json --out tools/counters/buckets33

| n | furthest gate |
|--:|---|
| 40 | `no interior j=S j chain at octave parity 0` |
| 26 | `no boot chain` |
| 25 | `no gap-free two-form family` |
| 17 | `register step does not close` |
| 8 | `no inner interior chain` |
| 6 | `no exit chain` |
| 4 | `no inner family at pow2 j` |
| 4 | `no interior j=0 chain at octave parity 0` |
| 2 | `inner run is not an sside at this octave` |
| 1 | `no visit witness for state A at either octave parity` |

The three items in front of everything else are unchanged from wave-33's
prompt -- the 40-row nested INTERIOR lap, the 26 `no boot chain`, and the
25 `no gap-free two-form family`.  Nothing this wave touched them, and 19
of nickdrozd's 23 are queued behind exactly those three.

## 8. Where the remaining 19 sit

* **5** `no interior j=S j chain` -- wave-33 item (1), the nested interior
  arm.  Not started.
* **4** `no boot chain` -- the second largest bucket, still unmeasured.
* **7** `no gap-free two-form family` -- reader level.  Wave-30's whole
  result was the reader being wrong for 51 rows; this bucket is the one
  saying it may still be wrong.
* **2** `register step does not close` -- the double nesting.
* **1** `no inner interior chain` -- and it is the measured non-affine one.

