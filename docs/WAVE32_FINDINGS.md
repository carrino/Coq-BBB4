# Wave-32: the inner search was blind, the replay ignored the shift, and the 40-row bucket is not a framing problem

Branch `claude/wave32-prompt-residue-cotlom`, cut from `main` at `105db12`
(wave-31 merged as #74).

Every number in this document was measured on **2026-07-30**, and each table
says which commit it was measured at and which committed probe measured it.
That is the wave-31 §11 constraint, and this wave is the first to be able to
say it of a bucket table without qualification: the probes are in the tree.

## 1. The one-line result

    4,930 of the frozen 5,156 settled  ->  4,939   (95.6% -> 95.8%)
    150 core undecided + 76 0RB shadows ->  143 core + 74 shadows

**+9 boards** — 6 from the items below, **2 more the input list did not contain
until the first 6 landed** (§3b), and **1 that is not a never-quasihalter at all**
(§3c) — and the two items of the wave-32 prompt came back as follows.

**Item (1) — the bounded inner carrier.** Not built, and it should not have been
built first. Measuring the bucket before designing for it found **two defects in
the emitter sitting in front of the carrier**, neither of them mathematics. They
account for **19 of the 39 rows**: the alphabet gap opens 13, and the replay bug
*is* the whole 6-row fill-off-endpoint bucket. The carrier is still wanted, but
for a smaller and much better specified target — **26 of the 60 nested arms**,
not 39 rows (§4).

**Item (2) — the 40-row `no interior j=S j chain` bucket.** Measured, and the
answer is the one the prompt named as the disqualifying case: the interior lap
is **not affine in `j`, on 40 rows of 40, at both octave parities**. No chain of
any depth expresses it, so it is not a framing problem and no peel will fix it.
What it *is*: **38 of the 40 rows run a full inner counter inside one interior
lap** — the nested shape, on the interior branch instead of the overflow one —
and the inner lap is itself not affine, so it is a **double** nesting (§5).

## 2. Item (1a): the INNER family was searched over the wrong alphabet list

`tailcert.two_form` reads the OUTER counter over `tailcert.TRY`: the `obS = 0`
rows of `ENCS` **plus three alphabets this module registers privately in
`ENCDATA`** — `Alph_01_11_11` (the `obS = 0` spelling of Mp's, added when the
two-form route was built) and wave-30's two INVERTED rows `Alph_11_10_11` /
`Alph_11_01_11`. All three are deliberately kept out of `ENCS` so that
`reg113.json`, `quad35.json` and `jexc80.json` keep reproducing.

`tailcert._nested_ovf` called `NC.families(mid, ENCDATA, ENCS, K=K)`. The inner
search could not see those three at all — the module's own alphabets were
invisible to half of the module.

Measured at `f4467cc` with `tools/counters/innerenc.py`, over item (1)'s 39 rows
(`tailcert_innerfam33.txt` + `tailcert_filloff6.txt`), 60 nested arms:

| n | nested arms, by what the inner search finds |
|--:|---|
| 8 | `ENCS` already finds a full-octave family |
| **26** | **`ENCS` finds NOTHING; the three private alphabets find one** |
| 26 | neither finds one — only partial runs (§4) |

The 26 are **13 rows**, all previously filed `no inner family at pow2 j`. The 32
keys the three alphabets contribute break down `Alph_01_11_11` 18,
`Alph_11_10_11` 12, `Alph_11_01_11` 2 — and **24 of the 32 carry octave shift
1**, which is what makes §3 a prerequisite rather than an independent fix.

The change is one argument: `families(mid, ENCDATA, TRY, K=K)`. **`ENCS` is not
touched and `families` is not changed**, so nothing `regcert` calls moved and
the A/B (§6) has nothing shared to disturb.

## 3. Item (1b): the replay ignored the family's OCTAVE SHIFT — that is the whole fill-off bucket

`nestcert.endpoints` puts the family's octave shift in the sside's CONSTANT term
(`a = 1`, `b = oct`), so the boot lands at `E_in (pow2 (j - 2 + oct))`.
`tailcert.validate` checked that landing correctly and then replayed the inner
laps from

    v = 1 << (j - 2)

For `oct = 0` that is right. For `oct >= 1` it walks the **right per-lap step
counts** — `v` and `v << oct` agree in their low bits, so they give the same
sequence of carry indices — but **too few laps**, so the run stops short of the
fill and the row is filed `inner fill lands off the measured endpoint`.

Worked through on `1RB0LD_1LC1RA_1LA1RC_0RB1LD`, whose diagnostic the wave-32
prompt quotes: at `p = 15`, `j = 4`, the chosen key has `oct = 1`, so the boot
lands at `E_in (pow2 3) = E_in 8`. The replay ran `v = 4, 5, 6` — three laps,
carry indices `0, 1, 0` — and reached `E_in 11`. The fill of three blocks is
`15`. The dump reads

    p=15 inner fill -> (3, (1,0,1,0,1,1,1,0,0,1), 0, ())
                  want (3, (1,0,1,0,1,0,1,0,0,1), 0, ())

and `(1,0)(1,0)(1,1)(1)` decodes under `Jp` to exactly 11 while
`(1,0)(1,0)(1,0)(1)` is 15. The prompt read this as evidence of a run that
"stops short by a fixed amount", which is what a bounded carrier is for. It is
not: the machine ran a **full** octave and the validator stopped counting early.

`v = 1 << (j - 2 + O['key'][4])` is the fix, and **all 6 rows of that bucket
then validate**, each at 192 anchors and 2 nested overflows.

### 3a. Then two renderer gaps, both closed with lemmas already in the tree

The rows now derived and could not be written down.

**The nested templates hardwired `oct = 0`.** `gbo` proved
`lift (cden [] [] k CS) = lift (Cin (pow2 k))` via `replace (1 * k + 0) with k`,
which does not even match a term reading `1 * k + 1`. Parameterized: the arm is
stated at `pow2 (j + oct)` throughout, `gbo`/`gxi` reindex by the shift, and
`hbo`/`hxe`/`lapo` follow. `nested_overflow_lift` is generic in `v0` and
`cview_fill_pow2` is generic in its index, so **no new Coq**. At `oct = 0` the
substitution reproduces the old text character for character — §6.

**A state that fires only in the EXIT chain has no witness in the BOOT chain.**
`visits` only ever looked at the boot, and `vis_of_run` can see a prefix of ONE
chain. `NestedLapLift.vis_via_fill` has been in the tree for exactly this since
wave-16 — its docstring measures the case at 8 of 30 — and `nestcert` uses it;
`tailcert` did not. With the replay fixed, this is where **all 6** rows stopped,
so it was not a rare fallback but the gate the whole bucket was queued behind.

`vis_via_fill` lands in `lift` space; `LapCertGlueLift.vis_csteps_of_lift` pulls
it back to the concrete `csteps` form `viso@B@` already has. Stating `visx@B@`
that way makes the two **interchangeable at the use site**, so the board's
`vis_` body is unchanged and boards that need no exit witness render identically.

### 3b. +2 more, because the open list GREW when the first 6 landed

Wave-31 §7 got +2 boards from re-sweeping the current open list instead of the
one the previous wave left behind. It happens again here, for a reason worth
recording because it is structural rather than lucky:

    core 150 -> 146 after 6 boards.  150 - 6 = 144, not 146.

Boarding a row re-roots the 0RB shadow table, and **two rows that had been
listed as shadows became core representatives** —
`0RB1LA_1LC1RD_1LD1RC_1RB0LA` and `0RB1LA_1RC1RD_1LD1RC_1RB0LA`. Neither was in
the list this wave swept. Both derive and board immediately, at 192 anchors and 2
nested overflows each, `functional_extensionality_dep` only, and both exercise
`pow2 (j + 1)` and `visx` as well.

**So: re-run the closeout regeneration and then sweep AGAIN, until the open list
stops changing.** One pass is not enough, and the second pass is free. After the
second pass core is 144 with no further promotions, so this wave converged in
two.

### 3c. `1RB1RD_1RC0LD_1LB0RA_1LC0LC` is a QUASIHALTER, and the sweep's `t` never reached it

This is the one row §10 could not re-measure inside a sweep's budget — it is far
slower than the other 145 under `tailcert`, and it had sat in the residue through
thirty-two waves of never-quasihalting emitters. John read it by hand on
2026-07-30:

> just diverges to the right using all states but B after 2331 steps

Confirmed against the raw simulator over 3,000,000 steps: **`StB` is entered for
the last time at index 2331**, `StA`/`StC`/`StD` keep firing, the head drifts
right at about one cell per three steps and the tape never reaches further left
than −13.

So `StB` is eventually quiet and the machine **quasihalts**. It was never going
to board as a never-quasihalter, which is why every counter emitter filed it
under one gate or another — the gate label was a category error, not a
measurement.

What it needs is a score BOUND, and the route has been in the tree for many
waves: `Checkers/Wrap.ngram_check_qhbound` wraps `StB` to a halt, closes the
2-gram abstraction of the configuration at index `t` (**4 contexts**), and checks
that closure is halt-free and per-state acyclic — halt-free gives `NonHalt`,
acyclicity gives liveness so no state other than `StB` can be quiet, and `StB`'s
last visit is exhibited concretely. `QHBound 2401`, well inside the closeout's
`B_board` = 66,349, so the board is the standard `iqh_le` shape and the whole
certificate is one `vm_compute`.

**Why no wave found it, and this is the third instance of the same failure this
wave:** `tools/sweep_qhbound_residue.py` searches `CAND_T = (64, 256, 1024)`.
The last `StB` visit is at 2331. **Every candidate `t` was below the one index
that had to be exceeded.** Nothing about the route was missing — the search
range was. At `t = 2400, n = 2` the certificate is found on the first try.

Note what this says about a gate label. The row was filed
`no gap-free two-form family`, and that was *true* — it has no two-form counter
family, because it is not a counter. **A gate label says where one emitter
stopped, not what the machine is.**

So the obvious follow-up got asked: `tools/sweep_qhbound_deep.py` runs the same
gate over the whole open list with `t` read off each machine's own measured
last-visit index instead of a fixed candidate list.

    0 of the remaining 143 open rows are QHBound-decidable this way

and the **positive control** matters more than the zero: run on the boarded row
it reproduces `q = B, s = 2331, n = 2, t = 2400` exactly. So the zero is a
measurement, not a broken sweep. `1RB1RD_1RC0LD_1LB0RA_1LC0LC` was the only one,
and the residue really is 143 never-quasihalting candidates.

## 4. What the bounded inner carrier is actually for — 26 arms, and the run shape

`tools/counters/innerrun.py` reports the run a nested arm actually makes, with
`families`'s "must be exactly `2^(K-1+o)..2^(K+o)-1`" requirement taken out. Of
the 60 nested arms, **26 have no full-octave family under any alphabet in `TRY`**
and only partial runs. Their shapes, measured at `f4467cc`:

| n | shape of the best key's run, against the octave `families` demands |
|--:|---|
| **17** | a small constant ABOVE `pow2 m` **and** stopping short: `lo+1..lo+5` with `hi-28..hi-128` |
| 7 | offset only — `lo+61`, `lo+95`, `lo+125`, `lo+253` |
| 2 | short only — `hi-31`, `hi-63` |

The dominant form is therefore both at once, and `hi-2^(m-1)` is the recurring
short-fall: the run stops at `pow2 m + 2^(m-1) - 1`, HALFWAY to the fill. Two of
the 26 report a `lo` *below* `pow2 m` under the probe's inferred octave, so the
octave a bounded family should be stated at is itself not always obvious — read
it off the dump, do not compute it.

Wave-29 §5d's `K = 5: 132..191` is reproduced exactly. **This** is the carrier's
target, and it is worth noting what the shape says: strip the leading `10` and
`132..191` is the low six bits running `4 .. 63` — a full sub-counter run under a
fixed high prefix. Whether that is better expressed as a bounded carrier
(`inner_to_add_lift`, `k <= tovf v`, plain induction on `k`) or as a full
`inner_to_fill_lift` on a REFRAMED family whose high blocks are absorbed into the
tail is an open design question this wave did not settle, and it is the first
thing to decide before writing the lemma.

**Do not restate the target as 39 rows.** 13 of the 39 needed no carrier at all,
and 6 more needed none either.

## 5. Item (2): the 40-row bucket is NOT a framing problem

The wave-32 prompt asked three questions, cheapest first. The first one settles
it, and the third turns out to be unaskable.

### 5a. The interior lap is not affine in `j` — 40 of 40, both parities

`tools/counters/intfit.py`, measured at `105db12` over
`buckets31/no_interior_jS_j_chain_at_octave_parity_0.txt`. It fits PER OCTAVE
CLASS and first checks that the cost is a function of `(parity, j)` at all,
because wave-29 §7 measured a period-P frame making a single fit report
"exponential" on branches that are really `4k+7`/`4k+9` per parity:

    40 / 40 rows: NOT AFFINE at octave parity 0 AND at octave parity 1

The cost is a clean function of `(parity, j)` on every row — this is not the
wave-29 §7 trap — and it grows geometrically. Exact recurrences, per row, with
both parities agreeing on every one:

| n | law |
|--:|---|
| 13 | `n(j+1) = 4*n(j) + (affine in j)` |
| 8 | `n(j+1) = 3*n(j) + (affine in j)` |
| 19 | no exact integer multiplier at the depth the frozen octave range reaches |

and the ratio at the top of the measured range, parity 1: `~4` on 20 rows, `~3`
on 8, `~2.5` on 12. The exemplar `1RB---_0LB1RC_0RD0RC_1LB1LD` runs
`4, 12, 32, 88, 252, 740, 2200` at `j = 0..6`.

A `srun` chain costs `a * j + b` by construction. **So no chain of any depth,
at any framing, expresses this lap.** The 40 rows are not waiting for a better
peel.

**Control, and this is what makes the verdict trustworthy.** The same probe over
the 12 rows wave-31 boarded reports **12 / 12 affine at both parities**, and the
laws match what those boards state. `REG_1RB0LC_1RC1LA_1LD1RB_0RB0LD` declares
its peeled interior half at `4*j+8`; the chain's index is `j' = j - 1`, and the
probe measures `4*j+4 = 4*(j-1)+8`. Exact agreement — so a "not affine" verdict
from this probe is about the machine, not about the probe.

### 5b. No deeper peel derives — 40 of 40

The standing do-not-retry entry (WAVE30 §8, restated WAVE31 §8) covers a deeper
peel on the **`j = 0`** half only; `dblpeel_probe.py` earned it. The **`j = S j'`**
half had never been tried, which is why the prompt asked for it.

`tools/counters/jspeel.py`, measured at `105db12`. Per row and per parity it
tries: prefix depth 2 and depth 3 (each with the extra concrete case the reindex
leaves behind), `q0`'s low digit peeled into the POST — `dblpeel_probe`'s move,
applied to this half — for `dig(0)`, `dig(1)` and the terminator, and depth 2
combined with each of those. Exact first, then up to `lift`.

    40 / 40: no deepening derives, at either parity

Which is what §5a predicts, and the two measurements are independent: `jspeel`
derives chains, `intfit` only simulates. **This is the do-not-retry entry the
prompt asked to be written if the peel failed** — see §8.

### 5c. "Which side needs the concrete cell" cannot change the answer

The prompt's third question was whether the LEFT-only peel in `P0`/`P1` (and in
`emit_lapcert.GLUE_SPLIT`) is the problem — a machine whose head steps RIGHT out
of the anchor has no concrete cell there, because the interior chain is derived
`el=False, er=True` with the far side walled.

It is not asked, because it cannot matter. The measurement in §5a is the number
of raw steps from the anchor at `p` to the anchor at `p + 1`. That number is a
property of the machine and the anchor family; **no choice of framing changes
it**, and no framing makes `Theta(3^j)` affine. A right-side peel could only ever
help a lap that is affine and mis-framed.

### 5d. What the 40 rows ARE: a nested interior lap, and a DOUBLE one

`tools/counters/intnest.py` takes the deepest interior lap available at each
parity, collects its blank-head rests, and asks `nestcert.families` the same
question `_nested_ovf` asks of the OVERFLOW phase. Measured at `105db12`:

| n | rows |
|--:|---|
| **38** | a **FULL inner counter family at BOTH parities** — values exactly `2^(j-1)..2^j-1`, octave shift 0 |
| 2 | no inner counter (`1RB---_0LB1RC_0RD0RC_1LB1LD`, `1RB---_0RC0RB_1LD1LC_0LD1RB`) |

So the interior branch of these rows is the shape the overflow branch already
has: a second counter runs a full octave inside one lap of the first, and its
`Theta(2^j)` cost lives in an `exists n` no formula names. That is
`NestedLapLift.inner_to_fill_lift` / `nested_overflow_lift`, on the interior arm.

**But it is not a straight transfer.** A single nesting predicts a ratio of 2 —
summing an affine inner cost `a*i + b` over `2^(j-1)` inner laps is
`Theta(2^j)` — and §5a measures 3 and 4. `tools/counters/intnest2.py` measures
the inner lap directly, per inner carry index `i`, over all 38:

    76 / 76 arms:  the INNER lap is NOT AFFINE either
                   (every inner anchor located: 16/16 and 32/32 per arm)

Sample cost sequences at `i = 0..4`:

| row | inner lap cost | base |
|---|---|--:|
| `1RB---_0LB1RC_1LB0RD_1LB0RC` | 30, 96, 354, 1380, 5478 | ~4 |
| `1RB---_0LC1RB_0LB1RD_1LC0RD` | 16, 56, 208, 808, 3200 | ~4 |
| `1RB---_0LB1RC_1LB0RD_1LC0RC` | 26, 60, 154, 428, 1242 | ~3 |
| `1RB---_0LB1RC_1LB0RD_1LC0RD` | 22, 42, 88, 202, 494 | ~2.4 |

So there is a third level, and the interior branch is wave-30 §6g's double
nesting seen from a different bucket — the same ratio-4 signature.
`NestedLap2.boot_via_fill` composes with itself and `nestcert` already chains up
to `MAXCOUNTS = 4` counts, so the machinery may be closer than the size of this
suggests; what is NOT available is an interior arm that accepts a nested lap at
all.

**A probe bug worth recording, because the first run of this measurement was
wrong and looked plausible.** `intnest2` took the inner family's ENCODING from
the first full-octave key and its VALUE RANGE from the longest-run key. Those are
routinely different keys, so the match table it built could not be hit and 20 of
the 40 rows reported `anchors 0/N`. Reported as "not affine" — the same verdict
the correct run gives — it would have been a true conclusion resting on no
measurement at all. It is caught only because the probe prints how many anchors
it located. **Print the denominator.**

## 6. The A/B, and why this one had nothing to disturb

`rerender_check.py` covers the prefixes `emit_lapcert` owns (LAPC/NLAP/PEEL/
LAPQ) and cannot see the `REG_*` boards `tailcert` writes, so this wave adds
`tools/counters/rerender_tail.py` — render-only, no `coqc`.

Run from a pristine worktree at the merge base `105db12` and again from the
patched tree, then `diff -rq`: **all 12 committed REG boards render
BYTE-IDENTICAL**. The `oct = 0` substitution and the unchanged `vis_` body are
what buy that.

The wave-32 prompt expected this check to matter, because item (1) as specified
changes `nestcert.families`, which `regcert` also calls. **It did not need to
change.** `git diff --stat` for the code is one file, `tools/counters/tailcert.py`
— the alphabet list is an *argument*, not a definition.

For the same reason the standing "re-run every emitter after a change to a
reader" move is a no-op here: `emit_lapcert`, `regcert` and `restscan` do not
import `tailcert`, and the only rows that left the open list are the 6 this wave
boarded, so the other 144 are already swept against those emitters at their
current state. Nothing was skipped that could have paid.

## 7. What is in the tree

| file | what |
|---|---|
| `tools/counters/tailcert.py` | the three fixes: `TRY` for the inner search, the octave-shift replay, the parameterized nested templates + `VISX` |
| `theories/Machines/Counters/REG_*.v` | 6 new boards, all 6 exercising `pow2 (j + 1)` AND `visx` |
| `tools/counters/innerrun.py` | the run a nested arm actually makes, full-octave requirement removed |
| `tools/counters/innerenc.py` | `families` over `ENCS` vs over `TRY`, per row and per arm |
| `tools/counters/intfit.py` | is the interior lap affine in `j`, per octave class |
| `tools/counters/jspeel.py` | deeper peels on the `j = S j'` interior half |
| `tools/counters/intnest.py` | does the interior lap carry an inner counter |
| `tools/counters/intnest2.py` | is that inner lap itself affine |
| `tools/counters/rerender_tail.py` | the A/B harness for `REG_*` |

Each of the 6 boards compiles and `Print Assumptions nqh_<ID>` is
`functional_extensionality_dep` only. `census_cache.py --check` is **MATCH** at
the unchanged hash `12362a25…e15d833f`; `theories/Census/` was not touched and no
library file was either, so no board outside the six was recompiled.

## 8. DO NOT RETRY (measured this wave)

* **Any framing, peel or chain depth against the 40 `no interior j=S j chain`
  rows.** `intfit.py`: the interior lap is NOT affine in `j` on 40 of 40 rows at
  BOTH octave parities, growing by a factor of 3 or 4 per octave. A `srun` chain
  costs `a*j+b`; the lap cannot be one, so the bucket is not a framing problem.
  The control (12/12 boarded rows measure affine, matching their boards' stated
  laws exactly) is what makes this a verdict about the machines.
* **A deeper peel on the two-form interior branch at `j = S j'`** — this is the
  entry the wave-32 prompt asked for, and it now covers the half the wave-30/31
  entry did not. `jspeel.py`: prefix depth 2 and 3, `q0`'s low digit peeled into
  the post (`dig(0)`, `dig(1)`, terminator), and depth 2 combined with each, at
  both parities, exact and up to `lift`. **0 of 40.**
* **Reading the fill-off-endpoint bucket as evidence of a partial inner run.**
  All 6 rows ran a FULL octave; the validator's replay bound ignored the family's
  octave shift. Read §3 before stating any endpoint off that diagnostic.
* **Running the never-QH emitters at `1RB1RD_1RC0LD_1LB0RA_1LC0LC`.** It is a
  quasihalter (§3c) and is now boarded as one. Its old `no gap-free two-form
  family` label was true and useless.
* **Looking for more quasihalters in the residue by widening `t`.**
  `sweep_qhbound_deep.py` reads `t` off each machine and gets **0 of 143**, with
  a positive control that reproduces the one row that did fire. The remaining
  residue is never-quasihalting candidates.
* **Sizing the bounded carrier at 39 rows.** 19 of the 39 needed no carrier —
  13 an alphabet, 6 a replay bound. The target is 26 nested arms (§4).
* Standing: WAVE31 §9, WAVE30 §8, WAVE29 §7, WAVE28 §4, WAVE27 §5, WAVE26 §6,
  WAVE25 §6, WAVE24 §7, WAVE18 §5, WAVE16 §5.

## 9. Standing lessons, paid again

* **MEASURE THE BUCKET — AND THE READER — BEFORE DESIGNING FOR IT.** Both items
  came back differently from how the prompt stated them, and in both cases the
  cheap measurement came first. Item (1)'s named deliverable was a Coq lemma;
  19 of its 39 rows wanted a Python argument and a loop bound. Item (2)'s named
  deliverable was a framing; the framing is impossible.
* **ASK WHETHER IT IS THE MACHINE OR THE PREDICATE — AND THE PREDICATE INCLUDES
  THE SEARCH SPACE.** Wave-30 asked it of the alphabet and found 51 rows read
  under an inverted one. Here the alphabet was right and *present in `ENCDATA`*;
  it was the LIST HANDED TO ONE CALL that was wrong. Both halves of a module
  should search the same space, and it is worth grepping for the ones that do
  not.
* **A CONTROL IS PART OF A MEASUREMENT.** "Not affine on 40 rows" is worth
  nothing without "affine on the 12 that boarded, at the laws they state". The
  control took one extra run and it is what makes §5a citable.
* **PUBLISH THE PROBE, NOT JUST THE NUMBER.** Every table above names a
  committed probe and a commit. Wave-30 §6d cost wave-31 a build for want of
  exactly that. This wave also adds `buckets.py`, so the row LISTS are
  regenerable too — `buckets31/` was assembled by hand and could be read but not
  re-derived.
* **PRINT THE DENOMINATOR.** §5d's first run measured nothing at all on half its
  rows and reported the same verdict as the correct run. It was caught only
  because the probe prints `anchors n/N`. A probe that states a verdict without
  stating how much it looked at cannot be checked — by the next wave, or by the
  one writing it.
* **A GATE LABEL SAYS WHERE AN EMITTER STOPPED, NOT WHAT THE MACHINE IS.** §3c:
  a row carried `no gap-free two-form family` for three waves. The label was
  true — it has no two-form family, because it is not a counter at all. Every
  emitter in `tools/counters/` assumes never-quasihalting, so none of them could
  ever have said so.
* **AND WHEN A SEARCH FINDS NOTHING, RUN THE POSITIVE CONTROL.** §3c's zero is
  only worth stating because the same sweep fires on the row that boarded.
* **RE-SWEEP AFTER THE CLOSEOUT REGEN, NOT JUST AFTER THE LAST WAVE.** §3b: the
  open list GREW by two when six boards landed, because boarding re-roots the
  shadow table. Wave-31 §7 got +2 the same way. Two waves running is not a
  coincidence — iterate until the list stops moving.

## 10. The gate table AFTER this wave — measured 2026-07-30 over the 143

`tailcert.py --list tools/closeout/core_rows.txt` (no `--emit`, so these are
`scan`'s FURTHEST-gate labels), at `5ffdebb`, 143 of the 144 open rows:

    0 / 143 fully derived

| n | furthest gate | vs WAVE31 §10 |
|--:|---|--:|
| 40 | `no interior j=S j chain at octave parity 0` | = |
| 29 | `no boot chain` | +9 |
| 25 | `no gap-free two-form family` | **−1** |
| 20 | `no inner family at pow2 j` | **−13** |
| 17 | `register step does not close` | = |
| 5 | `no exit chain` | +4 |
| 4 | `no interior j=0 chain at octave parity 0` | = |
| 2 | `no inner interior chain` | = |
| 1 | `no visit witness for state A at octave parity 0` | = |
| — | *inner fill lands off the endpoint* | **−6, all boarded** |

The deltas are exactly what §2 and §3 predict and nothing else moved: the 13 rows
the alphabet fix opened are the +9 and +4, and the 6-row fill-off bucket is gone
because those rows are now boards.

The one row that would not finish under `tailcert` within a 50-minute sweep —
`1RB1RD_1RC0LD_1LB0RA_1LC0LC`, far slower than the other 145; budget for it. A
later `--emit` pass did eventually complete it and confirmed wave-31's
`no gap-free two-form family`, but it needed no gate label in the end:
it is a QUASIHALTER and is now boarded as one (§3c). So the table above covers
**all 143** rows that remain open, with no carried entries.

The per-bucket row lists are under `tools/counters/buckets32/`, with
`GATETABLE.md` beside them, and they are now **regenerable**:
`tools/counters/buckets.py` splits a `tailcert --out` JSON into them.
`buckets31/` was assembled by hand.

> **The table in this section is the MID-wave state.**  §12 onward is the second
> half of wave-32 (item (1) proper, the bounded carrier), and it moves 23 of
> these rows.  `buckets32/` has been **regenerated at the end of the wave** and
> therefore matches §16, not this table — there is deliberately only ONE list on
> disk, so no next wave can read a stale one.  This table is reproducible with
> `tailcert --list tools/closeout/core_rows.txt` at `6202911`.

Boards are verified individually — each compiles and `Print Assumptions` is
checked — and the stage integration is checked structurally by `audit.py`, as in
previous waves; the 50 closeout stages are not recompiled (that is the whole
4,938-board build).

## 12. Item (1): the BOUNDED INNER CARRIER, proved — and it is 20 lines

`theories/Counters/NestedLapLift.v`, next to the twin it is named after:

    Lemma inner_to_add_lift : forall k v, k <= tovf v ->
      exists n, stepn tm n (lift (Cin v)) = Some (lift (Cin (Nat.iter k Pos.succ v))).

exactly as the prompt specced it — **plain induction on `k`**, side condition
`k <= tovf v` and nothing else, carried through the step by `JpCounter.tovf_succ`.
No per-`m` premise: `k` is exponential in the board's symbolic index (`2^(j-1)-1-c`
on the measured runs below), so `vm_compute` could not discharge one and the board
could not state it.

`Print Assumptions inner_to_add_lift` is `functional_extensionality_dep` only, and
`NestedLapLift.v` is confirmed OUTSIDE the census closure
(`census_cache.closure_v_files()`), so it is a legal home. `census_cache.py --check`
is MATCH at the unchanged hash `12362a25...e15d833f`.

**`Nat.iter`, not `Pos.iter`.** The prompt writes `Pos.iter Pos.succ v k`, and that
does not typecheck: `tovf : positive -> nat`, so `k <= tovf v` forces `k : nat`.
It would be the wrong iterate even so — Coq's `Pos.iter f x xH = f x` applies `f`
ONCE, so a `positive` count has no `k = 0`, and a plain induction needs exactly
that base case. `Nat.iter` is also the house spelling (`WaveCounter.anc`).

One helper was needed and is the converse of an existing lemma:

    Lemma tovf_allones_0 : forall v i, cview v = (i, None) -> tovf v = 0.

`JpCounter.tovf0_allones` runs the other way. The step case has to rule out the
all-ones anchor — the one place `Hin` says nothing — and the side condition rules
it out through `tovf`, so the implication is needed in this direction.

### 12a. The step, measured against the raw simulator

The standing move, paid: `1RB0LC_0RC1LD_1LB1RC_0LA0LB`, parity 1, `Ip` at
`oct = 1`, shape `half`.

| `p` | `j` | `v0` | `vend` | `k` | boot lands on `CinS` | `k=0` | `k=1` | `k=2` | full run |
|--:|--:|--:|--:|--:|:-:|:-:|:-:|:-:|:-:|
| 3 | 2 | 2 | 2 | 0 | yes | ok | ok | **no** | ok |
| 15 | 4 | 8 | 11 | 3 | yes | ok | ok | ok | ok |
| 63 | 6 | 32 | 47 | 15 | yes | ok | ok | ok | ok |

The `no` is the result, not a defect: at `p = 3`, `tovf 2 = 1`, so `k = 2`
violates `k <= tovf v` and the lemma does not claim that step. **The simulator
disagrees exactly where the side condition stops applying and agrees everywhere
inside it** — which is the sharpest evidence available that the premise is the
right one and is not doing less work than it looks.

## 13. The run is one of THREE shapes, and only one of them needed the lemma

`innerrun.py` over item (1)'s 33-row list, best key per arm (54 nested arms):

| n | shape | `lo` | `hi` |
|--:|---|---|---|
| 20 | offset | `2^m + c` | `2^(m+1) - 1` — **the fill** |
| 16 | HALF | `2^m + c` | `2^m + 2^(m-1) - 1` |
| 10 | FULL | `2^(K-1+o)` | `2^(K+o) - 1` — what `families` already takes |

**The offset shape needed no new mathematics at all.** `inner_to_fill_lift` runs
from ANY `v` to `fill v`, so an offset START was always in range; it was the
SEARCH that refused it, because `families` tests `vals == list(range(2^(K-1+o),
2^(K+o)))` and an offset start fails the first element. Half of the bucket was a
reader bug wearing a missing-lemma costume — the same lesson as §2, one wave
later and one gate deeper.

So `nestcert.bounded_runs` reports `(key5, lo, hi, shape)` with `shape` in
`{'fill','half'}`, and `shape` picks the lemma at render time. The in-octave test
is `lo.bit_length() == hi.bit_length()`, which is not a heuristic: `tovf v =
2^width(v) - 1 - v`, so "the run does not carry past the top of its octave" IS
`k <= tovf v0`. **A key the search accepts is a key whose Coq side condition is
discharged by construction.**

Runs that are in-octave but end at neither the fill nor the half are REFUSED —
82 accepted against 66 refused. That is the reader being honest: `hi = 159 =
2^7 + 2^5 - 1` has endpoint word `rep uS 5 ++ uD ++ uD ++ so`, TWO zero blocks,
and how many there are at a general `j` is not something one octave's reading can
say. Both accepted shapes were checked to reproduce at two consecutive octaves on
the same arm (`65..95` at `m=6` and `129..191` at `m=7`), which is what makes
their `j`-law a law rather than a coincidence.

Verification that the symbolic endpoints denote the right words: every accepted
candidate's `CinS`/`CinE` was instantiated at the concrete `j` and compared with
`ENC[name](lo)` / `ENC[name](hi)` — **164 match, 0 mismatch**.

## 14. What actually binds is the INDEX-SHIFT TRAP, not the carrier

`sden_parts` folds an sside's constant count into its prefix as `pre + u * b`, so
**`b` must be >= 0** — a negative one silently denotes a DIFFERENT word instead of
failing. The bounded endpoints' counts are

    start   j + oct - width(c)          end (half)   j + oct - 1

so an offset needs `oct >= width(c)` and a half endpoint needs `oct >= 1`. That is
wave-29's index-shift trap (`pow2 j + 1`, count `j - 1`, measured 0/12) in its
general form, and it is the binding constraint on this route — not the lemma,
which took an afternoon.

`nestcert.bounded_endpoints` returns None rather than a template when the count is
not an sside, and `_nested_ovf` files the row `inner run is not an sside at this
octave`. Buying the headroom means peeling the OUTER index (`j = S j'`, as
`derive_offset` does), which restates the whole arm — boot, interior, exit and the
visit bullets — and is **not** done here. 2 rows end the wave filed there.

## 15. `_nested_ovf` reported the LAST candidate's blocker, not the furthest

Found by the before/after diff, and worth recording because it is a measurement
artefact that would have been published as a result. `_nested_ovf` enumerates
candidate keys and overwrites `last` on each failure, so the reported gate was
whichever key happened to be tried last. With only full-octave keys that rarely
bit; appending bounded candidates — which fail EARLY and in bulk — moved 6 rows
from `no boot chain` to `inner run is not an sside` and one from `no inner
interior chain` to `no boot chain`, i.e. **BACKWARDS, purely because the search
got wider**.

Fixed by ranking the failures and raising the furthest (`max(fails, key=_rank)`),
and `inner run is not an sside` is placed in `_RANK` between `no inner family at
pow2 j` and `no boot chain` — a family WAS found and only its index shift is
unstatable. After the fix the same sweep reports **0 rows whose furthest gate went
backwards**, and the `not an sside` bucket is 2 rather than 8.

## 16. The gate table AFTER item (1) — BEFORE at `6202911`, AFTER at `85f3c37`

`tailcert.py --list tools/closeout/core_rows.txt`, 143 open core rows, no `--emit`:

    0 / 143 fully derived        (both sides)

| n before | n after | furthest gate | Δ |
|--:|--:|---|--:|
| 40 | 40 | `no interior j=S j chain at octave parity 0` | = |
| 29 | 26 | `no boot chain` | **−3** |
| 25 | 25 | `no gap-free two-form family` | = |
| 20 | **4** | `no inner family at pow2 j` | **−16** |
| 17 | 17 | `register step does not close` | = |
| 2 | **17** | `no inner interior chain` | **+15** |
| 5 | 5 | `no exit chain` | = |
| 4 | 4 | `no interior j=0 chain at octave parity 0` | = |
| 1 | 2 | `no visit witness for state A at octave parity 0` | +1 |
| — | 2 | `inner run is not an sside at this octave` | **new** |
| — | 1 | `no visit witness for state D at octave parity 1` | **new** |

**23 rows move, 0 board**, and 0 regress. That is the third wave running in which
opening a gate moves rows and boards none (wave-31 §8b moved 30 and boarded 0;
§2 of this document moved 13 and boarded 0), and it was predicted in the prompt.
The BEFORE column reproduces §10's table exactly, re-measured at `6202911`.

Where the 16 rows that left `no inner family` went: 8 to `no inner interior
chain`, 4 to `no boot chain`, 2 to `not an sside`, 2 to a visit witness.

### 16a. The two rows one gate from boarding are blocked on the FLAT arm

`1RB0LC_0RC1LD_1LB1RC_0LA0LB` (state A) and `1RB1LA_0LA1RC_0RD0RB_1LB0RA`
(state D) get **past `validate`** — the bounded run replays against the raw
simulator at every anchor — and stop at `visits`. Measured: on both, the failing
parity is the **FLAT** arm, not the nested one, and the state fires in neither the
boot prefix nor the exit prefix nor an inner lap. `visits` has no fallback for a
flat arm at all (a nested one has `vis_via_fill`). That is a pre-existing gap
newly exposed because the OTHER parity now derives, it is not what item (1) is
for, and per the prompt it is filed rather than chased.

## 17. The A/B, which this time had something to disturb — and did not

Wave-31's A/B came back clean because it touched nothing shared; §6's likewise.
This one changes `nestcert`, which `regcert` calls, so it is the first A/B this
track has run that could genuinely move committed boards.

Both harnesses, pristine worktree at `6202911` vs the patched tree:

| harness | boards | result |
|---|--:|---|
| `rerender_check.py` (LAPC/NLAP/PEEL/LAPQ) | 870 | **byte-identical** |
| `rerender_tail.py` (REG_*) | 12 | **byte-identical** |

It came back clean for a reason that was designed in rather than hoped for:
**`families` is not changed**. Its body was refactored onto the `_gather` helper
that already existed beside it, and the bounded search is a separate function only
`tailcert` calls. The refactor was checked to be behaviour-preserving directly —
old body vs new over 7,200 comparisons (300 random `mid` phases × both alphabet
lists × K ∈ {4,5,6,7} × maxoct ∈ {0,1,2}), **0 differences** — and the full-octave
route in `_nested_ovf` still goes through `nestcert.endpoints` on the identical
call, so a board that derived before derives by the same code path.

Note for the next wave: `rerender_check.py` reports ~800 of 870 boards as
DIFFERING from the tree. That is the known baseline noise the prompt warns about
and is why this is an A/B; the literal test cannot pass.

## 18. What is in the tree, and what is deliberately NOT

In:

* `NestedLapLift.inner_to_add_lift` and `tovf_allones_0` (funext-only);
* `nestcert.bounded_runs` / `bounded_endpoints`, and `families` refactored onto
  `_gather` with its behaviour unchanged;
* `tailcert._nested_ovf` on the bounded search, `validate` replaying to the
  measured endpoint rather than to the fill, and the furthest-gate fix;
* `buckets32/` regenerated at this commit, matching §16.

Deliberately not:

* **the bounded RENDER template.** No row derives, so there is nothing to render
  and nothing to compile; writing the template would be writing untested Coq
  emission. `render` instead **refuses a bounded arm loudly** — otherwise it would
  silently emit the `inner_to_fill_lift` template for a run that does not reach
  the fill, producing a wrong board whose `coqc` failure looks like an ordinary
  derivation failure and gets the file deleted;
* **`vis_via_add`**, the bounded twin of `vis_via_fill`. It is the piece the next
  wave needs the moment a bounded row boards and needs an exit-chain witness, and
  it is a five-line copy of `vis_via_fill` with `inner_to_add_lift` in place of
  `inner_to_fill_lift` — but nothing exercises it today.

## 19. DO NOT RETRY (measured, this half of the wave)

* **The bounded inner carrier as a way to BOARD rows.** 0 of the 16 it opens.
  It is built, proved and committed; do not rebuild it, and do not expect boards
  from opening a gate. Three waves, three times, ~60 rows.
* **A bounded family whose count needs `b < 0`.** Not a search-space question and
  not a lemma question — `sden_parts` cannot spell it. The only route is peeling
  the outer index, and that is an arm-wide restatement (§14).
* **Reading a bounded endpoint's `j`-law off ONE octave.** 66 of the 148
  in-octave runs end somewhere with no law a single reading can determine. Check
  two consecutive octaves on the same arm before believing a shape.

## 20. Standing lessons, paid again

* **MEASURE THE BUCKET BEFORE DESIGNING FOR IT** — and the measurement said the
  prompt's own framing was half wrong: 20 of 39 arms needed no new mathematics,
  only a search that would look at them. The lemma the prompt asked for was
  correct and necessary; the *size* it was asked for was not.
* **AND MEASURE IT AT A COMMIT.** The BEFORE table here was re-measured rather
  than copied from §10, and that is what caught §15.
* **A SOUNDNESS ARGUMENT IS A MEASUREMENT** (§12a), and the boundary case is
  worth more than the passing ones.
* **SWEEP AFTER, NOT BEFORE.** §15 exists only because the sweep was diffed
  per-row instead of by bucket totals. The totals looked fine.

### A note on the prompt's reading list

`docs/LADDER_PLAN.md` does not exist in this tree and never has — there is no
`§4b` anywhere under `docs/`. The nearest documents are `docs/RULE_LADDER.md`
(sections 0–7, no 4b) and `docs/NESTED_LAP_PLAN.md` (§4 is "Risks, honestly",
with no subsections). The substantive specification for item (1) is
`WAVE32_PROMPT.md` §(1) plus `WAVE29_REGISTER_FINDINGS.md` §5d, both of which
exist and were followed.

## 11. What the next wave should build

`docs/WAVE33_PROMPT.md`.
