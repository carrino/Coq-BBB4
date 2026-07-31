# The fifteen `no value family` rows, measured

_Branch `claude/fifteen-nofam-measurement-iuw18b`, cut from `main` at `28e27ab`
(PR #88 merged).  Tool: `tools/ladder/nofam.py` (new).  Data:
`tools/ladder/nofam15.jsonl`, `tools/ladder/nofam15.log`, row list
`tools/ladder/nofam15_rows.txt`.  `tools/ladder/valfam.py` was imported and
not edited.  No Coq.  This is a measurement and a taxonomy; nothing here is a
fix and nothing here carries proof weight._

The fifteen are the rows of `tools/closeout/core_rows.txt` (the live core of
62) that are unclosed in BOTH `core143_ph.jsonl` and `core143_gray.jsonl`
with the reason string

    no value family: no anchor whose counter side decodes over
    ladder-named digits with +1 steps

(the other 14 unclosed live-core rows split 11 `families found but none
closed` / 3 `time cap`).

## The gate, first

LADDER_PLAN §4g's kill criterion for this session was: **fewer than four of
the fifteen showing a monotone reading under some (base, code, step,
terminator) the current search does not try** means the ladder's ceiling is
real and the rest is wave work.

**Twelve of the fifteen show one.**  The gate is cleared by a factor of three,
and §4g's closing line holds for the fifth time: `no value family` is a label
that records how a search failed, not a property of the machines.

The one that decides it is not close.  On `1RB---_0LB1RC_1LB0RD_1LC0RD`, at
anchor `B1/R`, terminator `11`, step `+1`, digit width 1, **constant far side
over all 900 anchor visits, zero visits skipped**, the counter side reads

* under the weights the search assumes, `w_i = 2^i`: **0** width classes read;
* under the weights the machine states, `w_i = 1, 1, 2, 3, 5, 8, …`: **10** of
  10 width classes read exactly, the largest of them 290 consecutive values.

Every axis except one is held fixed between those two lines.  The axis that
moves is the numeration's weight sequence, and it is the only thing between
this row and a family.

## The counts

Of fifteen rows:

| | rows |
|---|---:|
| a monotone reading exists at some anchor | **12** |
| — numeration is NOT `w_i = b^i` (needs a constructor the search lacks) | **9** |
| — numeration IS base-`b`; the search cannot reach the reading for other reasons | **3** |
| no monotone reading found at any anchor | **3** |
| — counter-side width classes grow LINEARLY: not a counter, wave-route shape | **2** |
| — sub-geometric and irregular: unresolved | **1** |
| RULE_LADDER §6's tail (shape set infinite under every finite abstraction) | **0** |

Breaking the nine down by which numeration:

| numeration | weights | rows |
|---|---|---:|
| Fibonacci | `1, 1, 2, 3, 5, 8, …` | **6** |
| redundant base-`b` over cell PAIRS | `1, 1, 2, 2, 4, 4` and `1, 1, 3, 3, 9, 9` | **2** |
| binomial (combinadic) — not a weight sequence at all | `C(p_j, j+1)` | **1** |

The far side, at the anchor carrying the best reading: constant 5, second
counter 6, bounded oscillation 2, template 1, no reading 1.

The anchor is wrong on **0** of fifteen (see below).

## Per row

`ex` = width classes read exactly (distinct values in first-appearance order
form an arithmetic progression of difference `step`); `big` = largest such
class; `gap` = largest number of anchor visits skipped between two family
members.  `tl=*` means the reading needs a SET of terminators (§4f's phases),
`tl=-` none.

| spec | verdict | anchor | reading | ex/big | gap | far side |
|---|---|---|---|---|---:|---|
| `0RB0RD_1LC1RB_1RA0LC_1LB0LC` | base-`b`, search cannot reach it | D0/R | base-2, l=1, tl=`*`, +1 | 16/20 | 1 | second counter |
| `0RB0RD_1LC1RB_1RA0LC_1LD0LC` | base-`b`, search cannot reach it | A1/R | base-2, l=1, tl=`*`, +2 | 15/20 | 1 | template |
| `0RB1LC_1LC0RD_1RD0LC_1LA1RB` | base-`b`, search cannot reach it | A0/L | base-2, l=2, tl=`0011`, +1 | 5/54 | 5 | second counter |
| `0RB1LC_1LC1RD_1LA0LC_0RD1RB` | NUMERATION | A0/L | weights `1,1,2,2,4,4`, tl=`01`, +1 | 9/64 | 2 | second counter |
| `1RB---_0LB1RC_1LB0RD_1LC0RD` | NUMERATION | B1/R | **fibonacci**, tl=`11`, +1 | 10/290 | 0 | constant |
| `1RB---_0LB1RC_1LD0RC_1LB1RC` | NUMERATION | B1/R | **fibonacci**, p=1, tl=`11`, +1 | 10/290 | 0 | constant |
| `1RB---_1LC0RB_1LD1RB_0LD1RB` | NUMERATION | D1/R | **fibonacci**, p=1, tl=`11`, +1 | 10/291 | 0 | constant |
| `1RB---_1LC0RD_0LC1RB_1LB0RD` | NUMERATION | C1/R | **fibonacci**, tl=`11`, +1 | 10/291 | 0 | constant |
| `1RB---_1LC1RD_0LC1RD_1LB0RD` | NUMERATION | B1/R | **fibonacci**, p=2, tl=`11`, +1 | 10/291 | 0 | constant |
| `1RB0RB_0LC1RD_1LC1LA_0LA1RB` | NUMERATION | A1/L | **fibonacci**, p=1, tl=`*`, +1 | 20/34 | 7 | second counter |
| `1RB0RB_1LC0RC_1RA0LD_0LB0LC` | unresolved | — | best is 1 class of 4 | 1/4 | 0 | second counter |
| `1RB0RB_1LC1LD_0LC1RA_0LD0RA` | NUMERATION (binomial) | B1/L | **combinadic**, key `(width, popcount)` | 33/121 | — | popcount register |
| `1RB1LB_1LC0RD_0LB1LA_0LA1RA` | not a counter | — | classes grow ~`n/4` | 0/0 | — | second counter |
| `1RB1LD_1RC1RB_1LC1LA_0RC0RD` | not a counter | — | classes grow ~`2n/3` | 0/0 | — | template |
| `1RB1RC_1LA0LB_1LD0RD_1LB0RC` | NUMERATION | B0/R | weights `1,1,3,3,9,9`, tl=`1`, +1 | 7/243 | 6 | bounded oscillation |

(`1RB0RB_1LC1LD_0LC1RA_0LD0RA`'s binomial figures in the table are the
4000-visit ones; the 900-visit canonical run gives 21 classes read exactly,
largest 36.  Every other figure in the table is from the canonical run.)

## Is the far side the obstacle?

On the six rows whose best anchor carries a `second counter` far side, and on
the two `bounded oscillation` ones, the far side is doing something — but it
is not what stops the reading, because the reading was obtained anyway by
measuring the counter side on its own.  The two facts worth keeping:

* **`second counter` (6 rows).**  The far side's own successor is a function
  of it: it is a register, not noise.  On `1RB0RB_1LC1LD_0LC1RA_0LD0RA` it is
  exactly `1^(popcount − 2)` — the second parameter of the binomial reading,
  spelled on the tape.  These rows need `E(p, v)` in the honest sense: two
  quantities, not one quantity plus a template.
* **`unbounded and independent`: 0 rows at the best anchor.**  Every far side
  measured is a register, a template, a bounded oscillation, or constant.
  Nothing in the fifteen has a far side that just grows without structure.

Five of the fifteen have a **constant** far side over every single anchor
visit at the best anchor.  For those, `far side varies` was never the story at
all — which is worth saying plainly, because that is the bucket §4e built the
run template `word^(a·p + b)` for and these rows are not in it.

## Is the anchor wrong?

No, on all fifteen.  Measured three ways (`successor_test`, `anchor_probe`):

* at the best plain `(state, head)` anchor, the fraction of counter-side
  strings with a UNIQUE successor is ≥ 0.91 on every row and 1.00 on
  fourteen;
* refining the anchor to `(state, head, one cell of context each side)` adds
  nothing: the same number, 1.00 on fourteen and 0.91 on the fifteenth;
* the `record` anchor — the visit at which the head reaches a cell it has
  never reached — is either as good (0.99–1.00, seven rows) or has too few
  visits to matter (eight rows, 14–20 record visits each).

So the recurring configuration these machines have IS a `(state, head)` visit.
`find_families` is looking in the right place.

## Is this row a counter?

The question RULE_LADDER §6 asks is whether the reachable shape set is
infinite under every finite abstraction.  The fingerprint is the number of
DISTINCT counter-side strings per width, measured over 4000 anchor visits:

| spec | classes by width | verdict |
|---|---|---|
| the six fibonacci rows | `1 1 2 3 5 8 13 21 34 …` (ratio 1.618) | counter, Fibonacci rank |
| `1RB0RB_1LC1LD_0LC1RA_0LD0RA` | `1 3 7 15 31 63 …` = `2^n − 1` | counter, every string of every popcount |
| `1RB1RC_1LA0LB_1LD0RD_1LB0RC` | `1 1 1 3 3 9 9 27 …` (ratio 3) | counter, base 3 |
| `1RB0RB_1LC0RC_1RA0LD_0LB0LC` | `1 1 2 3 6 8 9 12 10 13 14 15 21 22` | sub-geometric, irregular — unresolved |
| `1RB1LB_1LC0RD_0LB1LA_0LA1RA` | `1 1 1 1 2 2 2 2 3 3 3 3 4 4` ≈ `n/4` | **not a counter** |
| `1RB1LD_1RC1RB_1LC1LA_0RC0RD` | `1 2 2 3 4 4 5 6 6 7 8 8 9 10` ≈ `2n/3` | **not a counter** |

**Nothing in the fifteen is §6's tail.**  The two rows with no reading have
the SMALLEST shape sets in the set, not the largest: a linear number of shapes
per width is a bouncer's fingerprint, not a Collatz-like machine's.  They do
not belong to nobody — they belong to the wave route, and the ladder route
should stop counting them against itself.  The third unread row
(`1RB0RB_1LC0RC_1RA0LD_0LB0LC`) is sub-geometric too; it is the one row this
session did not resolve either way.

## The fifth constructor, named

**`Fam.weights`: the numeration's WEIGHT SEQUENCE, inferred, not assumed.**

*What it parameterizes.*  `Fam.decode` computes `v = Σ d_i · b^i`.  Replace
`b^i` by an inferred non-decreasing positive integer sequence `w_0 ≤ w_1 ≤ …`
so the value is `v = Σ d_i · w_i`.  `base-b` is `w_i = b^i` and stays exactly
what it is today; the six Fibonacci rows are `w_i = F_{i+1} = 1, 1, 2, 3, 5,
8, …`; two more rows are `w_i = 1, 1, 2, 2, 4, 4` and `1, 1, 3, 3, 9, 9`,
which is base `b` over two-cell digits with a redundant sum encoding — the
same generalization, reached from the other side.

*How it is read off the machine.*  `nofam.fit_weights`: inside a width class,
take the distinct strings in order of FIRST APPEARANCE and require
`Σ (d' − d)·w = 1` between consecutive ranks.  Exact rational Gaussian
elimination, equations added greedily, contradictions counted rather than
averaged away.  Differences and not absolute ranks because a class whose top
digit is pinned carries a per-width offset, and fitting the rank absolutely
would have to solve it away by setting the top weight to zero.  This is the
same move §4e made for the fill law, §4f for the terminator and §4g for the
code: read it, do not assume it.

*Which rows it buys.*  **8 of the 15 directly** (6 fibonacci + 2 redundant).
On **2** of those 8 — `1RB---_0LB1RC_1LB0RD_1LC0RD` and
`1RB---_1LC0RD_0LC1RB_1LB0RD` — it is the ONLY thing missing: constant far
side over every anchor visit, zero visits skipped, step 1, one terminator,
prefix 0, digits the ladder names.  On **3** more it is the weight sequence
plus the near-head prefix of fix 3 below, and on the remaining 3 it is the
weight sequence plus the terminator set of fix 4.

It is also what `numsys.py` has been reporting since §4e without a reader
attached: the six rows this measurement calls `fibonacci` are exactly the six
labelled `FIBONACCI` in `numsys_core143.txt`, from a completely independent
statistic (class sizes, no decoding at all).  Two tools that share no code
agree on the same six machines.

*What it costs as a `Fam` field.*

* `Fam.weights: tuple[int]`, beside `code` and `step`; `Fam.b` stays the digit
  alphabet size.  `key()` gains one component.  `decode` becomes a dot
  product — free.
* `next_ds`/`succ` are already stated on the VALUE (§4g did that), so they go
  through `of_value(v + step)` unchanged.  The top of an octave is already
  tested by value; it becomes `Σ (b−1)·w_i` instead of `b^p − 1`.
* **The real cost is `of_value`.**  For `b^i` the encoder is division.  For a
  general weight sequence the representation is not unique (Fibonacci: `1100`
  and `0100` are both 2) and the machine uses ONE canonical form, so
  `of_value` has to produce the machine's canonical string, not any string
  with the right value.  Two ways, both bounded: index the width class
  enumerated from the observed walk (`all_strings`/`sample_digits` already
  enumerate at the widths the arms are mined at, and `numsys.py`'s class-size
  fingerprint is exactly the guard that the enumeration is complete); or infer
  the canonical form as a forbidden-factor set — Zeckendorf is "no `11`",
  which is a regular language and is *why* the class sizes are Fibonacci.
  The second is the one that generalizes and the one that will need a lemma
  on the Coq side; the first is enough to measure with.
* `repair` already goes through `of_value` since §4g's fix, so it inherits
  this for free — and that same §4g note is the warning: the positional
  rebuild bug it fixed is exactly the bug a weight sequence would reintroduce
  anywhere `of_value` is bypassed.
* `all_strings`/`reach` must enumerate CANONICAL strings, or `cover` will
  report uncovered members that the machine never reaches.
* Stage B: the kernel's `CTR` decode is a fold, so a weight list is no harder
  than a base.  The canonicalization is the part that needs a theorem.

*What it does NOT buy.*  Three rows read as base-2 already (see below), two
rows are not counters, one is unresolved, and one needs something else:

**A sixth thing the data names, and it is not a weight sequence.**
`1RB0RB_1LC1LD_0LC1RA_0LD0RA` takes, for each width `n` and each popcount `k`,
every one of the `C(n−1, k−1)` strings, and walks each popcount class in colex
order — 33 classes read exactly, largest 121 consecutive values
(`nofam.binomial_probe`).  That is the **binomial (combinadic) number
system**: the value of a string is `Σ_j C(p_j, j+1)` over the positions `p_j`
of its set cells, and the weight of a set cell depends on its RANK among the
set cells, not on its position alone.  No `w_i` can say that.  The popcount is
the second parameter and it is spelled on the far side as `1^(k−2)`, which is
why the same row also reads as `far side is a second counter`.  Stated
precisely so it is not confused with the fifth constructor; **one row, and not
worth a field until something else joins it.**

## Four things in `valfam.py`, written down and NOT changed

A ladder-closure session is running concurrently and `valfam.py` was
read-only.  Each of these was reached from a row above.

1. **`find_families:960` — the far-side TEMPLATE pass is gated off exactly
   where it is needed.**  `if pop and pop.most_common(1)[0][1] >= min_chain:
   continue` switches the pass off whenever ANY constant-far-side group
   reaches the chain threshold.  On `0RB0RD_1LC1RB_1RA0LC_1LB0LC` at `D0/R`
   the members are the visits whose far side is `0·1^p` — every one distinct,
   so every constant group is tiny — while the mid-flight visits share a
   constant far side `011` 179 times over.  The large group is the one that is
   NOT the family, and it is what turns the pass off.  §4e's own text says the
   pass is for "the case where every constant-far-side group falls under the
   chain threshold"; that condition is too strong.
2. **The template pass cannot use §4g's two axes.**  Inside it, `_try_parse`
   is called without `code=` or `step=`, so a two-parameter family is
   `binary`/`+1` only.  `0RB0RD_1LC1RB_1RA0LC_1LD0LC` reads at `+2`.
3. **`p in range(l)`: a one-cell digit never gets a near-head prefix.**  Both
   discovery passes and `probe_families` iterate the prefix inside the digit
   width, so `l = 1` means `p = 0` always.  A machine whose lowest cell is a
   phase bit rather than a digit — §4g's own description of why the step can
   be 2 — is a one-cell-digit family at `p = 1`, and three of the readings
   above need exactly that (`1RB---_0LB1RC_1LD0RC_1LB1RC` at `p=1`,
   `1RB---_1LC0RB_1LD1RB_0LD1RB` at `p=1`,
   `1RB---_1LC1RD_0LC1RD_1LB0RD` at `p=2`).
4. **The terminator is the common suffix of one constant-far-side group.**  On
   rows with no such group `_common_suffix` is computed over a set with no
   common structure.  Three readings above need a terminator taken off the
   whole walk, and two need a SET of them (§4f's phases) BEFORE a family
   exists — `fit_phases` runs after, on a family already found.

None of these four is the fifth constructor.  Together they are what stands
between the three base-2 rows in the table and a family, and they would have
to be fixed for the weight sequence to reach the three non-constant-far-side
rows that need it.

## What this says about the next session

* The weight sequence is worth **8 of 15** here and is the fifth instance of
  §4e's rule.  It is the one thing to build.
* The two `not a counter` rows should be handed to the wave route and removed
  from the ladder's denominator.  The ladder's ceiling on the live core is
  38 of 62 with fifteen `no value family`; on this measurement at most
  **two** of those fifteen are genuinely the ladder's ceiling, and neither is
  RULE_LADDER §6's tail.
* `1RB0RB_1LC0RC_1RA0LD_0LB0LC` is the one row this session did not resolve.
  Its counter-side classes grow sub-geometrically and irregularly and its far
  side is a register at 12 of 16 anchor-sides; it may be a two-register
  machine whose two registers were never separated.

## Reproducing

```sh
cd tools/ladder
python3 nofam.py nofam15_rows.txt --visits 900 --json nofam15.jsonl
```

~9 minutes, no Coq, no network.  `nofam15_rows.txt` is reproducible by
intersecting `tools/closeout/core_rows.txt` with the rows of
`core143_ph.jsonl` and `core143_gray.jsonl` that are unclosed with reason
`no value family` in both.

`nofam.py` reads `valfam.py` for the walk (`raw_anchor_visits`), the run/cell
helpers and `gray_decode`, and for nothing else; it writes nothing that
`valfam.py` reads.
