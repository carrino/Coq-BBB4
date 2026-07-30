# Wave-31: the two-form board renderer — 14 boards, and the framing is the point

Branch `claude/wave31-prompt-residue-ec2clt`, cut from `main` at `dc0adbc`.
Item (0) merged as #73; §7–§11 below are the second batch on the same branch,
restarted from `f4467cc`.

## 1. The one-line result

    4,916 of the frozen 5,156 settled  ->  4,930   (95.3% -> 95.6%)
    162 core undecided + 78 0RB shadows ->  150 core + 76 shadows

**+14 boards** (12 from item (0), 2 more the old input list had missed), item (1)
built and **measured to reach 30 of 74 rows rather than all of them**, and item
(4) measured **dead at 0 of 11**.  Every number in this document was measured on
**2026-07-30** against the residue at `f4467cc`; see §11 on why that date matters.

§2–§6 are item (0), which is where 12 of the 14 came from:
`tools/counters/tailcert.py`
derived, validated and could not write down twelve certificates.  It can now.
Every one of the twelve compiles and `Print Assumptions nqh_<ID>` is
`functional_extensionality_dep` only.  Nothing under `theories/` changed —
`census_cache.py --check` is still **MATCH** (hash
`12362a25…e15d833f`), and no library file was touched, so no board outside the
twelve was recompiled.

| n | alphabet | overflow arm | validation |
|--:|---|---|---|
| 6 | `Alph_00_01_1` | FLAT — 0 nested overflows | 192 anchors |
| 6 | `Alph_10_11_11` | nested — 4 nested overflows, 56 inner laps | 192 anchors |

The list is `tools/counters/tailcert_derived12.txt`; the boards are
`theories/Machines/Counters/REG_<ID>.v`.

## 2. The renderer

`tailcert.py`'s docstring advertised `--emit` and `main()` never implemented it:
`PREFIX`, `OUTDIR` and the imports of `coqc` and `mirrorize` were all present and
unused.  What is new is `render` / `process` / `visz` and the templates above
them — about 400 lines, no new Coq.

It is regcert's piecewise-`Cc` renderer with the register dimension taken out
and the two-form one put in.  The board states

    Cc p = if podd p then (st1, (E p ++ tl1, S0, fr1))
                     else (st0, (E p ++ tl0, S0, fr0))

with `RegGlue.podd` the octave parity, and closes in `lift` space throughout
(`LapCertGlueLift.glue_neverqh_lift` + `vis_via_ovf_lift`), so an exact landing
and a landing one blank past the anchor take the same template.  There is no
`virt`, so `SkipGlue` is not imported at all.

Three structural differences from `regcert`, and each one cost a design decision:

### 2a. The interior branch is a SPLIT, per parity — four chains

`emit_lapcert.GLUE_SPLIT` is the shape of each half (`j = 0` concrete; `j = S j'`
with one unit copy peeled into the chain's prefix), but it is one arm, not two.
The per-parity pair is `gz@B@`/`gp@B@`/`lapi@B@` with a `lapi_` dispatch on
`podd p`, and the destination frame is the SAME parity — `RegGlue.podd_succ_int`.

Order matters in the glue: rewrite `podd_succ_int` **before** `podd p = b`.
Rewriting `Hb` first turns `podd p` into a literal and leaves
`podd (Pos.succ p)` — a different term — untouched, and the `if` on the
successor's side never reduces.

### 2b. The overflow arm crosses parities, and is one peel deeper

`_derive` states it as

    B0 = (st[b],  (uS, uS, 1, 0, soS ++ tl[b]),  S0, far[b])
    B1 = (st[nb], ((), uD, 1, 2, soD ++ tl[nb]), S0, far[nb])

Destination state `st[nb]`, destination frame `far[nb]` — `podd_succ_fill` flips
the parity and `cbn [negb]` selects the other branch of `Cc`.  The count `1*j+2`
on the landing (against the flat route's `1*j+1`) is the extra peel: with
`cview p = (S j, None)` giving `E p = rep uS j ++ soS`, a source that carries a
unit copy in its prefix forces `j = S j'`, so the branch is stated at

    cview p = (S (S j''), None)

and the chain index is `j''`.  That framing is why these rows derive here and
not through `emit_lapcert.derive`, which fails at `no overflow chain` on both
parities.

### 2c. The peel's leftover is `p = 1`, and it is NOT symmetric between `lap` and `vis`

`cview p = (S 0, None)` is `p = 1` (`IXPGadgets.cview_none_shape`).  In `lap_`
the case is **refuted**, not proved: the lap is only required for `p0 <= p` and
`p0 >= 8`, so `rewrite (cview_none_shape p 0 E) in Hp; apply Hp; vm_compute`
closes it.

`vis_` cannot do that.  `LapCertGlueLift.vis_via_ovf_lift`'s premise ranges over
**every** overflow anchor with no `p0` bound — its own conclusion is unbounded in
`p`, which is what makes it usable at all — so `p = 1` needs a real witness for
each of the four states.  `Cc 1` is concrete, so the witness is one
`vm_compute` run per state (`visz`, the same device as
`emit_lapcert.VISZ_LEMMA`).

Measured before writing the template, on all 12: every state is reached from
`Cc 1` within 12 steps (max 12, median 2).  Had any state been missing there,
the arm would have needed `vis_via_int_lift` instead — worth recording, because
the interior split's `j = 0` half covers every interior anchor uniformly and has
no leftover case at all.

## 3. The 12 rows are SINGLE-form, and that is the useful finding

Measured on all twelve: `st[0] == st[1]`, `tl[0] == tl[1] == []`, and
`fr[0] == fr[1]`.  `two_form` returns them as a two-form family only because a
single key covers `8..255` on its own and the reader assigns the same frame to
both parities (`two_form`, the `a == b` branch).

So **the frame split is not what boards these rows** — the OVERFLOW FRAMING is.
The rows are plain counters with a split interior and an overflow arm stated one
peel deeper than `emit_lapcert`'s, and two of them
(`1RB0RD_0RC0LD_1LD1RC_0LA1LB`, `1RB1LA_0RC1RD_1LD0LB_0LA0RB`) are exactly the
rows wave-30 §3a filed as blocked on the overflow branch through the FLAT route.

Consequence for the next wave: the emitted `Cc` has two syntactically identical
branches on all twelve.  That is honest — the renderer is general and the
genuinely two-form rows in the residue will use it — but it means these boards
are **not** evidence that the per-parity frame machinery is exercised.  The first
row whose `two_form` returns `a != b` will be.

## 4. What is in the tree

* `tools/counters/tailcert.py` — `render`, `process`, `visz`, the templates, and
  `--emit` / `--force` in `main()`.  Everything else in the file is untouched:
  the reader, `_derive`, `validate`, `visits`, `boot` and `scan` are wave-30's.
* `theories/Machines/Counters/REG_<ID>.v` × 12 (× 14 after §7).
* the regenerated closeout tables (`_CoqProject`, `theories/Closeout/*`,
  `tools/closeout/*`), from the standard four-command batch.

Nothing under `theories/Counters/` or `theories/Checkers/`.

## 5. Reproducing

    apt-get install -y coq && coq_makefile -f _CoqProject -o Makefile.coq
    make -f Makefile.coq $(ls theories/Counters/*.v theories/Checkers/*.v \
      | sed 's/\.v$/.vo/' | tr '\n' ' ')
    python3 tools/counters/tailcert.py --list tools/counters/tailcert_derived12.txt
    python3 tools/counters/tailcert.py --list tools/counters/tailcert_derived12.txt --emit

The first run reports `12 / 12 fully derived`, the second `12 / 12 boarded`.
`--emit` skips a row whose board file already exists; pass `--force` to
re-render.

## 6. Standing lessons, paid again

* **MEASURE BEFORE DESIGNING.**  Two measurements shaped this build before a
  line of Coq was written: the `Cc 1` state reachability (§2c), which chose the
  visit route, and the frame degeneracy (§3), which says what these boards do
  and do not demonstrate.
* **READ THE INDEX OFF THE DERIVATION.**  `_derive`'s `1*j+2` and `validate`'s
  `j - 2` are the same statement; taking the peel depth from either one and not
  cross-checking against the alphabet's `cview_none_*` is how a template ends up
  one `S` out.
* **A `p0` BOUND IS NOT INHERITED.**  `lap` has one and `vis` does not, because
  the glue lemma that chains the visits is unbounded by construction.  Reading
  `vis`'s obligation off `lap`'s would have produced a template that cannot
  close.

---

# Second batch: items (1) and (4), and a reproducibility failure in wave-30

## 7. +2 boards the old input list had missed

`tools/counters/tailcert_derived12.txt` was measured against the then-current
162-row list.  Re-running `tailcert --list` over the **current** open core rows
finds **14**, not 12:

    0RB0LC_1LC1RB_0LD1LA_1RA0RC   Alph_10_11_11, mirrored
    0RB1RC_1LC0LA_0LD0RA_1RA1LD   Alph_10_11_11, direct

Both are nested arms (192 anchors, 4 nested overflows, 56 inner laps each) and
both board unchanged through the renderer.  No emitter change was needed; the
only thing wrong was the input list.  `4,928 -> 4,930`, core `152 -> 150`.

**Standing move paid again:** after any change to a reader, re-run the sweep over
the CURRENT open list, not over the list the last wave left behind.

## 8. Item (1): the `lift` fallback reaches 30 of 74, and 44 are the machine

`_derive` required the reached configuration to equal the interior split's target
syntactically.  `_int_chain` now tries exact first and falls back to `lift`.

Measured over the 126 open rows that have a two-form family at all — 504 frames:

| | frames |
|---|---:|
| exact | 316 |
| up to `lift` | 94 |
| blocked | 94 |

and per row, over the 74 rows the two assertions filed:

| n | verdict |
|--:|---|
| 30 | derive at **all four** halves once `lift` is allowed |
| 44 | **blocked even up to `lift`** — 38 of them with the `j = S j'` half dead at BOTH parities |

Per-row verdict patterns over all 126:

| n | pattern |
|--:|---|
| 52 | `0z:exact 0p:exact 1z:exact 1p:exact` |
| 38 | `0z:exact 0p:blocked 1z:exact 1p:blocked` |
| 15 | all four `lift` |
| 10 | parity 0 exact, parity 1 `lift` |
| 5 | parity 0 `lift`, parity 1 exact |
| 3 | all four blocked |
| 2 | `z:lift p:blocked` at both parities |
| 1 | `z:blocked p:exact` at both parities |

So the wave-31 prompt is wrong about its own item (1) in **both** directions: it
is not "pure plumbing" (it is a real gate for 30 rows), and it does not open the
gate for the 67 (44 rows are a fact about the machine).  Its "29 frames up to
`lift`, 9 exactly, 0 blocked" was over 19 rows and does not generalise.

### 8a. The slack shape, and why it is renderable

Uniform wherever it occurs:

* the **LEFT side always lands exactly**.  It carries the opaque
  `E q0 ++ tail`, so a trailing blank there would sit in the MIDDLE of the word
  and `lift` could not hide it.  `_int_chain` **refuses** anything else rather
  than render a template that cannot close;
* the reached **FAR side** is the anchor's plus trailing blanks — measured
  `(1,1) -> (1,1,0)`, `() -> (0,)`, `(1,) -> (1,0)`, always exactly one.

`_far_peel` emits `WTape.lift_app_blank` with one nested `++ [S0]` per blank so
each rewrite peels exactly one.  `Nat.mul`/`Nat.add` are in its `cbn` list on
purpose: the far count is `a * j + b`, `rewrite` does not compute, and without
reducing first the side reads `pre ++ rep [] (0 * j + 0) ++ [] ++ []` and
`lift_app_blank` has no occurrence to match.  The exact template gets away
without it because it finishes by `reflexivity`, which is up to conversion.

### 8b. Item (1) yields 0 boards, exactly as the prompt predicted

Over the 30 rows it unblocks, the furthest gate becomes:

| n | gate |
|--:|---|
| 16 | `register step does not close` |
| 9 | `no boot chain` |
| 3 | `no inner family at pow2 j` |
| 1 | `no exit chain` |
| 1 | `no inner interior chain` |
| **0** | **boards** |

## 9. Item (4) is DEAD: the solo cascade boards 0 of 11

The `no boot chain` bucket is **11 rows**, not the prompt's 22 (that count was
pre-item-(1); see §11).  `cascade_emit.py --solo` on every one of them:

| n | why |
|--:|---|
| 5 | `no overflow phase at K=7` |
| 2 | `no solo cascade: the main count does not follow the descent` |
| 2 | `no interior chain` |
| 1 | `solo level 4: S is not in the phase` |
| 1 | `no solo cascade: no count below octave 6` |

**0 boards, and five distinct causes.**  That is not one missing piece — it is
the route not fitting the bucket.  The prompt's "If it boards some, that is
free" cashes out at nothing.  **Do not re-run the solo cascade against this
label.**

Tooling note, not a result: the first attempt was killed at row 4 with exit
137 (OOM) with four sweeps competing for RAM.  `cascade_probe` needs a couple of
GB per row; run it one row at a time under `ulimit -v` rather than trusting a
`--solos` batch to survive.

## 10. The gate table AFTER item (1) — measured 2026-07-30 over the 150

    0 / 150 fully derived

| n | furthest gate |
|--:|---|
| 40 | `no interior j=S j chain` |
| 33 | `no inner family at pow2 j` |
| 26 | `no gap-free two-form family` |
| 20 | `no boot chain` |
| 17 | `register step does not close` |
| 6 | inner fill lands off the measured endpoint |
| 4 | `no interior j=0 chain` |
| 2 | `no inner interior chain` |
| 1 | `no visit witness for state A` |
| 1 | `no exit chain` |

The per-bucket row lists are committed as `tools/counters/buckets31/*.txt`, plus
`tailcert_innerfam33.txt` and `tailcert_filloff6.txt` — item (2)'s 39 rows — so
the next wave starts from lists, not from a re-derivation.

## 11. Wave-30 §6d was not reproducible from the tree, and nothing said so

Wave-30 §6d reports 27 `register step does not close` / 22 `no boot chain` / 8
`no inner family` / 8 inner-fill-off-endpoint over the 70, "with `lift` allowed
on the interior split".  Running `tailcert` **as committed** reproduces none of
that: it files 74 rows at the two interior assertions and reports 1 register-step
row and 11 boot-chain rows.

The reason is not a mistake in the numbers — it is that **the `lift` fallback
they were measured with was never committed**.  §6d measured a patched working
tree, wrote the table into a document as the state of the bucket, and the patch
did not land.  Item (1) of the wave-31 prompt is that patch, described as
plumbing already implied by §6d.

With item (1) in, the buckets come back (17 and 20 against 27 and 22 — the rest
is the population being 150 rather than 70), which confirms §6d was measured
honestly.  It was just not measured against anything a later wave could run.

**Standing constraint, and the one to carry forward:** a bucket size in a
findings document is worthless without (a) the date, (b) the commit it was
measured at, and (c) the assurance that the code it was measured with is in that
commit.  Every table in this document carries the first two and §8's numbers
were re-derived from the committed `_int_chain`, not from a working tree.

## 12. What the next wave should build

`docs/WAVE32_PROMPT.md`.  Short version: item (2), the bounded inner carrier, is
the only item in the wave-31 prompt whose stated size survives contact with the
data (33 + 6 = 39 rows) and the only one that needs new Coq.  The 40-row
`no interior j=S j chain` bucket has no item in that prompt at all and is now the
largest single thing in the residue.
