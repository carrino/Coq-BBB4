# Wave-31: the two-form board renderer — 12 boards, and the framing is the point

Branch `claude/wave31-prompt-residue-ec2clt`, cut from `main` at `dc0adbc`.

## 1. The one-line result

    4,916 of the frozen 5,156 settled  ->  4,928   (95.3% -> 95.6%)
    162 core undecided + 78 0RB shadows ->  152 core + 76 shadows

**+12 boards**, all from item (0) of the wave-31 prompt: `tools/counters/tailcert.py`
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
* `theories/Machines/Counters/REG_<ID>.v` × 12.
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
