# Counter codegen — what actually blocks the remaining boards (measured)

_Written 2026-07-25.  Goal: get the interleaved-counter core onto the board.
This is a MEASUREMENT of `tools/counters/emit_interleave.py` against every
unboarded growth=L counter, plus two experiments that failed.  It exists so
nobody repeats them.  Companion to `docs/COUNTER_EMITTER_WAVE8.md` (the
emitter's own design doc, another session's) and
`docs/RESIDUE_708_DIAGNOSIS.md`._

## Population (from the committed `tools/counters/wave8_fingerprints_v2.jsonl`)

| set | count |
|---|---|
| counter core | 2,480 |
| ├ recognized `cls=COUNTER` | 1,738 (growth **L 658**, growth **R 1,080**) |
| └ `cls=NOFIT` | 742 (= the residue analysed in `RESIDUE_708_DIAGNOSIS.md`) |
| boarded `ILC_*.v` (L route) | 61 |
| boarded `ILCM_*.v` (mirror/R route) | 99 |
| **growth=L still to board** | **597** |

## What the emitter's anchor search is looking for

The whole route hangs on one object, the **anchor**: a recurring configuration
whose tape *is* the counter's value.  `anchor_scan` snapshots every moment where
state = `edge`, the head cell is blank, **the far side is entirely blank**, and
the near side is non-empty; `_tail_for` then asks whether those near-side words
read as `Enc(p) ++ tail` for **consecutive** p, with a fixed `tail` of length
≤ 6.  In Coq that is exactly

```coq
Cc p := (StB, (Jp p ++ [S0], S0, []))
```

Worked example — `0RB---_0LC1RB_1LA1LD_1LC0RB`, the one machine of the 597 that
derives today:

```
t=  5   left = 1          head=0  right=blank   ->  p=1
t= 13   left = 111        head=0  right=blank   ->  p=2
t= 17   left = 101        head=0  right=blank   ->  p=3
t= 29   left = 11111      head=0  right=blank   ->  p=4
t= 61   left = 1111111    head=0  right=blank   ->  p=8
```

Step gaps 4, 8, 4, 12, 4, 8, 4, 16: the carry ripple (short when the low bit is
clear, longest at the 7→8 overflow).  That variability is why the lap lemma
splits on `cview` into an interior-carry and an overflow branch.  With the
anchor, `glue_neverqh` needs only `Cc p → Cc (p+1)`, a boot into `Cc p0`, and a
per-lap visit witness — induction on `p` covers the rest forever.

## Measured failure profile over all 597

`emit_interleave.py --list` (derive+validate only, no coqc): **1 / 597 derive.**

| count | share | failure |
|---|---|---|
| 378 | 63% | `no fixed anchor tail up to length 6` |
| 133 | 22% | `only N anchor snapshots` |
| 80 | 13% | `no interior skeleton fits the raw lap` |
| 3 | — | `no overflow stop fits the raw lap` |
| 2 | — | `no lap closure` |

**85% fail before the lap is ever considered** — the blocker is anchor-finding,
not lap-fitting.

## Experiment 1 — widen the search parameters: NO GAIN (do not retry)

Tail cap 6 → 24, `anchor_scan` budget 200k → 3M steps, `nmax` 60 → 240,
snapshot floor 12 → 8.  Result: still **1** derive, same profile.  The anchor is
not merely *longer* or *rarer* than the caps allow; the predicate does not match
at all.

## Experiment 2 — add the `Ip` encoding: better diagnosis, still 0 new derives

`ENC = {'Jp': Jp, 'Ip': Ip}` was already wired through the Python; only
`process()` hardcoded `'Jp'`.  Trying `Ip` as well (now landed, see
`enc_table`) moves the profile:

| stage | Jp only | Jp + Ip |
|---|---|---|
| no fixed anchor tail | 378 | **306** (−72) |
| only N anchor snapshots | 133 | 133 |
| no interior skeleton fits | 80 | 109 (+29) |
| no overflow stop fits | 3 | **40** (+37) |
| no lap closure | 2 | 8 (+6) |
| **derives** | **1** | **1** |

So **72 machines have a perfectly good `Ip` anchor** and fail further down, in
the lap skeleton.  Verified by hand on `0RB---_1LA1RC_0LD0RB_1RB1LD`: at
state C, head blank, right side blank, the left list is exactly
`Ip(p) ++ [S1]` for consecutive p = 64, 65, 66, … (`enc=Ip, tail=[1,0], p0=1`).
Its real blocker is `no overflow stop fits the raw lap`.

**Correction to an earlier claim in this session:** the 46%-of-blocked
`SEP2` class was described as needing a NEW 0-separator Coq encoding.  That was
wrong — `SEP2` in `tools/kcopy_classify.py` records stride and inversion, not
the separator *value*, which it infers.  Those machines' separator is `1`, i.e.
they are `Ip`, which the repo already has.  No new encoding was needed for them.

## Remaining blockers, ranked, with what each is worth

1. **157 lap-skeleton failures** (109 interior + 40 overflow + 8 closure) —
   the fixed comb-free 6-window skeleton (P1/RIP/STPI/STPO/RET/FIN) does not fit.
   All 72 `Ip`-anchored machines are behind this.  **Start here**: it is pure
   Python (`derive`), and it gates the only machines already known to anchor.
2. **133 `only N anchor snapshots`** — the predicate demands a **blank far
   side**, but these machines hold their counter against a **wall** (confirmed
   by hand-inspection and by `tools/kcopy_classify.py`, which finds their
   anchors: e.g. `1RB0LB_1LA0LC_0LB0RD_1RD0RC` has a `001` wall, anchor state C,
   values 3009…3014).  Needs `Cc p` to carry a fixed non-empty far side.
   `glue_neverqh` already accepts an arbitrary anchor, so this is emitter +
   template work with **zero new soundness surface**.
3. **306 `no fixed anchor tail`** — neither `Jp` nor `Ip` decodes them.
   `tools/counter_encodings.tsv` gives the per-machine encoding measured
   independently (stride k, offset, data position, inversion, wall side, anchor
   state), which is the input a widened encoding table needs.

## What is already cheap on the Coq side

An `Ip` template variant needs **only substitutions**, not new theory:

* `cview` is defined once in `MonoCounter.v` — encoding-independent;
* `tovf` (`JpCounter.v`) is a fixpoint on `positive` alone — reusable as-is;
* `pair_rot : forall (x y : Sym) j, rep [x;y] j ++ [x] = x :: rep [y;x] j` is
  **generic in its symbols** — reusable as-is;
* `ILCounter.v` already provides `Ip`, `Ip_head`, `cview_some_I`,
  `cview_none_I`, `pair_fold`.

So the emitted template's deltas are `Jp` → `Ip` and `cview_*_J` → `cview_*_I`
in the three `lap_exact` rewrite sites.  It is deliberately **not** built yet:
until blocker 1 is fixed no `Ip` machine reaches emission, so the variant would
have nothing to emit.  Emission is therefore **gated to `Jp`** in `process()`
(an `Ip` machine reports `derived+validated, but emission needs the Ip template
variant`) so a known-inconsistent board can never be written.

## Status of this pass

* Landed: encoding-aware anchor derivation (`enc_table`, `Jp` then `Ip`),
  deepest-error reporting, emission gated to `Jp`, and
  `tools/counter_encodings.tsv` (1,280 machines' measured encodings/anchors).
* **New boards from this pass: 0.** The gain is diagnostic: the blocker is now
  located precisely, and two plausible-looking approaches are measured dead.
