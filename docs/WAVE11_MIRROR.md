# Wave-11 — the mirror harvest, the wall verdict, and the inner counter

_Written 2026-07-25, same session as `WAVE10_SHAPES.md` (branch
`claude/residue-reduction-4-2-07rtlv`).  This wave turned to the frozen
deferred list itself: of its 5,156 machines, 3,376 already had boards in-tree
awaiting the route-A closeout, leaving **1,780 unproven** — 767 growth=R
counters, 359 growth=L, 336 NOFIT, 318 non-core._

## 1. The mirror harvest: 128 boards, 128/128 first try

`--mirror` on both shape emitters (`mirror_common.py`): derive + validate +
emit entirely against the MIRRORED table, close through
`Mirror.mirror_never_qh` — the wave-9 ILCM route, zero new theory.  Of the
767 unproven growth=R counters:

| | |
|---|---:|
| Jp-mirror derivable → boarded (`ILS1M_*`) | 64 |
| Ip-mirror derivable → boarded (`ILS4M_*` 32 + `ILS4FM_*` 32) | 64 |
| encoding overlap between the two | 0 |
| axioms, every board | `functional_extensionality_dep` only |

The remaining 639 partition **exactly like the L side did** (no new levers):
~180 wall-held anchors, ~115 exponential-overflow, ~105 skeleton misfits,
rest longer tails/other encodings; 521 of the 639 already carry measured
encodings (`SEP2` 412 = Ip, `SEP2i` 72 = Jp, `KCOPY1` 33 = Kp).

## 2. The wall verdict (measured, ASYMMETRIC — record the grid)

`derive_tail_far` / `anchor_scan_far` (emit_interleave.py) derive anchors
with a FIXED non-blank far side, snapshots grouped by stripped far word;
`emit_shape1.py` threads the wall through the frontier-close window.
Measured (grid: wmax 4, tail cap 6, both branches replayed):

| pool | far-anchor harvest |
|---|---|
| 359 unproven growth=L, direct | **1** — L-side walls anchor now (the exemplar `1RB0LB_1LA0LC_0LB0RD_1RD0RC` moves from `only N snapshots` to `no shape-1 skeleton fits`) but their laps bounce off the wall with window chains the affine templates lack |
| 639 growth=R, Jp-mirror | **44 boarded** (`ILS1M_*` with walls) — on the mirror side the wall family IS template-shaped |

So the lever is alive where the lap stays affine and lap-blocked where it
does not; the L-side walls join the skeleton-misfit queue (wall-bounce
window chains), they are NOT anchor-blocked any more.

## 3. The load-bearing discovery: the exponential overflow IS a counter

Inner-anchor probe of `1RB1LA_0LA1RC_0LD0RB_0LA1RD`'s overflow lap
(p = 15 → 16, 180 steps): the (state A, blank head) snapshots inside the lap
read

```
11010101 → 11010111 → 11011101 → 11011111 → 11110101 → … → 11111111
```

— the machine implements the `2^k−1 → 2^k` transition by running an INNER
interleaved counter through ~2^k inner laps, each affine, with the same
anchor discipline as the outer counter (mid-carry snapshots included).  So
the "inner induction" the exponential family needs is not new structure at
all: it is a SECOND INSTANTIATION of the existing lap machinery — inner
anchor family `Ci`, inner interior/overflow branches via the same
`cview`/window lemmas, composed by the same well-founded induction, and the
composite plugged in as the outer overflow's existential witness.
`glue_neverqh` never sees the difference.  This gates ~209 machines
(~94 L + ~115 R) and is the next hand-author-one-first milestone.

## 4. The NOFIT surprise

Ten of the 336 unproven NOFIT machines — never recognized as counters by
wave-8 fingerprinting — board DIRECTLY through the far-anchor Jp template
(one with an 8-step close / 11-step overflow stop; the skeleton search
absorbs it).  The NOFIT wall is partly a recognizer artifact, again.

## 5. Scoreboard after wave 11

| | |
|---|---:|
| boards this session (waves 10+11) | **309** (127 L-side + 128 mirror + 44 walls + 10 NOFIT) |
| unproven on the frozen 5,156 | 1,780 → **~1,598** (dash-machine filename accounting makes this an upper bound) |
| proven awaiting route-A closeout | 3,376 → **~3,558** |
| next blocks, ranked | exponential/inner-counter ~209 (§3 — the refined spec); wall-lap skeletons ~300 (L+R); skeleton misfits ~110; Kp emission (`emit_kp.py`, sibling) ~33+; non-core triage 318; route-A closeout assembly (container-safe, any time) |

Census untouched throughout; `census_cache --check` = MATCH at every commit.
