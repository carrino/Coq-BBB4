# Wall-LAP bounce skeleton — first trace (seed for the next wave)

_Wave-12 session, after the IXP harvest.  The ~300 wall-LAP candidates
(WAVE11_MIRROR.md §2: L-side walls whose anchors `derive_tail_far` already
finds but whose laps "bounce off the wall") need a NEW window-chain skeleton;
this note records the first measured lap segmentation so the next session
does not start from zero._

Exemplar `1RB0LB_1LA0LC_0LB0RD_1RD0RC`, anchor (Jp, edge C, tail `[0]`,
far wall `[0,0,1]`, p0 = 1).  One interior lap (m = 23, j = 3, 32 steps):

| phase | steps | shape |
|---|---|---|
| ERASE ripple | 2 per low pair (t=1..6) | leftward cycL over the j low `[1,0]` Jp pairs, DEPOSITING blanks rightward (the erased cells pile onto the far side as `0^2j`) |
| stop-flip | t=7..9 | 3-step window at the clear pair |
| REBUILD | 1 per cell (t=10..19) | rightward cycR-style run writing the new `[1,1]^j` low region AND re-consuming the deposited blanks, until the head hits the wall's `1` |
| BOUNCE ×2 | 8 + 5 (t=20..32) | zigzag cycles anchored ON the wall block: a 3-4 cell window at the wall (`C/B/A` dance), a leftward mini-run over the freshly rebuilt pairs (`D`), and a return; the SECOND bounce closes the lap exactly |

MEASURED (this session): the exemplar's laps are AFFINE on both branches —
interior `n(j) = 20 + 4j` (j = 0..5), overflow `n(K) = 22 + 4K` (K = 2..6).
So the bounce count is FIXED and the whole lap is a longer-but-fixed window
chain: `ERASE^j . STOPFLIP . REBUILD^(2j+c) . BOUNCE1 . MINIRUN . BOUNCE2`
— cycL/cycR units plus TWO fixed wall windows, a seven-window affine
skeleton.  This family is a skeleton-search extension of `emit_shape1.py`,
NOT new theory.

Remaining questions before templating:
2. The REBUILD unit consumes the blanks the ERASE deposited — the far-side
   window bookkeeping must carry `0^2j` between phases (the deposit lives
   OUTSIDE the wall, unlike every existing template where deposits sit
   between the counter and the wall).
3. The overflow branch was not traced yet; profile it separately
   (COUNTER_CLOSEOUT.md §5: never assume the overflow matches the interior).

The MINIRUN in the trace covers only the low-pair region (amplitude 2-3
cells at j = 3), so a fixed-window bounce pair looks plausible; a
`lap_len` profile over j and a second machine's trace are the next two
measurements.

---

## Measured yield (wave-12, `emit_wallj.py`) — the Jp wall pool is NOT one shape

The erase/rebuild skeleton above was templated (`emit_wallj.py`, boards
`WLJ_*`/`WLJM_*`) and swept over the 53 Jp-anchored wall machines the
full unproven-pool scan found (23 direct + 30 mirror).  **Yield: 1 board.**

| outcome | n | what it means |
|---|---:|---|
| boarded | **1** | the exemplar `1RB0LB_1LA0LC_0LB0RD_1RD0RC` |
| `no Jp-wall interior skeleton` | 26 | same lap profile (`20+4j`), different windows — see below |
| `shape:` mismatches | 13 | far blank run 0 or 1 (not 2), or the close exits with a left residue |
| `no Jp-wall overflow stop` | 12 | interior fits, overflow stop differs |
| anchor tail not `[S0]` | 2 | different anchor |

**The second sub-variant (traced, not templated).**  On
`0RB1LC_1LA1RB_1LA0RD_0LC1RD` the head stays `S1` (not `S0`) across the lap
and the polarity is inverted: the "erase" pass deposits **`S1`s**, and the
rebuild consumes `[S1]` depositing `[S1]` — unit
`(QD,[],S1,[S1]) -> (QD,[S1],S1,[])`, against my template's
`(QD,[],S0,[S0]) -> (QD,[S1],S0,[])`.  Same erase/rebuild geometry,
complementary symbol.  Templating that variant is the obvious next step
for this pool and should pick up a large share of the 26.

**Do not** conclude from the exemplar that a wall family is one shape — the
W-Ip pool needed offset variants (see `UNCERTAIN_MACHINES.md` §3) and the
W-Jp pool needs at least a polarity variant.  Trace two or three members
before templating, not one.
