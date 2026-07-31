# The QUAD route's terminal is itself quadratic — measured, with the exact law

_Untrusted measurement, no `theories/` change, boards nothing.  Written
because it answers a question two routes have now stopped at, and it says
which of them is worth building.  Reproduce every number here with
`tools/counters/quad_emit.py` and the raw simulator; none of it needs the
kernel._

## 0. TL;DR

`TCp`, the QUAD route's terminal carry-and-clear at `k = S k'`, costs
**exactly `(k+2)^2` steps** on `1RB1LA_0LA0LC_1LC1RD_0RB0RD`.  It is not
affine, so `derive_chain` cannot express it and `quad_emit` refuses the row
with `no TCp chain`.  That is not a narrow search: the target is
unreachable from the source in the whole symbolic step language (closure:
**4 states, 2 dead ends, target absent in any form**).

The route's architecture assumes the quadratic lap is a COMPOSITION of
affine rungs — `QuadGlue.quad_lap` is `MeasureGlue.mrun` over the ladder,
and each rung is meant to be a chain.  On this machine the quadratic-ness
sits in the TERMINAL as well, one level below where the route expects it.
So the row needs a decomposition of `TCp` itself, not a wider search.

This is John's reading of the row — *"a counter where it takes n bounces
to carry n bits over"* — located precisely: the n-bounces-per-carry is in
the terminal.

## 1. What was fixed on the way, and what it bought

`extract()` asserted the ladder's mark count is `J+1` interior and `J+2`
overflow.  Measured on `1RB0LD_0LC0RB_1LA1RC_0RC1LD`: one rung runs
uniformly ONE SHORT of that — 6 marks at `J = 6`, 7 at `J = 7`, 7 on the
overflow branch — while another rung of the same machine matches exactly.
A consistent second law, not noise, and the constant refused the row
before any of the interesting work started.

`quad_emit` now reads the offset off two adjacent `J` and checks only the
SLOPE (one rung per unit walked, which is what makes a ladder
well-formed).  This is the discipline the same function already applies
forty lines down for the right-hand rung base — *"Read which off the rungs
rather than assuming the aligned form"* — and the lesson `LADDER_PLAN` 4k,
PR #84 and PR #87 each paid for separately.

Regression: **6 of the 32 committed `QMG_*` machines re-extracted, 6/6
OK**, across three alphabets (`Kp`, `Alph_00_10_1`, `Bp`).  Boards that
satisfied the old constants have offset 1 resp. 2, so the weaker check
cannot lose them — checked rather than asserted.  (The full 32 timed out
at 900 s; each extraction is 30-200 s.  Shard it.)

Effect: the QUAD rows clear that gate and fail LATER, which is how §2
became measurable at all.

## 2. The measurement

On `1RB1LA_0LA0LC_1LC1RD_0RB0RD`, `TCp` is asked for

    src  (StA, left [], head S0, right 1 ++ 1^k ++ 0)
    dst  (StB, left 0^(k+1) ++ 1, head S0, right [])

i.e. clear the run of `k+1` ones and carry one cell further out.  Against
the RAW simulator (`emit_lapcert.sim`, both sides open — not the symbolic
step language):

| k | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| steps | 4 | 9 | 16 | 25 | 36 | 49 | 64 | 81 | 100 |

First differences 5, 7, 9, 11, 13, 15, 17 — the odd numbers — so the cost
is **`(k+2)^2` exactly**, matched at every `k` in 0..8.  A chain's cost is
`a*index + b`; no `a`, `b` gives a square.

The symbolic closure agrees from the other side.  `intgap._closure` from
that source under the whole step language reaches **4 states** with **2
dead ends** and never the target — not even a state with the target's
state and head symbol.  One of the two dead ends is the source itself
re-parenthesised (`right = 1 ++ 1^k ++ 0` and `right = 1^(k+1) ++ 0` are
the same tape), which is what a configuration the language cannot leave
looks like.

**Do not conclude "structural" from a hand-rolled simulation.**  `TCp` is
derived with `er = True`, so the LEFT side is opaque; a probe that hands
it a concrete empty tape reports "destination never reached" at every `k`,
which is an artifact of the probe.  That mistake was made and caught here.
Left-window variants (`()`, `0`, `1`, `00`, `10`, `01`, `11`) were also
tried: all give the same 4-state closure, so the frame length is not the
issue either.

## 3. What this means for the eight

Eight live core rows are ladder partials that stop at ONE line —
*"interior arm: no chain at stride 1, 2, 3 or 4 -- the carry ripple is not
affine in the run length"* — with 9 to 25 arms each already kernel-proved
(`tools/coqproject_exempt.txt` lists them).  All four `QUAD`/`QUAD` rows
in the residue are among them; the other four are labelled
`PARITY-AFFINE`, which is the same ripple sampled where the parity trick
happens to fit.

`emit_ladder`'s refusal is honest and its comment says so: *"A row whose
cost is genuinely quadratic has no stride that works and is refused here;
that is the count language of RULE_LADDER 5, not a gap in this emitter."*
§2 now confirms the same fact from the QUAD route's side, with a closed
form.  So the two routes are not two chances at these rows — they are two
statements of one obstruction.

## 4. The two doors, and which one is real

1. **Decompose the terminal.**  `TCp` costing `(k+2)^2` says the terminal
   is itself a ladder — `k+2` bounces over a region of width `k+2`.  The
   route already knows how to compose a quadratic out of affine rungs;
   what it cannot do is compose one out of a rung that is itself
   quadratic.  Giving `TCp` its own inner ladder (and `mrun` its abstract
   state) is a route change, not a search change, and it is where the
   eight rows go.
2. **The count language** (`RULE_LADDER` §5).  Let an arm's cost be a
   function of the run length rather than a constant.  `LapGlue` is the
   standing precedent: its lap obligation is an EXISTENTIAL over step
   counts, which is exactly why the wave-19 fractals boarded with a `3^k`
   lap and why the REACHST tier boards rows whose laps are never modelled
   at all.  This is a checker change with its own soundness proof.

Door 1 is narrower and reuses `MeasureGlue` as it stands.  Door 2 is the
principled one and would retire the whole "the certificate language
carries `a*j + b`" family of blockers, which after the wave-34 inversion
is **27 of the 47 open rows** (`RESIDUE_MAP.md`, "The families").

## 5. Do not retry

* **Widening the `TCp` search, at any framing.**  The cost is a square;
  no chain expresses it (§2).
* **A hand-rolled simulation of an `er = True` chain.**  The opaque side
  makes it report false negatives (§2).
* **Blaming the mark-count constant for these rows.**  It was a real
  defect and it is fixed, but it was the first gate, not the wall (§1).
