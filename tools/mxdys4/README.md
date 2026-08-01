# mxdys's four rows — macro-rule extraction and liveness measurement

UNTRUSTED search/measurement tooling (repo rule: only the Coq checkers
carry soundness).  Full write-up: `docs/WAVE36_MXDYS_FOUR.md`.

The four rows (`rows.txt`):

    1RB1LC_0LC0RB_1LA1RD_0LA0RD   1RB1LC_1LB1RA_0LC0LD_0RA0RD
    1RB1LC_1LC1RA_0LC0LD_0RA0RD   1RB1LD_1LC1RA_0RB0LC_0RA0LD

## The two things worth reusing

**`gaps.py SPEC...`** — worst gap between consecutive visits of each state,
against the tape width at that moment.  Run this BEFORE spending a session
on a `ReachSt`/`ReachStI` board: the measure there is linear in the
half-tape `S1` counts, so a state whose gap grows faster than the width is
outside the tier permanently, whatever certificate class you search.  It is
what closed `StD` on rows 1 and 4 (gap `Theta(2^width)`).

**`extract.py SPEC MODE`** (`MODE` = `L1` left half-tape unary, `R1` right
half-tape unary) — automatic macro-rule extraction.  Runs the raw machine
from a symbolic configuration to the next `StA` configuration and prints
the transformation, over a grid of parameters.  A row whose orbit keeps one
half-tape a bare unary run (check with `macro1.py` / `macro4.py`) collapses
to a finite word-rewriting system, and this reads that system off directly
instead of guessing it.

## Boarding rows 1 and 4 (wave 37)

**`cmacro1.py [N]`, `cmacro4.py [N]`** — the same macro systems as
`macro1.py`/`macro4.py`, but restated in the **`cconf` coordinates the Coq
proof is written in**: `(l, s, R)` for row 1 and `(p, s, r)` for row 4,
with `chd`/`ctl` at the list ends and an explicit blank between the unary
run and the tail.  Each one differentially validates every rule against the
raw simulator, then checks the `mu` deltas and the parity lock of
`docs/WAVE36_MXDYS_FOUR.md` §4a over 4000 macro steps.  Re-derive here
before touching Coq: the frame form of §2a hides which rules read past the
run and what happens at the tape edge, and the `cconf` form does not.

**`pin_kn.py SPEC [QEXT] [BUDGET]`** — at which `(k, n, t, fuel)` does the
`NGramHist` closure discharge every state BUT `QEXT`?  On rows 1 and 4 the
answer is `k=3, n=2` (134 / 131 contexts); `k=2, n=2` misses one state on
each row and `k=2` with `n=3` or `n=4` does not close at all.

**`emit_ngx.py`** — writes the closure half of the two boards
(`lset`/`rset`/`cert` + the final theorem) into
`theories/Machines/Mxdys4/NGX_*.v`, replacing everything after the MARK
line and leaving the hand-written liveness proof above it alone.
Idempotent; re-run it whenever the closure parameters change.

## The rest

* `sim.py` — raw simulator (`Sim(spec)`), imported by the others.
* `macro1.py` — row 1's four macro rules, differentially validated against
  the raw simulator, plus a labelled macro trace.
* `macro4.py` — row 4's three macro rules, differentially validated.
* `certE.py`, `certM.py`, `certM3.py SPECFILE k MAX` — measure searches
  generalising `tools/reachsti/cert_search.py` from `ones` to **extents**
  (`ext l` = distance from the head to the outermost `S1`), with a `k`-cell
  window and capped extents.  Bellman-Ford over the difference constraints,
  invariant = the closure of the real orbit's nodes.  On failure they
  return the blocking negative cycle, which is how the spurious node that
  stops rows 2 and 3 was located (`docs/WAVE36_MXDYS_FOUR.md` section 5).
