# Why no lossy decider can finish this residue — measured, wave-12

_Written after John asked the right question: "is there a hammer to run all the
theorems/deciders we already have on the residue?"  There is one
(`tools/nghist/wave8_sweep.py`), it had never been run on the current residue,
and this file records what happened when it was._

## The answer: yes there is a hammer, and it cannot work

The NGramHist sweep over the current 1,385-machine residue:
**0 boardable out of 896 machines swept** (the sweep was stopped once the
mechanism below was measured; 0/896 with no hit is already conclusive).
That is not a tuning problem.  The mechanism is now measured directly.

## The mechanism

`nghist_prove.cert_for_state` proves "state `q` is visited infinitely often"
by showing the **q-avoiding subgraph** of the closure has no infinite path —
either it is acyclic (`HRank`) or a count/pattern measure strictly decreases
along every q-avoiding edge.

Probed on three residue machines across the precision grid:

| machine | k=2,n=2 | k=3,n=2 | k=4,n=3 | k=6,n=3 |
|---|---|---|---|---|
| `0RB---_0RC0LD_1LD1RC_0LA1LB` | 61 nodes, all cyc | 81, all cyc | 206, all cyc | 324, all cyc |
| `1RB1LA_0LA1RC_0LD0RB_0LA1RD` | 72, all cyc | 99, all cyc | 199, all cyc | 313, all cyc |
| `0RB1LC_0LC1RD_1RB1LC_0LA0RB` | 72, all cyc | 105, all cyc | 222, all cyc | 331, all cyc |

("all cyc" = the q-avoiding subgraph is cyclic for **every** obliged state.)

The closure **always closes**.  Raising history and gram size only grows the
graph — 61 to 324 nodes — and never breaks the cycles.

## Why, in one sentence

A counter's carry into the high bits happens only after ~2^k steps, so any
FINITE window admits the abstract path "stay in the low bits forever".  That
path is a q-avoiding cycle, it is spurious, and no amount of history removes
it because the window is finite and the wait is unbounded.

This is the same wall from the other side as `COUNTER_CLOSEOUT.md` §0: RepWL
reports NOCLOSE 706/708 (the closure never forms), NGramHist closes but reports
NOMEAS (the closure forms with spurious cycles).  Two failure modes, one cause.

## What this does and does not license

* It **confirms** mxdys' stated condition — an exact forward model is required
  — for the LIVENESS half specifically.  Non-halting is easy here; "every state
  recurs" is what needs exactness.
* The `<=7` / all-8 "outside mxdys' enumeration" story in `NGHIST_WAVE7.md` §0
  is NOT relied on here and should be treated as unverified: John (who knows
  the enumeration conventions) says it is bad info, and nothing in this file
  depends on it.  The measurement above stands on its own.
* It **does not** license more per-machine emitters.  `WAVE9_FINDINGS.md` §7 is
  still right: one theorem per machine is the wrong exponent.  Wave-12 built
  five emitters for 205 boards against a 1,385 residue and the trajectory is
  clearly bad.

## The build this points at

A **verified lap decider**: a computable function taking a machine plus a
candidate anchor description, running the symbolic lap, and returning a
certificate — with ONE soundness theorem discharged once and per-machine cost a
`vm_compute`.  Same architecture as the `RepWL`/`NGramCPS` deciders already in
the tree, but exact rather than lossy.  `WTape`'s `wsteps`/`cycL`/`cycR` are the
primitives; `Ip`/`Jp`/`Kp`/`Dp`/`Mp` are the digit alphabets.

John's structural reading is what makes the liveness half cheap in that design:
these machines are bouncers that touch all four states per bounce, or counters
that touch every state each doubling.  An exact lap model sees that directly —
it is exactly the per-state visit witness `glue_neverqh` already consumes — so
liveness comes for free once the lap is modelled, with no measure search at all.

## Do not re-run

* NGramHist/NGramCPS liveness over this residue at ANY (k, n, t): measured
  above, cyclic at every setting.
* RepWL over the counter core: `COUNTER_CLOSEOUT.md` §5, NOCLOSE 706/708.
