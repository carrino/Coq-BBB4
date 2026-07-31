# Instruction beeps: what BBB(4) costs when the beep is an instruction

_Scoping measurement, 2026-07-31.  Question: this development proves
BBB(4) results where the beep is a **state** (`QuasiHaltsSt`).  What
would it take to prove the same results where the beep is an
**instruction** — a transition `(q,s)` — instead?_

Everything numeric below was measured this session with two tools
committed alongside it (`tools/instrbeep/`); nothing is recalled.  The
state-level column of every table reproduces the committed census
numbers exactly (3,995,005 nodes, residue 228,726, BB(4) = 107 with the
right champion), which is the control that the instruction-level column
is worth reading.

**Short answer.**  The port of the *machinery* is small and mostly
mechanical — an estimated 3–5k hand-written Coq lines against a 33k-line
hand-written surface — because every abstraction in the tree already
carries the head symbol, and the `irules` engines already carry
per-instruction fire lists.  The port of the *result* is a new campaign:
41% of the machines the census's n-gram tier kills lose that proof, and
854 of the 5,156 frozen deferred rows stop being never-quasihalters and
start needing a score (851 of them in rows that already carry a board).

---

## 1. The two levels, and how they are ordered

With `FiresAt tm (q,s) n` = "the configuration at index `n` has state
`q` and reads `s`" (so the instruction fires at step `n+1`):

* `VisitsAt tm q n  <->  exists s, FiresAt tm (q,s) n` — a state's visit
  set is the union of its two instructions' fire sets.

Two consequences, both one-line proofs, and they are the whole
relationship:

1. **`NeverQuasiHaltsI tm -> NeverQuasiHaltsSt tm`.**  If every fired
   instruction fires unboundedly often then every visited state is
   visited unboundedly often.  The converse is false: `1RB1LA_0LA1RA`
   (SCOPING §4) is transition-level QH with score 7 and state-level not
   QH at all.
2. **`QuietAfter tm q s -> QuietAfterI tm (q, head@s) s`.**  A state's
   last visit *is* one of its instructions' last fires, so the
   instruction-level score of a machine is `>=` its state-level score,
   and `BBB_I(4) >= BBB_St(4)`.

So instruction-level quasihalting is strictly weaker (more machines
quasihalt), scores only go up, and the whole never-QH side of this
development is a *strictly stronger* claim than it needs to be at the
state level — which is why the port is not free.

**The champion is unchanged.**  Probed to 6e7 steps
(`tools/instrbeep/probe_instr.c`), `1RB1LD_1RC1RB_1LC1LA_0RC0RD` has

| | last visit / fire | score |
| --- | --- | --- |
| state `D` (state level) | 32,779,477 | **32,779,478** |
| instruction `D0` (instruction level) | 32,779,477 | **32,779,478** |

`D1` dies one step earlier, `A1`/`C1` at 32,769,2xx, `A0`/`B0`/`B1` at
~1.18e7, and `C0` never stops.  So `BBB_I(4) >= 32,779,478` with the
same witness and the same value — the record is *not* raised by the
change of level on this machine.  Whether some *other* machine beats it
at instruction level is exactly the open question the port would have to
re-settle.

---

## 2. What transfers for free

### 2a. Both cycle tiers, hence 83% of the census tree

The census discharges in-place cycles and translated cyclers by
`QHBound n1` — *any* eventually-quiet state made its last visit before
the loop window, because the block `[n1, n1+p)` repeats forever.  The
instruction-level statement is the same sentence with "instruction" for
"state" and the same proof: an instruction not fired inside the repeating
block never fires again.  So `QHBoundI n1` comes out of the identical
certificate, and those tiers need **no new residue and no new search**.

Measured over the full tree (both verdicts are exact at these tiers, so
this is a classification, not an estimate):

| tier | state neverQH / instr neverQH | state neverQH / **instr QH** | state QH / instr neverQH | state QH / instr QH |
| --- | ---: | ---: | ---: | ---: |
| C (in-place, 1,029,749 nodes) | 277,035 | **353,202** | 0 | 399,512 |
| T (translated, 2,286,534 nodes) | 609,711 | **865,950** | 0 | 810,873 |

The two zero columns are the sanity check on §1's lemma 2 — no machine
is a state-level quasihalter and an instruction-level never-quasihalter.
The 1.2M machines in the bold columns become quasihalters, but their
scores are all bounded by the cycle anchor (< 512 at this gas), so they
still discharge in-walk against `B_census = 2000`.  They change verdict,
not workload.

### 2b. The abstractions already know the head symbol

This is the load-bearing structural fact, and it is what makes the port
mechanical rather than a rewrite:

* `Closure.v` is parameterised by `a_state : A -> St` with
  `covers_state : covers a c -> a_state a = fst c`.  Every instance
  already proves the head symbol too — `NGram.v`'s `ng_covers` and
  `RepWL.v`'s `rw_covers` both contain `t_head (snd c) = s`.  Adding
  `a_sym : A -> Sym` + `covers_head` is a projection, not a new
  obligation.  `edge_ok`, `rank_ok`, `appears`, `live_ok`,
  `live_lex_ok`, `runner_ok`, `state_live_ok` then re-index over
  `St * Sym` with no change of argument.
* `Checkers/IRules/Engine.v` already defines `Tr := (St * Sym)` and the
  engine already returns `F : list Tr`, the transitions fired in one
  meta-cycle.  `Meta.v` throws the symbol away in one place:
  ```coq
  Definition st_in (q : St) (F : list Tr) : bool :=
    existsb (fun t => st_eqb (fst t) q) F.
  ```
  The instruction-level checker is that function with the symbol kept.
  The ~5k lines of RLE/affine/meta-cycle engine underneath do not move
  at all — the largest single subsystem is also the cheapest to port.
* `Wrap.v` redirects a whole state to halt (`tm_wrap tm q`).  The
  single-instruction redirect `tm_wrapI tm q s` is a *smaller*
  perturbation of the machine, so its closures are easier to close, not
  harder; the lemmas are the same with the guard
  `fst c = q /\ t_head (snd c) = s`.
* `Cycle.v`'s `cvisits` window scan becomes `cfires` (add
  `sym_eqb (chd c) s` to the disjunct); `Counters/LapGlue.v`'s premise
  `Hvis : ... exists k c, csteps tm k (Cf p) = Some c /\ fst c = q`
  gains `/\ chd (snd c) = s` — the witnessing configuration is the one
  the board already produces.

---

## 3. What does not transfer: the measurement

Tier N is the n-gram closure plus per-goal acyclicity — the tier that
kills 196,595 census nodes.  Widening the goal from a state to an
instruction enlarges the goal-avoiding subgraph (only nodes matching
state *and* symbol are excluded), so a state-level rank certificate need
not survive.  Measured on the same walk:

| tier N verdict | machines |
| --- | ---: |
| proven at both levels | 116,412 |
| **proven at state level, unproven at instruction level** | **80,183** |
| unproven at state, proven at instruction | 0 (as §1 requires) |
| unproven at both (already residue) | 232,434 |

The 80,183 split cleanly into two very different problems, and the split
is the most useful number in this document:

**(a) 69,586 are genuine new quasihalters, and they are cheap.**  Probed
at 3e6 steps, 3,475 of a 3,480-machine sample still show the instruction
dead — and their instruction-level scores are *tiny*: median **3**, 90th
percentile 9, maximum **80** in the sample.  These are overwhelmingly
machines that read a symbol once near the blank tape and never again
(A0 fires at step 1 and the machine never returns to A on a 0).  A
single-instruction wrap closure from a `t` of a few dozen steps proves
it, the score comes off the simulated prefix, and the bound is three
orders of magnitude below `B_census` — so they discharge in the walk and
never reach the deferred list.

**(b) 10,597 are still live, just not provably so at this tier.**  All
2,120 sampled are all-live at 3e6 steps.  Their inter-fire gaps, over a
2e6-step probe of 400 of them:

| largest inter-fire gap | machines | reading |
| --- | ---: | --- |
| <= 64 steps | 240 (60%) | a finer rung / a re-searched rank certificate should do it |
| <= 1,000 | 3 | likewise |
| <= 100,000, gaps flat | 120 (30%) | needs a measure, not acyclicity |
| <= 100,000, gaps still growing | 37 (9%) | fires once per doubling epoch |

The last two rows are the real content.  A plain acyclicity rank proves
"the goal recurs within `rank a` steps" — a *uniform* bound — so it can
never certify an instruction whose avoidance stretches grow without
bound.  That shape is not exotic: it is what a counter does when one
branch is taken once per epoch.  The lexicographic tier
(`Closure.v`'s `lex_ok`/`lex_reach`, whose measures are evaluated on the
concrete configuration and are unbounded) *can* express it, and the
census's `rank_tier` and RepWL tier both sit downstream of tier N and
caught 77.1% of the raw state-level tier residue.  **This tool stops at
tier N**, so 10,597 is an upper bound on that class's cost, not an
estimate of it; measuring it properly means running the full Coq
pipeline at instruction level, which is the first thing to do if this
port is ever attempted.

### The boarded rows

Of the 5,156 frozen deferred rows — the ones that needed a board rather
than an in-walk tier — probed to 5e6 steps:

| class | rows | what happens to the board |
| --- | ---: | --- |
| already quasihalters at state level | 3,292 | board keeps its shape (`NonHalt /\ QHBound /\ QuasiHalts`); the bound must be re-derived per instruction, and 199 of them show a *larger* instruction-level score |
| every fired instruction still live | 1,010 | `NeverQuasiHaltsSt` board generalises by widening the goal set |
| **state-level live, instruction dies** | **854** | board changes character: it must now prove a quiet instruction and an exact score |
| of the 42 open core rows | 22 all-live / 18 state-quiet / **2 instruction-dies** | |

The 854 (851 of which already carry a board — §4 splits them by
provenance) are the expensive rows: a never-QH proof and a
quasihalt-with-score proof are different arguments, not different
spellings.  The mitigating fact is that this repo already carries 3,292
rows proved in exactly that shape, with the closers to match
(`LapGlueQH`, `LapGlueQuiet`, `Wrap`, `KpWallQH`), so it is re-aiming
existing machinery rather than inventing any.

**One trap, paid for this session.**  A finite horizon lies about
liveness.  At 5e6 steps, 199 frozen rows appeared to have their score
jump from 1 to ~2^22 (`1RB---_0RC0LD_1LD0RB_1LD1RC` and friends).  At
5e7 the same instructions fire again at ~2^25: they are epoch-sparse,
not quiet.  Any instruction-level verdict from a probe must be re-probed
at a larger horizon before it is believed.

---

## 4. The estimate

| piece | size | risk |
| --- | --- | --- |
| Semantic core: `FiresAt`, `QuietAfterI`, `QuasiHaltsI`, `NeverQuasiHaltsI`, `QHBoundI`, the two order lemmas of §1 | 150–250 lines | none |
| `Cycle.v` + `TCycler.v`: `cfires` scans, `QHBoundI n1` | ~350 lines | none |
| `Closure.v` re-indexed over `St * Sym` + `covers_head` in the NGram/RepWL/hist instances | 400–600 lines | low, mechanical |
| `Wrap.v` single-instruction redirect | ~250 lines | low |
| `IRules` `Meta.v`/`MetaBlk.v` fire-list gate (engines untouched) | ~100 lines | low |
| Fuel / Drift / LapAvoid / NGramHist / RepWL / ReachStI / LadderCheck re-indexing | 800–1,200 lines | low |
| `Counters/` toolkit closers (`Hvis` gains the head symbol) | ~400 lines across ~40 files | low |
| Census: `TNF_QH` `QHBoundI`, `Decide.v` tier contracts, and a **new mixed tier** ("each instruction is either liveness-certified or quiet-certified with a bound") | 900–1,100 lines | medium — the mixed verdict is the one piece with no state-level analogue at census scale |
| Corruption tests for all of the above | ~1,000 lines | low |
| **Total hand-written Coq** | **~3–5k lines** | against a 33k-line hand-written surface today |

Plus, none of it hand-written:

* **Certificate re-search** at instruction granularity for every board
  and every census tier — the untrusted Python/C sweeps in `tools/`.
  Compute, plus generator plumbing; 60% of the tier-N losses look
  recoverable by re-search alone.
* **Board regeneration**: 2,396 files / 5.47M generated lines re-emitted
  from the new certificates.
* **Census re-walk**: ~7 h at `-P4` under the native switch (24 h for
  `census-verify`), and the 154 committed `.vo` replaced.

And the part that is not an estimate but a campaign:

* the **851 boarded rows** that flip from never-QH to QH,
* the **2 of 42** open core rows that do the same,
* and the tier-N class (b) machines that survive the downstream tiers —
  low thousands, each eventually a board.

### Why the line count flatters the port

Hand-written Coq is the *least* representative metric this project has.
Measured over `theories/Machines/`:

| | files | lines |
| --- | ---: | ---: |
| generated boards | 2,277 | 5,368,206 |
| hand-written boards | 119 | 44,771 |

and 198 of the last 341 commits touch `tools/` — the certificate
*search*, not the Coq.  Weighting the port by lines therefore counts the
part that does not repeat and ignores the part that does.  Splitting the
work by what actually recurs:

| | repeats at instruction level? |
| --- | --- |
| semantic core, closure engine, irules engines, counter toolkits, census plumbing, closeout assembly | **no** — the 3–5k-line delta above |
| the 119 hand-written boards | **mostly no** — only **7 files** carry a row that flips |
| the 2,277 generated boards | **yes, every one** — re-searched at instruction granularity and re-emitted |
| the census walk | **yes, in full** |
| the residue campaign | **partly, plus an unmeasured tail** |

Of the 851 flipping rows, **844 sit in generated boards and 7 in
hand-written ones**.  So the flip costs no new mathematics per machine —
but it does cost a different certificate type from the emitters for 844
rows, and the search behind all 5,100 boarded rows runs again either way.

**Verdict.**  The design work does not repeat and the hard individual
proofs mostly do not — that is the real saving, and it is the part that
carried this project's risk.  Everything downstream of "we know how to
prove this shape" does repeat: search, emit, walk, assemble.  Weighted
by effort rather than by lines, re-founding the development on
instruction beeps looks like **30–50%** of the original — not a rewrite,
but not a port either.  The honest caveat is that the tail is not
measured: the 10,597 machines that lose acyclicity liveness were tested
against four of the census's seven tiers, and the three untested ones
are exactly those that recovered 77.1% of the state-level residue.  So
the cheap first move, if this is ever attempted, is to run the **full**
Coq decider pipeline at instruction level rather than this four-tier
proxy — that single measurement is what turns the range above into a
number.

---

## Reproducing

```sh
cc -O2 -o ladder_i     tools/instrbeep/ladder_i.c
cc -O2 -o probe_instr  tools/instrbeep/probe_instr.c

# the full TNF walk at both levels (~2 min, single core)
./ladder_i --gas 512 --holdouts tools/BBB4_holdouts_3713.txt \
           --residue residue_i.txt

# per-machine last-visit / last-fire, with inter-fire gaps
cut -f1 tools/closeout/frozen_map.tsv | tail -n +2 | \
  ./probe_instr --steps 5000000 > frozen_probe.tsv
```

`ladder_i` at the state level must print the committed census numbers
(3,995,005 nodes, residue 228,726, max halting step 107) — if it does
not, the instruction-level column means nothing.
