# Wave-12 — 205 boards, and the measurement that ends the emitter era

_Branch `claude/residue-reduction-4-2-cont-29bbkn`, off the merged wave-10/11
work plus the route-A closeout kit.  This wave boarded the exponential-overflow
family and two wall families, then measured why the whole per-machine approach
is the wrong shape.  **Read §4 and §5 before starting any new template.**_

## 1. Scoreboard

| | |
|---|---:|
| boards this wave | **205** (67 `IXP_*` + 96 `IXPM_*` + 26 `WLS_*` + 16 `WLSM_*` + 1 `WLJ_*`) |
| `D_remaining` | 1,589 → **1,385** |
| frozen rows settled by a board | 3,771 / 5,156 (**73.1%**) |
| `closeout_partial` | kernel-verified, `functional_extensionality_dep` only |
| census | `census_cache --check` = MATCH at every commit; `theories/Census/` untouched |

New Coq: `Counters/IXPGadgets.v`, `Counters/MpCounter.v`,
`Checkers/LapDecider.v`.  New emitters: `emit_ixp.py`, `emit_wall.py`,
`emit_wallj.py`.  New probes: `reanchor_probe.py`, `ovkind_probe.py`,
`mp_probe.py`, `scan_wall.py`, `mk_pool.py`.

## 2. A build break that had been hiding work

`make closeout` did not work.  `_CoqProject` listed 777 files against 1,438 in
the tree, and **533 of the boards the `CB_*` stages `Require` were never
listed** — all of wave 10/11 as well as this wave's.  It died with
`No rule to make target ILS1M_….vo`.  Fixed by adding the 533 (+ one
transitive dep).

**This will recur.**  `gen_stages.py` syncs only the `theories/Closeout/`
section of `_CoqProject`; board files still have to be added separately.  Ten
lines in the generator would close it permanently.

## 3. The anchor search was genuinely defective

`emit_interleave._tail_for_snaps` had three independent bugs: it read the
candidate tail off the LAST snapshot only, required the consecutive run to END
at that snapshot, and used a fraction-of-all-snapshots threshold that no family
can meet when a trace mixes several.  `derive_tail_best` /
`derive_tail_best_far` replace it with a grouped longest-run search (all four
states in one pass, prefer blank far then shortest tail) and are wired as
FALLBACKS into all five emitters, so prior boards derive unchanged.

Effect: failures moved from `no anchor family` (bailing before any template
ran) to genuine shape mismatches.  **Boards from the fix alone: 4.**  A real
false-negative source, not the binding constraint.

## 4. Four things this wave got wrong (all corrected in-tree)

Recorded because each cost real time and each was caught by John, not by me.

1. **"The wall-inner nest needs three-level recursion" — false.**  It was a
   mis-set anchor.  All 12 are plain counters, interior affine `8+4j`,
   overflow affine `4K+3`.  See `UNCERTAIN_MACHINES.md` §1.  The real blocker
   is small: the counter skips values (`2^K-1 -> 2^(K+1)`), so `Pos.succ` is
   the wrong successor and the family needs reindexing — no new glue, since
   `glue_neverqh` is already generic in `Cf`.
2. **"70% headroom, worth several hundred boards for one function" — false.**
   The sample was the *first 400 of a sorted list* (every machine started
   `0RB…`), and it classified overflows by where they LAND rather than what
   they COST, conflating IXP cases with template fits.  Corrected measurement
   over all 1,385 is in `RESIDUE_HEADROOM.md`.
3. **"These are mxdys' survivors" — false.**  Only **27** of the 5,156 are his
   holdouts (`TERMINOLOGY.md`); 5,129 are not.
4. **The `≤7` / all-8-transition "outside mxdys' enumeration" story
   (`NGHIST_WAVE7.md` §0) is bad info.**  John, who knows the enumeration
   conventions, says so; there is no separate list of machines mxdys skipped —
   it is just the complement of the 3,713.  Nothing in `WHY_NO_HAMMER.md`
   depends on it.  **Do not build on `NGHIST_WAVE7.md` §0 without re-deriving
   it.**

## 5. The load-bearing measurement: no lossy decider can finish this

Full detail in `docs/WHY_NO_HAMMER.md`.  Summary:

The hammer exists (`tools/nghist/wave8_sweep.py`), its wave-8 result files were
**empty in-tree**, so the current residue had never been swept.  Swept it:
**0 boardable out of 896.**

Then measured the mechanism.  Liveness is proven by showing the *q-avoiding
subgraph* of the closure has no infinite path.  Across `k=2..6`, `n=2..3`, on
three residue machines: the closure **always closes** (61 → 324 nodes) and the
q-avoiding subgraph is **cyclic for every obliged state at every setting**.

Cause, in one sentence: a counter carries into the high bits only after ~2^k
steps, so any FINITE window admits the abstract path "stay in the low bits
forever" — a spurious q-avoiding cycle no measure can rank.  Same wall as
RepWL's NOCLOSE 706/708, from the other side.

So exactness is genuinely required, **for the liveness half specifically**.
Non-halting is easy here; "every state recurs" is what needs an exact model.

## 6. But the exponent was wrong, and that is the real lesson

`WAVE9_FINDINGS.md` §7 already said it: *"The highest-value next build is not
another emitter… we prove one theorem per machine… the exponent is wrong."*
This wave built five emitters anyway, for 205 boards against a 1,385 residue.

The five emitters are hand-unrolled instances of ONE checker.  Every lap chain
they derive has the same shape: each tape side is a fixed prefix, ONE repeated
block whose count is affine in the carry index `j`, and a fixed suffix.

`theories/Checkers/LapDecider.v` starts that checker and compiles **closed
under the global context — no axioms**.  Landed: symbolic sides
(`pre ++ rep u (a*j+b) ++ post`) with their denotation `sden`, symbolic
configs, the three-way step type (framed window / leftward cycle / rightward
cycle), cycle soundness lifted from `WTape.cycL`/`cycR` with affine counts, the
`LapStep` obligation stated once — which is exactly what `glue_neverqh`
consumes — and `ChainSound` with composition.

Remaining: window-step soundness, the boolean checker, `LapStep -> glue`.

## 7. The encodings (five, and why they kept surprising us)

`Ip` and `Jp` put the marker BEFORE each bit, `Kp` has none, `Dp` doubles bits,
and **`Mp` (new this wave) puts the marker AFTER each bit** — John read it off
`0RB---_0RC0LD_1LD1RC_0LA1LB` as *"msb on the right, 1 to the right of every
bit"*.  Verified: it marches 1..1023 and 1..2046 CONSECUTIVELY, so unlike the
widening family `Pos.succ` is correct and `LapGlue` applies unchanged.

`Mp` differs from `Ip` by a **one-cell frame shift**, which is why the `Ip`
recognizers half-fire on it: when `b0 = 1` the word opens `[S1;S1]` exactly as
an `Ip` word does, a prefix decodes, and the lap template then misses.  237 of
the 1,385 decode as `Mp`, 202 with affine slope-4 interiors.

The lesson generalizes: **encoding, frame offset and tail should be SEARCHED at
derive time, not hard-coded.**  Five encodings were each discovered one at a
time, two of them by a human reading the tape.  In the `LapDecider` design they
are just digit alphabets — no emitter forks.

## 8. Do-not-retry, added this wave

* **NGramHist/NGramCPS liveness over this residue at ANY `(k,n,t)`** — §5,
  cyclic at every setting measured.
* **More per-machine lap emitters** — §6.  Build the checker instead.
* Widening the IXP/wall skeleton searches without tracing first: three template
  passes this wave produced 1, 4 and 13 boards respectively.  Trace two or
  three members before templating, never one.
