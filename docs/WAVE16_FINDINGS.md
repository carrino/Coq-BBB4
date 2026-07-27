# Wave-16 — the lap never had to close exactly; 126 boards, `D_remaining` 1,016 → 890

_Branch `claude/coq-bbb4-next-session-ctox52`, off merged wave-15 + PR #40.
This wave took the ranked item (1) of the wave-15 prompt — the `AFFINE/AFFINE`
bucket, "a confirmed search gap" — and found the gap is not in the search.
**Read §2 before touching `derive_chain` again, and §5 before assuming a
population needs a new theory.**_

_A CONCURRENT session ran a separate wave-16 on the HOLDOUTS front (PR #42,
`docs/HOLDOUTS_MXDYS_SN.md`, 6 boards); the two are disjoint and were merged.
**After the merge `D_remaining` is 884**, not the 890 in the scoreboard below
— 1,016 − 126 here − 6 there, so nothing was lost either way.
`NEXT_SESSION.md` §2e is this track (RESIDUE) and §2d is that one
(HOLDOUTS)._

## 1. Scoreboard

| | |
|---|---:|
| boards this wave | **126** (all `LAPC_*`, through the one checker) |
| `D_remaining` | 1,016 → **890** (→ **884** merged with the holdouts track) |
| frozen rows settled | 4,140 → **4,266 / 5,156 (82.7%)** |
| new Coq | `Counters/LapCertGlueLift.v` — additive, axiom footprint unchanged |
| board axiom footprint | `functional_extensionality_dep` only, on all 126 |
| closeout | `audit.py` OK — tables still partition the frozen list exactly |
| census | `census_cache --check` = MATCH at every commit; `theories/Census/` untouched |

`LapDecider.v`, `LapGlue.v` and `LapCertGlue.v` are **untouched**. No existing
board changes.

## 2. The bucket was never blocked on the chain search

Wave-15 §5b: *"`ovfshape` says the lap is affine and `derive_chain` cannot find
it… it is a search gap"*, and the wave-14/15 prompts both said to instrument
`derive_chain` and find what it refuses.

Instrumented, **`derive_chain` finds the chain**. What rejects it is the test
for having arrived. On `0RB1LA_1RC0LA_0LD1RB_1LA1LD` (Jp, interior `4j+8`) the
chain `[SCycL 2 0; SWin 4; SCycR 2; SWinR 4]` lands on

```
reached  q1 h0  L=[|11^(1j+0)|10]  R=[0|^(0j+0)|]
target   q1 h0  L=[|11^(1j+0)|10]  R=[ |^(0j+0)|]
```

— one trailing blank, and `CTape.lift_side l = fun n => nth n l S0` cannot see
it. `LapDecider.lap_of_run` and `LapGlue`'s `Hlap` **both already ask only for
a `lift` equality**; the emitted *overflow* branch already exploits exactly
that (`geo_*`), and the hand-written `WLS_*` boards discharge it with
`WTape.lift_app_blank`. Only two things wanted the syntactic form:

* **`lapcert.side_eq`** strips trailing blanks from `rest` only. When a side
  carries no rep, `sden_parts` folds everything into `P` and `rest` is empty,
  so the leniency is dead *precisely* where the whole side is a constant word
  — which is the end of a lap, right after the machine writes a blank beside
  the head.
* **`lapcert._shape_to`** compares `pre/u/a/b` syntactically, so even a lenient
  match is discarded: no rotation can delete a trailing blank.

The measurement that settles it: with the matcher made faithful to `lift`, the
emitter goes from **0 to 29** on the bucket, and then from 29 to **116** once
the same slack is allowed on the overflow branch; §7 items 3 and 4 took it to
**126**.

## 3. What was built

### `theories/Counters/LapCertGlueLift.v` (new, additive)

`LapCertGlue.reach_ovf` chains INTERIOR laps by exact `cconf` equality, so an
interior lap that closes up to `lift` cannot use it. The fix is not a new
argument, it is the same one moved into `stepn`/`lift` space, where
`LapGlue.glue_reach` already chains:

* `reach_ovf_lift` — same well-founded induction on `JpCounter.tovf`, chained
  with `stepn_add` + `csteps_lift` + a rewrite by the lap's own `lift`
  equality, so the blank slack never accumulates into a term mismatch;
* `vis_via_ovf_lift` — its `vis_via_ovf` twin;
* `glue_neverqh_lift` — `LapGlue.glue_neverqh` with the visit premise weakened
  from a concrete `csteps` run to `stepn` on the lifted anchor. `glue_neverqh`
  pushes that premise through `csteps_lift` immediately, so the concreteness
  was never used; `glue_reach` is reused verbatim;
* `vis_lift_of_csteps` — the one-line bridge that lets a board keep its
  existing per-state `srun_st` witnesses.

`Print Assumptions` on all four: `functional_extensionality_dep`.

### The emitter

`side_eq` / `_match` / `_shape_to` / `_win_candidates` / `derive_chain` take a
`lift` flag, **default `False`**. The exact route is tried first and preferred
— it is cheaper and it keeps `reach_ovf` available — and the lift route runs
only where the old code raised `no interior chain` / `no overflow chain`.

Threading the flag into `_win_candidates` is load-bearing and was the first
thing to get wrong: the target-aware window cuts (wave-13 §4.1) decide whether
the winning cut is ever offered as a candidate at all. With the flag on the
acceptance test alone, the bucket still derived 0.

`_shape_to` needed more than leniency. Accepting the first **denotational**
match returns the empty rotation — the reached config already denotes the
target, that being why the chain got there — leaving the rep side misaligned
(`post (0,0,1)` against the anchor's `(1,0)`), which the board's glue cannot
render and which `derive()` then rejected downstream as `overflow close
mismatch`. It now **scores** each rotation by how many sides reach the
target's syntactic shape and takes the best, accepting slack only where
rotating cannot help. With `lift=False` the score is 2 or nothing — the
shipped behaviour exactly.

The overflow half needed **no new Coq**: `geo_*` already closes up to `lift`,
so `HD`'s right side becomes `@FAR@ ++ [S0]` and the close gains one
`rewrite lift_app_blank`.

## 4. Numbers

`ovfshape.py` re-run over all 1,016 (the committed `frozen_unproven.txt`):

| interior / overflow | count |
|---|---:|
| `AFFINE`/`EXP2` | 500 |
| `-`/`no-anchor` | 246 |
| **`AFFINE`/`AFFINE`** | **175** |
| `QUAD`/`QUAD` | 41 |
| `PARITY-AFFINE` | 13 |
| `HIGHER`/`HIGHER` | 13 |
| `EXP3` / `EXP4` / `AFFINE`-`HIGHER` | 10 / 9 / 9 |

**The `AFFINE/AFFINE` count is 175, not the 141 wave-15 §5b records.** That
number no longer reproduces with today's tools; use the rerun.

Emitter over the whole residue, after the fix:

| outcome | count |
|---|---:|
| **boards** | **116**, then **126** with §7 items 3-4 |
| no overflow chain | 735 |
| no interior chain | 105 |
| no anchor | 35 |
| no visit witness (StA targeted) | 15 — see §6b |
| multi-cell far slack | 7 — now boarded |
| lift route under `glue_qh`/`glue_qh_abs` | 3 — now boarded |

Cross-referenced against `ovfshape`, the two big remaining buckets are:

| failure | dominant shape |
|---|---|
| no overflow chain (735) | 492 `AFFINE`/`EXP2` (THE TASK), 211 no-anchor, **23 `AFFINE`/`AFFINE`** |
| no interior chain (105) | 41 `QUAD`, **14 `AFFINE`/`AFFINE`**, 13 `PARITY-AFFINE`, 13 `HIGHER` |

so 37 in-model machines remain unboarded — the smallest named populations
left, and the natural next check with the question §6 asks.

Regression: of the 376 previously emitted `LAPC_*` boards, **370 re-derive**;
the 6 that do not fail identically on the pre-change tools.

## 5. DO NOT RETRY (measured this wave, each 0 of 31 on the bucket)

* **A depth-aware memo in `derive_chain`.** The DFS `seen` set is depth-blind,
  which is a genuine incompleteness and it *fires* — on 29 of 31 machines a
  config is re-reached at a shallower depth and pruned. It is still not the
  blocker. Fixing it alone boards nothing.
* **`SFold` at `m = 3,4`** instead of `m ∈ {1,2}`.
* **Window cuts that enable a rotation or fold**, by analogy with the
  cycle-enabling cuts.
* **More search budget.** `maxdepth = 24` is *never reached* on this
  population (`dhit = 0` on all 31, `dmax` 7–21). This was never a budget
  problem — which matches `nestboot`'s (24,64)→(64,512) result.
* **Blank-padding the anchor's `FAR`** to absorb the slack into the anchor
  family instead of the matcher: 1 of 11.

## 6. The lesson

Wave-15's standing lesson was *when the expert has named the tools, measure
them*. The twin of it: **when a population is "in model but the search can't
find it", check what the search is being asked to prove before widening it.**
Five widenings of `derive_chain` were tried across waves 13–16; the binding
constraint was a two-line acceptance test that had been stricter than the
theorem since the checker was written. The theorem statement — `lift c' = lift
(Cf (Pos.succ p))`, right there in `LapDecider.LapStep` — said so all along.

Corollary worth carrying: **`LapGlue`'s premises are the specification; the
emitter's templates are one implementation of them.** When a board will not
render, check the premise before extending the theory.

## 6b. The 15 "no visit witness" machines are NOT visit-witness machines

Wave-15's prompt, ranked item (2): *"Their missing state is genuinely LIVE,
but fires only in the INTERIOR lap, where `LapCertGlue.vis_via_ovf` cannot see
it. A `vis_via_int` dual … would catch them."*

Built the dual — `LapCertGlueLift.vis_via_int_lift`, and it is the easy
direction: reaching an interior anchor costs at most ONE lap, because
`cview p = (j, None)` means `p` is all ones and the successor of an all-ones
positive is `xO _`, whose `cview` is `(0, Some _)` by computation
(`cview_none_succ`). Wired the emitter to look for the missing state in the
INTERIOR chain and close through it.

**It fires on none of the 15, because the premise is false.** Simulated all
15: `StA` is visited 2–3 times and its LAST visit is at step 4–11. It is not
live at all — these are quasi-halters whose quiet state is `StA`.

So why do they not take the quasi-halting closers?

* `glue_qh` needs `Huntarget` — nothing targets `StA`. Something does: e.g.
  `1RB1RC_1LC0RB_0LC1RD_0RB1LA` has `D1 -> 1LA`.
* `glue_qh_abs` needs a state set closed under the table, containing the
  machine from index `d` on and excluding `StA`. `absorb_search` cannot find
  one, and cannot in principle: `closed_b` is a **digraph** fact over all
  symbols, so any set holding `StD` must hold `StA`.

The needed fact is symbol-aware: `StD` never READS `S1` after the boot. That
is a lap-level invariant, not a digraph one, and it is a real build — but it
is a different build from the one that was queued, and the queued one was
measured to be worth zero. The bound would be tiny (`QHBound 12` covers all
15).

`vis_via_int_lift` is proved, compiled and axiom-clean, and the emitter path
for it is wired and guarded — it simply has no customer yet. Kept rather than
reverted because interior-only visits are a real shape the closers could not
previously express; noted here so the next reader does not mistake it for
dead weight or re-derive it.

## 7. What is next

1. **`no overflow chain`, 735 machines.** Now by far the largest bucket, and
   500 of the 1,016 are `AFFINE`/`EXP2` — the exponential overflow, i.e. THE
   TASK of the wave-15 prompt (`docs/NESTED_LAP_PLAN.md`), untouched by this
   wave. This wave does not change its analysis.
2. **`no interior chain`, 105.** Worth one instrumented look with the same
   question this wave asked, on the machines that are *not* `EXP2`.
3. **The 7 multi-cell far-slack machines.** The guard rejects them rather than
   emit an unprovable `HD`; a general `strip`-based close (`ExactClosure.
   strip_lift` rather than a fixed number of `lift_app_blank` rewrites) takes
   them.
4. **The 3 wanting the lift interior route under `glue_qh` / `glue_qh_abs`.**
   Each needs the same weakening `glue_neverqh_lift` got — mechanical, and
   `LapCertGlueLift.v` is the place.
5. Unchanged from wave-15: the 15 `no visit witness`, the 13 `PARITY-AFFINE`
   (~3 boards, do not oversize), the 35 `no anchor`, and the mxdys holdouts.
