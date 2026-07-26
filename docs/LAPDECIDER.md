# The lap decider: one soundness theorem, per-machine a `vm_compute`

_Wave-13.  This is the build `WHY_NO_HAMMER.md` pointed at and `WAVE9_FINDINGS.md`
§7 asked for three waves earlier: the exact lap model that waves 8-12 kept
re-deriving by hand, extracted into a CHECKER whose soundness is discharged
once._

## 0. Why this shape

Two measurements fix the architecture, and they pull in opposite directions.

* **Exactness is required.** `WHY_NO_HAMMER.md`: the NGramHist closure always
  closes, but the q-avoiding subgraph the liveness certificate needs is cyclic
  at every `(k,n)` measured, because a counter's carry after ~2^k steps is
  invisible to any finite window.  Same wall as RepWL's NOCLOSE 706/708, from
  the other side.  mxdys states the complementary condition exactly: *"my
  inductive decider can only decide a TM when it can model the forward
  behavior exactly."*
* **One theorem per machine is the wrong exponent.**  Waves 8-12 built five
  emitters for ~500 boards against a 1,385 residue.

So: an exact forward model, but one whose per-machine cost is a kernel
computation rather than a proof script.

## 1. The model

A symbolic tape side is

    sside := (pre, u, (a, b), post)   denoting   pre ++ rep u (a*j+b) ++ post ++ X

with `j` the carry index and **`X` an opaque tail** — for a counter that is
`Ip q0 ++ tail`, the high bits above the carry, which the lap never reaches.
`X` is universally quantified in every soundness statement, which is exactly
why one chain covers every `p` in the branch at once.

`theories/Checkers/LapDecider.v` is **axiom-free**.

## 2. The step language

It is a forward simulator, not a pattern matcher.  Every step is DERIVED by
the checker (it runs `wsteps` itself and reads the result off), so a
certificate is a list of small numbers.

| step | what it does | soundness from |
|---|---|---|
| `SWin n` | `n` real steps inside the two concrete prefixes | `wsteps_frame` |
| `SWinL n` / `SWinR n` | ditto with an OPEN side at a tape edge; needs that side fully concrete and its tail empty | `wsteps_frame_l` / `_r` |
| `SCycL n m` | consume the left block leftward, deposit under the first `m` cells of the right prefix | `WTape.cycL` |
| `SCycR n` | consume the right block rightward | `WTape.cycR` |
| `SRotL/R m`, `SUnrotL/R m` | move a block BOUNDARY: `rep (v++w) k ++ v = v ++ rep (w++v) k` | `rep_rot_gen` |
| `SFoldL/R m` | move the block's constant OFFSET: `(pre'++rep u m, u, (a,b)) -> (pre', u, (a,b+m))` | `rep_add` |

The window steps are the fiddly ones and were built first.  The trick that
makes `SWin` free: **the window IS the pair of concrete prefixes**, so the
entry is concrete and `wsteps true true` returns `None` precisely when the run
would leave what we know.  `sden` is already right-associated around exactly
that split, so the `wsteps_frame` instance is definitional — `swin_sound` is
four lines.

`SFold` was not in the original design and is not optional: rotations move a
boundary but cannot change `b`, and an overflow anchor is naturally REACHED as
`uD ++ rep uD j ++ …` while `cview` STATES it as `rep uD (S j) ++ …`.  Nothing
else reconciles those two.

## 3. What a board costs now

`srun_sound` turns a successful symbolic run into a concrete `csteps` for every
`j` and every tail.  Per machine the Coq file is:

* the TM table and the anchor `Cc p = (E, (Enc p ++ tail, S0, far))`;
* two `srun … = Some (…, ca, cb)` facts, closed by `vm_compute`;
* four **anchor glue** lemmas — the only per-machine mathematics — each a
  `cview` rewrite plus `app_assoc`;
* boot, visits, and the closing theorem.

`theories/Counters/LapCertGlue.v` holds the rest generically: `reach_ovf` (the
well-founded induction on `tovf` that every hand board re-proved as its own
`reach_fin2`) and `vis_via_ovf`.

`LAPC_1RB1LA_1LC1RD_1LB1RA_0LA0RB.v` is the architecture proof: the same
machine as `ILS4_…`, whose hand board spent 9 window lemmas + 9 transported
phases + 2 assembled laps.

## 4. Encodings are digit alphabets

`Ip`, `Jp`, `Kp`, `Dp`, `Mp` differ only in four words and one count offset,
so they are five ROWS of `ENCDATA` in `tools/counters/emit_lapcert.py`, not
five emitters.  Growth direction is likewise searched, not declared: a
right-growth machine is derived on its mirror and transferred through
`Mirror.mirror_never_qh` (the wave-9 route, no new theory).

    interior  (cview p = (j, Some q0)):  E p = rep uS j ++ sS ++ E q0
                                         E (succ p) = rep uD j ++ sD ++ E q0
    overflow  (cview p = (S j, None)):   E p = rep uS (j+obS) ++ soS
                                         E (succ p) = rep uD (S j) ++ soD

| enc | uS | sS | uD | sD | obS | soS | soD |
|---|---|---|---|---|---|---|---|
| `Ip` | `11` | `10` | `10` | `11` | 0 | `1` | `1` |
| `Jp` | `10` | `11` | `11` | `10` | 0 | `1` | `1` |
| `Kp` | `1` | `0` | `0` | `1` | 1 | — | `1` |
| `Dp` | `11` | `00` | `00` | `11` | 1 | — | `11` |
| `Mp` | `11` | `01` | `01` | `11` | 1 | — | `11` |

## 5. The tools

| file | role |
|---|---|
| `tools/counters/lapcert.py` | a faithful Python MIRROR of `sstep`/`srun`, plus the chain search |
| `tools/counters/emit_lapcert.py` | anchor search → chain derive → differential validation → Coq |

Both are UNTRUSTED.  The kernel re-runs `srun` on every emitted chain; a wrong
certificate makes `srun` return `None` and the board fails to compile.  The
emitter additionally validates both branches against the raw simulator — step
counts AND exact configurations — on ~200 anchors per machine before emitting.

### The search

Nearly deterministic, which is why it is cheap.  A walled window is FORCED
forward, so the only interesting cuts are: the maximal one (the wall, where
only a cycle or a rotation can make progress), any cut that lands on the
target, and any cut at which a cycle becomes available.  At a wall the
candidates are the cycles that close and the handful of legal rotations.

**A wrong assumption worth recording:** the first version took only the
MAXIMAL window cut, on the reasoning that determinism makes stopping early
pointless.  False — the last window of a lap must often stop short so that a
rotation can land the configuration on the anchor's syntactic form.  Making
the window search target-aware is what turned 0 chains into all of them.

## 6. Measured

| | |
|---|---:|
| existing hand-emitted `ILS4_*` boards re-derived automatically | **24 / 25** sampled |
| new boards off the 1,385 residue | see `WAVE13_FINDINGS.md` |

## 7. The named gap: quasi-halting counters

Of the residue, ~143 machines derive a LAP but have a state that genuinely
goes quiet — they are quasi-halters, not never-quasihalters, so
`glue_neverqh` is the wrong closer.  That is not a defect: a QH board is worth
the same as an NQH board provided the quiet bound is certified.

* **47** have `StA` targeted by NO transition, so its only visit is at index 0
  and `LapGlueQH.glue_qh` gives `QHBound 1` outright — wired in.
* **96** have `StA` targeted but fired only during the bootstrap.  These need
  a bound of `t0+1` where `t0` is the boot length, which needs one new fact:
  *the lap visits only states in `S`*.  That is computable from the chain
  (collect the states of every window sub-step and cycle unit run) but needs
  a new soundness theorem, since `cycL`/`cycR` currently state only their
  endpoints.  **This is the next build.**

## 8. Do not retry

Everything in `COUNTER_CLOSEOUT.md` §5 and `WAVE12_FINDINGS.md` §8 still
stands.  Added here:

* **Maximal-only window cuts in the chain search** — measured, finds nothing;
  the search must be target-aware (§5).
* **Reaching the anchor's syntactic form by rotations alone** — impossible in
  principle, the constant offset needs `SFold` (§2).
