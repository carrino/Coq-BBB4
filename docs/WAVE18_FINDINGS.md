# Wave-18 — THE TASK lands: the exponential overflow boards, 225 of them

_Branch `claude/coq-bbb4-residude-oy73r4`, off merged wave-16 + wave-17.
This wave took **THE TASK** of the wave-15 and wave-16 prompts — the
`AFFINE`/`EXP2` bucket, the residue's dominant class, whose overflow lap costs
`Θ(2^j)` — and produced its first boards. `D_remaining` **883 → 658**._

_**Read §2 before touching any chain search in this tree again.** The wave-16
lesson was not spent; it had one more level to give._

## 1. Scoreboard

| | |
|---|---:|
| boards this wave | **225** (all `NLAP_*`, through the one checker) |
| `D_remaining` | 883 → **658** |
| frozen rows settled | 4,273 → **4,498 / 5,156 (87.2%)**, from 82.9% |
| new Coq | `Counters/NestedLapLift.v` — additive; `LapDecider.v`, `LapGlue.v`, `LapCertGlue.v`, `NestedLap.v` all untouched |
| board axiom footprint | `functional_extensionality_dep` only, on all 225 (checked, one `Print Assumptions` per board) |
| closeout | `audit.py` OK — the tables still partition the frozen list exactly |
| census | `census_cache --check` MATCH at every commit; `theories/Census/` untouched |

No existing board changes. The nested route is a FALLBACK inside
`emit_lapcert.derive`, tried only where the flat one raises `no overflow
chain`, so nothing that derived before takes a different path.

## 2. The blocker was the wave-16 acceptance test, one level down

`docs/NESTED_LAP_PLAN.md` had Stage A (find the inner family) and Stage B
(`Counters/NestedLap.v`, the composition theorem) DONE since wave-15, and
Stage C — the emitter — stuck with a measurement attached:

> the **boot** chain is the blocker: 1 of 12 … **It is NOT a search-budget
> problem.** Raising `(maxdepth, nmax)` from `(24, 64)` to `(48, 256)` and
> `(64, 512)` changes nothing on any failing machine.

Correct, and the reason was written three lines further down without being
recognised:

> REAL inner anchor `st=B L=11111111100 R=0`
> SYMB `CinS = rep [1,1] 4 ++ [1]` — 9 cells, real is 11

That is verbatim the wave-16 symptom. `tools/counters/nestboot.py` was
written in wave-15 and calls `lapcert.derive_chain` with the default
`lift=False` — the acceptance test wave-16 measured to be **stricter than the
theorem**. The two trailing blanks it refuses are invisible to
`CTape.lift_side l = fun n => nth n l S0`, and no obligation anywhere in
`LapDecider`/`LapGlue`/`NestedLap` ever asked about them.

**The 2×2, so the two candidate causes are separated rather than confounded**
(`tools/counters/nestboot2.py`, 30 machines of the bucket, K = 6; a cell
counts a machine only if BOTH the boot and the exit chain derive):

| | exact joints | joints up to `lift` |
|---|---:|---:|
| best-scoring inner key (= `nestboot.py`) | 5 / 30 | 9 / 30 |
| **every inner key enumerated** | 7 / 30 | **17 / 30** |

Key enumeration alone (the wave-13 §4.1 correction the plan already
prescribed) is worth +2; the `lift` joints are worth +10 on top of it. And on
**all 17** the inner family's own interior lap derives too — so the joints
were the binding constraint on the whole Stage-C population, not merely on
the boot.

## 3. What was built

### `theories/Counters/NestedLapLift.v` (new, additive)

`NestedLap.nested_overflow` chains its three pieces by exact `cconf` equality
at the two inner joints (`Hboot` lands ON `Cin v0`; `Hin` closes ON
`Cin (Pos.succ v)`). Weakening both to `lift` is the same move
`LapCertGlueLift.v` makes for `LapCertGlue.reach_ovf` — redo the induction in
`stepn`/`lift` space, where the blank slack cannot accumulate into a term
mismatch, and pull back to a `csteps` run ONCE at the end:

* `cview_fill_pow2` — `cview (fill (pow2 j)) = (S j, None)`. The converse of
  `IXPGadgets.cview_none_shape`, and what lets the INNER alphabet's own
  overflow decomposition name the exit chain's start word.
* `inner_to_fill_lift` — `NestedLap.inner_to_fill`'s well-founded induction on
  `JpCounter.tovf`, in `stepn`/`lift` space. This is where the `Θ(2^j)` lives,
  and it lives inside an `exists n`; `2^j` is never written down.
* `vis_via_fill` — a state that fires only in the EXIT half of the overflow is
  still visited from the outer overflow anchor. Needed because `vis_of_run`
  sees a prefix of ONE chain and a nested overflow lap is three pieces;
  measured to be what **8 of 30** sampled machines need.
* `nested_overflow_lift` — boot + inner + exit, pulled back by
  `LapCertGlueLift.stepn_csteps_at`. Its conclusion is verbatim what
  `lap_of_run` produced, which is why `LapGlue.glue_neverqh`,
  `LapGlueQH.glue_qh` and `LapGlueAbs.glue_qh_abs` all consume it unchanged.

`Print Assumptions` on all four: `functional_extensionality_dep`.
`cview_fill_pow2` is `Closed under the global context`.

### `tools/counters/nestcert.py` (new) and the emitter

Per machine, inside the outer anchor `emit_lapcert` already found:

1. simulate ONE overflow phase and decode every blank-head configuration in it
   under every `obS = 0` alphabet at every `(state, tail, far)` split — the
   inner family search, ENUMERATED not ranked;
2. derive three chains with the EXISTING `derive_chain`, exact first and then
   up to `lift`: boot `B0 → Cin(pow2 j)`, exit `Cin(fill(pow2 j)) → B1`, and
   the inner family's own interior lap;
3. check the two landing shapes are the anchor plus TRAILING BLANKS and
   nothing else (anything else raises, and the machine is skipped);
4. **differentially validate all three against the raw simulator** — exact
   step counts and exact configurations, at `j = 2..7`, replaying every one of
   the 246 inner laps, not just the endpoints.

The Coq glue is four lemmas per board (`epow2_`, `gbo_`, `gxi_`, `gen_`) plus
`lapin_`/`lapo_`; `gso_` and `geo_` are the flat emitter's, unchanged, because
the exit chain's landing IS an ordinary overflow endpoint.

**The inner alphabet is searched independently of the outer one.** Measured
inner ≠ outer on 37% of this bucket (wave-15 Stage A), which is the real
reason `emit_ixp.py` — `Ip` at both levels — derives 0 of it.

## 4. Numbers

`ovfshape.py` re-run over the whole 883 at the start of the wave:

| interior / overflow | count |
|---|---:|
| **`AFFINE`/`EXP2`** | **500** |
| `-`/`no-anchor` | 239 |
| `AFFINE`/`AFFINE` | 52 |
| `QUAD`/`QUAD` | 41 |
| `PARITY-AFFINE` | 13 |
| `HIGHER`/`HIGHER` | 13 |
| `EXP3` / `AFFINE`-`HIGHER` / `EXP4` | 10 / 9 / 6 |

(The `AFFINE/AFFINE` count is 52, not wave-16's 175 — wave-16 boarded 126 of
them. `AFFINE`/`EXP2` is 500, exactly wave-16's figure.)

The emitter over the whole 883, cross-referenced against that classification:

| shape | n | boarded | what the rest fail on |
|---|---:|---:|---|
| **`AFFINE`/`EXP2`** | 500 | **225 (45%)** | 134 no inner family at `pow2 j`, 111 no exit chain, 20 no boot chain, 8 no interior chain, 2 no inner interior chain |
| `-`/`no-anchor` | 239 | 0 | 211 "no overflow phase" + 28 "no anchor" — these never had a decodable anchor family; the nested probe just reports it differently |
| `AFFINE`/`AFFINE` | 52 | 0 | 23 no inner family, 15 no visit witness (StA), 14 no interior chain |
| `QUAD` / `PARITY` / `HIGHER` / `EXP3` / `EXP4` | 83 | 0 | all on the INTERIOR branch, which this wave does not touch |
| `AFFINE`/`HIGHER` | 9 | 0 | 5 no inner family, 2 no boot, 2 no inner interior |

So the residue's failure profile at `D_remaining = 658` is

```
 265  no inner family at pow2 j  (162 of them AFFINE/EXP2)
 211  no overflow phase          (the no-anchor bucket)
 105  no interior chain          (QUAD 41, HIGHER 13, PARITY 13, EXP3 10, EXP4 6, AFFINE/AFFINE 14, EXP2 8)
 111  no exit chain
  28  no anchor
  22  no boot chain
  15  no visit witness (StA is targeted)
   4  no inner interior chain
```

**Read the boot/exit split with §4b.**  `derive_nested` at first reported the
LAST key tried rather than the furthest any key got, which filed a machine
whose best key derived a boot and failed on the exit under "no boot chain".
The table above is after the fix; the raw numbers from the wave's own sweep
(68 boot / 65 exit) are the pre-fix ones and should not be quoted.

## 4b. The two remaining chain buckets are EXPONENTIAL, not search gaps

Both were measured the way `ovfshape` measures a lap -- raw step count against
`K`, at the inner key the emitter actually selects (`tools/counters` probes,
recorded in `docs/` only, since they answer a one-time question):

| bucket | sampled | AFFINE | EXPONENTIAL (ratio -> 2) |
|---|---:|---:|---:|
| `no exit chain` | 24 | **0** | **24** |
| `no boot chain` | 22 | 2 | 14 (+6 no key at that anchor) |

So no `srun` can express these halves, and no widening of `derive_chain` can
find one: `sside` carries `a*j + b`.  This is the case
`NESTED_LAP_PLAN` §3 flags and tells you to check before building a third
level -- *"`innerfam` requires the decoded values to be exactly
`2^(K-1)..2^K-1`, and a SUBSEQUENCE of a longer count satisfies that too"*.
An exponential EXIT says the inner counting is not finished at
`fill (pow2 j)`; an exponential BOOT says it started before `pow2 j`.  Either
way the inner family is mis-identified at one end, and that -- not the chain
search -- is where the next 130 machines are.

## 5. DO NOT RETRY (measured this wave)

* **A wider inner-key tail.** `inner_keys`' `maxtail` at 6 instead of 3 DOES
  find families: 13 of 40 machines that report "no inner family" at 3 gain a
  key, and `K ∈ {5,6,7}` changes nothing, so tail length — not the octave — is
  what hides them. Re-running the whole 299-machine failure set at 6 boards
  **ZERO**: 33 machines move from `no inner family` to `no boot chain` / `no
  exit chain`. The longer-tailed families exist and no chain lands on them.
  `nestcert.MAXTAIL` records this.
* **Raising `maxkeys`.** Key counts on the failing bucket are **0–4**. The
  40-key cap has never been binding.
* Everything on wave-16 §5 and wave-15 §5 still stands; nothing here reopens
  them.

## 6. The lesson

Wave-16's was *when a population is "in model but the search cannot find it",
check what the search is being asked to prove before widening it.* This wave
is the same defect surviving a level of abstraction: the fix went into
`lapcert.derive_chain` as a **parameter with a `False` default**, and
`nestboot.py` — written one wave earlier, in the same tree, by the same track
— never had its call site revisited. The measurement it produced
(`boot: 1 of 12, and it is NOT a search budget`) was correct, was believed,
and pointed at the wrong thing for two waves.

**Corollary worth carrying: when a fix lands as a defaulted flag, grep for
every caller of the function, not just the one that motivated it.** The
wave-16 write-up says the flag "defaults to `False` … the lift route runs only
where the old code raised". That is right for `emit_lapcert`, and it silently
excluded the prototype that most needed it.

## 7. What is next

1. **`no inner family at pow2 j`, 265** (162 of them `AFFINE`/`EXP2`) — now
   the largest bucket. §5 rules out the cheap widening. What is left is the
   one Stage A already named: 21% of these inner counters run at **another
   octave or offset**, and both the glue (`epow2_`, `gbo_`) and the search
   hard-wire `v0 = pow2 j`. `NestedLapLift.nested_overflow_lift` is stated at
   an arbitrary `v0`, so this is emitter work, not theory. Note
   `NESTED_LAP_PLAN`'s index-shift warning: the naive reindex to `v0 =
   pow2 j + 1` needs count `j-1`, which an `sside` (`a*j + b`, `b : nat`)
   cannot carry, and the naive construction measured 0 of 12.
2. **`no exit chain` (111) / `no boot chain` (22).** §4b measured these:
   the missing half is EXPONENTIAL, so this is NOT a search gap and no
   `derive_chain` widening can touch it. The inner family is mis-identified at
   one end — the counting does not start at `pow2 j` (exp boot) or does not
   stop at `fill (pow2 j)` (exp exit). Fix the identification, or nest
   `nested_overflow_lift` inside itself (it is stated generically in `Cin`, so
   it should compose); measure which before building either.
3. **`no interior chain`, 105.** Unchanged by this wave and now the shape-most
   diverse bucket: `QUAD` 41, `HIGHER` 13, `PARITY-AFFINE` 13, `EXP3` 10,
   `EXP4` 6, `AFFINE/AFFINE` 14, `EXP2` 8. The 41 `QUAD/QUAD` are the largest
   population in the whole residue that has never had a design pass;
   `Bounce_8.v`'s `MeasureGlue` nesting is the precedent.
4. **The 15 no-visit-witness machines** — unchanged from wave-16 §6b, and its
   analysis stands: they are quasi-halters whose quiet state is `StA`, they
   miss `glue_qh` (`StA` IS targeted) and `glue_qh_abs` (`closed_b` is a
   digraph fact), and what is actually true is symbol-aware. `QHBound 12`
   covers all 15.
5. **The 239 no-anchor machines** need `alphabet_infer.py` first, and may or
   may not then be `EXP2`.
