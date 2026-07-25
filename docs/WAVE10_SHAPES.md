# Wave-10 — the lap-shape templates: 4-window Jp, 2-phase Ip, and what remains

_Written 2026-07-25, the shape-template session (branch
`claude/residue-reduction-4-2-07rtlv`, off the wave-9 emitter branch).
Executes `COUNTER_CLOSEOUT.md` §10 steps 1–3.  Companions: `WAVE9_FINDINGS.md`
(the orientation cube and the Ip unblock), `COUNTER_CLOSEOUT.md` (the plan and
the do-not-retry list)._

## 1. Headline

**127 new boards** from three template variants, all kernel-verified
(`Print Assumptions` = `functional_extensionality_dep` only), zero new
soundness surface:

| template | emitter | boards | shapes covered |
|---|---|---:|---|
| 4-window Jp (`ILS1_*`) | `emit_shape1.py` | **72** | ranks 1, 3, 6 (`-CC|+CB|-BC|+CB`), 8 (`-BB|+BD|-DB|+BD`) |
| 2-phase Ip (`ILS4_*`) | `emit_shape4.py` | **31** | rank 4 (`-DA|+AB`) 25/25 first try, plus `-CD|+DA`, `-DB|+BC`, `-CD|+DB` |
| flip-P1 Ip (`ILS4F_*`) | `emit_shape4.py --flip (auto)` | **24** | the AFFINE members of `+AB|-BA|+AB`, `+CB|-BC|+CB`, `+BC|-CB|+BC`, `+DC|-CD|+DC`, `+CD|-DC|+CD` — two close variants (A eats the last return pair's S0; B, the `+AB` family, a bare `[S1]` deposit) |
| hand board (in the 72) | — | 1 | the shape-1 reference |

Wave-8/9 predicted "one template per lap shape".  Measured: **one template
per encoding-side covers every affine shape of that side** — the window chain
depends only on the pair dance (`Jp`: ripple `[S1;S0]→[S1;S1]`, width-1
return; `Ip`: 1-cell ripple, width-2 rewrite return `[S1;S1]→[S0;S1]`), not
on which states play the roles and not on the phase count.  The lapshape
signature was the right CLUSTERING key but is not the right TEMPLATE key.

## 2. The rep-algebra junctions (the thing §10 step 1 wanted established)

Worked out by hand in `ILS1_1RB0RB_1LA1LC_1LB0RD_0LC1RD.v`, then parameterized:

1. **Blank far-side CELL.**  `Cc p = (E, (Jp p ++ tail, S0, [S0]))` makes both
   branches of the Jp lap close EXACTLY — the closing overshoot lands inside
   the `[S0]` window (wave-9's discovery, now load-bearing on the Jp side).
   On the Ip side the interior never looks right of the frontier, so
   `far = []` and the interior is exact for free.
2. **No P1 prologue on the Jp side.**  The anchor's blank head rotates through
   the cycL ripple unit as the unit's own data cell (`u=[S1;S0]`, head `S0`),
   killing Interleave_TGT's P1 window and its `pair_rot` juggling.
3. **Odd return runs.**  `S1 :: rep [S1] (2*j) ++ far` is definitionally
   `rep [S1] (S (2*j)) ++ far`; the goal-2 junction closes with
   `rewrite <- rep_slide` instead of `rep_shift`.
4. **The wall (lift) overflow.**  Wall machines (tail `[0;1;0]` etc., and ALL
   `ILS4` machines) rebuild the wall one cell deeper on overflow and consume
   the anchor's synthetic deep blank: the overflow closes up to ONE trailing
   blank on the LEFT.  Uniform close: `fold_tgt` / `fold_ovL` bring both
   sides to `rep [S1] a ++ fixed`, then `closeO` (an `a = b -> lift = lift`
   lemma via `lift_side_app_blank`) discharges it with `lia`.  The INTERIOR
   stays exact, which is all the deep-visit `tovf` induction needs.
5. **Ip interior junction** is `pair_rot` (generic in its symbols, as
   promised); the Ip overflow far-side excursion is an open-right window
   (`wsteps_frame_r`) and the deep state is witnessed from a `reach_fin2`
   landmark + a prefix of the close — wave-9's visit-obligation pattern.

## 3. The split that actually matters: affine vs exponential OVERFLOW

`lapshape.py` clustered by INTERIOR lap only.  The overflow branch splits the
population again, and TEMPLATE-fit follows the overflow, not the signature:

| shape (count) | enc | overflow cost | status |
|---|---|---|---|
| `-CC|+CD|-DC|+CD` (31), `-DD|+DC|-CD|+DC` (28), `-CC|+CB|-BC|+CB` (13), `-BB|+BD|-DB|+BD` (9) | Jp | affine `a+4j` | **72 boarded** (`ILS1`); 6 stragglers = B-row `1RB` family + 2 walls |
| `-DA|+AB` (25) | Ip | affine `4j+7`-ish | **25 boarded** (`ILS4`) |
| `+CB|-BC|+CB` (12) and the affine members of the flip shapes | Ip | affine | **24 boarded** (`ILS4F`): shape-4 chain with a frontier-FLIP P1 (2 steps in the far `[S0]` window), ripple `2j+1` / `2j'+2` through the wall; 8 residual members have a third close variant (`no flip skeleton`) — stragglers |
| `+AB|-BA|+AB` (29), `+BC|-CB|+BC` (14), `+DC|-CD|+DC` (6), `-CA|+AB` (9), `+CD|-DA|+AB` (8), `+CD|-DC|+CD` (6)... | Ip | **`~c·2^j' + 4j' + d`** (measured 10·2^j'+4j+4, 8·2^j'+…) | **the exponential-overflow family**: all-ones → 101010 takes a full rewrite pass per position; needs an INNER induction (a sweep lemma), not a window chain |

The exponential overflow is a real structural boundary: no finite window
chain can express a lap whose cost is linear in the counter VALUE.  It is
NOT a dead end — `glue_neverqh` only needs an existential `csteps` witness
per lap, which an auxiliary induction (inner anchor family for the rewrite
passes) provides — but it is a new template FAMILY, one level of induction
deeper, and it gates ~70 machines.

## 4. Stragglers with diagnosed mechanisms (do not lose these)

* **B-row `1RB` overflow-return family (6 machines):**
  `1RB1LC_0LC1RB_… / 1RB1LC_1RC1RB_…` (shape 1),
  `0RB1LD_{0RC,1LC,1RC}1RB_… / 1RB1LD_0LC1RB_…` (shape 3).  Their overflow
  return runs in StB while the interior returns in StD ⇒ the template needs a
  SECOND RET/FIN pair for the overflow branch (mechanical extension of
  `emit_shape1.py`; the derive already isolates it — `U['RET']` differs
  between branches).
* Two shape-1/3 machines report `laps not affine` at the derived anchor —
  unprofiled; check their anchor variant before believing the verdict (§2
  rule of WAVE9).
* **Eight flip-family machines** (`1RB1LA_0LA1RC_0LD0RB_---1RA`,
  `…_1RA0RC`, `0RB1RB/1RB0RD/1RB1RB_1RC1LB_0LB1RD_0LA0RC`,
  `0RB1RC/1RB1RC_0LC1RD_1RB1LC_0LA0RB`, `1RB1RC_0LA0RD_1RD1LC_0LC1RB`)
  fail `no flip skeleton` — a third FIN2/STPO shape; derive-only replay
  will show the windows in minutes.

## 5. Scoreboard

| | |
|---|---|
| boards this session | **127** (72 `ILS1_*` + 31 `ILS4_*` + 24 `ILS4F_*`) |
| running counter-family total in tree | 190 (wave ≤9) + 127 = **317** |
| of the 243 traceable | **127 boarded**; remaining 116 = ~94 exponential-overflow + 16 diagnosed stragglers (8 flip-variant-3, 6 B-row `1RB`, 2 unprofiled) + a few anchor oddities |
| `D_census` | unchanged (Class-1 boards only; fold-in deferred to stable hardware per §10 step 5) |

All batches: census_cache --check = MATCH before and after every commit;
theories/Census untouched.
