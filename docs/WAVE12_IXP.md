# Wave-12 — the IXP harvest: 159 exponential-overflow boards from two templates

_Written 2026-07-25 (branch `claude/residue-reduction-4-2-cont-29bbkn`, off the
merged wave-10/11 branch).  Executes the WAVE11_MIRROR.md §3 milestone: clone
the hand-authored inner-counter reference
`IXP_1RB1LA_0LA1RC_0LD0RB_0LA1RD.v` across the 221-machine
exponential-overflow family (`tools/counters/ixp_targets_L.txt` 94 direct +
`ixp_targets_R.txt` 127 via `--mirror`)._

## 1. Headline

**159 new boards** (66/94 direct `IXP_*`, 93/127 mirror `IXPM_*`), every one
kernel-verified with `Print Assumptions` = `functional_extensionality_dep`
only, census untouched (`census_cache --check` = MATCH at every commit).

The emitter is `tools/counters/emit_ixp.py`: `validate_ixp.py`'s six-chain
symbolic replay forked into a derive layer.  Per machine it derives

  * the outer affine interior chain (P1 RIP STPI TRN RET FIN),
  * the inner anchor family `Cin v = (Ein, Ip v ++ [S1], S0, Ff)` detected by
    decoding blank-head snapshots INSIDE the K=5 overflow lap (greedy
    increasing-time subsequence for v = 16..31),
  * the inner lap (same RIP/STPI/TRN/RET units, fresh P1i/FINi),
  * the boot chain (STPO/FINx) — whose EXACT landing config defines the far
    word `Ff` (it can carry a trailing blank the stripped decode missed),
  * the exit chain (STPOe/FINe),

and validates interior p = 2..199, inner v = 2..299, boot j' = 0..7, exit
K = 1..8, and the COMPOSED outer overflow step-exactly against the raw
simulator for K = 1..7 before emitting.  The three positive gadgets moved to
the shared `theories/Counters/IXPGadgets.v`.

## 2. The family is TWO templates, not one

| variant | P1 shape | ripple | measured |
|---|---|---|---|
| V1 "flip" (the reference) | `(E,[],S0,[S0]) -> (Erip,[],S1,[S0])`, head flip inside the far window | 2j+1 interior/inner, 2j'+2 boot, 2K exit | 69 boards |
| V2 "pop" | `(E,[S1],S0,[S0]) -> (Erip,[],S1,PD)`, pops the head-adjacent S1, deposits a free 2-cell word `PD` past the frontier | 2j interior/inner, 2j'+1 boot, 2K-1 exit | 90 boards |

Load-bearing V2 discoveries:

1. **The ripple state `Erip` is a free role** (P1 may change state); so are
   the inner anchor state `Ein` (≠ the outer edge on many machines) and the
   inner far word `Ff` (`[0]`, `[1,0]`, `[0,0]`, `[0,1]`, `[0,1,0]`, … —
   measured, member by member).
2. **V2's FIN closes over the P1 deposit `PD`** (not over `[S1;S0]`), and the
   boot FINx becomes the CLOSED window `(QR,[],S1,[S1]++PD) ->
   (Ein,[S1],S0,Ff)`; the exit close reads the P1i deposit's tail.
3. **`Ff` must be read off the boot chain's exact landing**, not off the
   stripped snapshot decode — V2 boots land with an extra far blank
   (`Ff = [0,0]`), and defining `Cin` with the stripped word makes
   `boot_ov`'s `c' = Cin (pow2 n)` literally false.
4. V2's visit witnesses route through the OVERFLOW branch only (tovf
   induction + boot-prefix windows); the interior-branch `vc` route of V1
   does not survive the j = 0 interior (no S1 to peel).

## 3. The remaining 62 (`tools/counters/ixp_remaining.txt`, exact strings)

| class | n | diagnosis | route |
|---|---:|---|---|
| pop-variant combos | 34 | interiors affine (slope 4, intercepts 4–16) but the P1 window differs: pop-2 (`lw=2`, ripple 2j−1, needs a j=0 CASE SPLIT in `lap_int` — the popped pair is `[1,0]` when j=0) and pop-1 with a TWO-BLANK outer far (`Cc` far `[0,0]`; the interior close is an open-right excursion that is exact only in the far-2 anchor) | mechanical: a third template pass parameterizing the outer far word + P1 window width; vis lemmas must go tovf-only |
| wall-inner | 12 | the inner anchor carries a **ones-wall on the far side whose length is K-dependent** (nested marches at wall 4/8/12/16 in one trace; boot raw measures 9.5k–38.7k steps because `Cin(2^jp)` with a FIXED far never appears) | needs a two-parameter anchor `Cin (v, wall)` — same league as the deferred carry-shifted one-off; **do not build without a hand-authored reference first** |
| inner-split | 9 | inner lap closes raw but no P1i/FINi split replays (rem 4–13) | unprofiled; trace the inner lap window-by-window before believing the verdict |
| far-mutating P1i | 6 | P1i flips a DEEP far cell (`(1,0,1,0) -> (1,0,0,0)`) and FINi restores it | needs a far-swap window pair (P1i/FINi entries/exits with two far literals) |
| other | 1 | ripple deposit `(0,)` — not an S1 ripple | inspect |

## 4. Do-not-retry notes (measured this wave)

* Widening the V1 skeleton search caps gains nothing here either — the V1/V2
  split is STRUCTURAL (pop vs flip P1), visible in the first 5 steps of one
  interior lap trace.  Always trace before searching.
* `find_inner_anchor` must tolerate a leading spurious decode (the outer
  all-ones word decodes as `Ip v` for v = hi at an early time); require the
  greedy increasing-time march, not global consecutiveness.
* Exact-config raw measures fail on blank padding: the raw tape carries
  invisible trailing blanks mid-lap.  Compare `nrm`-stripped, then let the
  window replay pin the exact literals.
* The bootstrap may not hit the decoded `p0` exactly: search `Cc(p0..p0+8)`
  up to blank padding (`ceqb` compares lift-equal, so nrm matching is right).

## 5. Scoreboard after wave 12

| | |
|---|---:|
| boards this wave | **159** (66 `IXP_*` + 93 `IXPM_*`) |
| exponential-overflow family | 221 targets → **62 unproven** (all diagnosed, §3) |
| unproven on the frozen 5,156 | ~1,594 → **~1,435** |
| next blocks, ranked | wall-LAP skeletons ~300 (L+R); IXP pop-variant combos 34 (§3, mechanical); stragglers 14 (B-row 1RB + flip third-close); far-thread emit_shape4 + Kp emission ~33+; non-core triage 318; route-A closeout (container-safe, any time) |
