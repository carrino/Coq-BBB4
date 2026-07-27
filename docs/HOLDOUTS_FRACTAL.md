# The two fractals, decoded and boarded (2026-07-27)

`1RB0LA_1LC0RD_0LB1LA_0RB1LA` (BBB `fractal` cert #3) and
`1RB0LA_1LC1RD_0LC1LA_0RD0RB` (#5) were the last two holdouts for which
**BBB had no proof to port**: its own soundness note says legs 1/2/4/5
are concrete re-derivations but the "for all j" closure rests on leg 3,
and "the fixed-glue-set check evidences but does not by itself
mechanise the all-j induction; that full rigor is the parallel Coq
formalisation."  This is that formalisation.

- `theories/Machines/Counters/Fractal_3.v` — `nqh_1RB0LA_1LC0RD_0LB1LA_0RB1LA`
- `theories/Machines/Counters/Fractal_5.v` — `nqh_1RB0LA_1LC1RD_0LC1LA_0RD0RB`
- negative controls: `theories/Tests/CountersFractal_Corruption.v`
- both axiom-clean (`functional_extensionality_dep` only, inherited from `CTape`)
- `D_remaining` 1,009 → **1,007**; the `fractal` family is CLOSED.

---

## 1. What they actually are

Both machines are **binary counters whose digits are blocks**.  Write a
configuration at the moment the head sits on a blank in state `B` — the
shape that recurs — and the left half-tape (nearest cell first) is
always

```
#5 :  0^z        ++ 1 ++ b_0^1 ++ b_1^2  ++ b_2^4  ++ .. ++ b_{j-1}^(2^(j-1))
#3 :  0^(2z+2)   ++ 1 1 ++ b_0^2 ++ b_1^4 ++ b_2^8 ++ .. ++ b_{j-1}^(2^j)
```

where `b_{j-1}..b_0` are the binary digits of `z`.  Digit `i` is stored
as a **block of `2^i` cells** (`2^(i+1)` for #3).  One macro-step of the
machine increments the counter by one and eats exactly one blank on the
right (two, for #3).

That is the whole "fractal": a carry of length `m` is not a constant-cost
gadget, it is *the machine one level down*, so it costs `Theta(m^2)`
(#5) or `Theta(m^2) + Theta(3^log m)` (#3).

### The anchors

| | anchor (left list, nearest first) | tape | times |
|---|---|---|---|
| #5 | `0^(2^k - 1) ++ 1^(2^k)` | `1^(2^k) 0^(2^k)`, head on the last blank | 1, 6, 28, 120, 496, … |
| #3 | `0^(2^k) ++ 1^(2^k)` | `1^(2^k) 0^(2^k)`, head one past the last blank | 9, 31, 111, 403, 1479, … |

Lap costs, exactly:

```
#5 :  A(k) -> A(k+1)   in   6*4^k - 2^k
#3 :  A(k) -> A(k+1)   in   3*4^k + 4*3^k - 2^k
```

The `3^k` term in #3 is the thing that kills every certificate in the
repo: `Checkers/LapDecider.v` carries a side count as `a*j+b`, and no
`srun` in the language can produce a `3^k`.  `Counters/LapGlue.v`'s lap
obligation is `exists n, csteps tm n (Cf p) = Some c' /\ ...` — an
existential — so the exponential cost lives inside it and is never
written down.  **That is the only reason these two are boardable at
all**, and it is why `NestedLap.v`'s observation ("the lap obligation
never mentions the cost") generalises further than its own family.

---

## 2. The proof shape

Both files are the same three-part build.

**(a) Straight-line gadgets**, each an exact step count, each a `wsteps`
unit fed through `WTape`'s `cycL`/`cycR` or `wsteps_frame`:

| #5 | | #3 | |
|---|---|---|---|
| `bounceZ` | `B` writes, `C` walks left over `z` blanks | `phLD` | the left drift, 2 steps/unit |
| `brd`,`brdx` | `B`→`D` walks right over blanks and eats a 1 | `phBRun`,`phBSkip` | the two right sweeps |
| `turnbase` | left turnaround, 1-run of length one | `turnA` | left turnaround, general |
| `turnl` | left turnaround, general | `g1` | the one-digit bump (8 steps) |
| `inc1` | the carry-FREE increment | `inc3_1` | the carry-free increment |
| `close` | the period closer | `close3`,`head3`,`fin3` | the period closer |

**(b) The recursion**, indexed by `e` = period minus two (level `t` is
`e = 2^(t+1) - 2`):

```
SW  e : run the counter through a full period, z0 -> z0+e
INC e : one increment whose carry runs the full period length
E2  e : (#5 only) the two-parameter rewriting rule the carry unfolds into
```

with

```
#5 :  SW (e + S (S e))  <-  SW e (twice) , inc1 , INC e
      INC e             <-  turnl , E2 e
      E2 e              <-  SW e , close

#3 :  SW3n (e + S (S e)) <- SW3n e (twice) , inc3_1 , INC3n e
      INC3n e            <- phLD , turnA , g1 , SW3n e , close3
```

Every dependency is at level `<= t`, so a single `induction t` in
`SW_all` / `SW3n_all` discharges the whole system.  `#5`'s `E2` carries
a free parameter `b` that never appears in its own hypotheses — the same
device that makes the corresponding busycoq `FractalType0` arguments go
through (mxdys' `P1'` has the same free `m`), and the reason the
induction closes with **zero** leftover glue:

```
SW(2q) = SW(q)[low half] ; inc1 ; INC(q) ; SW(q)[high half]
```

lines up exactly, both in shape and in step count.

**(c) The closer.**  Anchor family `Cf p = anchor (Pos.to_nat p - 1)`,
bootstrap by `vm_compute` (6 steps for #5, 31 for #3), per-anchor visit
witnesses for all four states, then `LapGlue.glue_neverqh`.

---

## 3. Where the analogy to busycoq lands

mxdys pointed at
[`FractalType0.v` `TM48`](https://github.com/ccz181078/busycoq/blob/BB6/verify/FractalType0.v)
(`1RB0LF_1LC1RE_0LC1LD_1RB0LA_0RE0RB_---0LD`) as the model for #5, and
the transition tables really are close — `B`/`C` and the `0RE0RB` row
line up cell for cell with our `B`/`C`/`D`.  What ports is the *shape*
of the argument, not the text:

- `P1' n -> P1' (2n+1)` with a free `m` on the right  ⟷  our
  `E2 q a b` with a free `b`;
- three `follow HP1'` in the inductive step ⟷ our two `SW` uses plus
  `INC` (which itself re-enters `SW` one level down);
- `pow2_mod3` (the mod-3 case split that makes `n2 = n*2` decompose)
  has **no** analogue here: our block sizes are already powers of two,
  so the split is `e' = e + (e+2)` and needs no case analysis.

The busycoq proof closes with `sigma_score_unbounded_nonhalt` (non-halting
only).  Ours closes with `LapGlue.glue_neverqh`, which is the strictly
stronger `NeverQuasiHaltsSt` the BBB4 census actually needs — every
state recurs at unboundedly large indices, not merely "does not halt".

---

## 4. Reproducing the decode

The decode was done against a plain simulator before a line of Coq was
written; every gadget and both recursions were differentially validated
over random left/right frames and all levels up to `2^7` (#5) / `2^6`
(#3).  The measured facts a re-derivation should reproduce:

```
#5   anchor  (StB, (0^(N-1) ++ 1^N, 0, []))            N = 2^k
     lap     6N^2 - N
     Inc(m,z) framed both sides, cost 2m^2 + 2z + 3      (m = 2^t)
     E2(q,a,b) framed, cost 2q^2 + b + 1 - q             (q = 2^t, a >= q-1, any b)

#3   anchor  (StB, (0^N ++ 1^N, 0, []))                 N = 2^k
     lap     3N^2 + 4*3^k - N
     Inc3(m,z) framed both sides, cost 4m^2 + 6*3^t + 12 + 4z
     close3(e,z) cost 4e + 2z + 30
```

`tools/counters/sim.py` is the simulator; `tools/counters/chk.py`-style
"print every state-B-reading-blank checkpoint" is how the odometer word
`b_{j-1}^(2^(j-1)) .. b_0^1 1` becomes visible.  Everything under
`tools/` is UNTRUSTED; the kernel re-checks every board.

---

## 5. What this closes and what it does not

CLOSED: the BBB `fractal` family (both certs), and with it the last
family where BBB itself had no proof.

STILL OPEN in the holdout front (7 of the original 27, plus the wrap
pair): tower #20 (a ~1,500-line table interpreter — a checker port, not
a session), blockdbl #11/#13/#28 (needs `MeasureGlue`-style nesting like
`Bounce_8.v`), wave4 #15 (its gadget set is decoded — see
`NEXT_SESSION.md`), the two `1RB---` wrap-QH machines, and the v4-irules
`mmrow` machine.

The odometer-with-block-digits reading is worth trying on **blockdbl**
next: its `j = 2..7` probe data (`tools/counters/probe_bd.py`) has the
same "one lap is `Theta(m^2)` with `Theta(m)` turnarounds" signature that
made these two decode, and `Fractal_3.v`'s two-cells-per-digit variant is
already the general shape.
