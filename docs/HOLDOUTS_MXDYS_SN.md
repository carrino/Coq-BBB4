# mxdys' S(n) claim on the 11 live holdouts — measured, and four boarded

_2026-07-27, branch `claude/coq-bbb4-holdouts-proofs-pqgv89`.  John relayed
two claims from mxdys about the 11 remaining (4,2) holdouts
(`census_holdouts_kept.txt` ∩ `closeout/frozen_unproven.txt`):_

> **(1)** "they seem to have fully predictable forward behavior, i.e. you can
> define S(n), where c0 -->\* S(0) and S(n) -->+ S(n+1), and the usage count of
> a specific transition in S(n) -->+ S(n+1) is a simple function"
>
> **(2)** "1RB0LD_1RC0RC_1LA1RB_0LC0LD is bouncer counter, simpler than sync
> bouncer counter"

Both were tested.  **Claim (2) is proved** — it is now a kernel-checked
`NeverQuasiHaltsSt` theorem, and the reading is what made the proof cheap.
**Claim (1) holds on 8 of the 11**, measured; on the other 3 the *search*
fails, not necessarily the claim (§4).

Holdouts unproven: **11 → 7**.  `D_remaining`: 1,016 → 1,012.

---

## 1. What "simple function" was tested as

A sequence is a simple function of `n` iff it satisfies a short
constant-coefficient linear recurrence (C-finite; closed form
`sum_i p_i(n) r_i^n`).  `tools/counters/snfit.py` finds the MINIMAL such
recurrence exactly over ℚ, and **requires terms beyond those the fit
consumes**, so a reported fit is a prediction that was checked rather than an
interpolation.  That matters: an earlier ad-hoc basis (`{n^k, 2^n, 4^n}`)
reported NO FIT on the fractal pair purely because it lacked `3^n`.

S(n) candidates are *record* configurations — the machine touching a
brand-new tape cell — grouped by (state, side, head offset, RLE shape word).
A candidate passes only if **every run length of S(n) and all eight
transition usage counts** over `S(n) -->+ S(n+1)` are C-finite.

## 2. Result

| machine | family | S(n) | S(n) confirmed | laps checked | boarded |
|---|---|---|---|---:|---|
| `1RB---_1LC0LB_0RC0LD_1RD1RB` | wrap-QH | `1^(2^(n+1)-1) 0`, StB | ✔ | 9 | **this session** |
| `1RB---_1RC0RB_0LC0RD_1LD1LB` | wrap-QH | `0 1^(2^(n+2)-1)`, StB | ✔ | 8 | **this session** |
| `1RB0LD_1RC0RC_1LA1RB_0LC0LD` | blockdbl #11 | bouncer counter (§3) | ✔ | 8 | **this session** |
| `1RB0RB_1LC1RA_1RA0LD_0LB0LD` | blockdbl #13 | bouncer counter (§3) | ✔ | 8 | **this session** |
| `1RB1LC_1LC1RD_1LA0LC_0RD0RB` | blockdbl #28 | `0^(2n+2) 1^(2^(n+1)-1)`, StC | ✔ | 8 | no |
| `1RB0LA_1LC0RD_0LB1LA_0RB1LA` | fractal #3 | `1^(2^n) 0^(2^n+1)`, StB | ✔ | 9 | no |
| `1RB0LA_1LC1RD_0LC1LA_0RD0RB` | fractal #5 | `1^(2^n) 0^(2^n)`, StB | ✔ | 9 | no |
| `1RB1RA_0RC0RB_1LC1LD_0RA0LA` | v4-irules | `1^n 0 1^(3^(n+1))`, StA | ✔ | 9 | no |
| `1RB0RC_0LC1LB_0LD1LC_1RD0RA` | wave4 #15 | — | search fails | — | no |
| `1RB0RD_1LC1LB_1RA0LB_1LC1RA` | tower #20 | — | search fails | — | no |
| `1RB1LD_1RC0RB_1LA0RC_0LD0LA` | double #32 | — | search fails | — | no |

Two examples of the transition-count fits, verbatim from the tool:

```
1RB0LD_1RC0RC_1LA1RB_0LC0LD   S(n) = StB, 1^(3*2^n+1) 0 1^(2n+1) 0
  A0  (9/2)4^n + (5/2)2^n        C0  (9/2)4^n + (9/2)2^n
  A1  2*2^n                      C1  3*2^n
  B0  3*2^n                      D0  2*2^n
  B1  (9/2)4^n + (5/2)2^n        D1  (9/2)4^n + (5/2)2^n - 2
  total  18*4^n + 22*2^n - 2

1RB1RA_0RC0RB_1LC1LD_0RA0LA   S(n) = StA, 1^n 0 1^(3^(n+1)), head on the
                              blank past the right end
  A0 = B0 = C1 = 3^n + 1     A1 = 12*3^n - 1     D0 = 1     D1 = 3^(n+1)
  total  243*9^n + 63*3^n + 3   (= 3m^2 + 7m + 3 for m = 3^(n+1))
```

The v4-irules row was checked out to `t = 1,307,750,844` (9 laps) with a
purpose-built C simulator, because its anchors are `Θ(9^n)` apart.

**All eight transitions have positive, unbounded counts on every confirmed
row except the two wrap machines**, where `A0 = A1 = 0` — which is exactly why
those two quasihalt rather than never-quasihalt, and is the fact their board
turns into `QHBound`.

## 3. Claim (2), proved: #11 is a bouncer counter

`theories/Counters/BCtrCounter.v` + `theories/Machines/Counters/BCtr_11.v`.

BBB models #11 as `blockdbl_counter`: the anchor `1^(3*2^n+1) 0 1^(2n+1) 0`
doubles a solid block, one macro lap costs `18*4^n + 22*2^n - 2` steps and
turns around `Θ(2^n)` times.  Read that way the proof needs a nested lap,
which is why `HOLDOUTS_WAVE14.md` filed it as a `MeasureGlue` job and it
stayed unproven.

Sampled instead at **StA on the leftmost visited cell**:

```
A(0) 1 0^(3v+3) 1 <binary counter of value v, low digit first>
```

a **bouncer of length 3v+3 — affine in the counter's VALUE** — with the
counter beyond it, low digit adjacent.  Digits are two cells: `00` = 0,
`01` = 1.  The doubling BBB sees is just what one counter overflow does to
the bouncer, and never has to be modelled, because **one bouncer sweep is
already a complete lap**:

```
S(v) -->+ S(v+1)   in   12v + 4*carry(v) + 27 steps
```

### Why it is simpler than a *sync* bouncer counter

The counter's high end needs no case of its own.  The head walks the digits
in the StB/StC alternation and stops at the first digit-0 pair — and a pair
of **blank** cells past the top digit *is* a digit-0 pair.  Overflow and
interior carry are the same rule; `BCtrCounter.run_fwd` is one induction with
one base case covering both.  (In Coq the empty-list case needs its own
one-line gadget, `Hwalk0e`, purely because `CTape` represents a trailing
blank implicitly rather than as a cell.)

Contrast `docs/BOUNCER_COUNTER_READING.md`, which read #13 off a spacetime
diagram as "surely a bouncer counter" and identified the wall: LapDecider's
symbolic side is indexed by the **carry index j**, not the counter **value
p**, so it cannot say "this side's length is proportional to what the other
side encodes."  A hand proof does not need the two indices to interact: the
sweep is uniform in whatever tail follows it, and the walk is uniform in
whatever prefix precedes it.  That is the whole trick.

#13 is #11 under `σ = StA→StC, StB→StA, StC→StB, StD→StD` (checked:
`σ(tm_11) = tm_13` exactly).  σ moves the start state, so it is **not** a
`TM_swap`/`Mirror` transport — the machines really do have different orbits
from the blank tape (boots 34 vs 28, gap offsets 3 vs 2) — but every gadget
transcribes, exactly as `Wave_24` transcribed `Wave_6`.

## 4. The three the search misses, and why

The search assumes S(n) has a **constant RLE shape word**.  That is not a
property of the machine; it is a property of the *phase* you sample.  #11
itself is the proof: at the StA phase its tape is
`1 0^(3v+3) 1 <counter word>`, whose shape word grows with `v`, and the
search finds it only at the right-record phase where the shape is constant.

* **tower #20** — the record tape is a long word over the blocks `1 0` and
  `1^2 0`, i.e. a counter in a different alphabet.  Its S(n) is presumably
  indexed by that digit word, like #11's counter, and a fixed shape word can
  never match it.
* **fractal #3/#5** — these *were* found, but only in the `10` shape class,
  which has ~11 members in 4M steps; the bulk of their records are genuinely
  fractal (`1^(2^k) 0^a 1^b 0^c ...` with ruler-sequence block sizes).
* **wave4 #15, double #32** — same shape-raggedness; not diagnosed further.

So the honest statement is: **the search failing on 3 of 11 is evidence about
the search, not about mxdys' claim.**  Nothing measured contradicts claim (1).

## 5. The next board, already reconnoitred

John, on `1RB1RA_0RC0RB_1LC1LD_0RA0LA`: *"appears to bounce the same way, but
the zero 'wall' moves one right each macro cycle.  Then it extends back out
using state A and starts bouncing again."*  Measured, that is exactly right,
and it is the `WrapBouncer` shape with an explicit bounce count:

```
macro   mkA (w, m) = StA, tape 1^w 0 1^m, head on the blank past the right end
                     (w, m) -> (w+1, 3m);  m = 3^(w+1)
micro   mkB j k    = StB, tape 1^w 0 1^j 0^(3k), head on the blank past the end
                     mkB (j+1) k -> mkB j (k+1)   in 6k+10 steps
                     (invariant j + k = m+1, so the bounce count is explicit)
```

Anchors at `t = 9, 60, 369, 2748, 23001, 201852, 1801281, 16165500,
145351593, 1307750844`.  Since the bounce count is explicit in the anchor,
the same plain induction that `WrapBouncer` uses applies — **no
`MeasureGlue`, no well-founded measure**.  The one piece not yet traced is
the "extends back out using state A" turnaround between the last bounce and
the next anchor (`t = 2660..2748` in the w=2→3 cycle).

`#28` is the other cheap-looking one: its S(n) is confirmed and its shape
(`0^(2n+2) 1^(2^(n+1)-1)`) is a doubling block against a linear wall, i.e.
the same two-level pattern again.

## 6. Reproducing

```
python3 tools/counters/sn_scan.py 4000000      # the table in section 2
gcc -O2 -o fast_sn tools/counters/fast_sn.c    # the v4-irules row
./fast_sn 1RB1RA_0RC0RB_1LC1LD_0RA0LA 2000000000 1
```

| file | role |
|---|---|
| `tools/counters/snfit.py` | the C-finite recurrence finder (exact over ℚ, with validation slack) |
| `tools/counters/sn_scan.py` | record-shape S(n) search over the 11 |
| `tools/counters/sim.py`, `recs.py` | plain (4,2) simulator + record extraction |
| `tools/counters/fast_sn.c` | C simulator for the `Θ(9^n)` anchors |

**Budget matters**: a family whose anchors are `Θ(4^n)` apart needs ~4M steps
to show 8 laps, and the fitter *refuses* to certify without slack — so a
"no S(n) found" at a small step budget means "not enough laps", not "no
family".  Run `sn_scan.py` at 4,000,000 to reproduce section 2; the v4-irules
row needs the C tool.

All of `tools/` is UNTRUSTED; the kernel re-checks every board.
