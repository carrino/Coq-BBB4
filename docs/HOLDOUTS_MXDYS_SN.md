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
| `1RB1LC_1LC1RD_1LA0LC_0RD0RB` | blockdbl #28 | `0^(2n+2) 1^(2^(n+1)-1)`, StC | ✔ | 8 | yes (`BCtr_28.v`) |
| `1RB0LA_1LC0RD_0LB1LA_0RB1LA` | fractal #3 | `1^(2^n) 0^(2^n+1)`, StB | ✔ | 9 | no |
| `1RB0LA_1LC1RD_0LC1LA_0RD0RB` | fractal #5 | `1^(2^n) 0^(2^n)`, StB | ✔ | 9 | no |
| `1RB1RA_0RC0RB_1LC1LD_0RA0LA` | v4-irules | `1^n 0 1^(3^(n+1))`, StA | ✔ | 9 | yes (`Bnc3.v`) |
| `1RB0RC_0LC1LB_0LD1LC_1RD0RA` | wave4 #15 | — | search fails | — | no |
| `1RB0RD_1LC1LB_1RA0LB_1LC1RA` | tower #20 | — | search fails | — | no |
| `1RB1LD_1RC0RB_1LA0RC_0LD0LA` | double #32 | — | search fails | — | yes (`Double_32.v`) |

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

## 5b. The remaining four, sized

Seven of the eleven are boarded (section 2).  What follows is the measured
state of the other four, in the order they should be attempted — preceded by
#32, kept in full because it is the worked example the remaining four are
sized against.

### double #32 — `1RB1LD_1RC0RB_1LA0RC_0LD0LA` — **BOARDED**

`theories/Machines/Counters/Double_32.v`.  `Print Assumptions
nqh_1RB1LD_1RC0RB_1LA0RC_0LD0LA` = `functional_extensionality_dep` only.
Everything below is the reconnaissance it was written from; it held up
verbatim, so it is left as measured.  The one correction the transcription
forced: R1 and R2 traverse `rc5^(j-1)`, not `rc5^(j-2)` — the table's
`bt4 . rc5^(j-2) . rc5` for R2 is the same thing spelled differently, and
the step counts were right either way.  R3 really is `rc5^(j-2)`.

**The anchor question is settled.**  BBB's cert says the clean event is
head-on-rightmost-1 with comb count `a = 2^j`, `a -> 2a`, and records that an
earlier `a = 2^j-1 / a -> 2a+1` guess TIMED OUT.  `tools/counters/lap32.py`
sits on that timed-out anchor.  Measured in our (mirror) orientation the
`2^j` family is real, with the head at the LEFTMOST cell in StA:

```
anchor(k, m) = StA, ([], S0, (001)^k 0 1^m)      head on the first cell

   t        k     m
   24       1     4
   85       2     6
   283      4     8
   971      8     10
   3503     16    12
   13179    32    14
   50967    64    16
   200275   128   18
   793807   256   20
```

so `k = 2^n` doubles and `m = 2n+4`, exactly BBB's `a -> 2a`, `z -> z+2`.
One macro lap is `36k^2 + 29k - 4` steps (fitted exactly, n = 0..4) — the
`Theta(m^2)` quadratic bounce.

**Why the macro lap never had to be modelled.**  That lap is `Theta(k^2)`,
so it needs the same inner-loop treatment as the wrap bouncers.  The natural micro-anchor is the LEFT RECORD (head at the leftmost
cell, StA, reading blank), which occurs every `O(k)` steps — three of them per
increment of the comb prefix:

```
t     prefix      suffix                t     prefix      suffix
24    (001)^1     0 1^4                 240   (001)^4     1 0^3 1^4
45    (001)^1     0^6 1^2               283   (001)^4     0 1^8
58    (001)^2     1 0^3 1^2             336   (001)^4     0^10 1^2
85    (001)^2     0 1^6                 373   (001)^5     1 0^7 1^2
118   (001)^2     0^8 1^2               424   (001)^5     0 1^4 0^4 1^2
139   (001)^3     1 0^5 1^2             477   (001)^5     0^6 1^2 0^2 1^2
174   (001)^3     0 1^4 0^2 1^2         522   (001)^6     1 0^3 1^2 0^2 1^2
211   (001)^3     0^6 1^4               581   (001)^6     0 1^6 0^2 1^2
```

**All three suffix rewritings are now decoded, with exact step counts, and
each is UNIFORM in everything except the comb length `j`.**  Writing the
config as `(001)^j` followed by a block word:

| rule | rewriting | steps |
|---|---|---:|
| R1 | `0 1^m 0^p 1^q X  ->  0^(m+2) 1^2 0^(p-2) 1^q X` | `8j + 2m + 5` |
| R2 | `0^a 1^2 X  ->  (j+1),  1 0^(a-3) 1^2 X` | `8j + 5` |
| R3 | `1 0^b 1^c X  ->  0 1^4 0^(b-3) 1^c X` | `8j + 11` |

R2 and R3 are uniform in `a` and `b` as well: their cost is the comb traversal
`8j` plus a constant, so the head never walks those runs -- it rewrites a
bounded window near the front and returns.  Only R1 traverses a run (`2m` for
the `1^m` block).  Checked over `j = 1..4`, `m = 4,6,8`, `a = 6,8,10`,
`b = 3,5,7`, `c = 2,4,6` and four different tails each.

The micro-cycle is `R1 -> R2 -> R3 -> R1`, with the comb growing by one per
cycle, so composing the three gives the one-line law

```
(001)^j 0 1^m 0^p 1^q X  -->+  (001)^(j+1) 0 1^4 0^(m-4) 1^2 0^(p-2) 1^q X
```

which reproduces the whole measured orbit (j = 2..8 checked term by term),
including the doubling of the macro anchor as a consequence rather than an
assumption.

**The full step-gadget set is measured too.**  Nine identities, every one
uniform in the surrounding tape, every one a `reflexivity` in Coq.  Checked
differentially by `tools/counters/gadgets32.py` over five left contexts, five
tails and five middles:

```coq
(* rightward *)
bt4 : (StA,(L,S0,[S0;S1;S0]++R))            ->4  (StA,([S1;S1]++L,S0,[S1]++R))
rc5 : (StA,(L,S0,[S1;S0;S1;S0]++R))         ->5  (StA,([S1;S0;S1]++L,S0,[S1]++R))
(* turnarounds *)
tn4 : (StA,(L,S0,[S1;S0;S0]++R))            ->4  (StA,([S0;S1]++L,S1,[S1]++R))
tn6 : (StA,(L,S0,[S1;S0;S1;S1;S0;S0]++R))   ->6  (StA,([S0;S1;S0;S1]++L,S0,[S1;S0]++R))
md3 : (StA,(L,S0,[S0;S0;S1]++R))            ->3  (StA,([S1]++L,S1,[S1;S1]++R))
(* leftward *)
lc3 : (StA,([S0;S1]++M,S1,R))               ->3  (StA,(ctl M,chd M,[S0;S0;S1]++R))
la2 : (StA,([S1]++M,S1,R))                  ->2  (StA,(ctl M,chd M,[S0;S1]++R))
(* the two run sweeps R1 needs *)
b1  : (StB,(L,S1,R))                        ->1  (StB,([S0]++L,chd R,ctl R))
d0  : (StD,(L,S0,R))                        ->1  (StD,(ctl L,chd L,[S0]++R))
```

`rc5`/`lc3` are what the `8j` is made of: 5 steps out and 3 steps back per comb
block.  `b1`/`d0` iterated are what the `2m` in R1 is made of.  The assemblies,
read off the traces and confirmed by the step counts:

```
R2 = bt4 . rc5^(j-2) . rc5 . tn4 . lc3^j . la2                  4+5(j-2)+5+4+3j+2 = 8j+5
R3 = bt4 . rc5^(j-2) . tn6 . tn4 . lc3 . md3 . la2 . (lc3.la2)   ...              = 8j+11
R1 = bt4 . rc5^(j-2) . [A0 . b1^(m+1) . B0 . C0]
             . [A1 . d0^(m+1) . D1] . lc3 . la2                  ...              = 8j+2m+5
```

Nothing outside this list is needed.

**The closer was free.**  `WaveCounter.wglue_neverqh`
takes an ARBITRARY anchor type with a total successor and a preserved
invariant, which is exactly this: `A = (j, block word)`, `nextA` = the
rewriting above, `Inv` = the shape/size side conditions (`m >= 4`, `p >= 2`,
`a >= 4`, `b >= 3`).  No closed form for the anchor is needed at any point,
which is what makes the `Theta(k^2)` macro lap irrelevant.  The per-machine
work is the comb-traversal induction (`8j`) plus the three bounded-window
gadgets.

The abstract state for `wglue_neverqh` can be `(j, L)` with `L` a block word
`[(a_1,b_1); (a_2,b_2); ...]` denoting `0^a1 1^b1 0^a2 1^b2 ...` and an
implicit blank tail.  The composed successor is

```
(j, (1,m) :: (p,q) :: rest)  ->  (S j, norm ((1,4) :: (m-4,2) :: (p-2,q) :: rest))
(j, [(1,m)])                 ->  (S j, norm [(1,4); (m-4,2)])
```

where `norm` merges any block with a zero-length `0`-run into the previous
`1`-run (a denotational identity, since `wden ((a,b) :: (0,c) :: t)
= wden ((a,b+c) :: t)`).  The invariant that survives it is: `L = (1,m) :: rest`
with `m` even and `>= 4`, and every block of `rest` having both runs even and
`>= 2`.  Checked case by case against the four normalisation branches.

**As built.**  The abstract state is `nat * list blk` and `norm` is two
applications of a one-junction `nrm`, so the four branches above fall out of
`nrm ((1,4) :: nrm ((m-4,2) :: dec2 rest))` rather than needing a case split
in the definition.  The comb is carried by three accumulator fixpoints
(`comb`/`outp`/`inp` = `(001)^j`, `(010)^j`, `(101)^j`, each taking its tail
as an argument), which keeps every rewrite in cons form — the `rep`-algebra
junction rewrites that the earlier counter boards spend lines on do not
appear at all.  The negative controls are in
`theories/Tests/CountersDbl_Corruption.v`; the differential check for the
sweeps, the three rules and the composed lap is `tools/counters/rules32.py`,
which is `gadgets32.py` one level up.

### wave4 #15 — `1RB0RC_0LC1LB_0LD1LC_1RD0RA`

Confirmed as the mod-4 wave odometer.  The event config is a block word with
single-`0` separators and the block vector visibly halves:

```
t=581   0 1 0 1^16 0 1^8 0 1^4 0 1^2      blocks (16, 8, 4, 2)
t=591   0 1^2 0 1^17 0 1^8 0 1^4 0 1^2            (17, 8, 4, 2)
t=677   0 1 0 1^19 0 1^9 0 1^4 0 1^2              (19, 9, 4, 2)
t=687   0 1^2 0 1^20 0 1^9 0 1^4 0 1^2            (20, 9, 4, 2)
t=825   0 1 0 1^20 0 1^11 0 1^5 0 1^2             (20, 11, 5, 2)
```

with the lead alternating `1` / `1^2` — BBB's lead-1/2 micro-period, rule A
bumping the lead and rule B descending the vector.

**The good news is the glue is free.**  `theories/Counters/WaveCounter.v`'s
`wglue_neverqh` is ALREADY machine-independent: it takes an arbitrary anchor
type `A`, a total successor `nextA`, and a preserved invariant `Inv`.  Its
header even names #15 as a customer.  So the port is two pieces, neither of
them the glue:

1. the mod-4 arithmetic layer replacing `carry` / `nextf` / `fp` / `pbits` /
   `WInv` / `carry_ok` (~80 lines; `carry_ok` is the mod-2 form of exactly
   BBB's mechanised residue-safety leg
   `pair(pair((0,tail))) = (0, pair tail)`);
2. the per-machine lap — #15's rules touch 5 cells and fire a fixed 7-of-8
   set (rule A) or all 8 (rule B), so this is the bulk.

**The micro-lap is now MEASURED** (`tools/counters/lap15.py`, green over 1,495
anchors out to `t = 3,000,000`).  Same move as #32: sample at the LEFT RECORD
— head on the leftmost visited cell, `StC`, reading blank, left list empty —
and the tape is

```
(StC, ([], S0, 1^lead 0 1^v0 0 1^v1 0 ... 0 1^vn 0))
```

with `lead` alternating 1/2 and `v` the block vector frontier-first.  Two
rules alternate, and all three step counts are exact:

| rule | condition | rewriting | steps |
|---|---|---|---:|
| A | `lead = 1` | `lead := 2`, `v[0] += 1` | `10` |
| B | `lead = 2`, `i` least with `v[i] % 4 /= 0`, `i < last` | `v[i] += 2`, `v[i+1] += 1` | `4*sum(v[0..i]) + 4i + 18` |
| B' | same, `i = last` | `v[i] += 1`, append `2` | `4*sum(v[0..i]) + 4i + 22` |

Rule B is the mod-4 `carry`: the scan walks until a block is not `0 mod 4`
and deposits there; at the far end the deposit is a SPAWN (a new length-2
block), exactly as the mod-2 family's all-even case spawns a length-1 block.
Rule A is constant-cost and touches only the frontier, so **the whole
`8j`-style traversal cost lives in rule B alone**.

**Trap, and it cost a wrong rule once:** the branch is on the INDEX
(`i < last` vs `i = last`), *not* on the residue.  On the reachable orbit
residue 1 only ever occurs with `i < last` and residue 3 only with
`i = last`, so fitting the orbit alone suggests "residue 1 → deposit,
residue 3 → spawn" — which is false.  Probing off-orbit settles it: `[4,3,2]`
stops at `i = 1` with residue 3 and goes to `[4,5,3]`, the *interior*
rewriting.  `lap15.py`'s `probe_off()` keeps that pinned.

**The safety invariant is settled too.**  What rule B needs is that the scan
finds a block that is not `0 mod 4` and that the block it finds is ODD (an
even stop is not a third branch — measured, the machine then leaves the
anchor family altogether).  The predicate that gives it, verified on every
anchor and inductive under the composite over 2,988 vectors:

> walk the vector with a running parity bit `p`.  An even block must be
> `0 mod 4`; an odd block must be `1 mod 4` when `p` is even and `3 mod 4`
> when `p` is odd (flipping `p`); the LAST block is `2 mod 4` if `p` is odd
> and `3 mod 4` if `p` is even.

Equivalently — and this is the mod-2 family's `fp` in disguise — **the number
of odd blocks is odd**, and the odd blocks read left-to-right alternate
`1, 3, 1, 3` mod 4.  So `pbits`/`fp` does port after all, once the alternation
is carried as a running bit rather than a global XOR.

**The tape-level pieces are measured as well** (`lap15.py`'s `gadgets()`):
eight single-step joints uniform in `L`/`R` through `chd`/`ctl`, plus

```
ruleA   (StC,([],S0,   S1::S0::S1::R)) -10-> (StC,([],S0, S1::S1::S0::S1::S1::R))
entry5  (StC,([],S0,   S1::S1::S0::R))  -5-> (StC,([S0;S0;S1;S1],S0,R))
out6    (StC,(S0::L,S0,S1::S1::S1::R))  -6-> (StC,(S0::S1::S1::L,S0,S1::R))
ret1    (StC,(S1::L,S1,R))              -1-> (StC,(L,S1,S1::R))
```

Rule A is a SINGLE uniform window — no induction at all, which is why it is
constant-cost.  `out6` eats three `1`s and hands one back (net −2 per unit, 6
steps), so the outward sweep over a run of length `2k+1` is `6k` steps and
leaves exactly one `1`; **that odd-length requirement is the tape-level reason
the invariant is mod 4 and not mod 2**.  `ret1` is the 1-step/cell return,
giving rule B's `3 + 1 = 4` steps per cell.  What is left is the deposit and
carry-continue windows at the turnaround, then the assembly.

**John's reading supersedes all of the above: #15 is a plain BINARY
COUNTER.**  *"each bit is the zero stripe position mod 2.  the 2nd left most
stripe is the lsb ... reading left to right, 2nd zero is lsb and the value is
position % 2, next zero is 2's and value is position + 1 % 2, next zero is
4's and value is position % 2."*  Measured, that is exactly right.  Number
the zero stripes `z[0] = 0` (the anchor's own blank), `z[k+1]` the k-th
after it; then

```
bit k  =  (z[k+1] + k) mod 2       (equivalently: 1 iff the number of 1s
                                    strictly left of that stripe is EVEN)
```

and the TOP stripe-bit is always `0` — it is a sentinel, i.e. the implicit
leading `1` of a `positive`.  Dropping it, `p = 2^(width-1) + value`, and

> **one lap is `p -> p+1`, with no exceptions.**  Over 1,493 consecutive laps
> `p` runs `2, 3, 4, ..., 1495` with no gaps.  The spawn is not a special
> case — it is just the carry out of the top.

**This dissolves the whole mod-4 layer.**  The abstract state is a
`positive` advanced by `Pos.succ`, which is `LapGlue.glue_neverqh`'s
interface — the closer `BCtr_28` already uses — *not*
`WaveCounter.wglue_neverqh`.  There is no invariant to preserve and no
`carry`/`nextf`/`fp`/`pbits`/`WInv`/`carry_ok` port at all: "binary increment
terminates" is everything the carry needed.  `WInv4` above is true but
unnecessary.  The doc's "~80 lines of mod-4 arithmetic layer" is zero lines.

The tape is a closed form in `p`.  With `k = floor(log2 p)` and `r = p - 2^k`:

```
lead  =  1 + (p mod 2)
v[j]  =  2^(k-j) + sum_{i>=j} c(i-j) * bit_i(r),   c = 1, 3, 4, 8, 16, 32, ...
                                                   (c(0)=1, c(1)=3, c(d)=2^d)
total 1s on the tape  =  2p - 1
```

checked against every anchor out to `t = 3e6` (`lap15.py`'s `counter()`).
So `Cf : positive -> cconf` is directly writable, and what remains for the
board is only the lap lemma `Cf p --> Cf (Pos.succ p)` — where the deposit
gadget below still has to be stated correctly.

### tower #20 — `1RB0RD_1LC1LB_1RA0LB_1LC1RA`

Not re-measured this session; BBB's decode is complete and is the plan of
record.  The load-bearing idea is that the trailing region
`pat ++ (2)^r ++ [1]` has an infinite raw pattern set but factors into a
CLOSED 14-template FSM over `(template, r)`, `T1..T6 -> U1..U6 -> W1,W2 -> T1`
with fixed per-transition `(dr, dct, split)`.  Termination is by **rmin
closure** (`rmin[i] + dr[i] >= rmin[next[i]]`) plus nonnegative comb deltas,
so there is no reachability leg at all.  In our terms: a finite table plus a
well-founded argument — a checker port, not a hand proof, and the biggest of
the five.

### fractal #3 / #5 — `1RB0LA_1LC0RD_0LB1LA_0RB1LA`, `1RB0LA_1LC1RD_0LC1LA_0RD0RB`

The two where **BBB has no proof to port**.  Its own soundness note: legs
1/2/4/5 are concrete raw re-derivations, but the "for all j" closure rests on
leg 3, and "the fixed-glue-set check evidences but does not by itself
mechanise the all-j induction; that full rigor is the parallel Coq
formalisation."  The scoreboard was never bumped.

What exists to build on: `M(k) = 1^(2^k) 0^(2^k-2) 1`, width `2^(k+1)-1`;
strong induction on nesting depth, with every sub-call at a strictly lower
level and every summary applied only where its `>= 2^i` padding is present;
the run-crossing control alphabet is bounded and CONSTANT across levels (6
signatures for #5, 4 for #3, identical for k = 3..6); and the crossing
sequence is self-similar, `seq(k)` containing `seq(k-1)` as a contiguous block
(twice for #5, once for #3).  Section 2 above independently confirms their
S(n) — `1^(2^n) 0^(2^n+1)` and `1^(2^n) 0^(2^n)` at StB right-records, every
transition count C-finite with roots 4 and 3.

In Coq this is `well_founded_induction` on the level with the level-`j`
summary as the statement.  Hardest of the five, and the only one where
finishing would be a first rather than a port.

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
| `tools/counters/probe32b.py` | CTape-faithful mirror for double #32 |
| `tools/counters/gadgets32.py` | differential check for #32's nine step gadgets |
| `tools/counters/rules32.py` | differential check for #32's sweeps, rules and lap |
| `tools/counters/probe15.py` | CTape-faithful mirror for wave4 #15 |
| `tools/counters/lap15.py` | measured micro-lap + safety facts for #15 |

**Budget matters**: a family whose anchors are `Θ(4^n)` apart needs ~4M steps
to show 8 laps, and the fitter *refuses* to certify without slack — so a
"no S(n) found" at a small step budget means "not enough laps", not "no
family".  Run `sn_scan.py` at 4,000,000 to reproduce section 2; the v4-irules
row needs the C tool.

All of `tools/` is UNTRUSTED; the kernel re-checks every board.
