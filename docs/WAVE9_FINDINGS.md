# Wave-9 findings — the counter residue, consolidated

_Written 2026-07-25, at the close of the counter-emitter session.  This is the
full record of what was measured, what was built, and — as importantly — which
previously-recorded claims turned out to be wrong, including several of my own.
Companions now merged into this branch: `COUNTER_CLOSEOUT.md` (the RepWL /
708-residue session), `COUNTER_EMITTER_WAVE8.md` (the emitter design),
`MACHINE_NOTES_WAVE8.md` (the hand-inspection log, extended here)._

---

## 1. The headline

Four encodings are now formalized where there was one family, 97% of the
classified residue has a Coq encoding where 65% did, and 30 new boards are in
the kernel.  **None of that required new mathematics.**  Every barrier that
fell this session was a wrong structural assumption in a *recognizer*, and
every one of them fell to a human reading a single machine.

The residue was never hard.  We kept looking for it in the wrong shape.

---

## 2. The test that was missing, and its calibration

`Interleave_TGT`'s skeleton is `P1 . RIP^j . STP . RET^(c·j) . FIN`, so the lap
length must be **affine in the carry length `j`** — and on BOTH branches, the
interior (`cview p = (j, Some q)`) and the overflow (`p = 2^k − 1`).  Wave-8's
fingerprinting only ever checked that anchor values marched `p → p+1`; it never
measured the overflow branch, which is why a class that looked reachable was
not.

Measured with `tools/counters/anchor_profile.py`.  Control first, because a
test that accepts nothing proves nothing:

| population | sampled | both-branch affine |
|---|---:|---|
| already-boarded counters (control) | 17 | **17 / 17** |
| quasihalting counters | 40 | **0 / 40** at the anchors then known |
| unboarded never-QH core | 80 | **15 / 80** |

**The rule this yields, which is the single most transferable thing here:**
a consecutive decode is *necessary and nowhere near sufficient*.  The lap
profile is the arbiter, not the decoder.  I violated this rule myself (§5) and
it cost 34 machines' worth of misclassification.

---

## 3. The structural finding: the orientation cube

An interleaved counter's tape word has **three independent orientation axes**,
and every recognizer in this repo had collapsed them to one corner:

1. **marker position** — the marker sits before its bit in tape order, or
   after it, or there is no marker at all;
2. **MSB end** — most significant bit leftmost or rightmost;
3. **counter side** — which side of the head the word lives on.

`Ip`/`Jp` are exactly one corner (marker-before, MSB-deepest, marker present).
That is why 85% of the population failed to anchor at all — not a parameter
gap, a category error.  `tools/counters/orient_probe.py` sweeps all three plus
wall and suffix.

Two further axes are separate and already known: **inversion** (`Jp` is `Ip`
complemented; ~12% of the population) and **stride** (`SEP3`/`SEP4`, ~2%).

### Encodings formalized

| module | word | family | population |
|---|---|---|---:|
| `ILCounter.Ip` | `1 b0 1 b1 … 1` | SEP2 | 695 |
| `JpCounter.Jp` | as `Ip`, data complemented | SEP2i | 141 |
| **`KpCounter.Kp`** (new) | `b0 b1 … bk`, no markers | KCOPY1 | **389** |
| **`DpCounter.Dp`** (new) | `b0 b0 b1 b1 …` | KCOPY2 | **22** |

Both new modules are **zero-axiom** (`Closed under the global context`).
Coverage of the 1,280 classified machines: **1,247 (97%)**, up from 836 (65%).
Remaining: 11 inverted variants of `Kp`/`Dp` (mechanical), 22 stride-3/4.

---

## 4. Boards

30 new, each compiled with `coqc -native-compiler no -Q theories BBB4` from a
**deleted `.vo`** state and re-checked with `Print Assumptions` =
`functional_extensionality_dep` only, independently of the emitter that wrote
it:

| route | count | encoding |
|---|---:|---|
| `ILC_*` direct | 25 | `Ip` |
| `ILCM_*` mirror | 3 | `Ip` + `mirror_never_qh` |
| `ILD_*` | 1 | `Dp` (reference board) |
| `ILK_*` | 1 | `Kp` (reference board) |

Plus 44 merged from the RepWL branch (36 `RWL8_` periodic bouncers, 8 `TCyc8_`
translated cyclers).  Counter-family total in tree: 190.

### What the `Ip` unblock actually required

Threading `Ip` through the template — the literal wave-8 TODO — was necessary
and **not sufficient**.  Four things were hard-coded and all four had to become
parameters before one real machine compiled:

1. the encoding (ripple pair, stop flip direction, return unit *width* 2 not 1,
   return *count* `j` not `2j` — all swap with the encoding);
2. the anchor head symbol (10 of 15 template-shaped machines use `S1`);
3. the anchor tail (10 of 15 are `Ip p ++ [S1]`, which no blank-terminated tail
   matches);
4. **the far side — a blank CELL, not the empty LIST.**  These laps close by
   stepping one cell past the frontier; `far = []` pushes that outside the
   window and needs an open-right transport, `far = [S0]` keeps it an ordinary
   closed window.  Not a free parameter: for the reference machine `[S0]`
   closes both branches exactly while `[]` and `[S0;S0]` close neither.

### A visit-obligation pattern worth reusing

Log-rare carry states (the reference `Dp` machine's `StB` fires 16 times in
200,000 steps, at doubling intervals) are reached by no bounded anchor prefix.
Both new reference boards witness **every state from one landmark** — the
configuration the overflow close starts from — reached by well-founded
induction on `tovf`.  Strictly more general than wave-8's per-state prefix plan
and should be the default.  Where the prologue happens to visit everything
(the `Kp` board), the obligation collapses to four `reflexivity` windows.

---

## 5. Corrections

**Mine, this session:**

- `anchor_profile.py` shipped accepting **descending** anchor families.  The
  same tape decodes under both `Ip` and `Jp`, one ascending and one descending,
  and ranking by "longest consecutive run" over the *sorted* value set scored
  the descending reading equally.  The tell was affine fits with negative
  slopes in the committed data — a lap cannot take −8 steps.  Fixed by
  requiring `first[v+1] > first[v]`.  Headline numbers unchanged.
- `COUNTER_EMITTER_WAVE9.md` §1 attributed one machine's overflow numbers to a
  different machine.  Corrected in place with both exemplars re-measured.
- **34 machines were misclassified as doubled-bit.**  A doubled read of their
  tapes decodes consecutively at one anchor, so the scan took them; they are
  plain (`Kp`).  The merged `counter_encodings.tsv` had them right.  This is
  the §2 rule biting me.
- §1's "do not re-attempt the 298 through this template" is **too strong** —
  see below.

**In the wave-8 hand-off:**

- "64 quasihalting counters are blocked on the encoding" — they were not
  encoding-blocked, and the number does not survive measurement.
- "RepWL is dead on the counter core" was measured at `L ≤ 4`; the merged
  branch boards 36 machines at `L` 9–30.  **A dead-lever claim must record its
  parameter grid.**

---

## 6. The quasihalting counters, partially reopened

At the anchors reachable when wave-9 began, 0 of 40 were both-branch affine and
I wrote the class off.  At the orientation a human read supplied, the picture
changes:

`0RB0RC_1LC1RB_0LD1RA_1RC1LD` — marker-left, MSB-left, 1-cell wall, 14,553
consecutive anchors:

```
interior   j = 0  1  2   3   4   5      -> 2 + 4j, exactly, over 28,169 laps
overflow   j = 2  3  4   5   6   7  8      9
           n = 23 14 103 22  399 30 1559  38
```

The overflow splits on the **parity of `j`**: odd `j` is affine (`2 + 4j`, the
same line as the interior); even `j` — i.e. `p = 4^k − 1` — costs ~`4^k`.  So
**half of that class is already template-shaped**, and only the `4^k − 1`
overflows need something else.  Mirror sibling in the opposite corner:
`0RB1LC_1LA1RB_0LD0LA_1LB---`, identical up to a 10-step offset.

---

## 7. Where we actually are, versus an exact forward model

mxdys's inductive decider dismisses this whole population, limited to TMs whose
forward behaviour it can model *exactly*.  Comparing honestly:

- **The closer is not the weak part.**  `glue_neverqh` takes an *arbitrary*
  anchor family `Cf : positive -> cconf` and needs only lap, boot, visits.
  Every structure thrown at it this session — walls, non-blank heads, doubled
  bits, plain bits, either MSB end — went through with no new theory.
- **The search was not weak, it was wrong.**  §3.
- **The template is genuinely weaker.**  It requires a *fixed chain* of phases
  with affine step counts.  An exact forward model does not care what shape the
  lap is; that is precisely what bites on the `4^k − 1` overflows, and no
  parameterization fixes it.
- **The real gap is architectural.**  mxdys proves one soundness theorem and
  every machine costs a *run*.  We prove one theorem per machine.  At ~30
  boards a session against ~2,300 unboarded, the constant is irrelevant — the
  exponent is wrong.

**Recommendation.**  The highest-value next build is not another emitter but a
**verified lap decider**: a computable function taking a machine plus a
candidate anchor description, running the symbolic lap, and returning a
certificate — with one soundness theorem discharged once.  Per-machine cost
drops to a `vm_compute`.  Same architecture as the `RepWL`/`NGramCPS` deciders
already in this repo, but exact rather than lossy; `WTape`'s
`wsteps`/`cycL`/`cycR` are the primitives and the four encodings above are the
digit alphabets.  **Ask mxdys for the implementation before rebuilding it** —
much of this session was rediscovering what a sibling branch had already
measured.

---

## 8. Process: hand-inspection is now 7 for 7 (11 counting the merged branch)

Every class that looked hard was a recognizer or parameter gap, and each was
exposed by a human reading **one** machine.  This session's four:

| machine | read | overturned |
|---|---|---|
| `1RB1RD_1LC0LB_1RA1LC_0RD1LB` | "right wall, 2 copies of each bit" | a whole encoding (`Dp`); the largest unexplained bucket |
| `0RB0RC_1LC1RB_0LD1RA_1RC1LD` | "1 to the left of each bit, MSB on the left" | named an AXIS; reopens half the 298 |
| `1RB0LD_0LC1LA_0RC1LA_1RC0LD` | "wall on the right, msb on the left, normal counter" | `Kp`, 389 machines; corrected my own misclassification |
| `0RB1LC_1LC0LC_0RD1LA_1RD1RB` | "alternates A and C moving left" | the mechanism of the last unread machine of the 708 |

That last one was closed on `main` in parallel (`ce26eb9`) and the two accounts
agree: `D` writes `1` on both branches, so while scanning for a `1` it fills
every `0` it passes, then steps one further right before `B` writes the `0` —
the carry lands one cell past the standard place and **the digit frame advances
by one per carry**.  A binary digit whose read position shifts, not a base-3
digit.  My independent probe agrees on the negative half: a sweep over every
orientation with the anchor state left FREE finds no consecutive family, and
"inverted except the MSB" does not decode.  A lap proof needs `Cc (p, k)` with
`k` the accumulated shift — a new digit *discipline*, not a new digit type.

**The operational rule:** when a class looks hard, print a few machine strings
and ask a human before building anything.

---

## 9. State and reproduction

- Branch: `claude/counter-emitter-parameterize-37w5rw`, PR #30, merged with
  `origin/main` and with `claude/repwl-bigblock-residue-wybgiy`.
- `python3 tools/census_cache.py --check` → **MATCH**, verified before and
  after every commit.  `theories/Census/` untouched throughout.
- Frontier for the next run: `tools/counters/wave9_ip_todo.txt` (880 machines
  never attempted).  `emit_ip.py --list <file> --emit` is safely re-runnable —
  anything that fails `coqc` or `Print Assumptions` is deleted, not left
  behind.
- **Sampling warning:** the unboarded core is not uniform.  The first 900 in
  enumeration order yielded 8 boards (91% have no anchor family at all — that
  block is barren); random samples of the same pool run 3–5%.  Sample randomly,
  or profile first and emit only the both-affine hits.

### Tools added

| tool | does |
|---|---|
| `counters/emit_ip.py` | the `Ip` emitter (direct + mirror); derives windows by exact symbolic replay, validates against the raw simulator for `p = 2..99` on both branches, compiles, checks assumptions, deletes on failure |
| `counters/anchor_profile.py` | wide anchor search + two-branch affine profile |
| `counters/orient_probe.py` | the orientation cube (marker side × MSB end × counter side × wall × suffix) |
| `counters/dbl_probe.py` | doubled-bit detection and profile |

Everything under `tools/` is UNTRUSTED; the kernel re-checks every board, and a
wrong constant fails to typecheck rather than mis-proving.
