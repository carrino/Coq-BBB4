# Plan: the exponential-overflow (nested lap) decider

_Written 2026-07-26 at the end of wave-15, after reading the 163 existing
`IXP_*` boards.  **This retires the premise that the count language must be
extended.** Five waves of notes say the exponential overflow is
"unrepresentable" because `sside` carries `a*j+b`; that is true of a single
`srun` and it is the wrong conclusion._

## 0. The reframing, which is the whole point

`WAVE14_FINDINGS.md` §3 and `MXDYS_DECIDERS_PLAN.md` §1c both conclude that an
overflow costing `Θ(2^j)` is outside the certificate model, because

    sside carries a*j + b     srun returns ca*j + cb      both affine in j

and therefore that we need a count language with `powsum k x = ((k+2)^x-1)/(k+1)`.
That was the entire motivation for the mxdys integration, which wave-15
measured and rejected.

**It is not necessary.**  The lap obligation never mentions the cost:

    Definition LapStep (tm : TM) (Cf : positive -> cconf) : Prop :=
      forall p, exists n c', csteps tm n (Cf p) = Some c'
                        /\ lift c' = lift (Cf (Pos.succ p)) /\ 0 < n.

`exists n`.  The step count is existentially quantified at the top level, so
an exponential lap only needs a PROOF that some `n` works — never a formula
for it.

And we already do this, 163 times.  Every `IXP_*` board proves an exponential
overflow branch by composing three pieces, none of which is exponential:

    boot   (affine srun)   Cc (2^K - 1)        ->  Cin (2^(K-1))
    inner  (INDUCTION)     Cin v               ->  Cin (fill v)      [exists n]
    exit   (affine srun)   Cin (2^K - 1)       ->  Cc (2^K)          [up to lift]

The exponential cost lives entirely inside the existential that the inner
well-founded induction produces.  `2^j` is never written down.  The
affineness of `sside` is not the binding constraint and never was — the
binding constraint is that the checker has no step that CHAINS TO A SECOND
ANCHOR FAMILY.

So this is not a new count language.  It is one new chain step.

## 1. The target population (measured, wave-15)

`ovfshape.py` over the 510 `no-overflow` machines (319 surveyed):

| interior / overflow degree | count |
|---|---:|
| `AFFINE` / **`EXP2`** | 212 (66%) |
| no decodable anchor | 84 |
| `AFFINE` / `AFFINE` | 21 |
| `AFFINE` / `HIGHER` | 2 |

plus 134 more `AFFINE`/`EXP2` sitting in the `no-interior` bucket (§4 of
`WAVE15_FINDINGS.md`).  Call it **~500 machines** on the `EXP2` shape.

**Why `emit_ixp.py` gets 0 of them today.**  Its template is hard-wired to the
`Ip` alphabet with the anchor tail exactly `[S1;S0]` (the wave-12 flip shape).
The measured alphabets of this bucket are

| alphabet | count |
|---|---:|
| `Alph_10_11_11` | 86 |
| `Jp` | 73 |
| `Mp` | 68 |
| `Alph_00_01_1` | 6 |

— almost no `Ip`.  Widening `emit_ixp`'s template by hand is on the
do-not-retry list (`WAVE13_FINDINGS.md` §8) and rightly so.  Moving the nested
lap INTO the checker removes the hard-wiring instead of widening it.

## 2. The build

### Part 1 — the inner induction is already in the tree (near-free)

`LapCertGlue.reach_ovf` does well-founded induction on `tovf` to run interior
laps from any anchor until the counter overflows:

    reach_ovf : forall p, exists k p', csteps tm k (Cc p) = Some (Cc p')
                                    /\ exists j, cview p' = (S j, None)

The boards' `inner_to_fill` is the SAME induction (both are
`well_founded_induction lt_wf` on `tovf`), and `IXPGadgets.cview_none_shape`
already proves `cview p' = (S j, None) -> p' = fill (pow2 j)`.  So the generic
inner step is `reach_ovf` instantiated at the INNER family, and `pow2`, `fill`,
`fill_succ`, `fill_allones` are all proved already.

Expected: a thin wrapper, not a new induction.

**Stage A amends this:** do NOT phrase the inner run as `Cin v -> Cin (fill v)`
with `v = pow2 j`.  21% of the measured inner counters run at another octave or
offset.  Phrase it as `reach_ovf` already does — *run inner interior laps until
the inner `cview` reports overflow* — and let the exit chain be derived at
whatever inner value that turns out to be.  `pow2`/`fill` then become a special
case rather than an assumption, and `cview_none_shape` is still what names the
landing value.

### Part 2 — one composition theorem

`theories/Counters/NestedLap.v`:

    Theorem nested_overflow_lap :
      (* boot: an affine chain from the outer overflow anchor into the inner *)
      srun tm el er lboot cB0 = Some (cB1, ab, bb) ->
      Cc p = cden XL XR j cB0 ->
      cden XL XR j cB1 = Cin (pow2 j) ->
      (* inner: the inner family's INTERIOR lap, itself affine *)
      (forall v i q0, cview v = (i, Some q0) ->
         exists n, 0 < n /\ csteps tm n (Cin v) = Some (Cin (Pos.succ v))) ->
      (* exit: an affine chain from the inner fill back to the outer successor *)
      srun tm el er lexit cE0 = Some (cE1, ae, be) ->
      Cin (fill (pow2 j)) = cden XL' XR' j cE0 ->
      lift (cden XL' XR' j cE1) = lift (Cc (Pos.succ p)) ->
      exists n c', csteps tm n (Cc p) = Some c'
              /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.

Every sub-run goes through the EXISTING `srun_sound`.  **`LapDecider.v` is not
touched** — no new `lstep`, no new `sside`, no new soundness for the symbolic
tape.  That is the property that makes this cheap and keeps the axiom story
intact.

Estimated: one file, ~150 lines, the two `csteps_add` compositions plus the
`pow2`/`fill` bookkeeping that `IXPGadgets` already carries.

### Part 3 — the emitter, which is where the work actually is

The proof is small; the SEARCH is the job.  Per machine:

1. Detect that the overflow branch is `EXP2` (`ovfshape.py`, already written).
2. **Find the inner anchor family.**  This is the one genuinely new search.
   Run the raw simulator across one overflow phase and look for a repeating
   configuration family — same machinery as `anchors()` / `alphabet_infer.py`,
   but seeded from inside the overflow phase rather than from the machine's
   own trajectory from blank tape.
3. Derive the boot chain `Cc (fill (pow2 j)) -> Cin (pow2 j)` and the exit
   chain `Cin (fill (pow2 j)) -> Cc (Pos.succ p)` with the existing
   `derive_chain` — both are affine, so nothing new is needed.
4. Derive the inner family's interior lap with the existing machinery.
5. Differentially validate all three against the raw simulator (step counts
   AND exact configurations) before emitting, as every emitter does.

## 3. Staging, with a measure-first gate

**Do not skip Stage A.**  Every wave that templated before measuring is on the
do-not-retry list.

### Stage A — RUN, AND THE GATE PASSES

_Done 2026-07-26 (wave-15).  `tools/counters/innerfam.py`, on a random
150-machine sample of the 442 `AFFINE`/`EXP2` machines._

Method: take the outer anchor family `emit_lapcert.anchors()` already finds,
build the all-ones outer anchor `Cc(2^K - 1)` at `K = 6`, simulate forward to
`Cc(2^K)`, and decode every blank-head configuration in between under every
alphabet in the zoo at every `(state, tail, far)` split.  An inner counter
shows up as a key whose decoded values are CONSECUTIVE.

| | |
|---|---:|
| overflow phase simulated | **150 / 150** |
| an inner consecutive family inside it | **144 (96%)** |
| running exactly `2^(K-1) .. 2^K-1` | **118 (79%)** |
| consecutive, but a different range/octave | 32 (21%) |
| no inner family found | 6 (4%) |

**Gate (1) is large: 96%.  Proceed to Stages B-D.**

**The finding that changes the design: the inner alphabet is often NOT the
outer one.**

| outer -> inner | count |
|---|---:|
| `Jp` -> `Jp` | 56 |
| **`Alph_10_11_11` -> `Ip`** | 51 |
| `Mp` -> `Mp` | 29 |
| `Ip` -> `Ip` | 6 |
| `Mp` -> `Ip` | 2 |

53 of 144 (37%) have inner ≠ outer.  `emit_ixp.py` assumes `Ip` at BOTH
levels, so it can only ever reach the 6 `Ip -> Ip` machines — which is the
real reason it derives 0 of this bucket, more specific than "hard-wired to
`Ip`".  **The emitter must search the inner alphabet independently of the
outer one.**

**And gate (3) says do not hard-wire `pow2`/`fill`.**  21% of the inner
counters run at a different octave or offset (e.g. `64..127` where
`2^(K-1)..2^K-1` would be `32..63`, or `130..191`).  They are still
CONSECUTIVE, so the induction is unaffected — but Part 1 must not assume the
inner run starts at `pow2 j` and ends at the all-ones fill.  Use
`reach_ovf`'s own shape instead: *from the inner anchor wherever the boot
lands, run interior laps until the inner `cview` reports overflow*, and let
the exit chain be derived at whatever value that is.  That is strictly more
general than `pow2`/`fill` and no harder — `reach_ovf` already returns
`exists j, cview p' = (S j, None)`.

### Stage A (original specification, for reference)

On a sample of ~30 `AFFINE`/`EXP2` machines, spanning `Alph_10_11_11`, `Jp`
and `Mp`:

* dump one overflow phase in absolute coordinates (`spacetime.py`);
* ask whether the phase visits a repeating configuration family, and if so
  recover its `(st0, alphabet, tail, far)`;
* report THREE numbers:
  1. how many admit an inner anchor family at all;
  2. of those, how many have that family in the 24-alphabet zoo (vs needing
     `alphabet_infer.py` to infer a new triple);
  3. how many have the inner range `2^(K-1) .. 2^K - 1` that `pow2`/`fill`
     assume, vs some other range.

**GATE on (1).**  Large → Stages B-D, that is the wave.  Small → the "second
counting round in the shifted frame" reading (`WAVE14_FINDINGS.md` §2) does not
generalise off the flagship, and the design must be re-derived from tapes
before any Coq is written.  **(3) small is not fatal** but changes Part 1: the
inner run would terminate at something other than the all-ones fill, and
`reach_ovf` would need a general stopping predicate rather than `cview ... =
(S j, None)`.

_(Answered above: (1) = 96%, (2) = all in the zoo but 37% at a DIFFERENT
alphabet from the outer, (3) = 79%.)_

### Stage B — DONE (wave-15)

`theories/Counters/NestedLap.v`, and it is smaller than estimated: **63 lines
of proof**, and `Print Assumptions` on both `inner_to_fill` and
`nested_overflow` reports **`Closed under the global context`** — zero axioms,
not even `functional_extensionality_dep`, because neither touches `lift`.

`Checkers/LapDecider.v` is untouched, as designed.

**Validated the way the plan asked.**  `theories/Tests/NestedLapRegression.v`
re-derives the hand-authored `IXP_0RB0RB_0LC1RD_1RB1LC_0LA0RB` board's
OVERFLOW branch — the exact statement it proves by hand as `lap_ov_...` —
through the generic `nested_overflow` instead of its own composition, and it
compiles with the standing axiom only.  That is a regression test against a
known-good board, not a new claim.

The remaining hypotheses are exactly the three pieces the emitter must supply:

    Hin    : the inner family's interior lap (ordinary, affine)
    Hboot  : csteps from the outer overflow anchor to [Cin v0]
    Hexit  : csteps from [Cin (fill v0)] to the outer successor, up to lift

### Stage C — PROTOTYPED (wave-15); the boot chain is the blocker

Part 3.  Start from `emit_ixp.py` (it already knows the shape) but take the
inner family from the search rather than the hard-wired `Ip` + `[S1;S0]`.

**What the prototype measured.**  Build the four endpoints — all ordinary
affine `sside`s in the outer index `j` —

    outer all-ones    rep uS_out (j+obS) ++ soS_out ++ tail_out
    inner start       rep uD_in  j       ++ soD_in  ++ tail_in     (= E(2^j))
    inner fill        rep uS_in  j       ++ soD_in  ++ tail_in     (all ones)
    outer successor   rep uD_out (S j)   ++ soD_out ++ tail_out

and hand each pair to the EXISTING `derive_chain`.  On 12 machines:

* the **exit** chain derives readily (4 of 12 straight away, more with the fix
  below) — it is an ordinary affine chain and needs nothing new;
* the **boot** chain is the blocker: 1 of 12.

**It is NOT a search-budget problem.**  Raising `(maxdepth, nmax)` from
`(24, 64)` to `(48, 256)` and `(64, 512)` changes nothing on any failing
machine.  The symbolic start/target being handed to the search are wrong, not
small.

**The cause, and it is the wave-13 §4.1 lesson again.**  `innerfam.py` reports
the BEST-SCORING inner key, but a machine has ~16-27 keys that decode
consecutively, and only a particular one is the family the boot can actually
land on.  Retrying the boot against EVERY detected key instead of the first:

| machine | inner keys | keys giving a boot chain |
|---|---:|---:|
| `1RB0LD_1LB1LC_1LD1RC_0RC1LA` | 21 | 3 |
| `0RB1LC_1LA1RB_1RD0LA_---1LB` | 21 | 3 |
| `0RB0LC_1LC1RB_0RD1LA_1RB1RC` | 27 | 3 |
| `1RB0LD_1RC1RA_1LA0LD_0RA1LD` | 16 | 0 |
| `0RB1LA_1RC0LA_1RD1RB_1LD1RA` | 20 | 0 |

3 of 5, up from 1 of 5 — and the keys that work are never the best-scoring
one.  They are consistently **`Ip` at a state DIFFERENT from the outer, with a
short tail** (`Ip@C tail=[S1] far=[S1;S1]`, `Ip@D tail=[S1] far=[S0;S1]`),
which is exactly the hand-authored reference's

    Cin v = (StC, (Ip v ++ [S1], S0, [S0;S0]))

**So the emitter must enumerate inner keys, not rank them** — the same
correction that turned 0 interior chains into all of them in wave-13.

**The boot has its own SHAPE, and it must be measured.**  Running the
`ovfshape` question on the boot itself — cost of `Cc(2^K-1) -> Cin(2^(K-1))`
against `K` — over 41 machines:

| boot degree | count |
|---|---:|
| **`AFFINE`** | **31 (76%)** |
| `EXP` (ratio → 2) | 10 (24%) |

Examples: `0RB0LC_1LC1RB_0RD1LA_1RB1RC` boots in `4K+3` steps (15,19,23,27,31)
and its boot chain DERIVES; `1RB0LD_1LB1LC_1LD1RC_0RC1LA` boots in
35,63,115,215,411,799 — a second doubling — and no chain can exist for it,
by the same affineness limit that put these machines in the residue.

So the `EXP2` bucket splits again:

* **affine boot (76%)** — the two-level nested lap is the right model, and a
  failing boot is a SEARCH gap;
* **exponential boot (24%)** — either a THREE-level nest, or (more likely) the
  inner start has been mis-identified and the true inner anchor is reached
  before the doubling.  `innerfam` requires the decoded values to be exactly
  `2^(K-1)..2^K-1`, which a subsequence of a longer count also satisfies —
  so a counter running `1..2^K-1` would be reported EXACT with its start
  exponentially far into the phase.  **Check that before assuming a third
  level.**

**Where the affine-boot failures come from, and the next concrete step.**
`look.py`-style tape dumps show the symbolic inner target is short by the
trailing cells the probe discarded:

    machine 0RB1LA_1RC0LA_0LD1RB_1LB1LD   (outer Jp@B, affine boot 4K+8)
      REAL phase start    st=B  L=10101010110   R=e
      SYMB B0out          rep [1,0] 4 ++ [1,1,0]        <- matches exactly
      REAL inner anchor   st=B  L=11111111100   R=0
      SYMB CinS           rep [1,1] 4 ++ [1]            <- 9 cells, real is 11

The opaque tail `X` is universally quantified and must be the SAME at both
ends of a chain.  At `B0out` the real tape forces `X = []`; the inner anchor
needs `X = [S0;S0]`.  `innerfam` reports its key after `rstrip0`, so those
cells are gone by the time the target is built.

**An attempted fix that did NOT work, recorded so it is not repeated.**
Reading `u` and `post` off the real tape at two consecutive outer indices
(`Cin` at `j` and `j+1` differ by one block, as `alphabet_infer` does for the
outer family) and using `rep u j ++ post` with the real far side: **0 of 18**,
down from 3.  So the inner anchor is NOT of the form `rep u j ++ post` with
the count equal to the outer `j` — the decomposition assumption is wrong, not
just the trailing cells.  That is the thing to debug next, and the tape dumps
above are the place to start.

### Stage D — emit and close out

`inventory.py` + `gen_stages.py` + `audit.py`, as usual.

## 4. Risks, honestly

| risk | mitigation |
|---|---|
| The inner family is not in the alphabet zoo | `alphabet_infer.py` infers a triple `(A,B,C)` from tapes and `gen_alphabet.py` generates a PROVED module; wave-14 added 18 that way |
| The inner range is not `2^(K-1) .. 2^K-1` | Stage A gate (3); `reach_ovf` generalises to any stopping predicate at the cost of one extra hypothesis |
| Boot/exit chains cannot land on the inner anchor's syntactic form | This is exactly what `SFold` exists for (`LAPDECIDER.md` §2); rotations alone provably cannot do it |
| The overflow is `EXP2` but not a nested COUNTER (e.g. a sweep) | Stage A distinguishes them: a nested counter has a repeating family, a sweep does not |
| Two nesting levels (`EXP4`, `HIGHER`) | Out of scope; ~30 machines, and the same theorem should compose with itself if it is stated generically in `Cin` |

## 5. What this does NOT cover

* the 84 `no decodable anchor` machines in the same bucket — they need
  `alphabet_infer.py` first, and may or may not then be `EXP2`;
* `QUAD` (38) and `HIGHER`/`EXP3`/`EXP4` (31) — a nested lap of a different
  shape, or two levels;
* the 99 `AFFINE`/`AFFINE` machines in the `no-interior` bucket, which are IN
  MODEL and are a plain search gap — cheaper, and ranked above this in
  `NEXT_SESSION_PROMPT.md`.
