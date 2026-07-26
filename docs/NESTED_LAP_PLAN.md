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

### Stage A — measure the inner family (hours, no Coq)

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

### Stage B — the Coq (1 day)

Parts 1 and 2.  Axiom-free apart from the standing
`functional_extensionality_dep`.  Validate by RE-DERIVING one existing `IXP_*`
board through the new theorem and checking it still compiles — that is a real
regression test, not a new claim, because those 163 boards are known-good.

### Stage C — the emitter (2-3 days)

Part 3.  Start from `emit_ixp.py` (it already knows the shape) but take the
inner family from the search rather than the hard-wired `Ip` + `[S1;S0]`.

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
