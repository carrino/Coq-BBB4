# Wave-15 — mxdys' deciders measured and rejected; the liveness bucket closed with one induction

_Branch `claude/coq-residue-inductive-deciders-bzz3ae`, off merged wave-14.
This wave ran `docs/MXDYS_DECIDERS_PLAN.md` Stage 0 to its decision gate, got
a clear NO, and then took the ranked fallback item — the quasi-halting bucket
— with a much smaller theorem than the one wave-13 planned.  **Read §2 before
proposing any further mxdys integration, and §3 before building the
"states visited" layer, which is now unnecessary.**_

## 1. Scoreboard

| | |
|---|---:|
| boards this wave | **141** (`LAPC_*`, all through the ONE checker) |
| `D_remaining` | 1,176 → **1,035** (→ 1,016 after merging PR #37's 19) |
| frozen rows settled | 3,980 → **4,121 / 5,156 (79.9%)** |
| new Coq | `Counters/LapGlueAbs.v` — axiom-free |
| board axiom footprint | `functional_extensionality_dep` only (8 sampled + all 141 compiled) |
| closeout | `audit.py` OK — tables partition the frozen list exactly |
| census | `census_cache --check` = MATCH at every commit; `theories/Census/` untouched |

`LapDecider.v` and `LapCertGlue.v` are **untouched and still axiom-free**.

## 2. Stage 0: mxdys' deciders do not answer our question, and barely fire

The plan's gate was: *"(i) small → their search is tuned for BB(6) shapes; say
so plainly and fall back."*  Measured, (i) is small.

**Setup worked, and cost less than budgeted.**  `Inductive_inf.v` instantiates
the framework at `BBinf` (`Q := N`, `Sym := N`), so it parses our (4,2) machine
strings AS IS — **`BB42.v` / `Individual42.v` were never needed** for the
measurement, retiring Stage 0 steps 1-2.  The dependency closure of
`Inductive_inf.v` is **15 files, ~10 minutes**, not the README's "~1 month".
The native `./decider` builds with apt coq 8.18 plus `libcoq-core-ocaml-dev`.
(One local patch: `RRBA.v:4615` needs its `match if ... with` scrutinee
parenthesised for 8.18.  Harness and provenance: `tools/mxdys/`.)

**Caveat that matters for any future use:** `BBinf.v` has two `Admitted`
lemmas (`all_qs_spec`, `all_syms_spec` — its state enumeration is empty).  The
`BBinf` instantiation is a **search oracle only**; anything proof-grade needs
the finite `BB42 <: Ctx`.

### The numbers

| decider | proves | swept | decided |
|---|---|---:|---:|
| `Inductive` (`decide_hlin_nonhalt`), default config | `~halts` | **1,176** (all) | **12** (1.0%) |
| `Inductive`, 6 further configs (arithseq, exploop, both, block-size 2/3, bsz2+exploop) | `~halts` | 150-machine random sample of the 1,164 failures | **1** |
| `RWLAcc` (`decide_nonhalt`), block sizes 2-15, T = 1e7 | `~halts` | 7 | **0** |
| `RRBA` (`decide_loop2`) | `~halts` | — | **NOT MEASURED** (see below) |
| `UBRRBA` | halting only | — | n/a, the residue is non-halting |

Projecting the escalation rate over the whole failure set puts `Inductive`'s
total ceiling at **~20 of 1,176 (under 2%)**.

### Three findings that settle the route

1. **The count language we went there for is never exercised.**  Of the 12
   machines decided, **zero** used `nat_powsum` or `nat_powsum2`; 11 used
   `nat_mul` in trivial positions and one used neither.  No decided machine
   used any of the binary-counter tape constructors (`side_binary*`,
   `side_BL`).  `MXDYS_DECIDERS_PLAN.md` §1c mapped our 496 `EXP2` machines
   onto `nat_powsum 0` — that mapping is *plausible and untested*, because
   their search never gets far enough on our machines to build such a rule.
   Instrumenting the search (`tools/mxdys/measure2.ml`) shows the layer tower
   on our flagship counter still doing concrete window arithmetic at 6,000
   iterations; it never reaches a repeater it can generalise.

2. **Even a 100% hit rate would board zero machines.**  Their top-level
   theorem is `~halts`, and `D_remaining` moves only on `NeverQuasiHaltsSt` or
   `QHBound`.  §2 of the plan said this; it is worth restating as a number:
   `~halts` on all 1,176 shrinks `D_remaining` by **0**.  Non-halting has never
   been the binding constraint (`WHY_NO_HAMMER.md`), and the bridge that would
   convert their rules into liveness is Stages 1-3, i.e. the whole project.

3. **Their 12 are disjoint from our 141.**  All 12 machines `Inductive`
   decided are *still* in `D_remaining` after this wave's boards, and none of
   this wave's 141 boards came from a machine it decided.  Two non-overlapping
   small populations — so there is no synergy to harvest either.

### PROVENANCE, WHICH SETTLES THE "WHICH DECIDER" QUESTION

**mxdys named BOTH.**  His words to John, which are why this wave exists:

> *"see Inductive and RRBA deciders in
> https://github.com/ccz181078/busycoq/tree/BB6/"*

That is the author of both tools, told what we are trying to do, naming the
two of them together.  It outranks any argument from README prose about which
is the better shape match -- and this document contains TWO such arguments,
made in opposite directions within a day (see the two sections below).  Both
were over-narrow.  Record the lesson: when the expert has named the tools,
measure them; do not re-derive the recommendation from documentation.

So the real finding of this wave is not "which decider" but that **neither was
tested properly**:

| decider | what wave-15 actually did | what it needs |
|---|---|---|
| `Inductive` | swept 1,176 machines, 7 configs, **all with `ex_rules = []`** | the counter representations are HINT-GATED; supply `side_binary_Pos_inc_rule` from our own alphabet data |
| `RRBA` | never ran -- extraction defeated it until the last hour | now extracts (`Unset Extraction AutoInline`); sweep in flight |

Everything below stands as measurement.  The *conclusions* drawn about which
tool was "the" right one do not.

### The shape argument for `Inductive` (kept, but see the provenance note above)

_Added after John re-read the README against the shapes._

Layering, as mxdys states it:

| tool | layering |
|---|---|
| **`Inductive`** | "Nested Repeater" compression; **"rules can be nested"** |
| `RWLAcc` | "hardcoded **two layers**" |
| `RRBA` | "hardcoded **two layers**" |

`RRBA` and `RWLAcc` are CAPPED AT TWO LAYERS.  `Inductive` is the one with
unbounded rule nesting -- exactly the rung-2/rung-3 capability
`docs/RULE_LADDER.md` says we lack -- and a *nested repeater* is literally our
tape shape (`rep u j` inside an outer structure).

Our machines are SINGLE counters whose overflow re-runs the interior lap, i.e.
nested rules.  `RRBA`'s advertised class is "sync **BI**-counter" and
"shift-recursive".  On shape alone `Inductive` is the better match, and the
section below overweights one RRBA sentence.

**And that makes the hint gap the lead.**  The README line:

> "Nested Repeater by default ... also support Fixed Length Repeater and
> **Others (requires some hints from human)**"

The default compression already has nested rules and still scores 0 on our
residue.  The counter representations (`side_binary`, `side_binary_Pos`,
`side_BL`) are the "Others", and they are HINT-GATED.  Our residue is exactly
those.  Which fits every number we have:

* `Inductive` decides **48%** of the machines we boarded -- not weak on our
  general shape;
* **0%** of the residue *without hints*;
* the one hint attempt guessed blind (`T0 ∈ {0,50,200,1000}`, 2-cell digits,
  block size 2) against mxdys' real ones (`T0 = 7450`, 4-cell digits, block
  size 5).

**Priority: proper hint synthesis for `Inductive`, ahead of RRBA.**  We already
compute every input -- digit words (`uS`/`uD`), anchor states, tape-edge word,
and `boot_probe` for the `T0` analogue.  What is missing is deriving them at
the right BLOCK SIZE: our alphabets are 1-3 cells and mxdys' hints are 4-5,
which suggests our machines want a coarser macro-block than our anchor search
uses.  `tools/mxdys/hint.ml` takes `<spec> d0 d1 d1a` and is built.

### THE DECIDER I TESTED IS NOT THE ONE BUILT FOR OUR SHAPES (overweighted -- see above)

John, third push: *"we know the residue is not the Collatz class; we are
reproducing what mxdys already did."*  He is right, and the README says which
tool did it — read it against what our residue actually is:

| decider | mxdys' own description of what it decided |
|---|---|
| `Inductive` | "Finned", "helix", **SOME OF** bell eats counters, **SOME OF** sync bouncer counters |
| **`RRBA`** | "shift-recursive" (**counter balanced**, **counter inverting**), **sync bi-counter** (Skelet10) |
| `RWLAcc` | macro-machine, two hardcoded layers (shift rule, bouncer rule) |

Our residue is ~750 machines whose interior is affine and whose **overflow is
`Θ(2^j)`** — recursive counters.  That is `RRBA`'s stated class, almost word
for word.  `Inductive` claims only *some of* the counter families, and
`Inductive` is the decider this wave measured.

**So the honest headline is not "mxdys' deciders do not fire on our residue".
It is: the decider designed for our shape class was never run.**  Everything
in "The numbers" above is a measurement of `Inductive` (plus a 7-machine
`RWLAcc` sample), and it should be read that way.

### RRBA MEASURED AT LAST -- and its class does NOT contain our counters

The sharpest probe available: `tools/mxdys/control/D_ixp_family.txt`, 40 of the
149 `IXP_*` boards.  Those are machines we have ALREADY PROVED are
exponential-overflow interleaved counters -- the exact species the residue's
dominant class is made of, all known non-halting.  If RRBA covers our
counters, it must decide these.

    0RB1LC_1LA1RB_1LD0LA_0RD0RC   FAIL
    1RB1RC_0LA0RC_0LD1RB_1RC1LD   FAIL
    0RB0LD_1LC0LD_1LD1RC_0RC1LA   FAIL
    0RB0LC_1LC1RB_0RD1LA_1RB1LA   FAIL
    0RB1LC_1LA1RB_0LD0LA_0RD0LA   FAIL

Every parameter set tried is taken from mxdys' own `RRBAv*.v` proofs
(`n_skip` 0-1, `k` 4-6, `T` 1k-10k, including `s1k6T10000` which he uses in 385
of them), so this is not a strawman configuration.

**Conclusion: our counter species is not RRBA's species.**  Its advertised
class is "sync BI-counter" and "shift-recursive"; ours is a SINGLE counter
whose overflow re-runs the interior lap.  A zero `C_residue` is therefore
explained rather than mysterious, and the RRBA thread is closed.

_(Caveat: 5 machines at the time of writing, sweep still running.  But these
are the strongest possible positives -- if a decider misses machines we have
PROVED are in the family, more samples will not rescue it.)_

**What stays live.**  mxdys named *both* tools, and only one is now ruled out.
`Inductive` remains untested in the configuration that matters: its counter
representations are hint-gated and every wave-15 sweep ran `ex_rules = []`.
That is the remaining lead.

### `RRBA` NOW EXTRACTS -- the recipe is solved, the number is not

Late in the wave the extraction was unblocked.  The fix is one flag:

    Unset Extraction AutoInline.

The default inliner explodes on RRBA's functor body -- `coqc` stack-overflows
at the default stack and runs past 55 minutes with an unlimited one.  With
auto-inlining off it completes in ~25 min and emits 277 KB of OCaml, and
`rrba_measure` links against it.  (Do NOT also set `Extraction Conservative
Types`: it emits erased type arguments OCaml rejects.)

**But RRBA is SLOW** -- it did not finish the 40-machine control in 10 minutes
even at the smallest parameters in mxdys' own grid.  So the decisive number is
still missing, and `tools/mxdys/run_rrba.sh` exists to get it on a machine
with time.  Everything in "The numbers" above remains a measurement of
`Inductive` only.

### `RRBA` was the one honest gap

`RRBA` is the decider mxdys describes as handling *shift-recursive* and
*sync bi-counter* shapes, which is the closest description to our residue, so
it is the one worth a number.  It did not produce one:

* extracting `RRBA BBinf` **stack-overflows `coqc`** at the default stack, and
  with `ulimit -s unlimited` had not finished after 55 minutes;
* `Recursive Extraction Library RRBA` emits only a stub (`RRBA.ml`, 207 bytes
  of `open` lines) — the functor body does not survive library extraction;
* running `decide_loop2` under `vm_compute` instead did not finish one machine
  in 9.5 minutes.

`RRBA` is heavy in `PrimInt63`/`PArray`, which is the likely cause.  **Do not
record "RRBA finds nothing"** — it was never run.  If someone wants the number,
the route is the Rust `beaver/` tree (which has its own decider harness) or a
per-machine `native_compute` under an opam switch, not apt Coq.

### A POSITIVE CONTROL, added after John pushed back

John's objection was the right one: *"these deciders are exactly what solved
the residue"* — if so, a 1% hit rate means the harness is broken, not the
deciders.  So the measurement needs a control that can falsify it.  All four
runs below at `maxT = 1e6` (**ten times** the budget of the sweep above) and a
25 s cap per machine:

| population | n | decided |
|---|---:|---:|
| **machines WE boarded** (frozen rows with a board) | 40 | **19 (48%)** |
| BBB(4) holdout list (mxdys' own un-decided set) | 39 | **0** |
| our `D_remaining`, excluding holdouts | 39 | **0** |
| our `D_remaining`, first 60 rows | 39 | **0** |

**The harness is not broken.**  It decides 48% of the machines we boarded and
0% of the residue — and 0% of mxdys' own holdout list, which is the expected
answer there and confirms the rig end to end.  The residue sits on the far
side of the same capability boundary that produced their holdout list.  The
headline `12 / 1,176` is if anything generous: at ten times the budget the
sampled rate is 0.

### Our residue is NOT the BBB(4) holdout list

The prompt for this wave assumed it was (*"the residue is exactly the machines
this framework excluded"*).  Measured, that is false — the two populations are
nearly disjoint, and three candidate explanations were each ruled out:

| test | overlap with the 3,713 |
|---|---:|
| raw string | 22 / 1,035 |
| canonicalised under state-swap + mirror (the census orbit) | 22 |
| holdout as a COMPLETION of a frozen row (`TM_le`) | 22 |

The reason is **normal form**: 354 of our 1,035 rows begin `0RB`, which
bbchallenge TNF excludes outright — every one of the 3,713 begins `1RB`.  And
even restricted to `1RB` starts, 681 of ours meet 3,713 of theirs in 22
machines.  Only **27** of the 3,713 are anywhere in our 5,156-row census at
all (`tools/census_holdouts_kept.txt`).

So John's reading was right about the CHARACTER of the residue and wrong about
its IDENTITY: it is the same *kind* of population — machines whose forward
behaviour the inductive engine cannot model exactly — reached through a
different enumeration.  Which is exactly why their deciders do not help.

### THE HINT PATH — which this wave never tested, and which is the live lead

John, twice: *"there is more juice here... this is literally the code that
caught these."*  He is right that something was missed, and it is this.

**Every config swept above has `ex_rules = []`.**  The project README says the
counter methods *"require some hints from human"*, and the hint type is
literally our counter model:

    side_binary_Pos_inc_rule d0 d1 d1a qL qR QL QR :=
      (forall l r n, l <* d0 <* d1^^n <{{QL}} qL *> r -->+
                     l <* d1 <* d0^^n <* qR {{QR}}> r) /\ ...

`d1^^n` is our `rep uS j`; `d0` is our `uD`; `d1a` is the tape-edge word.
**An `ENCDATA` row IS a hint**, and we have 25 of them.  The hint is a SEARCH
hint, not an axiom — `Config_WF` demands a proof of the rule — so anything
found this way still has to be re-proved, which is exactly our normal cost.

**Tested, and it did not fire — but the negative is weak.**  Sweeping
`side_binary_Pos_inc_rule` built from each machine's own measured alphabet,
over 4 states x 4 states x 3 edge words x `T0 ∈ {0,50,200,1000}` x block size
= digit length: **0 of 6 machines**.  Then look at what mxdys' own hints
actually are (`IndSBCv1.v`):

    config_SBC 7450%N 5 A A A A [0] [1] [0;1;0] [1] [0;0;0;1] [0;1;0;1] [0;1;0]
    config_SBC 5604%N 3 A B A B [0] [1] [0;1;0] [1] [0;0;1;1] [0;0;1;0] [0]

`T0 = 7450` initial concrete steps.  Block size 5 or 3, not 2.  `d0`/`d1` are
FOUR cells, not two.  Edge words like `[0;1;0]`.  These are hand-found,
machine-specific parameters — which is what "requires some hints from human"
means, and why a blind sweep of a small box finds nothing.  **Do not read the
0/6 as "the hint path fails"; read it as "the hint path was not searched
properly".**

**This is the live lead, and it is ours to automate.**  Fifteen waves of
anchor search compute exactly these quantities: the digit words (`uS`/`uD`),
the anchor states, the tape-edge word, and a bootstrap length (`boot_probe`
already returns the `T0` analogue).  Nobody has tried synthesising a
`side_binary_Pos_inc_rule` from our own anchor data and handing it to their
search.  That is a half-day experiment with `tools/mxdys/hint.ml` (built, and
it takes `<spec> d0 d1 d1a` on stdin) and it is the first thing that could
change this wave's answer.

Two caveats to keep the expectation honest: their theorem is still `~halts`,
so a hit still needs the liveness half; and their own use of hints is a few
dozen INDIVIDUAL proofs, not a bulk decider run.

### Verdict

Gate (i) is small, so per the plan: **their search is tuned for BB(6) shapes
and this is not the route.**  §5 of the plan still paid for itself — the
count language a nested `LapDecider` needs is `a*j + b` extended by `powsum k`
and one multiplication — but that was already legible from `ovfshape.py`.

## 3. The quasi-halting bucket: an ABSORBING SET, not a states-visited layer

`wall_survey.py` over the residue put **149** machines in `novis`: the lap
derives COMPLETELY — anchor, both interior branches, overflow, bootstrap,
differential validation — and some state simply never fires inside it, so
`glue_neverqh` is *false* for them.  Everything except liveness already worked.

**What wave-13 §6 planned.**  Teach `wsteps_frame`, `cycL` and `cycR` to report
every INTERMEDIATE state of a run (today they state only their ENDPOINTS), so
a lap could be shown to AVOID the quiet state.  That is a new soundness
theorem per primitive of the step language.

**Why it is not needed.**  The quiet state is not avoided by accident of the
trajectory — it is *unreachable in the transition digraph from where the
machine already is*.  `LapGlueQH.glue_qh` already argues that a state targeted
by nothing can only occur at index 0.  That is the `d = 0` case of:

> if a set `Sset` of states is CLOSED under the transition table, and the
> machine is inside `Sset` at configuration index `d`, then it is inside
> `Sset` at every index from `d` on — so every state outside `Sset` made all
> of its visits before `d`.

One induction on `stepn` (`theories/Counters/LapGlueAbs.v`, `absorb_forward`).
It subsumes `glue_qh`, and it settles the machines `glue_qh` could not touch
*because their quiet state IS targeted* — by a transition whose SOURCE has
since left `Sset`, which a closure sees and a syntactic scan of the table does
not.

`QuasiHaltsSt` turns out to need only `QuietFrom` (`exists N, forall n >= N,
~VisitsAt`), not the exact last-visit index, so no bounded maximisation is
needed anywhere.

### Measured

| | |
|---|---:|
| `novis` machines | 149 |
| admitting an absorbing `Sset` | **141** |
| largest `d` over all 141 | **6** |
| boards emitted and compiled | **141** |
| `novis` remaining after the wave | 6 |

The quiet sets are `{StA, StB}` on 139 machines and `{StA, StD}` on 2 — i.e.
the bootstrap states, exactly as wave-13 §6 predicted (*"StB fires once at
index 1 by the same argument"*), but reached by closure rather than by a
second syntactic special case.

The bound is `d <= 6`, weakened to the census tier's 2000 by `qhbound_mono`.

### An emitter bug this exposed

The visit lemma prepended a single `StA` bullet (`@VISA@`) and then listed
only the REACHED states, which lines up against `destruct q`'s four goals only
while exactly one state is missing.  With two quiet states the bullets shift
and a later goal gets the wrong tactic.  Bullets are now generated per state
in order and `@VISA@` is gone.  `emit_graycert.py` carries the same latent
shape; it was **not** patched, because Gray anchors are exhausted (a full run
over the 1,035 finds `no Gray anchor` on every machine) and an untested
emitter path is exactly the wave-14 §4.1 failure mode.

## 4. The residue after this wave

`wall_survey.py` over the new 1,035 (891 surveyed when the profile stabilised):

| bucket | count |
|---|---:|
| anchor + interior derive, **overflow fails** | 510 |
| anchor derives, **interior fails** | 354 |
| no anchor family at all | 21 |
| complete lap, no visit witness | 6 |

**The two big buckets are one problem.**  Running `ovfshape.py` over all 354
`no-interior` machines:

| interior / overflow degree | count |
|---|---:|
| `AFFINE` / **`EXP2`** | 134 |
| `AFFINE` / `AFFINE` | 99 |
| `QUAD` / `QUAD` | 38 |
| no decodable anchor | 37 |
| `PARITY-AFFINE` | 13 |
| `HIGHER` (~`3^j`) | 13 |
| `EXP4` | 9 |
| `EXP3` | 9 |
| `AFFINE` / `HIGHER` | 2 |

So a machine bucketed `no-interior` is usually **not** blocked on its interior:
its interior is `AFFINE` (in model) and the search merely failed there first —
but its overflow is `EXP2`, so fixing the interior would move it into the
`no-overflow` bucket, not into a board.  The 99 `AFFINE/AFFINE` rows are the
genuinely search-limited ones and are the only part of this bucket where a
better interior search buys boards directly.

**Net: ~750 of the remaining 1,035 are gated on the exponential overflow**,
unchanged in character from wave-14 §3 and still needing the nested lap.

## 5. Do-not-retry, added this wave

* **mxdys' `Inductive` and `RWLAcc` on this residue.**  Measured: 12/1,176 and
  0/7.  Zero uses of `nat_powsum`.  And `~halts` alone moves `D_remaining` by
  zero, so even a full sweep boards nothing without Stages 1-3.
* **Building `BB42.v` / `Individual42.v` to run their deciders.**  `BBinf`
  already parses (4,2) strings; the instance is only needed for proof-grade
  use, and `BBinf`'s two `Admitted` lemmas mean the extracted decider is a
  search oracle, never a proof.
* **The "states visited" variant of `wsteps_frame`/`cycL`/`cycR`**
  (`WAVE13_FINDINGS.md` §6) *for the purpose of the quiet-state bucket*.  The
  absorbing-set closure gets 141 of 149 with one induction.  (If some future
  bucket needs intermediate states for a different reason, it is still
  unbuilt.)
* **`emit_graycert.py` for new boards.**  A full run over the 1,035 reports
  `no Gray anchor` on every one; wave-14 took all 11 there are.

## 5b. The in-model bucket is a CONFIRMED search gap -- and it is the target

`ovfshape.py` classifies 141 residue machines as `AFFINE` interior AND
`AFFINE` overflow: fully inside `LapDecider`'s model, no new theory required.
Running the emitter over all 141 (with the 25-alphabet zoo, including this
wave's `Alph_01_11_011`):

| outcome | count |
|---|---:|
| boards | **0** |
| `no interior chain` | 121 |
| `no overflow chain` | 20 |

So `ovfshape` says the lap is affine and `derive_chain` cannot find it.  That
is not a model limit and not an alphabet limit — **it is a search gap, now
confirmed on a named 141-machine population**, and it is the same shape as
`WAVE13_FINDINGS.md` §4.1, where making the window search target-aware turned
0 chains into all of them.

This is the highest-value target in the residue: the machines are in model,
the population is measured, and the fix is one search change rather than a
theory.  It was ranked first in the wave-14 prompt and skipped in favour of
the nested lap, which is the wrong order and cost this wave its second batch
of boards.

## 6. What to do next, in order

1. **The exponential overflow, ~750 machines** — unchanged, and now clearly the
   whole endgame rather than one bucket among several.  Wave-14 §6 route (1):
   teach `LapDecider` a NESTED lap (an inner anchor family run `2^j` times).
   `IXPGadgets.v` already carries `pow2`/`fill`/`cview_none_shape`.  Note
   §4 above: fixing the interior search alone does not board these.
2. **The 99 `AFFINE/AFFINE` no-interior machines** — in model, so this is a
   search gap, and wave-13 §4.1 is the precedent that interior-search gaps can
   be worth all of the machines behind them.  Instrument `derive_chain` on a
   few and find out why an affine interior is not being found.
3. **13 `PARITY-AFFINE`** — the `m = 2` re-index (`j = 2i + r`, block unit
   `u^2`).  Wave-14 measured only ~3 derive both parity branches naively; do
   not oversize it.
4. **21 no-anchor** and the **6 remaining `novis`**.  The 6 are the interesting
   ones: their missing state is genuinely LIVE but fires only in the INTERIOR
   lap, where `vis_via_ovf` cannot see it.  A `vis_via_int` dual would catch
   them — small, and it is the honest completion of this wave.
5. **The 27 genuine mxdys holdouts** (`tools/census_holdouts_kept.txt`; 22 are
   in the current `D_remaining`).

## 7. Deferred, unchanged

* Census fold-in (route B) — batch once on stable hardware; the only step that
  lowers `D_census`.
* The champion `1RB1LD_1RC1RB_1LC1LA_0RC0RD` and the carry-shifted one-off
  `0RB1LC_1LC0LC_0RD1LA_1RD1RB`.
* The `Closeout.vo` COMPILE needs the ~719-file board `.vo` closure (~85 min in
  a fresh container).  `inventory.py`, `gen_stages.py` and `audit.py` all ran
  clean this wave and the numbers in §1 come from them.
