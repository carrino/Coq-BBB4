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
| `D_remaining` | 1,176 → **1,035** |
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

### `RRBA` is the one honest gap

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
