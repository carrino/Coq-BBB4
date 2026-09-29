# Coq-BBB4: scoping the instruction-level (transition-level) BBB(4) proof

Status: scoping document, 2026-08-18.  Nothing here is built yet; this maps
the work of re-proving the BBB(4) value under the **instruction-level**
("transition-level") beeping/quasihalting convention the community is moving
to, on top of the finished state-level development (`BBB4_value`,
`docs/CLAIMS.md`).  Written from a full survey of `theories/` plus the BBB
harness repo (`carrino/bbb`); every load-bearing claim below carries a
file:line.

---

## 0. TL;DR

* **The convention.**  An *instruction* is a `(state, read symbol)` pair — 8
  per (4,2) machine.  Instruction `(q,a)` *fires* at configuration index `n`
  when the machine is in state `q` reading `a` after `n` steps.  A machine
  quasihalts iff some instruction fires at least once but only finitely
  often; its score is the last firing step.  This is the BBB harness's
  native bookkeeping already (`carrino/bbb` README "Definitions",
  "Transition-level bookkeeping").
* **Direction of the delta.**  Instruction-QH is *weaker* to satisfy
  (state-QH ⇒ instruction-QH), so never-quasihalting is a *stronger*
  obligation (`NeverQuasiHaltsInstr ⇒ NeverQuasiHaltsSt`).  Consequently
  **BBB_instr(4) ≥ BBB_state(4) = 32,779,478**, machines flip from the
  "never" side to the "score" side, and the value itself is today
  **unknown** — plausibly far larger (§2).
* **Reuse is very good.**  The machine model needs zero changes
  (`ExecState` already carries the head symbol; `trans_of` exists at
  `Checkers/IRules/Engine.v:48`).  The TNF tree, queue, swap/mirror
  transport, table/hash plumbing, and the closeout algebra are
  convention-blind.  Cyclers — **83% of the census's 3,995,005 nodes** —
  strengthen essentially for free.  The IRules engine is *already
  instruction-typed internally*.  The one genuinely non-porting route is
  `ReachSt` (127 machines).
* **The real work**, in rough order of size: (1) an upstream harness
  campaign to find the instruction-level champion and value — the spec
  cannot even be written without it; (2) per-instruction liveness
  certificates for the closure family (existing rank/lex certs must be
  re-searched, and some machines will genuinely fail — they are new
  quasihalters needing new exact-score proofs); (3) a fresh census walk
  with a retyped decider contract; (4) a fresh burn-down of a new, larger
  deferred set.
* **Yes, this is "a new census walk and burn-down like the state one"** —
  but starting with a mature toolchain, a decided reference answer for the
  state projection of every machine, and ~80% of the checker layer porting
  mechanically.

---

## 1. The convention delta, precisely

### 1.1 New definitions (`BBB4_Statement.v` additions, ~120 lines)

The model (`TM`, `Tape`, `step`, `stepn`, `InitES`) is untouched.  Add,
alongside the state-level definitions (never replacing them — the state
theorem stays):

```coq
Definition Instr : Set := (St * Sym)%type.            (* = IRules.Engine.Tr *)
Definition instr_of (c : ExecState) : Instr := (fst c, t_head (snd c)).

Definition FiresAt (tm : TM) (t : Instr) (n : nat) : Prop :=
  exists c, stepn tm n InitES = Some c /\ instr_of c = t.
Definition Fired (tm : TM) (t : Instr) : Prop := exists n, FiresAt tm t n.

Definition QuasiHaltsTr tm := exists t, Fired tm t /\ exists N, forall n, N <= n -> ~ FiresAt tm t n.
Definition NeverQuasiHaltsTr tm :=
  forall t, Fired tm t -> forall N, exists n, N <= n /\ FiresAt tm t n.
Definition QuietAfterTr (tm : TM) (t : Instr) (s : nat) : Prop :=
  FiresAt tm t s /\ forall n, s < n -> ~ FiresAt tm t n.
```

Bridge lemmas, all a few lines: `VisitsAt tm q n <-> exists a, FiresAt tm
(q,a) n`; `NeverQuasiHaltsTr -> NeverQuasiHaltsSt`; `QuasiHaltsSt ->
QuasiHaltsTr`; `QuietAfter tm q s -> exists a s', s' <= s /\ QuietAfterTr tm
(q,a) s'` per fired instruction of a quiet state.

Conventions to pin (mirror the state-level treatment):

* **Silent instructions.**  A never-fired instruction does not witness
  quasihalting (the `Fired` conjunct) — exactly the harness's `N` class and
  the same "cannot affect any BBB value" argument as silent states
  (`BBB4_Spec.v:35-39`).  Note there are far more of these: every undefined
  slot, and defined slots the run never reaches.
* **Halting machines** quasihalt trivially with score ≤ halting step, as
  before; BB(4) = 107 is noise at this scale.
* **Scores**: last fire at index `s` ⇒ score `S s`, steps numbered 1,2,… —
  identical arithmetic to `QuietAfter`/`Attains`.

The bound predicate and spec retype by swapping the quantifier:

```coq
Definition QHBoundTr (B : nat) (tm : TM) : Prop :=
  forall t s, QuietAfterTr tm t s -> S s <= B.
Definition AttainsTr (tm : TM) (B : nat) : Prop :=
  exists t s, QuietAfterTr tm t s /\ S s = B.
```

`BBBT4_is`, uniqueness, `qhbound_mono`-style algebra: verbatim ports.

### 1.2 Which side gets harder, which easier

| verdict | state level | instruction level |
|---|---|---|
| "never quasihalts" | every visited state recurs (4 slots) | every fired instruction recurs (8 slots) — **strictly stronger**; false for some current `nqh` machines |
| "quasihalts, score ≤ B" | every quiet state's last visit ≤ B | every quiet instruction's last fire ≤ B — more slots to bound, but quiet witnesses are **easier to find** (more instructions than states fall quiet) |
| exact score | last visit of one state | last fire of one instruction — same two-run shape |

The deep fact driving the hard part (from the checker survey): for a target
`q`, the **`(q,a)`-avoiding subgraph strictly contains the `q`-avoiding
subgraph**.  So no existing rank/lex/measure liveness certificate implies
its instruction-level counterpart: the Coq *statements* strengthen
mechanically, the *certificate searches* do not, and for some machines no
instruction-level certificate exists at all — because the machine genuinely
instruction-quasihalts.  `Checkers/IRules/Meta.v:24-27` already concedes
this in writing: "All 428 v1 irules certificates denote machines that never
quasihalt at state level, **including the transition-level-QH ones: a state
with one finite and one infinite transition still recurs**."

---

## 2. The blocker this repo does not control: the value is unknown

The state-level pipeline consumed a champion and value found by the harness.
Instruction level has no analogue yet:

* The harness (`carrino/bbb`) tracks per-transition fire counts, last-fire
  steps, and N/F/I classes natively, and its cycle certificates fix every
  transition's class — but its non-cycler never-QH certificate families
  (`neverqh_rank`, `neverqh_rwlrank`, n-gram: `docs/neverqh.md`) prove
  per-STATE liveness only.  Same gap as here.
* `results/champhunt/cull.csv` (432 machines, all **undecided at 10^10
  steps**) shows what the new frontier looks like: transitions with fire
  counts like 131,071 = 2^17−1 and last observed fire ≈ **5.7 × 10^9** —
  counter machines whose rare transitions fire at exponentially sparse
  indices.  Distinguishing "fires at ~2^k forever" (class I) from "went
  quiet at 5.7e9" (class F, i.e. a score candidate in the billions) is
  exactly the value-indexed recurrence problem the Ladder machinery solves,
  now needed per transition.  **The instruction-level BBB(4) may be orders
  of magnitude beyond 32,779,478.**
* The current champion itself stays a floor, and a cheap one: at index
  32,779,477 state `D` fires one of its instructions, and from 32,779,478 on
  the tail argument pins the *full configuration* — only `(C,S0)` ever fires
  again (`tail_run`, `not_visits_other`,
  `Machines/Counters/Champion_…RD.v:88,145` — both generalize verbatim
  because they pin the whole config, not just the state).  So
  `AttainsTr tm_champion 32779478` needs one fresh `vm_compute` probe of the
  symbol under the head at 32,779,477 plus the same closed-form tail, and
  **BBB_instr(4) ≥ 32,779,478 is nearly free**.

**Consequence for sequencing:** the Coq port of the *never/bound* machinery
can start now (it is value-independent), but the spec file, the champion
file, and the closeout constants (`B_board`/`B_champ` analogues) wait on a
harness-side instruction-level campaign: upgrade rank/rwlrank/ngram liveness
to per-transition, sweep the space, and champion-hunt the F-class last-fires.
That campaign is real search work with genuinely-hard frontier machines
(quasihalting is Σ₂-hard; the rare-fire counters are the new towers).

---

## 3. Reuse map

### 3.1 Reusable verbatim (convention-blind)

From the census survey (`Census/TNF_QH.v`, `Run*.v`, `Decide.v`):

* the TNF tree and node expansion (`TNF_Node`, `node_expand`, `all_trans`,
  `trans_ok`, `TNF_QH.v:804-829`), unused-state pointer machinery, `TM_le`
  monotonicity, `TM_swap`/mirror trace isomorphisms (`TNF_QH.v:214-362`,
  `Mirror.v:15-81` — swap/mirror act on states/directions, symbols ride
  along untouched);
* `SearchQueue` and the walk skeleton (`TNF_QH.v:925-1067`, `Run.v:91-166`,
  the `Run_Split*` layering) — generic over the decider contract;
* all table/data plumbing: `row_to_tm`, slot shorthands, `dmap_of`
  lookups, the data/certificate convertibility split (`Run.v:39-67` — the
  5.3 GB→0.27 GB trick), `CENSUS_VO_HASH` hygiene, walk-stamp resumability;
* the closeout induction skeletons (`deferred_split`, `CloseoutKit.v:345`;
  `ShadowKit`), the Reroot prefix bridge (`Reroot.v`, `RerootSwap.v`,
  `ShadowBoard.v`) — parametric in the transported property;
* untrusted search tooling (`RankSearch.v`, `RepWLSearch.v`,
  `tools/gen_census_lists.py`, `tools/gen_provenqh.py`,
  `tools/closeout/inventory.py`) — regenerate, don't rewrite;
* `Records.v`, `FuelClass.v`, `LadderKernel.v`: zero changes.

### 3.2 Mechanical ports (Coq edits, no certificate churn)

* **Cyclers** (`Cycle.v` 298 L, `TCycler.v` 322 L, `TCyclerN.v` 141 L): the
  pump reproduces the *exact configuration* at `n1 + N·p + i`, head symbol
  included; add `cvisitsI`/`gvisitsI` testing the pair, quantify over 8
  slots.  ~60 lines, certificates `(n1,p)` unchanged.  This covers the
  in-place + translated cycle tiers — **3,316,283 of the census's 3,995,005
  nodes (83%)** (`docs/CENSUS_RUNTIME.md:27-35`).
* **IRules** (15 files, ~8,050 L): already instruction-typed —
  `Tr := St*Sym`, `trans_of`, and `Fires tm F n a` (every transition in `F`
  fires) at `Engine.v:32-65`; `MetaQH.v:199-208` already derives the
  per-instruction cover + recurrence statements before *projecting down* to
  states via `st_in q F` (`Meta.v:94`).  Delete the projection, widen the
  4-bit visit mask to 8 (`AnchorVisits.v`), export `FiresAt` recurrence.
  ~150 lines; certificates unchanged (the fired set `F` is computed).
  Immediately re-verifies ~1,220 boarded rows + 2,190 IQHStage rows *and
  mechanically exposes which ones flip verdict* (§4.2).
* **Wrap.v quiet half** (550 L): `tm_wrap` blanks a whole state
  (`Wrap.v:29`); the instruction wrap blanks **one table cell**
  (`if st_eqb p q && sym_eqb x a then None`).  `wrap_agree` goes through
  with `fst c <> q` → `instr_of c <> (q,a)`, and — the key structural point
  — the construction is *already correct for a still-running state*: the
  wrapped machine keeps executing `q` on the other symbol, and
  halt-freeness of the closure says exactly "`(q,a)` never fires while `q`
  keeps running".  The machinery for the genuinely new proof obligation
  exists in embryo.
* **Ladder/Lap** (`LadderCheck.v` 4,842 L, `LapDecider.v` 705 L,
  `LapAvoid.v` 303 L, `LapGlueQuiet` etc.): visit witnesses are concrete
  `cconf`/`sconf` values with a `c_h : Sym` field that `srun_st` discards
  *on purpose* (`LapDecider.v:682-696`); `srun_instr` puts it back with
  `reflexivity`-grade proofs.  Avoid checks get *weaker* (avoiding one cell
  vs. one state), so existing avoid chains still pass.  Bulky but low-risk.
  Caveat: `LapGlueQuiet`'s `Hvis` ("every other state visited in every
  lap") becomes "every other *instruction* fires in every lap" — strictly
  stronger; some lap certificates won't satisfy it and fall to the wrap
  route instead.
* **Closers and transport**: `LiveAll.v` → `neverqh_tr_of_live8` (must keep
  a `Fired` hypothesis — 8 unconditional liveness facts are often false);
  `Mirror.v:89-115` tail; `Halt.v`.  ~60 lines total.
* **Closeout algebra** (`CloseoutKit.v` 371 L, `BBB4_Theorem.v`,
  `BBB4_Value.v`): retype `forall q s, QuietAfter…` to
  `forall t s, QuietAfterTr…`; `boarded`/`covers_*`/`qhbound_mono`/the
  Horner-form constants pattern all port unchanged in structure.  The
  generated `CB_*.v` regenerate from a new frozen map.

### 3.3 Mechanical Coq + full certificate regeneration (the volume risk)

The generic closure engine (`Closure.v` 1,146 L; `ClosureIdx` 894 L;
`ClosureExt`, `FuelSCC`, `Drift`) parameterizes over `a_state : A -> St`
with liveness gates keyed on `st_eqb (a_state a) q` over `all_St`
(`Closure.v:50-56, 442-448`).  **Every instance abstraction already pins the
head symbol exactly** — `ng_covers` (`NGram.v:115-123`), `hng_covers`
(`NGramHist.v:381-391`), `rw_covers` (`RepWL.v:79-84`) all carry
`t_head (snd c) = s` — so the refactor is: generalize the target parameter
to `a_tgt : A -> L` with `all_L` (instantiate `L := St` to keep the old
proofs, `L := Instr` for the port), one 3-line `covers_instr` lemma per
instance.  ~400-600 lines touched, one-time.

But the **certificates** (`cert : St -> list ngcomp` rank/lex tables) go
from 4 branches to 8, and per the avoiding-subgraph fact they must be
**re-searched, not translated**, with no guarantee of existence.  Exposure,
by boarded sites: ~3,887 ngram-lex, 775 fuelwide, 693 ngramhist-lex, 183
RepWL, 130 ngramhist-ext, 125 drift — plus the 6,806 `Wrap` QHBound sites
whose `live_ok` gate rides the same engine.  The right first move is
**measurement**: run the regenerated searches over the existing boarded
lists and count survivors before building anything else (§6, phase 1).

### 3.4 Real rework / genuinely new

1. **The `nqh` population.**  3,256 closeout rows + the 5,270-machine
   Proven tier + the 196,595 in-walk n-gram-ladder nodes currently conclude
   `NeverQuasiHaltsSt`.  Each machine needs either (a) a per-instruction
   liveness certificate (survives as never-QH), or (b) it *flips*: it
   instruction-quasihalts, and needs a wrap/MetaQH-style board with a score
   bound — and any flip is a potential value-raiser that must clear the new
   champion.  The IRules re-verification (cheap, §3.2) gives the first
   measured flip rate.
2. **The 1,894 `iqh` rows' `QHBound 2000`.**  The bound was state-level;
   other instructions of still-busy states can go quiet later than 2000.
   `MetaQH`'s window scan re-runs with an 8-way enumeration — same
   computation, different answers; some machines need a larger `B`.
3. **`ReachSt`** (1,102 L, 127 machines): the one non-porting route.  It
   proves "the `q`-avoiding sub-machine terminates from every
   configuration" via four hand-proved measure tables; the
   `(q,a)`-avoiding sub-machine is the whole machine minus one cell —
   usually beyond any finite abstraction (the `WHY_NO_HAMMER.md` wall).
   `ReachStI` is friendlier (its rank already takes the head symbol as an
   argument; the avoid gate is a two-token change) but certificates must be
   re-searched.  Plan for these 127 to need new ideas; schedule them last,
   like the 27 holdouts were.
4. **Exact-score proofs for flipped machines.**  Templates exist —
   `MetaQH.v:57-113` (take an instruction outside `F`, *easier* to find
   than a state outside `F`), the instruction wrap, `LapGlueQuiet`'s
   `AvoidRun` on cells, `BlankTail`'s full-config tails — but the scores
   themselves can be large (transient last-fires), and the frontier cases
   (rare-fire counters) are research work, not porting.
5. **The spec + champion files** — blocked on the harness value (§2).

---

## 4. The new census walk

### 4.1 What retypes

The decider contract (`QHDecider_WF`, `TNF_QH.v:900-921`) keeps its shape;
`R_Halt`/`R_Deferred` unchanged; `R_NeverQH` payload becomes
`NeverQuasiHaltsTr`, `R_QH`/`R_Leaf` become `QHBoundTr B_census` triples.
`Decide.v`'s tier order survives:

* `find_halt`, lookup tiers, `scan_loops` (cycle/tcycler leaf checks):
  port per §3.2 — the cycle leaf argument ("any eventually-quiet
  slot made its last fire before the cycle closed") strengthens because a
  cycle repeats whole configurations.  **~89% of nodes (halt + cycles +
  lookups) keep their cost and verdict.**
* `try_ngram` / `try_rank` / `try_rw` (never-QH tiers, ~5% of nodes): need
  the per-instruction engine + new in-walk certificate synthesis.  PLAYBOOK
  Rule 4 applies with extra force: keep these LIGHT; every machine the
  light tier loses goes to the deferred set, not into a slower walk.
* `try_qhb`: the candidate scan (`qh_candidate`, `filter … all_St`,
  `Decide.v:873-925`) becomes an 8-way instruction scan feeding the
  instruction wrap.  Note this tier gets *more productive*: instruction
  quasihalting is easier to witness, so machines that were never-QH work at
  state level become cheap `R_QH` leaves here.

### 4.2 Expected shape of the new deferred set

Two opposing forces: never-QH verdicts get harder (deferrals up), QH
verdicts get easier (deferrals down — many state-level never-QH machines
become bounded quasihalters the light tier *can* close, since their quiet
instructions last fire in the small transient).  Cyclers dominate the space
and land on the easy side.  The honest answer is that the new `D_census`
size is a **measurement, not an estimate** — but the state walk's tier
census says the exposure is concentrated in the 196,595 n-gram-ladder nodes
plus whatever fraction of the Proven/ProvenQH lookup tiers fails to
re-certify.  Plan for a deferred set larger than 5,156, in the low tens of
thousands at worst.

### 4.3 Compute plan

Unchanged discipline (PLAYBOOK, `NEXT_SESSION.md`): per-machine ports and
checker development are container-safe; the walk itself is
`native_compute` on stable hardware.  The state walk measured 385 core-min
(1 h 45 m at 4 jobs / 32 GB; peak unit 6.3 GB).  Per-node cost rises
modestly (8-way scans, slightly bigger closures); budget 1.5–3× — still a
single evening on the box.  Keep the committed-`.vo` + `CENSUS_VO_HASH`
mechanism verbatim; it is convention-blind.

---

## 5. Collecting the burn-down list, and burning it down

The state-level burn-down was **coverage-first**: the value was already
known, so the job was `Forall boarded` over a frozen deferred set.  Here the
value is the unknown, so the strategy inverts to **value-first**: the list
is collected *ranked by candidate score*, and the top of the list is
settled before the bulk, because until the champion is pinned neither the
spec nor any board's bound constant can be written.

### 5.1 The suspect-transition sweep (untrusted, harness side)

The raw material for the list is a statistic the harness already computes
on every simulation: per-transition fire count and last-fire step.  Define

> **suspect transition**: fired at least once, and silent for the trailing
> ≥ 90% of the run at the current budget.

Sweep the full TNF (4,2) space (the harness's `enumerate.c`, cross-checked
against the Coq census's 3,995,005 nodes) in escalating budget tiers
(10⁴ → 10⁶ → 10⁹ → 10¹⁰), carrying forward only machines that still have a
suspect or are undecided:

* **Cyclers resolve themselves.**  An in-place or translated cycle
  certificate fixes every transition's class exactly — fired-in-cycle = I,
  transient-only = F *with its exact last fire*, unfired = N.  ~83% of the
  space (the census's cycle tiers) therefore comes out of the sweep
  *decided at instruction level with exact scores*, giving an immediate
  untrusted value floor from the cycler class.  NB the transient-tightened
  holdout certs (`results/certs_tight/`) show true transients to
  **309,417,105 steps** — any cycler whose cycle omits one fired transition
  scores its transient, so this class alone can move the value.
* **The champion-horizon rule.**  A sweep can only *observe* last fires
  below its budget, so the budget must stay ≥ ~10× the largest live
  candidate score at all times; every time the candidate champion moves up,
  the undecided tail re-sweeps at a deeper budget.  (The state proof never
  needed this — its value was known before the census ran.)

### 5.2 The list, and what pass1.csv already says

**Burn-down list v0** = machines with a surviving suspect transition,
ranked by suspect last-fire, partitioned by who currently vouches for them:

| bucket | contents | what settles it |
|---|---|---|
| **flip candidates** | state-level `NeverQuasiHaltsSt` machines (Proven tier, `nqh` rows, holdout certs) with a suspect | prove the suspect I (stays never-QH) or F (new QH board, score = last fire) |
| **busy-state suspects** | state-QH machines with a suspect on a *still-live* state beyond their state score | instruction wrap at the suspect cell |
| **undecided** | no state-level verdict either (the old frontier + new) | full new proofs |

A first cut over just the 3,713 holdouts (`results/pass1.csv`, 10⁹ budget)
already yields **~17 machines / 22 suspect transitions with last fire
beyond 32,779,478**, splitting into two sharply different populations by
the ratio (trailing silence)/(mean firing gap):

* **Sparse-I lookalikes** (counts 7–11, mean gap ~10⁷, silence ≈ 100×
  mean gap): consistent with geometric gap growth; likely class I, but
  proving it needs value-indexed recurrence (Ladder/IRules) per transition.
  E.g. `1RB1LA_0LC0RC_1LC1LD_1RB0LA` `B0` (10 fires, last 92,981,720) and
  its three family variants.
* **Regime-change deaths** (counts ~9,000–25,500, mean gap 3–11k steps,
  silence ≈ **10⁵× mean gap**): fired *regularly* for ~7×10⁷ steps, then
  permanently silent for 9×10⁸.  No smooth gap-growth model fits; these are
  prime class-F candidates.  Top: `1RB0RC_1LC1LA_1RA1LD_0LB0LA` `D1`
  (9,090 fires, last **99,355,388** — 3.03× the state champion),
  `1RB1LC_1RC1RB_1RD1LA_1LA0RD` `D1` (25,480 fires, last 97,455,496),
  `1RB0RB_1LB0LC_1RD1LC_1LC0RA` `A0` (17,598, 95,865,237), and — notably —
  `1RB1RD_0RC1RB_1LC1LA_0RB0RD` `A0`+`B1` (last ~71.6M), a near-relative of
  the champion's own table.

**Named first experiment (phase 1): decide these 22 transitions.**  Each
machine already carries a state-level cert whose engine (irules/ladder/
rank) reveals its structure, so targeting is free.  Any single F verdict
dethrones the champion and re-anchors the whole campaign; 22 I verdicts
are strong evidence the incumbent survives.

**UPDATE (2026-08-18, the experiment's empirical half is done): all 22
suspects REFIRE.**  Deep simulation to 6×10¹⁰ steps shows every suspect
transition firing again past its pass1 "last fire", in geometric BURSTS —
regular fires within a burst, bursts spaced by gap ratios of ~4–17× — so
the "regime-change death" population above was an artifact of comparing
trailing silence to the *within-burst* mean gap.  E.g.
`1RB0RC_1LC1LA_1RA1LD_0LB0LA` `D1` (bursts ending 384K → 6.2M → 99.4M →
1.59G → 25.5G, ratio ≈16×) and `1RB1LC_1RC1RB_1RD1LA_1LA0RD` `D1`
(97.5M → 1.56G → 24.9G).  Consequences: (a) the pass1-derived
champion-candidate list is EMPTY at the 6×10¹⁰ horizon — no known machine
currently beats 32,779,478 at transition level, which materially supports
"the champion survives the convention change"; (b) these machines are
still not *decided* — sparse-I needs a per-burst recurrence proof
(Ladder-style value-indexed rules), and that, not wrap-style quiet proofs,
is what the frontier of the transition-level burn-down looks like; (c) the
(2,2) precedent (a transition champion that state-level never-QH) still
cautions that the unswept census bulk, not the holdout list, is where a
dethroning F transition would hide — which is what the collection walk
(section 7) exists to sweep.

### 5.3 Burning it down

Order of attack, cheapest per row first, mirroring the state playbook's
two-front discipline (port-work vs. research-work):

1. **Cycle-transient boards** (bulk, mechanical): cycler suspects get exact
   scores straight from the certificate; port §3.2 makes them kernel-checked.
2. **Instruction-wrap sweeps** (the tier that got *easier*): blank the
   suspect cell, closure-check the wrapped machine halt-free from a
   post-silence anchor → `QuietAfterTr` + exact score.  This is the
   QHBoard pipeline (`tools/gen_provenqh.py`) with an 8-way scan; expect it
   to absorb the majority of flip candidates at small scores.
3. **MetaQH instruction boards**: for IRules-certified machines, a
   transition outside the fired set `F` is a quiet witness — *easier* to
   find than a state outside `F`; the window scan re-runs 8-wide.
4. **Per-instruction never-QH re-search** (closure family): re-certify
   surviving never-candidates; failures feed back into queue 2.
5. **Ladder/lap value-indexed recurrence** for the sparse-I population:
   "fires at every counter overflow, overflows recur" — class I proofs that
   no finite budget can give.
6. **The frontier**: suspects that resist both directions — gap growth too
   irregular for the ladder, closure too rich for the wrap.  These are the
   new "27 holdouts"; expect single-digit-to-dozens of machines to eat most
   of the calendar, as before.

Then the endgame is structurally identical to the state proof: freeze the
walk's `D_censusTr`, `Forall boarded` it by app-chained `CB` stages with
`boarded := NeverQuasiHaltsTr \/ QHBoundTr B_board triple \/ champion
board`, empty the residue, and meet the champion's two-`vm_compute` lower
bound in `BBBT4_value`.

---

## 6. Phasing

| phase | work | where | size |
|---|---|---|---|
| 0 | Definitions + bridges (`Instr`, `FiresAt`, `QuietAfterTr`, `QHBoundTr`, mirror/swap/LiveAll transport), keeping all state-level results intact | container | ~300 lines, days |
| 1 | **Measure before building**: port IRules Meta layer + cyclers; re-run the ~1,220 IRules and 3,256 `nqh` boards through instruction checkers; count survivors/flips.  Port the instruction wrap and re-verify a QHBoard sample.  **Decide the 22 pass1.csv suspect transitions (§5.2)** — any F verdict re-anchors the value | container | ~400 lines + sweeps, 1–2 weeks |
| 2 | Harness campaign (upstream, `carrino/bbb`): per-transition liveness in rank/rwlrank/ngram deciders; full-space sweep; champion hunt over F-class last-fires; freeze a candidate value | harness + box | open-ended; the gating item |
| 3 | Closure-engine target generalization + certificate regeneration sweeps (`gen_provenqh`-style tooling, 8-branch certs) | container + box | ~600 lines + regen, 2–4 weeks |
| 4 | New census walk: retyped `QHDecider_WF`, light tiers, walk on the box; freeze new `D_census` | box | 1 walk + iterations |
| 5 | Burn-down: QH-side sweeps first, never-QH re-search second, `ReachSt`-class and rare-fire frontier last | both | the long tail, as before |
| 6 | Closeout + spec: new `CB_*` stages, `BBBT4_Spec.v`, champion file (two `vm_compute` runs + full-config tail — the current champion's own file shows the template generalizes) | container | days once 2–5 land |

Design decisions to make at phase 0:

1. **Parameterize vs. fork.**  Recommendation: parameterize the *generic
   engines* (`Closure.v` target alphabet — one refactor serves both
   conventions and keeps the state proof compiling), fork the *spec and
   census* layers (`BBBT4_Spec.v`, `Census/TNF_QHT.v`, new `Compute/`
   namespace) so `BBB4_value` never wobbles.
2. **Naming.**  Pick one term and stick to it; the harness says
   "transition-level", the community says "instruction-level".  Suffix `Tr`
   on predicates, `BBBT4`/`BBBI4` on the spec — decide once.
3. **Silent-instruction convention** — state it in the spec file with the
   same "cannot move the value" note as silent states.

## 7. Built (2026-08-18): the phase-0 walk framework

Phase 0 plus the walk skeleton is no longer a plan — it is in the tree and
compiles with stock apt Coq 8.18 (`make` builds it; nothing state-level was
touched, and `census_cache.py --check` still reports MATCH):

| file | what it is |
|---|---|
| `theories/BBBT4_Statement.v` | `Instr`, `instr_of`, `FiresAt`, `FiredTr`, `QuietAfterTr`, `QuasiHaltsTr`, `NeverQuasiHaltsTr`, `all_Instr`, and the state-level bridges (`visits_fires`, `never_qh_tr_st`, `qh_st_tr`, `quiet_after_st_tr`) |
| `theories/CensusTr/TNF_QHTr.v` | `QHBoundTr` + its completion/swap/mirror transport, `halt_le_qhboundtr`, the `DecidedTr`/`NodeDecidedTr` census section, `QHDeciderTr_WF`, and queue soundness (`SearchQueue_WF_Tr`, `..._upd_spec_tr`, `..._upds_spec_tr`).  The SYNTAX machinery — `TNF_Node`, `node_expand`, `QHResult`, `SearchQueue_upd(s)`, `Deferred` — is reused by import, so a transition-level walk runs the state census's own computation |
| `theories/CensusTr/DecideTr.v` | the cycle tiers at transition level: `cycle_qhboundtr`, `cycle_leaf_check_sound_tr`, `tcycler_leaf_check_sound_tr` (+`_L`) over the REUSED computational checks, `glift_instr` (the one new fact: the guarded window pins the head cell independently of the abstract far tape), and the phase-0 decider `decide_easy_tr` (halt → lookups → cycles → defer) with `decide_easy_tr_WF` |
| `theories/CensusTr/RunTr.v` | collection-mode wiring: `B_tr = 2000`, empty `D_tr`/`prov_tr`/`provqh_tr`, `decider_tr` (+WF), the symmetrized root (`q_0_tr`, `q_0_tr_WF` with the mirror argument), `q_iter_tr_WF`, the conditional `census_tr_from_empty`, and untrusted serialization (`queue_encs` as decimal `tm_enc` codes) |
| `theories/CensusTr/WalkTr_Collect.v` | the on-demand collection-walk driver (not in `_CoqProject`): 4096 rounds × 8192 pops, no-op past exhaustion; prints `(front, back)` sizes and the back queue's codes |
| `tools/censustr/decode_enc.py` | untrusted decoder: walk output → bbchallenge machine text (round-trip verified against `tm_champion`) |

**How to run the collection walk** (the box, like the state census):

```
make census-tr-collect        # native_compute, census opam switch
make census-tr-collect-vm     # vm_compute fallback, any coqc
python3 tools/censustr/decode_enc.py census_probes/censustr_collect.out
```

Measured in-container (apt coqc, vm_compute): 8,192 pops in 11.1 s and
131,072 pops in 147.5 s — ~1.1–1.4 ms/pop, holding at depth.  This walk
is far lighter than the state census's 385 native core-minutes because
the phase-0 stack has no n-gram/rank/RepWL tiers; the price is a large
back queue.

**The collection walk has RUN (2026-08-18, the box, native_compute: the
walk itself ~8.5 min).**  Back queue: **280,087 machines**
(burn-down list v0; superseded by `censustr_deferred_v2.txt` — each walk
replaces the last, and superseded snapshots live in this branch’s git
history).
`classify_deferred.py` partitions it against the state tiers as:

| bucket | count | share | meaning |
|---|---:|---:|---|
| `proven` | 5,129 | 1.8% | state-never-QH lookup machines: per-instruction re-certification targets, the flip/champion-risk population (141 of the tier's 5,270 were caught by the cycle tiers instead) |
| `provenqh` | 5,163 | 1.8% | state-QH lookup machines: wrap-route 8-way re-scans |
| `dcensus` | 5,111 | 1.8% | the frozen state D_census, back again (45 of 5,156 fell to cycles) |
| `partial` | 20,345 | 7.3% | TNF interior nodes (undefined slots), decided per-orbit through completion |
| `inwalk` | 244,339 | 87.2% | machines the state census decided IN-WALK (n-gram/rank/qhb/RepWL): melt at re-walk once the phase-3 per-instruction tiers land — tier work, not per-machine work |

So the per-machine frontier of the transition-level burn-down is
**~15.4K machines** (proven + provenqh + dcensus), and 94% of the v0
list is expected to be re-absorbed by the phase-3 tier ports before any
per-machine effort is spent.

### 7.1 The empirical flip census (2026-08-19, untrusted simulation)

Per-transition sweeps over the frontier buckets (fire counts + last
fires; "suspect" = some fired transition silent for the trailing 90%
of the budget), the same method that settled the pass1 22:

* **`proven` bucket (5,129 state-never-QH machines, the champion-risk
  population): 572 genuine flips (11.2%), every one with its dying
  transition's last fire ≤ 110.**  At 10⁸ the bucket gave 588
  suspects/337 tape-edge reruns; at 10⁹, 572 persist — these are real
  transition-quasihalters (the `Meta.v:24-27` class), but all are
  startup-transient deaths: scores ≤ 111, absorbed by `B_tr = 2000`
  as trivial wrap boards.  **Zero champion candidates.**
* **`dcensus` + `provenqh` buckets (10,274 state-QH-side machines):
  8,408 suspects at 10⁸** — expected, these are genuine quasihalters
  whose instructions die with their states — **all with dying
  transitions ≤ 2,331.  Exactly 2 machines exceed `B_census = 2000`**
  (`1RB1RD_1RC0LD_1LB0RA_1LC0LC` at 2,331 and
  `1RB0LC_1RC1LD_1RD0RB_0LB1LA` at 1,459 — the second is under it;
  so exactly ONE machine's instruction score provably exceeds the
  state-level 2000 bound so far): the predicted "busy-state
  instruction dies after the state bound" effect is real but
  negligible.  The 1,836 LIVE-at-10⁸ machines (including the champion
  itself, whose 32.8M death sits in the criterion's [budget/10,
  budget) blind window) are being escalated to 10⁹, where the
  champion must surface at exactly 32,779,477 as the sanity check.

* **The escalation of the 1,866 LIVE-at-10⁸ machines (10⁹ budget)
  closed the bucket**: 1,807 stay all-instructions-live (the old `nqh`
  rows, consistent with never-QH-Tr), 0 new suspects, and the 59
  post-collapse drifters (machines that outrun any finite tape after
  their quiet event — the champion family) were re-examined with
  per-transition reporting at the tape edge: **the champion surfaces
  at exactly 32,779,477, the previous champion at exactly 66,348, and
  everything else at ≤ 2,818 — the instruction-level score ranking
  REPRODUCES the state-level record progression, with zero machines
  beyond the champion bar.**

* **`inwalk` bucket (244,339 machines, swept on the box at 10⁸):
  82,327 suspects / 161,169 live / 843 tape-edge / 0 halts — zero
  suspects beyond the champion bar.**  82,319 of the suspects die at
  ≤ 2,000 (the in-walk-tier machines are overwhelmingly
  tiny-transient flips or small state-QH); the standouts are **8
  reroot-family (`0RB…`) machines with dying transitions at 7.9–9.9M
  steps** — below the champion but above everything else ever seen at
  transition level; they sit at the 10⁸ budget's blind edge and are
  being escalated to 6×10¹⁰ (burst counters could fake death there),
  along with an edge-reporting rerun of the 843.

  **Escalation verdict (6×10¹⁰): all 8 refire** — 16×-gap burst
  counters, the pass1-22 signature — and the 843 edge machines all top
  out at ≤ 711.  **The whole (4,2) space now has an empirical
  instruction verdict with zero machines beyond the champion.**  But
  the deep runs mark these 8 as THE frontier: at 6×10¹⁰ each has
  transitions in inter-burst quiet since ~3.26×10¹⁰ with the next
  burst predicted ~5×10¹¹ — beyond any feasible budget, and if those
  silences were deaths the scores would be ~32.6 BILLION.  Only
  Ladder-style per-burst recurrence proofs settle them; they are the
  transition-level analogue of the state burn-down's tower holdouts,
  and their boards are load-bearing for the value theorem.

Combined with the pass1-22 all refiring, every population examined so
far supports **BBBT4(4) = 32,779,478 with the unchanged champion** —
and the burn-down consequences are concrete: the 572 flips are
one-`vm_compute` wrap boards, the QH-side re-scans move at most a
couple of machines past `B_tr = 2000`, and the genuine frontier
remains the sparse-I burst counters needing Ladder-style recurrence
proofs.

### 7.1b Phase-1 in-walk tiers: built, measured

`ClosureTr.v` (the instruction-target closure/rank engine),
`NGramTr.v` (`ngram_check_neverqhtr`, the in-walk never tier) and
`WrapTr.v` (`tm_wrap_tr`, the one-cell halt-redirect, +
`ngram_check_qhboundtr`, the census-grade QHBoundTr tier) are
committed and wired into `decide_easy_tr` with the state census's own
rung ladders.  Sample measurement (8,192 pops, vm_compute): deferral
1,108 → **900**, at 48 ms/pop (the ladders engage).  Classifying the
900: 761 (84.6%) are still `inwalk`-type — the plain-rank
per-instruction gate alone recovers only ~30% of the shallow in-walk
population, confirming the certificate-shrinkage prediction (the
`(q,a)`-avoiding subgraph is strictly bigger) and that the state
census's remaining gates (rank rules, RepWL, lex) carry real weight.
Consequence, per the state PLAYBOOK's Rule 4: the scalable lever is
NOT more in-walk gates but OFFLINE boards loaded as lookups — starting
with wrap boards for the 82K empirical suspects, whose last-fires the
sweeps already measured.

### 7.1c The multi-cell + lex wrap tier (2026-08-19): 4/50 → 36/50

Diagnosing the one-cell wrap's 4/50 pilot catch rate (50 empirical QH
suspects, ALL of which quiet every quiet instruction by step 25 — so
the machinery, not the rung horizon, was the gap) found two stacked
failure modes, each mirroring a state-census lesson:

1. **Multi-cell wrap** (`tm_wrap_trs`): a transition-QH machine
   typically quiets SEVERAL instructions; wrapping one leaves the
   others as appearing-but-never-recurring closure nodes and the
   liveness gate rightly fails.  The checker now takes the whole
   claimed-quiet set `tgs : list (Instr * nat)`, each pair pinned by
   simulation.  The in-walk pin selector (`qh_pins_tr`) scans a
   4×-longer look-ahead — scanning only `t` steps would "pin" every
   busy instruction at its last within-window fire near the window
   edge, and the wrapped closure dies on the spurious cell.

2. **The lex-certificate gate** (`live_lex_ok_tr` +
   `ngram_check_qhboundtr_lex` + `rank_procedure_tr`): the plain rank
   gate demands every abstract cycle avoiding an instruction be
   rank-descending — but a sweeping machine's abstract closure
   self-loops inside its uniform runs (a node firing only the sweep
   instruction), so a plain rank for any OTHER appearing instruction
   CANNOT exist; measured on a clean n=6 closure, rank_ok passed for
   1 of 7 appearing instructions.  This is exactly why the state
   census's Tier Q carries `ngram_check_qhbound_lex` with the in-walk
   RankSearch certificate search.  The port reuses Closure.v's entire
   certificate vocabulary (`lexcomp`, `comp_exact`,
   `lex_edge_decrease`, `lexlt` well-foundedness) by instantiation —
   only the instruction-guarded gate and the closed-set walk lemmas
   are new (`ClosureTr.v`), and RankSearch.v's SCC/Bellman-Ford
   machinery is reused with just the avoid-filter moved from states
   to instructions (`rank_procedure_tr`, untrusted).

Also measured: context mixing at n ≤ 4 spuriously plants the wrapped
head cell (the (StA,S0) node vanishes at n = 6 on the diagnosed
machine), so the walk ladder gains rungs (5,256), (5,1024), (6,1024).

Pilot result: plain multi-cell 4/50 → nested plain-then-lex ladder
**33/50** → with wider n=5..6 rungs **36/50 (72%)**.  The remaining 14
need finer abstraction (RepWL blocks) or per-machine offline boards.

### 7.1d Walk-cost tuning (2026-08-19): the ladder must be paid for

Re-measuring the p1 subtree sample (8,192 pops) with the full 12+12
ladder: deferral **900 → 698**, but 394 s → **12,282 s** (~13 s per
ladder-paying machine, and every deferred-bound machine passing the
candidate filter pays in full).  Extrapolated over ~280K deferred
candidates that is a multi-day single-process walk — so the walk keeps
a TRIMMED configuration and the trimmings go to offline boards
(PLAYBOOK Rule 4, again):

- **One shared 16×tmax last-fire scan** (`qh_last_fires`) replaces the
  per-rung 4×t pin scans: pins are exact over a 16,384-step horizon,
  and a never-quasihalting drifter with recurrence period ≤ 16×tmax is
  never pinned and never pays for a closure.
- **The lex ladder gets its own rung list** (`qhb_lex_rungs_tr =
  [(2,1024);(3,1024);(4,1024)]`): a lex rung re-grows the sets and
  runs the per-instruction certificate search, so failing machines pay
  every rung — one deepest horizon per window is the right shape.  The
  plain ladder keeps the state census's nine rungs.
- **No n ≥ 5 rungs in-walk** (costliest on failures, ~3/36 pilot
  catches; the machinery stays in WrapTr.v for offline boards).

Production pilot: **33/50** at ~0.25 s/machine on catchers.  The walk
itself ships 4-way sharded (`make census-tr-collect-shards`, one
native_compute process per TNF subtree — deferral is per-machine, so
the shard back queues concatenate to the single walk's).

Confirmed on the p1 sample: the trimmed configuration runs in
**1,065 s vs 12,282 s (11.5×)** with IDENTICAL deferral (32, 698) —
on this subtree the trim lost nothing.

### 7.1e The v1 collection walk (2026-08-19, user's box, 4-way sharded)

`make census-tr-collect-shards`, native_compute, ~2.3 h (B0) + ~5 h
(B1); the A shards are single-node (a first transition into state A
self-loops on blank tape forever).  **v1 deferred = 181,289 — a 35.3%
in-walk cut from v0's 280,087** (was `censustr_deferred_v1.txt`, since
superseded by v2).  Buckets (classify_deferred.py):

| bucket    | v0      | v1      | Δ     |
|-----------|---------|---------|-------|
| proven    | 5,129   | 4,961   | −3%   |
| provenqh  | 5,163   | 1,704   | −67%  |
| dcensus   | 5,111   | 5,064   | −1%   |
| partial   | 20,345  | 13,206  | −35%  |
| inwalk    | 244,339 | 156,354 | −36%  |

The wrap tier crushed its home bucket (provenqh −67%); the dominant
remainder is `inwalk` — machines the STATE census decided with tiers
not yet ported.

### 7.1f Tier R: the rank-rules never tier (built)

The state census's biggest inwalk decider, ported: RankSearch's
SCC/Bellman-Ford certificate search with the avoid-filter moved to
instructions (`rank_procedure_tr`, untrusted), verified through the
new lex-gated never checker (`closure_check_neverqhtr_lex` +
`lex_find_tr` in ClosureTr.v, `ngram_check_neverqhtr_lex_with` in
NGramTr.v), laddered as `try_rank_tr` between the plain n-gram tier
and the wrap tier with the state census's own rungs
[(3,0);(3,64);(3,256);(3,1024)].  Pilot on 40 random v1-inwalk
machines: **8/40 (20%) caught, ~0.9 s/machine vm**.

Measured on the p1 sample: deferral **698 → 344 (−51%)** at 1,127 s
vs 1,065 s — nearly free, because every rank catch skips the wrap
ladders it would otherwise pay.  The depth-1 subtree's tier-stack
progression: 1,108 (halt+cycles) → 900 (plain tiers) → 698
(multi-cell + lex wrap) → **344 (+ Tier R)**.

### 7.1g The v2 collection walk (2026-08-21, user's box, through Tier R)

**v2 deferred = 110,910 (−38.8% from v1, −60.4% from v0)**, committed
as `censustr_deferred_v2.txt` (replacing v1 per the one-current-list
policy).  Buckets:

| bucket    | v0      | v1      | v2      |
|-----------|---------|---------|---------|
| proven    | 5,129   | 4,961   | 4,471   |
| provenqh  | 5,163   | 1,704   | 1,704   |
| dcensus   | 5,111   | 5,064   | 5,064   |
| partial   | 20,345  | 13,206  | 5,822   |
| inwalk    | 244,339 | 156,354 | 93,849  |

Tier R took 40% out of `inwalk` and 56% out of `partial`, and — as a
never-tier must — left the QH buckets untouched.  This walk predates
Tier W (RepWL); the list-burn conveyor applies it offline over v2,
no re-walk needed.

### 7.1g Tier W: RepWL (built) + the list-burn conveyor

The state census's biggest unique deep-tier decider
(docs/CENSUS_RUNTIME.md residue ablation: RepWL-only catches beat
rank-only and qhb-only combined), ported as
`CensusTr/RepWLTr.v`: the whole block-run-length abstraction, its
five measures, the certificate machinery and the interned
SCC/Bellman-Ford search are REUSED — the port is `rw_instr` (the
abstract config pins the head symbol, like an n-gram context), one
covers congruence, a fail-closed soundness case for the M4 cut
successor, and the assembly through `closure_check_neverqhtr_lex`.
Wired as Tier W after the wrap tier with the state census's own
parameters ((L,T,t) rungs, fuel 5120, cut 32).

Pilot on the same 40 random v1-inwalk machines as Tier R: **25/40
(62.5%)**, union rank ∪ RepWL = **27/40 (67.5%)** — projecting to
~100K of the 156K inwalk bucket.

**The list-burn conveyor** (tools/censustr/gen_listburn.py +
collect_listburn.py, `make census-tr-listburn`): run the walk decider
DIRECTLY over the deferred list in 16 parallel native units — no
TNF/queue overhead, and it shards perfectly where the tree walk has
only two non-trivial subtrees.  Survivors (still-UNKNOWN) are the
next burn-down list; the full tree walk happens once, at freeze
time.  Smoke-tested end-to-end (30 machines: 17 neverqh, 13
survive).

### 7.2 The kernel-level IRules re-check (first pass)

`Checkers/IRules/MetaTr.v` (committed) re-runs the v1 certificates
through `irules_check_neverqhtr` — the same certificate and replay,
with the prefix gate strengthened from per-state to per-instruction.
Final split over the 250 v1 boards: **97 survive as kernel-checked
`NeverQuasiHaltsTr` (`Machines/IRulesTr_Batch_01.v`, zero new
search), 153 flip (61.2%)** — a far higher flip rate than the
bucket-wide 11.2%, consistent with counter machines' long boot
prefixes firing instructions outside the meta-cycle's set.
**Cross-validation: all 153 kernel flips are exactly empirical
suspects (153/153 agree, 0 disagreements)** — the kernel and the
simulation see the same machines.  Each flip's quiet instructions die
inside the anchor prefix — wrap boards, not champion risks; the 97
survivors are the first rows of the instruction-level Proven lookup
tier.

**WIRED (2026-08-21):** `prov_tr` had stayed `[]` — the 97 theorems
existed but nothing consumed them.  `RunTr.v` now carries them as the
Proven lookup tier, `prov_tr_all` discharging `Forall
NeverQuasiHaltsTr` from the boards; verified that all 97 come back
`R_NeverQH` through `decider_tr` before any ladder runs.  They are
Required directly, NOT through the state census's data/certificate
split (`Proven_List.v` data vs `Proven_Data.v` theorems, joined by a
convertibility type-check in `Run.v`): that split keeps 5,270 boards /
2.65 GB out of every walk unit, and these 97 plus their nine
`IRules_Batch` dependencies are 739 KB.  Add the split back when the
board count justifies it — it is the first thing the conveyor needs at
scale.

### 7.1h The list-burn measured (2026-08-21, 400 v2-inwalk machines)

The conveyor works, and it is how a new tier reaches an existing list
without a re-walk.  The v2 walk ran at `2cd42f9`, which predates Tier
W (RepWL, landed `edf8b26`), so burning v2 with the CURRENT walk
decider measures Tier W's marginal catch directly:

**228/400 (57%) decided `neverqh`, 172 survive** — 69 min for 400
machines, single-threaded vm_compute (~10.4 s/machine).  Extrapolated
over v2's 93,849 `inwalk` machines that is roughly 40K survivors, from
Tier W alone.

The ESCALATED config (`decider_tr_deep`) is the cost story: the same
400 machines passed **242 CPU-min without finishing**, against 69 min
for the walk config — a >3.5x multiplier and climbing.  So escalation
is NOT a first pass.  The shape that follows is a two-stage burn, the
same ladder logic the walk itself uses:

1. cheap pass with the walk config — clears the majority (57% here) at
   ~10 s/machine;
2. deep pass on the SURVIVORS only, where the per-machine cost is
   affordable because the population is a fraction of the list.

Sizing for the box: stage 1 over all of v2 is ~110,910 x 10.4 s / 16
cores ~= 20 core-hours; stage 2 over ~40K survivors at the deep rate
is the part that needs measuring before committing.

The deep run ended up KILLED at ~244 CPU-min with no output at all,
which exposed a real fragility rather than just a slow tier: a burn
unit was ONE atomic `Eval vm_compute` over its whole slice, so any
kill -- OOM, preemption, a closed laptop -- lost every finished
machine.  At 20 core-hours per pass that is not survivable.  Fixed:
gen_listburn now emits one Eval + Compute PER SUBLIST, and
collect_listburn concatenates all of a shard's blocks and treats a
missing tail as UNBURNED -- counted separately and kept on the
burn-down list, never silently dropped.  Verified by truncating a
3-chunk shard after 2: 8 verdicts kept, 4 unburned carried forward.

### 7.1i v3: the Tier W burn completed (2026-08-23)

Repaired and finished on the user's box.  **v3 = 52,505 (-52.7% from
v2's 110,910; -81.3% from v0's 280,087)**, committed as
`censustr_deferred_v3.txt`.  The two halves of the burn agree on Tier
W's rate -- 54.4% on the 41,592 that survived the first attempt, 51.6%
on the 69,318 re-burned after the sizing fix -- and the second run
finished all 35 files with UNBURNED 0.

| bucket    | v0      | v1      | v2      | v3     |
|-----------|---------|---------|---------|--------|
| proven    | 5,129   | 4,961   | 4,471   | 3,927  |
| provenqh  | 5,163   | 1,704   | 1,704   | 1,704  |
| dcensus   | 5,111   | 5,064   | 5,064   | 5,064  |
| partial   | 20,345  | 13,206  | 5,822   | 1,840  |
| inwalk    | 244,339 | 156,354 | 93,849  | 39,970 |

Two readings.  `partial` has nearly collapsed (20,345 -> 1,840): TNF
interior nodes were never hard, just unported.  And `dcensus` has not
moved by a single machine across four lists -- 5,111 -> 5,064 -> 5,064
-> 5,064 -- which is exactly what it should do.  Those are the state
census's own holdouts, boarded by ReachSt / Ladder / counters, and no
in-walk tier was ever going to touch them.  They are now 9.6% of the
list against 1.8% at v0.

`inwalk` is still 76%, so the tiers have not run dry -- but note what
it now costs: these are the machines that pay every tier to fail.

**v3 IS A BURN PRODUCT, NOT A WALK PRODUCT.**  It is the right
burn-down target, but the deferred list that eventually freezes into
[D_censusTr] must come from a WALK that empties the queue -- the
census theorem quantifies over the TNF tree, not over a list.  Walk #3
with the full stack is still owed; the burn bought the floor cheaply
and told us where the remaining work lives.

### 7.1j The frontier prefix, measured both ways (2026-08-23)

The parallel walk's prefix exists only to produce pending nodes to
shard.  The first version ran `Nat.iter 3 q_suc_tr` and two things
about it were wrong, both caught by watching it run:

* `SearchQueue_upds q f n` is **2^n pops, not n** -- so "3 iterations"
  was 24,576 pops of the FULL ladder.
* The front queue is a **working set, not a level of the tree**.  Swept
  against pop count it saturates at ~48 nodes by 32 pops and stays
  there (48 at 32 / 64 / 128 / 1024 / 2048 pops) while the back grows
  linearly.  A deeper prefix buys no extra shards and only pushes more
  machines into the list decided by a weaker tier.

Expansion never needed the ladder either: `node_expand h s i` takes its
hole from `R_Halt s i`, so only `find_halt` can expand a node, and a
node `find_halt` cannot place is one no tier can expand.  Hence
`decider_tr_fast` (halt-or-defer, WF by `find_halt_sound`) and a
32-pop prefix.  Measured, same machine:

| | old: 3 x q_suc_tr | new: 32 fast pops |
|---|---|---|
| time | **6,439 s (1.79 h)** | **0.011 s** |
| front (shards) | 32 | **48** |
| back (weakly-decided rows) | 349 | **27** |

The old prefix cost an hour and three quarters to produce FEWER shards
and MORE untested rows.  48 shards is three waves at `WALK_JOBS=16`,
against the 4-way subtree split whose B1 carried the tree alone.

### 7.1k The straggler: sharding a DFS stack (2026-08-24)

The 48-way frontier split from 7.1j finished 46 shards in minutes and
then ran two for hours.  The last one, `WalkTr_Par_47`, was still going
at **~17 CPU-hours with 15 cores idle**.  Decoding its single node
explained it instantly:

```
front[47] = (3282709385, 3) = 1RB---_------_------_------  ptr (Some StC)
```

That is `child S1 DR StB` -- the fourth element of `q_0_tr`, completely
unexpanded.  A quarter of the TNF tree, handed to one process.

The cause is in `SearchQueue_upd`: it pops the head and pushes the
children back at the **front** (`node_expand h s i ++ t`).  Iterating
it is therefore a depth-first walk, and the front queue is a DFS
**stack** -- its tail holds the shallowest, biggest, least-touched
nodes.  7.1j measured that the front "saturates at ~48" and read it as
a working-set size; it is really the stack depth of a DFS that has
never come back up to the root's siblings.  Sharding a stack hands out
wildly unequal subtrees by construction, and no amount of extra
popping fixes it: the tail is exactly what popping never reaches.

The fix is to stop popping and expand **levels**: `SearchQueue_level`
(RunTr.v, untrusted, next to the other serialization helpers) runs the
decider over *every* front node once, keeping order, so the frontier is
a genuine tree level.  Measured with `decider_tr_fast`, all under
0.2 s:

| levels | front (shards) | back (weakly-decided rows) |
|---|---|---|
| 1 | 24 | 2 |
| 2 | 188 | 13 |
| **3** | **1,700** | **92** |
| 4 | 14,608 | 879 |

Level 3 is the design point.  1,700 subtrees dealt round-robin over 48
shards is ~35 apiece, so siblings land in different shards and the size
variance averages out; 92 weakly-decided rows are noise against a ~50K
list, and each one is a node whose holes are unreachable within 130
steps, so burning it clears its whole hole-completion family at once.

`make census-tr-resplit RESPLIT_NODES=<i>` survives as the escape hatch
for ordinary variance (it now expands levels too), and
`gen_walk_shards.py` prints the tail of the file it could not parse --
the earlier "no `list (N * N)` block found" hid a `coqc` error that had
been redirected into that very file.

**Rule for the next split:** never shard the front queue of a
pop-driven walk.  Shard a level.

### 7.1l v4: the level-sharded walk #3 completed (2026-08-31)

Walk #3 ran the level-3 frontier (1,700 nodes, 92 prefix-deferred)
dealt round-robin into **96 shards** at 16 jobs on the user's box.  All
96 exhausted their slices (every `censustr_par_*.out` prints `= (0,`);
no straggler -- the 7.1k fix held.  Decode was already deduplicated:
52,559 raw rows, 52,559 unique.

`censustr_deferred_v4.txt` = **52,559** (v3 was 52,505), classified:

| bucket | v3 | v4 | delta |
|---|---|---|---|
| proven | 3,927 | 3,889 | -38 |
| provenqh | 1,704 | 1,704 | 0 |
| dcensus | 5,064 | 5,064 | 0 |
| partial | 1,840 | 1,932 | +92 |
| inwalk | 39,970 | 39,970 | 0 |
| total | 52,505 | 52,559 | +54 |

The signature is exactly the prefix boundary moving and nothing else:
three buckets byte-identical, `partial` up by the 92-vs-27
prefix-deferral difference plus shard-side jitter, and `proven` down 38
because those full machines now sit *below* a prefix-deferred ancestor
whose subtree the walk never enters -- the ancestor row covers the
family, so the census is sound and the burn-down list is strictly
higher-leverage (one partial row clears many completions).

`dcensus` is pinned at **exactly 5,064 for the fourth consecutive
list** (v0 5,111 -> v1..v4 5,064): the machines that were hard at state
level are precisely the ones no walk tuning reaches, and they wait for
the ReachSt / Ladder / counters endgame routes.

v4 is a WALK product (unlike v3, which was a burn product), so it is
the first list eligible to freeze into `D_censusTr` for Milestone A:
generate the `DeferredTr` tables from it, set `D_tr := D_censusTr`,
re-walk (cheap: every listed machine hits the lookup tier first), and
an empty queue yields
`forall tm, QHBoundTr 2000 tm \/ Deferred D_censusTr tm` -- the first
instruction-level census theorem.  One-current-list policy: v3 is
retired with this entry; `LISTBURN_SRC` now points at v4.

### 7.1m Why 39,970 machines defer: the diagnosis (2026-08-31, in-container)

Two measurements over the v4 `inwalk` bucket -- the machines the STATE
census decided in-walk that our instruction tiers miss -- explain the
whole population.

**State-tier attribution** (193-machine sample, every 208th row, each
run through the state tiers one at a time in 13 s): rank 65.8%, RepWL
29.0%, ngram (6,800) 3.6%, ngram (4,400) 0.5%, qhb 1.0%.  Nothing was
leaf-decidable, nothing was undecided: pure tier-power gap, owned
almost entirely by Tiers R and W.

**Per-transition sweep** (`trcensus.c`, 1e7 steps): the sample splits
**77% SUSPECT / 23% LIVE**.

* SUSPECT (~30,600 of 39,970): genuine TRANSITION-quasihalters -- the
  state tier proves the state recurs, but one of its two instructions
  stops firing.  Their quiet points are TINY: 96.6% quiet by step 20,
  100% by step 200.  `B_tr` is irrelevant to them; only the wrap route
  can decide them, and it currently fails.
* LIVE (~9,300, almost all rank-tagged): every instruction keeps
  firing, but the resistant ones fire with EXPONENTIALLY growing gaps
  (counts of ~20 in 1e7 steps, last fires at 3*2^21, 2^23) -- counter
  machines.  No window-lex certificate sees that mechanism.  They are
  the same species as the dcensus endgame (counters route) and are
  PARKED there, not fought with rungs.

**Why the wrap route fails today** (per-target diagnostics on the
SUSPECT rank machines): 76% die with the wrapped n-gram closure hitting
a dead node whose instruction IS the pin, at n=3 and still at n=6
(64/84 -> 62/84 -- width is exhausted, matching their survival of the
deep config).  The structural reason: a STATE pin is control flow
("never enter q"), but an INSTRUCTION pin (q,s) is a TAPE-VALUE
property -- q is entered constantly by the busy sibling, and the
window abstraction's edge refill over-approximates the off-window tape,
manufacturing an s-under-q abstract config; wrapping makes it a dead
end and the rung dies.

**The fix, measured before built**: run the SAME wrap on the RepWL
abstraction instead.  An untrusted probe of `rw_succs_cut` over
`tm_wrap_trs tm pins` with the generic per-instruction rank/lex gates,
on all 148 SUSPECT sample machines at the single rung
(L=2, T=3, t=1024, cut=128):

| outcome | share |
|---|---|
| closure CLOSED, all liveness gates pass | **81.8%** |
| dead node, non-pin (size cut -- bigger M/other (L,T)) | 9.5% |
| dead node at pin (other rungs) | 5.4% |
| closed but a gate fails | 3.4% |

RepWL's run-length blocks carry exactly the tape precision the pin
exclusion needs.  Extrapolated: **~25K of the 52.5K list from one new
verified checker**, with engine and search already in the tree --
`closure_check_neverqhtr_lex` is target-generic and `rw_procedure_tr`
already searches certificates over the RepWL closure.

**Tier W-wrap build plan** (next):
1. ClosureTr.v: generic `closure_check_qhboundtr_lex` -- the wrap
   analog of `closure_check_neverqhtr_lex` (closure of the WRAPPED
   successor relation, pins via `wrap_pin_ok`, per-appearing-instruction
   rank/lex gates), concluding NonHalt /\ bound /\ QuasiHaltsTr.
   WrapTr.v's n-gram-specific soundness proof is the blueprint.
2. RepWLTr.v: instantiate at rconf / `rw_succs_cut M tmw L T` /
   `rw_covers'` with `rw_procedure_tr` certs.
3. DecideTr.v / RunTr.v: `try_rw_qhbtr` rungs after the n-gram lex
   rungs (walk: [(2,3,1024)]; deep adds (3,3,1024), (2,2,1024), bigger
   cut), plus the burn config.

After the melt, the boarding-scale populations left are dcensus 5,064
(unchanged, ReachSt/Ladder/counters) + LIVE counters ~9,300 + the
wrap/rung residue -- state-census scale, as intended.

### 7.1n Tier W-wrap BUILT and verified (2026-08-31)

The 7.1m plan, landed:

* **Checkers/WrapTr.v [WrapGeneric]**: the wrap argument factored out
  of [ngram_check_qhboundtr_lex_sound], generic in the abstract domain
  -- any (A, enc, instr, succs, covers) whose successor relation
  simulates the WRAPPED machine.  [wrap_check_qhboundtr_g] +
  [wrap_check_qhboundtr_g_sound] conclude the census R_QH trio
  [NonHalt /\ (QuietAfterTr -> S s' <= S t) /\ QuasiHaltsTr].
* **CensusTr/RepWLTr.v**: the RepWL instantiation --
  [rw_check_qhbtr] (verified) and [rw_tier_qhbtr] (parameter-closed,
  certificates from [rw_procedure_tr] over the wrapped closure).
* **CensusTr/DecideTr.v**: [try_rw_qhbtr_at] as the third rung family
  of [try_qhbtr] (after the plain and lex n-gram wraps), new section
  variable [rw_qhb_rungs].
* **CensusTr/RunTr.v**: walk ladder [(2,3,1024)]; deep ladder
  [(2,3,1024); (3,3,1024); (2,2,1024); (4,2,1024)].

Measured on the 148 SUSPECT sample machines through the REAL walk
decider ([decider_tr], vm_compute, walk fuel 5120 / cut 32):

    R_QH      121  (81.8%)     R_Unknown  27  (18.2%)

-- byte-for-byte the 7.1m feasibility number, now kernel-checked end
to end, at walk fuel (the leak was precision, not fuel).  Per-machine
cost on caught machines replaces the old full-ladder deferral path;
the walk config stays one rung so failing machines pay one wrapped
closure.

Extrapolated melt: ~25K of the 52.5K list.  Next run (user's box):
`make census-tr-listburn` over v4 (LISTBURN_SRC already points there)
with the deep config -> expect survivors ~27K = v5, then walk #4 to
re-derive it as a walk product.

### 7.1o v5: the Tier W-wrap burn, measured (2026-09-01)

The full-list burn of v4 (52,559 rows, deep config, 27 shards / 16
jobs, ~6 h wall on the 16-core box):

    qh (Tier W-wrap)  28,867  (54.9%)     leaf (deep cycles)  92
    neverqh                0              UNKNOWN         23,600

The zeros are the right zeros: [neverqh 0] because this list is
precisely the residue every never-tier already failed on, [halt 0]
because a deferred TNF node's hole is by construction not reached
within the gas.  The tier caught ~96% of the 1e8 sweep's 30,056
SUSPECT machines (sweep, full inwalk bucket: 30,056 SUSPECT /
9,914 LIVE / 0 HALT / 0 EDGE -- the 7.1m sample split held at 10x
the horizon).

**censustr_deferred_v5.txt = 23,600** (burn product; the walk analog
comes with walk #4).  Burn-down: 280,087 -> 181,289 -> 110,910 ->
52,505 -> 52,559 -> 23,600 (-91.6% from v0).  Composition:

| bucket | v4 | v5 | moved |
|---|---|---|---|
| inwalk | 39,970 | 15,350 | -24,620 |
| provenqh | 1,704 | 227 | -1,477 (87% of the bucket) |
| dcensus | 5,064 | 3,840 | -1,224 -- FIRST movement in five lists |
| partial | 1,932 | 313 | -1,619 |
| proven | 3,889 | 3,870 | -19 |

The dcensus movement is notable: wrapped-RepWL decides 1,224 machines
the STATE census could only defer -- a tier it never had.  The
surviving inwalk 15,350 is approximately the 9,914 LIVE counter
machines plus ~5.4K wrap-resistant suspects; the residue is now
dominated by the two endgame populations (counters + dcensus), i.e.
boarding scale.  The LIVE list (from inwalk_sweep_1e8.txt) is the
counters route's burn-down input when that machinery gets built.

Next: walk #4 (the wrap tier is in decider_tr, so the walk re-derives
~v5 as a WALK product) -> the Milestone A freeze candidate.

### 7.1p The LIVE population diagnosed: counters all the way down (2026-09-01, in-container)

Probed while walk #4 runs, on the 1,807-machine LIVE sample
(qhh_live_1e9.txt, per-transition fire stats at 1e9 steps).  The
surface profile first suggested a split -- 959 "dense" machines whose
every fired transition stays hot through the last 10% of 1e9 steps
(0-3 transitions never fire at all), vs ~850 with visible exponential
gaps -- and the dense half looked like easy NeverQH-by-recurrence.
Every follow-up measurement collapsed that hope into one picture:

1. **Extent sweep (all 1,807)**: 1,713 (94.8%) occupy <= 64 tape
   cells after 1e7 steps with LOGARITHMIC growth (+3-4 cells per
   decade; e.g. [0,28] at 1e9).  Log extent + geometric gap histogram
   (2^k-gap count ~ 1e9/2^k) = **binary counters**.  The "dense"
   machines are counters too: all 8 instructions fire on ordinary
   increments, and only deep carries (rare, geometric) produce the
   gap tail.  Residue: 87 fast-extent (sweepers), 7 poly (bouncers).

2. **RepWL closure grid** (20 samples x 8 rungs up to (6,2)/(4,4),
   fuel 40,960, cut 128): ZERO closures close, plain or wrapped --
   fuel-out at ~41K nodes still growing, or cut-out.  Counter tapes
   are irregular short-run bit patterns: run-length blocks compress
   nothing and the closure tries to enumerate ~2^28 patterns.  Tier
   W-never-at-RepWL is dead on arrival for this population.

3. **n-gram per-instruction cert probe** (n in {3,4,6}): closures
   CLOSE for the halt-free machines, and the cert-fail set is
   IDENTICAL at every n -- the avoiding cycles are not leak but the
   real carry loops.  A carry chain is finite but unbounded, so ANY
   finite abstraction contains a tg-avoiding cycle for the carry
   instructions; no rank/lex certificate can exist.  (This is also
   why the STATE census caught these cheaply: per-STATE obligations
   never see carry loops -- every state recurs within a few steps.
   Per-instruction liveness through a counter is intrinsically
   harder than anything the state census ever proved.)  Encouraging
   detail: most instructions' certs PASS (fail sets are typically
   the 2-3 carry instructions), so an induction has a certified base.
   Machines with `---` halt cells additionally lose the plain closure
   to the familiar edge-refill leak (phantom halt), and the wrapped
   closure to phantom pin fires -- 8 of 11 sampled; 3 closed clean.

4. **Leaf checks can't save them**: the walk's loop-scan gas is 512
   and no bounded period exists anyway (gaps grow like log t), so
   neither raising the scan gas nor a cycle=>NeverQH corollary
   applies (measured before the counter fingerprint was recognized;
   recorded so nobody re-walks that path).

**Consequence**: the ~9.9K LIVE machines need the counter liveness
argument -- the one genuine invention this port always owed.  Shape
of the certificate (Tier C, to be designed): per instruction tg,
either (a) not-fired -- wrapped closure where it survives, or (b)
recurrence via counter induction: symbolic run-crossing rules
(RepWL's block machinery is the natural substrate) proving
C(k) ->+ C(k+1) for symbolic k with tg firing en route at depth-k
recurrences -- bit k flips infinitely often because bit k-1 does,
rooted in the lex-certified dense instructions.  bbchallenge's
bouncers/counters certificates are the reference design.  The 94
non-counter LIVE machines (sweepers/bouncers) go to bigger
conventional rungs instead.

Probe artifacts: scratchpad nqh/ (NqhDiag/NqhGrid/NqhRank shards),
live_classes.txt, live_extents.txt, maxgap.c, extent.c, extall.c.

**The route exists and is mostly BUILT.**  Tier C is not a new
checker: [MetaTr.irules_check_neverqhtr] (landed with the 7.2 IRules
port) already concludes [NeverQuasiHaltsTr] from an IRCert -- the
symbolic rule replay walks the carry loop ONCE with symbolic k, so
every carry instruction lands in the recurring fired set F and the
engine's per-instruction [Fires] induction supplies exactly the
unbounded-gap liveness no finite closure can.  The prefix gate
(tvis mask: every prefix-fired instruction is in F) is the strictly
stronger transition-level condition, and never-fired instructions
pass vacuously.  What is missing is only the CONVEYOR:

  1. harness side (user's box, ../BBB): run the irules cert searcher
     (the wave-3 list-C sweep tooling, src/verify.c's prover) over
     the LIVE rows of inwalk_sweep_1e8.txt (~9.9K machines);
  2. container side: transcribe hits with the gen_irules*.py family
     into ProvTr stage batches ([Forall NeverQuasiHaltsTr] lists for
     decide_easy_tr's [Prov] table), kernel-verify each cert with
     [irules_check_neverqhtr] in probe batches (the state pipeline's
     shape exactly -- gen_irulesnqh_stage.py is the template);
  3. if the counters need v3-blk certificates (block runs,
     multi-decrement) rather than the v1 subset (single-symbol runs,
     one k, -1 decrements), port MetaBlk -> MetaBlkTr: the only Coq
     work in the plan, and Meta -> MetaTr already established the
     pattern (swap the state mask for the tvis mask).

The searcher's hit rate on this population is the one open number;
the cert-version mix (v1 vs v3-blk) decides whether step 3 is needed.

### 7.1q v6 and the Milestone A freeze (2026-09-02)

**Walk #4 = v6: 23,692 rows**, the first walk product with Tier W-wrap
in the walk decider.  Guards held (96 shard outputs, every one ending
in an empty queue).  v6 = v5 + exactly 92 machines, and the 92 are
accounted for: every bucket matches v5 except partial 313 -> 405, i.e.
the 92 R_Leaf catches of the v5 deep burn -- cycles the deep loop-scan
(gas 4096) sees and the walk config (gas 512) cannot.  Composition:
proven 3,870 / provenqh 227 / dcensus 3,840 / partial 405 / inwalk
15,350.  Burn-down: 280,087 -> 181,289 -> 110,910 -> 52,505 -> 52,559
-> 23,600 -> 23,692 (walk product).

**Frozen.**  tools/censustr/gen_deferredtr.py -> DeferredTr_00..02.v
(8,000-row shards) + DeferredTr_Data.v ([D_censusTr]); [D_tr :=
D_censusTr] in RunTr.v.  Measured: 14 s per shard to compile, 0.4 s
for Data; [dmap_of D_censusTr] builds in 44 s under vm_compute and
looks its rows up correctly.  The list-burn keeps an EMPTY deferred
map ([D_burn]) -- with the frozen map every burned row would be a
lookup hit and the burn would burn nothing.

**The kernel-checked re-walk (CensusTr/RunTr_Split.v).**  The state
census split its walk by hand (per-grandchild roots, hand-split heavy
subtrees, one WF lemma each: Run_Split, Run_Split2, seven
Run_Split_<tag> files).  The transition census splits the way its
parallel collection already does: [SearchQueue_levels] under the
halt-only decider opens the tree to the level-3 frontier (1,700 front
+ 92 back nodes), and every frontier node's subtree is walked
separately.  Two lemmas make that a proof:

  - [SearchQueue_level_spec_tr]: a level expansion preserves
    [SearchQueue_WF_Tr] under any [QHDeciderTr_WF] decider (the
    [SearchQueue_upd_spec_tr] case analysis, applied to every front
    node in one round);
  - [frontier_decided_tr] / [census_tr_of_units]: N unit facts
    [unit_ok N i 0 frontier_nodes_tr = true] -- unit i certifies, by
    one native computation, that every frontier node with index = i
    (mod N) walks to an empty queue under [decider_tr] within ITER_TR
    = 4096 successor rounds -- give
    [census_tr : forall tm, QHBoundTr B_tr tm \/ Deferred D_tr tm].

tools/censustr/gen_walk_units.py emits the N = 96 units
(theories/CensusTr/Compute/UnitTr_XX.v, [native_cast_no_check]) and
the assembler Census_TheoremTr.v; `make census-tr-walk` runs them in
one xargs pool and checks the theorem.  Round-robin by index is the
collection walk's own dealing, so unit costs track walk #4's shard
costs minus the deferred nodes' failing ladders -- which were the
expensive nodes.  Its wall time is the number that says how far the
transition census is from the state census's 45-minute walk.

### 7.1r MILESTONE A REACHED: the first transition-level census theorem (2026-09-02)

    census_tr : forall tm, QHBoundTr B_tr tm \/ Deferred D_tr tm   -- CHECKED

`make census-tr-walk WALK_JOBS=16` on the 16-core box: 96/96 units,
Census_TheoremTr.v assembled and checked.

    real 143m30s      user 2098m31s (~35 CPU-h)      sys 3m17s

Every 4-state 2-symbol machine either transition-quasihalts within
B_tr = 2000 (or never transition-quasihalts) or is one of the 23,692
frozen rows of D_censusTr -- the exact analog of the state census's
`census_from_empty` theorem, over a per-instruction obligation, from
the kernel.  B_tr is still the placeholder (the harness champion
campaign sets the real one; every tier is parametric in it).

**Cost against the state census's ~45-minute walk: 3.2x wall, and
CPU-bound** (2098 CPU-min / 16 jobs = 131 min ideal against 143
measured, so the round-robin dealing packs to ~91%; no straggler --
the last unit finished in 1,079 s).  Where the ~35 CPU-hours go is
the next measurement (census_probes/censustr_walk_times.txt now
records per-unit seconds), but the structural difference is clear:
the state walk pays LOOKUPS for its ~5K proven-tier and ~5K deferred
machines, whereas this walk still COMPUTES its 28,867 Tier W-wrap
catches (a wrapped RepWL closure each, seconds apiece) and every
never-tier catch on every re-walk.  The state census's answer to the
same cost was the committed, hash-guarded census .vo cache
(tools/census_cache.py, 154 files): pay once per list change, re-walk
by loading.  The transition census has no .vo cache yet; the 2h23m is
the from-source price, reproducible with one command.  Policy to
settle: adopt the cache for Compute/UnitTr_*.vo + Census_TheoremTr.vo
(a few MB) once the list stabilizes, or first move the wrap catches
into a proven-QH stage table so the walk itself gets cheaper.

Burn-down status is unchanged by the freeze (23,692 rows).  The
theorem now makes every further list reduction a re-freeze: shrink
D_censusTr (Tier C for the ~9.9K counters, boards for dcensus,
re-certification for proven/provenqh/partial), regenerate the tables,
re-walk 2h23m (or load the cache), and the theorem holds over the
smaller list.

### 7.1s Tier C found: the counter route is a verified CHECKER, and it derives 73% of LIVE (2026-09-02, in-container)

Reading the state census's counter machinery for the Tier C port
overturned 7.1p's "template route = per-machine proofs" assumption:

- **Checkers/LapDecider.v** is an exact lap decider: a certificate is
  two lists of small numbers ([lstep] chains: [SWin], [SCycL/R],
  rotations, folds), [srun] replays them symbolically for every carry
  index j and every opaque tail at once, and [srun_sound] /
  [lap_of_run] / [vis_of_run] discharge the lap and the per-state
  visits ONCE.  [Counters/LapGlue.glue_neverqh] closes to
  [NeverQuasiHaltsSt]; [LapCertGlue.vis_via_ovf] handles states that
  fire only in the overflow lap; [NestedLap] composes exponential
  overflow branches from affine pieces.  846 LAPC/NLAP boards exist.
- **Encodings are inferred, not guessed**: tools/counters/
  alphabet_infer.py reads the three-word family E xH = C, E (xO q) =
  A ++ E q, E (xI q) = B ++ E q off the tape (17+ families, six of
  them the hand-written Ip/Jp/Kp/Dp/Mp/Bp), and emit_lapcert.py
  searches them at derive time.

**Measured on LIVE** (local 1,807-machine sample; 100 profiled):

| probe | result |
|---|---|
| bin/irules (harness, user's box, first 27 rows) | 3 hits, all meta (1,1) = linear run growth |
| anchor_profile (Ip/Jp only) | 10/100 both-branch affine, 67 no anchor |
| alphabet_infer on the 67 no-anchor | 60/67 recognized (18 NEW A=00 B=10 C=1, 15 Bp, 11 Dp, ...) |
| **emit_lapcert derive (no emit)** | **73 / 100 certificates derived** (~6 s/machine) |

Family mix of the 73: Bp 15, Alph_00_10_1 14, Dp 11, Alph_10_11_11
9, Alph_000_010_01 9, Alph_000_100_1 5, Kp 4, Jp 2, Mp/Ip/others 4.
The 27 misses all fall through every deriver to the cascade class
("no cascade: N counts in the phase" x19, "main count is a..b" x7,
"no overflow phase" x1) -- the exponential-overflow shapes wave 14
left, plus whatever is not a counter at all.  Extrapolated: ~7.2K of
the 9,914 LIVE machines are one Tr port away from kernel-checked
[NeverQuasiHaltsTr]; a wider 500-machine derive is running to tighten
the rate.

**The Tr port (small, generic, one checker):**

  1. [vis_of_run] certifies a state via a PREFIX of the lap chain; the
     prefix's end config has a concrete head symbol [c_h c1], so the
     SAME prefix certifies the instruction (c_st c1, c_h c1) for every
     j and every tail -- [fire_of_run] is [vis_of_run] plus one
     projection.  Carry classes come free: interior-all-p prefixes,
     interior-odd-p prefixes (j = S j', peeled), overflow prefixes via
     [reach_ovf] -- all three recur from every anchor.
  2. [glue_neverqhtr] := [glue_neverqh] with the per-instruction visit
     premise for every FIRED instruction.  The one new piece: a sound
     OVER-APPROXIMATION of the fired set -- boot mask by
     [AnchorVisitsTr.csteps_tvis], lap mask by a per-[lstep] fired
     mask ([SWin]: the window run's instructions; [SCyc]: the unit's;
     rotations/folds: none) with an intermediate-config soundness
     lemma -- so "every fired instruction has a witness" is a finite
     check per machine.  Same shape as [MetaTr]'s prefix gate.
  3. emit_lapcert.py emits per-instruction prefix witnesses + masks
     instead of per-state witnesses; NestedLap gets the same treatment
     for the NLAP shapes.

Combined with the irules conveyor for the linear-growth minority (7.1p
addendum), the counter residue of LIVE drops from ~9.9K to the
cascade class, ~2-2.7K.  That, plus dcensus (3,840, the state's own
counter core -- the same route applies) and the re-certifications, is
the shape of the endgame.

### 7.1t Both Tier C checkers landed; irules is a 32% route, all v3-v7 (2026-09-02)

**Harness sample (user's box)**: `bin/irules --max-steps 200000` over
500 LIVE machines: **158 certificates (31.6%)** -- 39 v3, 89 v5, 24 v6,
6 v7, **zero v1**.  So the irules conveyor's kernel target is the
block/rule-prefix checker, not MetaTr.  Built and pushed (50ca2a2):

- **Checkers/IRules/MetaBlkPfxTr.v**: [irulesblkpfx_check_neverqhtr],
  MetaBlkPfx's checker with MetaTr's instruction-mask prefix gate
  ([csteps_tvis] + [tr_in F]) and conclusion [NeverQuasiHaltsTr]; the
  soundness proof is MetaBlkPfx's verbatim up to the final block, which
  is MetaTr's.  Axioms: functional_extensionality_dep only.
- **Counters/LapGlueTr.v**: [glue_neverqhtr] -- LapGlue's lap argument
  run on the WRAPPED machine [tm_wrap_trs tm pins] (pins = the
  instructions the certificate claims never fire): laps chaining
  forever make the wrapped machine non-halting, [WrapTr.wrap_trs_agree]
  then identifies its run with tm's and rules out every pinned
  instruction, and the per-instruction visit premise is discharged by
  lap-chain PREFIXES ([fire_of_run(_instr)] = [vis_of_run] plus a
  projection) and [fire_via_ovf].  No change to LapDecider.  Same axiom
  footprint.  A certificate's "fired set" needs no new soundness
  machinery at all: running [srun] on the wrapped machine IS the
  proof that only unpinned instructions fire in the lap.
- **tools/censustr/gen_irulesnqhtr_stage.py**: the Tr stage emitter for
  the irules certs, two-phase (probe verdicts, then stage the passing
  certs into [pts_NN : list TM] + [Forall NeverQuasiHaltsTr pts_NN] for
  [prov_tr]).  A cert that passes the state gate but fails the Tr gate
  is a VERDICT FLIP -- the machine transition-quasihalts -- and is
  reported, not staged.

Conveyor status: the irules side is ready to consume the certs the
moment they are on the branch (results/certs_live500 + the full
live_all run); the lap-certificate side needs the emitter's Tr board
template next (per-instruction prefix witnesses over the derived
chains, pins = never-fired instructions, [srun] on the wrapped tm).

### 7.1u The lap-certificate route boards at the instruction level (2026-09-02)

**Built and measured in one afternoon, because the checker did the
work.**  `tools/counters/emit_lapcert.py --tr` renders an
INSTRUCTION-level board from the same derivation as the state board:

  - the board's local [tm] is re-pointed at the WRAPPED machine
    [tm_wrap_trs tm pins] (pins = the instructions the machine never
    fires, read off a 200K-step simulation -- untrusted; a wrong pin
    makes every [srun] fail), so every lap/boot lemma is reused
    verbatim and now doubles as the proof that no pinned instruction
    fires;
  - the per-state visits become per-instruction chain-prefix witnesses
    ([lapcert.reach_instr]), searched over the same three sources as
    the states -- overflow/boot chain from B0, interior chain from A0,
    nested exit chain from BE0 -- and closed by [LapGlueTr]'s twins
    [fire_via_ovf(_lift)] / [fire_via_int_lift] / [fire_via_fill];
  - the closer is [glue_neverqhtr]; mirrored machines transfer through
    [TNF_QHTr.neverqhtr_mirror].

Routes covered: one/split interior, exact and lift-slack, flat and
NESTED overflow.  Not yet: the offset-nested and peeled overflow
routes and the quasihalting closers ([glue_qh]/[glue_qh_abs] have no
Tr twin -- their machines transition-quasihalt and belong to the QH
side), ~2% of the derive population.

**Measured on the 100-machine LIVE sample**: state derive 73/100;
Tr boards (before the nested route landed) 68/100, with the six
nested machines boarding individually afterwards -- i.e. the Tr route
reaches essentially the whole derive population.  The route mix of
the 73: one+lift 28, split 22, one plain 11, split+lift 5, nested 6,
peel 1; 60 of 73 via the mirror.  The wider 500-machine derive is
holding at 75%.  Ten LAPT boards are committed
(theories/Machines/CountersTr/), axioms
[functional_extensionality_dep] only; `tools/censustr/gen_provtr_lap.py`
collects them into [ptl_NN : list TM] + [Forall NeverQuasiHaltsTr]
stage files for [prov_tr].

What this means for the endgame: ~73% of the ~9.9K LIVE counters
(~7.2K machines) are one emitter run away from kernel-checked
[NeverQuasiHaltsTr] -- a run that costs ~6 s derive + ~5 s coqc per
machine, i.e. an afternoon on the 16-core box sharded 16 ways.  The
irules conveyor (MetaBlkPfxTr, 32% of LIVE, overlap unknown) adds to
that.  Open question before the bulk run: board granularity -- one
12 KB file per machine is the state census's convention (1,928
boards) but 7K of them is 85 MB of source; a per-file chunking of the
emitter is the obvious fix and costs nothing in the proof.

### 7.1v CORRECTION: the real LIVE population, and Tier TC lands on a quarter of it (2026-09-02)

**The §7.1p/7.1s/7.1u population numbers were measured on the wrong
list.**  The 1,807-machine "LIVE sample" (qhh_live_1e9.txt) those
sections quote has ZERO overlap with the LIVE set actually inside the
frozen v6 deferred list.  Reproduced locally (trcensus, 1e7 steps,
over buckets_v6/deferred_inwalk.txt): 9,919 LIVE machines, split by
tape-extent growth into four classes that need four different routes:

| class (extent growth) | count | share | what they are | route, measured |
|---|---|---|---|---|
| logarithmic | 4,523 | 46% | binary counters | lap certificate (Tier C): **49/100** derive on the real class, not 73% |
| linear | 2,483 | 25% | small-period translated cyclers (instruction gap <= 113) | **Tier TC, this section: 2,456/2,483 kernel-checked** |
| sqrt | 1,996 | 20% | bouncers | RepWL closures at wider rungs close 3/8 sampled ((3,3),(5,2),(6,2)) |
| polynomial | 898 | 9% | unknown | none yet |

Two more corrections fall out of the re-diagnosis:

- **The v5 "deep" list-burn was never deep.**  The `census-tr-listburn`
  Makefile target never passed `--deep` to gen_listburn.py, so the
  16-shard burn that "confirmed" the residue ran the WALK decider
  (gas 512, walk rungs).  Fixed: `LISTBURN_DEEP ?= --deep`, deep loop
  gas 65536, rw_rungs_deep gains (6,2,0).  A genuine deep burn has not
  run yet.
- **B_tr was 2,000; it is now 32,779,478** (the champion floor;
  verdicts are monotone in B by qhboundtr_mono).  The leaf checks guard
  on `n1 <=? B`, so at 2,000 every translated cycler whose anchor sits
  past step 2,000 fell straight to deferred.  Even at the raised bound
  the in-walk leaf checks catch only 10/40 sampled linear machines
  (lp_candidates are weak), which is why the class needs certificates.

**Tier TC (Checkers/TCyclerTr.v).**  `tcycler_check_neverqhtr tm n1 P W`
is TCycler's checker with the target alphabet changed from 4 states
to 8 instructions: the lap induction (`tcycler_laps`, `tcycler_fold`)
is reused verbatim, the two scans become `cfires` (prefix) and
`gfires` (guarded lap), the inclusion gate is `forallb (cfires (n1+P) t
==> gfires P t) all_Instr`, and the pumped occurrence fires the same
instruction because `glift` plants the head cell (`glift_cinstr`).
Side L runs the checker on `mirror_tm` (`neverqhtr_mirror`).
Compiled first try; no new axioms.

Certificates come from `tools/censustr/tc_find.py` (UNTRUSTED: find the
period of the (state, read) stream over 60K steps, read off n1/P/W/side
from the head positions) and are staged by
`tools/censustr/gen_provtr_tc.py` (probe phase: `Eval vm_compute`
verdicts; stage phase: `ProvTr_TC_NN.v` with `ptc_NN` +
`Forall NeverQuasiHaltsTr ptc_NN`, 250 per file).  On the 2,483 linear
LIVE machines: tc_find 2,474 found (9 not periodic within budget), probe
2,456 true / 18 false (all 18 are tc_find tail artefacts with
n1 ~ 59,9xx, period 1-9 -- spurious short periodicity at the end of the
budget).  tc_find now rejects tails shorter than `--min-tail` 2000
steps; a 1M-step / 100K-period re-run on the 27 left over found 27
certificates (periods up to 88,381), all kernel-checked (ptc_10).
Eleven stage files, each ~2-4 s to compile; `prov_tr` is now
`prov_tr_irtr ++ ptl_00 ++ ptc_00 ++ ... ++ ptc_10`: **all 2,483
linear-extent LIVE machines are in the proven tier.**

**Bulk lap-certificate emit (user's box, 16 shards, in flight):** at
4,489/9,919 processed, 1,137 OK (25%), 2,952 "no anchor", 308 "no
interior chain", 92 "no overflow chain".  The 66% no-anchor share is
the non-counter classes above going through a counter emitter; on the
counter class alone the route is ~49%.

**Burn-down after this section** (9,919 LIVE):
- linear 2,483: done (2,483 staged).
- log 4,523: ~2,200 via lap certificates when the bulk emit finishes;
  the other half needs the missing lap routes (offset-nested, peel) or
  a different counter engine.
- sqrt 1,996: 923 proven by RepWL at the tape period (§7.1w); a
  second pass at higher fuel, then the deep burn for the rest.
- poly 898: undiagnosed.

### 7.1w The gap has a name: the RANK tier's instruction twin, and the fake macro-cycle (2026-09-02)

**Attribution.**  Running the state census's tiers one at a time
(`scan_loops`, `try_ngram`, `try_rank`, `try_qhb`, `try_rw`, census
parameters) on samples of the three open classes -- 40 bouncers (sqrt),
40 polynomial-extent machines, the 34 log-extent counters the lap
emitter reports "no anchor" for -- gives one answer: **`try_rank`
(the n-gram closure with rules (a)/(b) rank certificates, rungs (3,0),
(3,64), (3,256), (3,1024)) decided 114 of 114 at the state level.**
`try_ngram` decided none of them, RepWL 38/40 of the poly class only.
Cross-checking the 9,919 LIVE machines against every state-level
closeout record (`tools/closeout/frozen_map.tsv`, the `*_caught.tsv`
sweeps) confirms it: 9,790 have NO record -- they never reached a
deferred list at the state level; the rank tier took them in the walk.

**The instruction twin fails on 1-3 instructions per machine, and it is
the abstraction, not the measures.**  `rank_tier_tr` (DecideTr) is the
same closure, the same rules, target alphabet changed from states to
instructions.  Per-instruction probes on the real samples (rungs (3,t),
(4,1024)): every machine's closure closes; the certificate fails for
1-3 of the 8 instructions (sqrt 29/40 fail, poly 40/40, noanchor
26/34).  Dumping the stuck SCC for a bouncer (target (A,1), which fires
when the left sweep crosses an interior 0) shows one 60-node SCC holding
the WHOLE bounce: right sweep, turn, left sweep, turn.  The abstraction
admits a left sweep that crosses only 1s all the way to the blank end --
a far tape of the form 1^k 0^omega is consistent with every 3-gram the
real tape (10111)^k 0^omega has -- so an abstract macro-cycle avoids
(A,1) forever and no count-of-1s measure decreases on it (the tape
grows).  The state target A never has this problem: A0 fires at the
blank end on every bounce, so every macro-cycle passes through a target
node.  The same picture holds for the poly and non-binary-counter
samples: one stuck SCC, containing nearly all instructions, per failing
target.

Two things fall out immediately:

- **The deep rank rungs catch a slice the walk cannot.**  At (4,1024)
  the certificate closes for 11/40 bouncers and 8/34 no-anchor counters;
  `rank_rungs_tr` stops at n=3, `rank_rungs_deep` has (4,1024), (5,1024),
  (6,4096).  The first genuine `--deep` list-burn (never run, §7.1v)
  will take these.
- **`Checkers/NGramHistTr.v` landed**: NGramHist (cells carry the last-k
  (state, read) records; it closed 669 state-level deferred counters)
  instantiated on `ClosureTr.closure_check_neverqhtr_lex` with the
  instruction projection `ha_instr`; the `hcomp` certificates and their
  exactness proofs are reused verbatim, soundness
  `ngramhist_check_neverqhtr_lex_sound`.  Measured with a forked
  untrusted prover (instruction-target certificate search) at the state
  stage's rungs (k,n,t,fuel) = (2,2,40,20000), (2,3,40,20000),
  (4,2,40,20000): final numbers: no-anchor counters 6/34, bouncers 4/40 (6 more do
  not even close), poly 1/40.  The history records do not exclude a
  long uniform run of 1s, so the fake bounce survives; the tier is a
  minor contributor and its emission conveyor is not built.

**What does exclude the fake bounce: block structure.**  RepWL's
repeated-word abstraction knows every block of (10111)^k contains a 0.
The tape-period detector (`period.py`, untrusted) over the whole sqrt
class: period 5 for 607 machines (30%), 3/6 for ~470, 1-2 for ~370, 7
for 88, 8 for 85, 9 for 44, longer for ~50.  The walk's and the deep
ladder's RepWL rungs stop at L=6, so a third of the class was never
tried at its own period -- exactly the state census's big-block finding
(REPWL_BIGBLOCK_WAVE8: L=9..30 caught what L<=6 could not).  The
in-container grid at L in {2,3,4,5,6,8,10,12}, T=2, fuel 400K on the
first five bouncers (three finished before the container's memory
limit killed the run): **every one closes at its detected period and
nowhere else** -- period 8: closes at (8,2) with 1,056 nodes, dead or
fuel-exhausted at every other L; period 3: closes at (3,2) (263 nodes),
(6,2) (1,160) and (12,2) (4,408); period 8: closes at (8,2) with 19,366
nodes.  The instruction-level tier `RepWLTr.rw_tier_tr` (closure +
per-instruction rank/lex certificate + verified check in one
vm_compute) probed at L in {p, 2p} over the 40-bouncer sample (fuel 100K, cut
128, in-container vm_compute): **27 of the 35 machines whose rows all
finished certify** (82 of 95 rows returned before the 30-min per-file
cap; 13 rows -- the fuel-exhausting wrong-L ones -- timed out).  For 3
of the 27 only the doubled block certifies (the write pattern's period
can be 2p), so the rows now carry L in {p, 2p, 4p}
(`censustr_rw_rows_v6.tsv`: 6,582 rows over the 1,996 sqrt-class
machines) and the probe is one lazy match chain per machine that stops
at the first true L.  Box run: `make census-tr-rwprobe` (16-way
native), then `make census-tr-rwstage` -> `ProvTr_RW_NN.v` for
`prov_tr`.  Sweep result (fuel 30K, cut 32, one machine per file, 300 s cap,
vm_compute; the first attempts at fuel 100K / cut 128 / native_compute
ran for hours per file): **923 of 1,991 certify (46%)**, block lengths
5 (571), 6 (146), 7 (82), 8 (82), 9 (42) -- nothing at L<=4 or L>=10.
The period-1/2 "bouncers" (~370) certify nowhere; they are the
bouncer-counter hybrids, not block-periodic.  Staged as ProvTr_RW_00..09
(ptw_NN).  A second pass over the 1,068 left (`censustr_rw_rows_v6_pass2.tsv`,
fuel 100K, cut 128, 900 s cap) is prepared for the cases where the
closure needs more room.

Deep-burn samples (decider_tr_deep, gas 65536, the widened rungs) on the
same three samples: in flight.

**Route decision.**  sqrt/bouncers: Tier W at the detected tape
period (above), then the deep rank rungs for the remainder.  log
counters: lap certificates (~49%) + deep rank (4,1024) on the
non-binary ones (8/34) + NGramHistTr (6/34, conveyor not built).
poly: still open -- rank_tier_tr fails 40/40, NGramHistTr 1/40, tape
periods are mostly 1, and the instruction-level RepWL tier at L=2..4
with fuel 100K fails on all 61 rows probed (the state-level RepWL
(2,2,0) took 38/40 of the same machines: the same fake-cycle gap in
block-structured form).  898 machines (9% of LIVE) stay on the
deferred list until a new abstraction exists; the state census's
per-machine sync-bouncer-counter glue (BOUNCER_COUNTER_READING.md) is
the only known lead.

### 7.1x The v7 re-walk: census_tr checked against the 17,989-row list (2026-09-05)

`census_tr : forall tm, QHBoundTr B_tr tm \/ Deferred D_tr tm` re-checked
on the box with D_tr = the v7 tables (v6 minus the 5,703 rows the
proven tier covers; 17,989 rows) and prov_tr = 5,800 machines (97
IRulesTr + 2,297 lap boards + 2,483 translated cyclers + 923 RepWL
bouncers).  96 native units, `make census-tr-walk WALK_JOBS=7`; unit
times 420-2,466 s.  Two operational lessons, both now in the Makefile:
a unit process peaks at 2.7-3.8 GB (it loads the native code of every
certificate stage), so WALK_JOBS=16 on 31 GB OOM-kills a third of the
first wave -- budget WALK_JOBS <= RAM_GB/4; and a unit counts as done
only if its .vo is newer than RunTr_Split.vo, so stale units from an
earlier walk are rebuilt rather than skipped (skipping them fails the
assembly with "inconsistent assumptions").

Axiom footprint (`Print Assumptions census_tr` / `prov_tr_all`, on
the box): `FunctionalExtensionality.functional_extensionality_dep` only.

Bookkeeping lesson from the same day: the first RepWL stage files
paired probe verdicts with machines by *file order*, and past 100 files
that order is lexicographic; the kernel refused the first mis-paired
lemma.  `gen_provtr_rw.py stage` now keys every verdict by the machine
spec written in its probe file.  The counts (923 / 17,989 / 1,073) were
unchanged; the pairing was not.

### 7.1y The state-proven rows re-checked: quiet machines, and the rank gap is a window-size gap (2026-09-06)

The v7 list carries 3,870 rows that the STATE census proved never-QH
(§7.1v: the "state-proven" class).  Each has a state route on record
(tools/proven_map.tsv, the boards): an irules certificate, a translated
cycler, or an n-gram rank rung (n, t).  The instruction checkers take
the same certificates and rungs, so the cheapest conveyor is "same
route, instruction checker".  Three probes in the container:

| state route | rows | instruction checker | accepted | rejected |
|---|---:|---|---:|---:|
| irules cert (BIRCertP / IRCert) | 898 | MetaBlkPfxTr / MetaTr, same cert | 600 (`ProvTr_IR_00..02`) | 298 |
| translated cycler (tcyc manifest) | 33 | TCyclerTr, `tc_find` period | 30 (`ProvTr_TC_11`) | 3 |
| rank rung (n, t) | 2,780 | `rank_tier_tr tm n t 200000 512`, same rung | 206 (`ProvTr_RK_00..07`) | 2,539 (+35 timed out) |

**A third of the state-proven rows are quiet-instruction machines.**
A 2M-step scan (last fire step of each instruction; "quiet" if some
fired instruction does not fire again in the second half) says 1,215 of
the 3,870 have an instruction that stops.  The heuristic over-reports
slightly: 48 of the 600 machines the irules checker PROVES live are
"quiet" by the scan, with last fires at 450K-700K of 2M -- instructions
that fire once per counter overflow.  Take the quiet count as ~1,150.
Those machines are never-QH at the state level and QH at the
instruction level; they belong on the `QHBoundTr` side of the theorem,
where no route exists yet (§7.1v).

**The irules conveyor is exhausted on the live side.**  All 298
rejected irules certificates are quiet machines by the scan.  Zero
rejections on live machines: the instruction-mask gate of MetaBlkPfxTr
accepts every state certificate whose machine is actually live.

**The rank gap is a window-size gap.**  Accept rate by the state rung:

| rung (n, t) | rows | accepted |
|---|---:|---:|
| (2, 0) | 1,682 | 0 |
| (3, 0) / (3, 64) | 718 | 0 |
| (4, 0) / (4, 64) | 173 | 71 (41%) |
| (5, 0) | 50 | 20 (40%) |
| (6, 0) / (6, 64) / (6, 256) | 69 | 45 (65%) |
| (7, 0) / (7, 64) | 56 | 44 (79%) |
| (8, 0) | 20 | 17 (85%) |
| (10, 0) / (11, 0) / (12, 0) | 9 | 9 (100%) |

At the state rung n = 2 or 3 the instruction target never certifies
(the fake macro-cycle of §7.1w lives in the coarse abstraction), but
from n = 4 up the same rung certifies at 40-100%.  So the gap is not
"rank rules do not work at instruction targets"; it is "the
instruction target needs a wider window than the state target did".
The walk's rank ladder stops at n = 3 (`rank_rungs_tr`); the deep
ladder adds (4, 1024), (5, 1024), (6, 4096).  Of the 2,539 rejections
807 are quiet by the scan; the other 1,641 (all at (2, 0) / (3, 0),
live) are being re-probed at (4, 0) in the container -- results go in
§7.1z.

Cost: rungs n >= 7 take minutes per machine (the closure at window 7+
is large), n <= 6 seconds.  `gen_provtr_rk.py probe` writes the rows
in chunks; probe n >= 7 rows one per file under a timeout, or one slow
row stalls a 100-row file (the first layout lost 35 rows that way).

Where the 3,870 stand after this: 836 proven at the instruction level
(600 + 30 + 206), ~1,150 quiet (QHBoundTr side, no route), ~1,850 live
and unproven, nearly all of them the (2, 0) / (3, 0) rank rows.
`prov_tr` is 6,636 machines after this stage (6,739 with the
escalation stages of §7.1z, 6,776 with RepWL pass 2).

### 7.1z Rank escalation: a wider window does not rescue the (2, 0) / (3, 0) rows (2026-09-06)

The 1,641 live rank rejections of §7.1y (state rung (2, 0) or (3, 0))
re-probed at (4, 0) with the same fuel: 85 accepted (82 of the (2, 0)
rows, 3 of the (3, 0) rows), 1,556 rejected -- 5%.  Staged as
`ProvTr_RK_08` (prk_08).  A (6, 0) sample of 150 of those failures:
18 accepted, 116 rejected, 16 timed out (10-row files under 1800 s;
window 6 costs 1-4 min per machine) -- 12-13%, staged as
`ProvTr_RK_09` (prk_09).  So each wider window buys a slice, at a
price that only the box can pay for the full 1,556: the right vehicle
is the deep burn (ng rungs to (10, 4096), rank to (6, 4096), RepWL,
lex), which tries all of that in one pass -- these rows are not in
`censustr_deferred_v7_inwalk.txt`, so the first deep burn did not see
them.  Next box job after the overnight run:
`make census-tr-listburn LISTBURN_SRC=censustr_stproven_live_rest.txt LISTBURN_DEEP=--deep LISTBURN_JOBS=8`.  Their list is `censustr_stproven_live_rest.txt`: the 1,782
state-proven rows that are live by the 2M-step scan and still
unproven at the instruction level (921 of the 3,870 are now proven,
1,167 quiet).

### 7.2a RepWL pass 2: the sweep is exhausted (2026-09-06)

The second RepWL sweep over the 1,068 unproven bouncers (rows at fuel
100000 / cut 128, L in {p, 2p}, 900 s per machine, 16 jobs, ~14 h on
the box): 37 certified, 155 rejected, the other ~880 hit the cap with
no verdict -- the closures at cut 128 are the ones §7.1w/§7.1v
measured blowing up.  Staged as `ProvTr_RW_10` (ptw_10).  So the
bouncer class stands at 960 / 1,996 and the remaining 1,036 are not a
sweep problem: they need the certificate route of §7.1v (search the
RepWL certificate offline with a round cap, check only the certificate
in Coq).

### 7.2b The deep list-burn is infeasible as configured; v8 tables cut (2026-09-07)

`make census-tr-listburn LISTBURN_SRC=censustr_deferred_v7_inwalk.txt LISTBURN_JOBS=8`
(the 9,657 LIVE + quiet in-walk rows, `decider_tr_deep`): after 20.6
CPU-hours per shard not one 400-machine sublist had printed on any of
the 8 shards, and two shards exited with nothing at all (4-6 GB
resident each, the box at its 31 GB ceiling).  So the deep decider
averages well over 3 min per machine on this population.  The cost is
`rw_rungs_deep`: nine RepWL rungs at node cut 128 / fuel 40960, the
setting §7.2a just measured at 900 s+ per machine for the bouncers --
per rung.  Killed.  Verdict: the deep ladder is the wrong tool here.
Every machine on the list already failed the cheap tiers, and §7.1v
says what each class needs instead (lap routes for the counters, the
certificate route for the bouncers, a new abstraction for the
polynomial class, a `QHBoundTr` route for the quiet ones); a bigger
ladder finds none of that.  Do not run `--deep` over a whole class
again; if a deep decider is ever wanted, drop the RepWL rungs from it.

v8 tables: `proven_specs.py --minus` (now reading the IR and RK
stages too) removes 963 more rows from v7 -> `censustr_deferred_v8.txt`,
17,026 rows; `DeferredTr_00..02` + `DeferredTr_Data` regenerated.
Next box job: `make census-tr-walk WALK_JOBS=7` against them.

### 7.2c The v8 re-walk: census_tr checked against the 17,026-row list (2026-09-07)

`make census-tr-walk WALK_JOBS=7` on the box, D_tr = the v8 tables
(17,026 rows), prov_tr = 6,776 machines (97 IRulesTr + 2,297 lap
boards + 2,513 translated cyclers + 960 RepWL bouncers + 600 irules
re-checks + 309 rank re-checks): build phase well under an hour, 96
units in ~2.5 h (901-1,812 s each in the last wave), assembly
`Census_TheoremTr.v` -- CHECKED.  `Print Assumptions census_tr` on the
box: `FunctionalExtensionality.functional_extensionality_dep` only.
This is the consolidation point for
branching sessions: everything proven so far is in the kernel-checked
theorem, and the remaining 17,026 rows are the §7.1v/§7.1y classes
with no cheap route left (see the path in the 2026-09-07 assessment:
QH-side conveyor, NGH conveyor on the closeout boards, the nested/peel
lap ports, the bouncer certificate route).

### 7.3a The QH side, measured: it is the LIVE side with one dead instruction (2026-09-08)

The `QHBoundTr` side of v8 -- 5,436 quiet in-walk rows, 1,167 quiet
state-proven rows, 592 closeout state-QH boards, 632 partial/provenqh
rows, 7,827 in all -- had no route.  The conveyor built for it
(`tools/censustr/gen_provtr_qh.py`, `CensusTr/QHConveyorTr.v`) takes
each machine's exact per-instruction last fires from a 10M-step scan
and calls the wrapped n-gram QHBound checkers of `Checkers/WrapTr`
(plain, and lex-gated via `rank_procedure_tr`) at `t` just past the
last quiet fire, then stages the accepted rows as `ProvTr_QH_NN` for
`provqh_tr`.  It works end to end (probe, stage, kernel check on a
sample) and it does not pay:

| probe | rows | accepted |
|---|---:|---:|
| plain, n in {2,3,4}, t = tmax + {1, 65, 1025} | 226 | 27 (12%) |
| lex-gated, same ladder, on the plain rejects | 199 | 0 |
| n in {5, 6}, plain + lex, on 60 of those rejects | 60 | 3 (5%) |
| late-quieting rows (last fire 3.1-3.3M), full ladder | 27 | 0 |

The hypothesis behind the conveyor -- that the deferred quiet machines
quiet later than the in-walk ladder's t <= 1024 -- is false.  Of the
first 5,600 scanned rows, 98% quiet before step 64; the in-walk tier
saw the right t and failed on the closure.  (The 27 late ones, quiet
at ~3.15M, are real quasihalters with a score a tenth of B_tr, and the
closure fails on them too.)

**What the residue is.**  All 7,827 QH-side rows classified by
tape-extent growth exactly as the LIVE population was (§7.1v):
log-extent (counters) 3,745, sqrt-extent (bouncers) 3,288, linear
(translated cyclers) 794.  The dead instruction is a single one in 95%
of them, `A0` (the very first transition) in 54%, `B0`/`C0`/`D0` in
most of the rest.  The full 10M-step scan (7,266 rows in when this
was written): 6,811 quiet, 455 live at 10M (the 2M-step scan's false
quiets); of the quiet ones 6,233 quiet before step 64, 49 between 64
and 1M, and 529 late -- last fire between 1M and 4.7M.  The largest
quiet last fire in the population is 4,734,693
(`1RB1LB_0RC0LA_1LC0LD_1RA1RC`), a seventh of B_tr: on this
population and this scan horizon the instruction-level value stays at
the state champion's.  The 529 late quieters are real quasihalters
with million-step scores and no route yet (the closure fails on them,
table above); they are the value-relevant class to watch.  So a
quiet-instruction machine is a LIVE-class machine whose initial
transition is never taken again; `QHBoundTr` for it means "A0 last
fires at s < 64, every other fired instruction recurs" -- and the
second half is exactly the never-QH obligation the LIVE routes prove,
for the same three classes with the same routes (lap certificates,
RepWL/the certificate route, translated-cycler laps).

**The route, then.**  Not a wider wrapped closure: QH variants of the
LIVE-route checkers, where the instructions fired in the anchor prefix
but absent from the recurring set are the pins (quiet after their last
prefix fire, checked as in `WrapTr.wrap_pin_ok`) and the conclusion is
`QHBoundTr` at the anchor instead of `NeverQuasiHaltsTr`.  In yield
order: `TCyclerTr` (linear, ~650 rows; the lap induction is reused
verbatim, only the "every fired instruction recurs in the lap" scan
changes), `LapGlueTr` (log, ~2,500 rows; the emitter already pins
never-fired instructions), and RepWL-wrap (sqrt, ~2,200 rows;
`rw_tier_qhbtr` exists and inherits the bouncers' closure problem, so
this class waits on the certificate route of §7.1v either way).
Bookkeeping: `qh_scan.py` (scratch) records every instruction's last
fire; `gen_provtr_qh.py` stays as the staging pattern for whichever
checker certifies a row.

### 7.3b The first QH-side stage: quiet-instruction translated cyclers (2026-09-08)

`Checkers/TCyclerQHTr.v`: `tcycler_check_qhboundtr tm n1 P W` is
`TCyclerTr.tcycler_check_neverqhtr` with the gate inverted.  The lap
[g1 -> g2] of period P from the anchor n1 is reused verbatim (the
`tcycler_fold` / `tcycler_laps` lemmas of the state checker); instead
of "every instruction fired in the first n1 + P steps fires in the
lap" it asks that SOME instruction fired before n1 does not fire in
the lap.  Every configuration past n1 folds into the lap, so an
instruction absent from the lap last fires before n1, and one present
in it fires again after any index: hence `NonHalt`, the unfolded
`QHBoundTr n1` (every quiet instruction's score is at most n1) and
`QuasiHaltsTr` (the prefix-fired absentee), which is the shape
`provqh_tr` needs.  One axiom.  Side L runs the checker on
`mirror_tm` and transfers through `qhboundtr_mirror` / `mirror_fires`.

Conveyor: `tc_find.py` (unchanged) over the 7,827 QH-side rows found
793 periodic laps -- the linear class of §7.3a, one row in ten;
`gen_provtr_tcqh.py` (the TC generator with the QH checker and the
`NonHalt /\ QHBoundTr 32779478 /\ QuasiHaltsTr` stage lemma via
`QHConveyorTr.qh_bound_of_le`) probes them at ~100 per second: 731
accepted, 62 rejected (the same lap-detection misses as the never-QH
conveyor).  Staged as `ProvTr_QH_00..02` (pqh_00..02), the first
entries of `provqh_tr`.  Their scores are the anchors n1, all far
below B_tr; the QH side's value question stays with the late
quieters of §7.3a.

Next on this side, in the order of §7.3a: the lap-certificate
(counter) variant, then RepWL-wrap for the bouncers.

### 7.3c The counter route on the QH side: LapGlueQHTr and the LAPQ boards (2026-09-08)

`Counters/LapGlueQHTr.v` (`glue_qhboundtr`, one axiom): the never-QH
counter glue with the boot moved.  `LapGlueTr.glue_neverqhtr` runs
the whole lap argument on the machine wrapped at the pins from the
blank tape, so a pinned instruction firing in the boot prefix -- which
is exactly what a quiet-instruction counter does with A0 -- would
halt the wrapped run at step 0.  The QH glue takes the boot
`stepn tm t0 InitES = Some (lift (Cf p0))` on the ORIGINAL machine and
runs only the laps and the per-instruction fires on the wrapped
machine from the anchors; `WrapTr.wrap_trs_agree` from the boot
configuration then says the original run past `t0` is the wrapped one
and no pin fires at any index >= t0.  Conclusion: `NonHalt`, the
unfolded `QHBoundTr t0`, `QuasiHaltsTr` (a pin that fired in the
prefix, `existsb (cfires tm c0 t0) pins`).  Every lap and fire lemma
of the never-QH boards is reused as is; only the boot lemma and the
closer change (`QHConveyorTr.lap_qh_stage`, `qh_triple_unmirror` for
the mirrored boards).

`emit_lapcert.py --qh`: the emitter's `--tr` renderer with the pins
extended -- an instruction that fired but has no lap witness is pinned
when its last fire (200K-step scan) is before the boot, a DeriveError
otherwise -- a boot lemma on the original machine, the witness lemma,
and the QH closer; boards are `Machines/CountersTr/LAPQ_<ID>.v`.
`gen_provtr_lapqh.py --start N` collects them into `ProvTr_QH_NN`
stages for `provqh_tr` and lists the boards in `_CoqProject`.

Measured on 200 rows sampled from the 2,470 in-walk log-extent QH rows
(derive + render, no compile): **159 derived (80%)**; the rest: no
anchor 24, no interior chain 10, nested overflow route 7 -- the same
residue shapes as the LIVE counters (§7.1v), where the route caught
51%.  Two boards emitted and kernel-checked here.  The bulk emit is a
box job: `tools/censustr/qh_lap_emit.sh` over
`censustr_qh_log_rows.txt` (3,745 rows, 16 shards, about an hour),
then stage with `--start 3`, wire `pqh_03..` into `provqh_tr`, and
cut v9.  Expected: ~2,500-3,000 machines, the largest single stage of
the QH side.

### 7.3d The counter emit on the box: 2,502 boards, v9 = 13,783 rows, re-walk CHECKED (2026-09-09)

`tools/censustr/overnight_qh.sh` (PR #145) ran the chain on the box:
`QHConveyorTr.vo` and below, `qh_lap_emit.sh` over the 3,745
log-extent QH rows (16 shards, 55 min), `wire_qh_stages.py`,
`cut_deferred.py v8 v9`, `make census-tr-walk WALK_JOBS=7`.

**Emit: 2,502 of 3,745 rows derived and kernel-checked (67%)**, 13
stages `ProvTr_QH_03..15`, `provqh_tr` = 731 + 2,502 = **3,233**
machines.  The 200-row sample (§7.3c) said 80%; the population is
67%, the same sample-vs-population gap as the LIVE counters (§7.1v).
Per shard 128-207 of 234.  The 1,243 failures by reason:

| reason | rows | route |
|---|---:|---|
| no anchor | 582 | peel / nested lap ports (§7.1v) |
| no overflow chain (nested route is S0-only) | 286 | the S1 nested case |
| no interior chain | 181 | not a lap counter shape |
| no visit witness for state D | 111 | peel port |
| avoid route: only flat exact boards are wired | 52 | wire the avoid route in `--qh` |
| every fired instruction has a lap witness | 23 | **not quasihalters by the lap**: re-run `--tr`, candidates for `prov_tr` |
| tr: route not supported (islack/oslack/nest/peel) | 7 | -- |
| nested: no exit chain | 1 | -- |

The 23 "every fired instruction has a lap witness" rows are the
interesting ones: the emitter's lap contains every instruction the
prefix fired, which is the never-QH shape, while the 10M-step scan
had put them on the QH side (a quiet instruction by last fire).  One
of the two is wrong per row; the lap is a proof and the scan is a
heuristic, so run those 23 through `emit_lapcert.py --tr` and stage
the boards into `prov_tr`.

**The v9 cut**: `proven_specs.py` counts 10,009 proven machines
(6,776 never-QH + 3,233 QH); v8 minus those = **3,243 removed,
13,783 kept** (the 2,502 boards, the 731 cyclers not yet cut from
v8, and the trailing-hole rows §7.3b's regex fix recovered).  The
tables shrank to two shards (`DeferredTr_02` dropped).

**Re-walk**: build phase (13 stages, RunTr, RunTr_Split) 20 min after
`coqnative` on the boards; 96 units in ~2 h 15 min at WALK_JOBS=7
(260-2,113 s each, the shorter list walks faster); assembly
`Census_TheoremTr.v` -- CHECKED.  `Print Assumptions census_tr`:
`FunctionalExtensionality.functional_extensionality_dep` only.

One box-side lesson, now in the script: the emitter compiles boards
with `-native-compiler no`, and a stage compiled natively links
against its boards' native modules, so a board emitted ON the box
(unlike the LAPT boards, emitted in the container and compiled
natively by the box's first build) fails the stage's `coqnative` with
"Unbound module".  `coqnative -Q theories BBB4 board.vo` adds the
module without re-checking the proof; the script runs it over the
boards before the walk.

**Burn-down after v9 (13,783 rows)**, by the §7.1v/§7.3a classes:

* never-QH side (~5,950): bouncers 1,036 (RepWL closures blow up,
  certificate route), counters 2,226 (nested/peel ports), polynomial
  898, state-proven live re-checks 1,782;
* QH side (~4,590 of the 7,827): bouncers 3,288 (the sqrt-extent
  class, same certificate route), the 1,243 counter failures above,
  the 63 cycler laps that did not check, and the 529 late quieters
  (inside the counters and bouncers);
* closeout state-QH boards 592 and partial/provenqh rows 632, both
  awaiting the NGH conveyor.

The largest single class on either side is now the bouncers, 4,324
rows in all, and the counter ports (peel, nested S1, avoid) are the
next 1,000.

### 7.3e The bouncers: the RepWL PARAMETER route (2026-09-18)

**The counter ports are small.**  The state-level lap derive on a
sample of the 1,243 QH counter rows the `--qh` emit did not derive:
56 of 70 have no counter phase at any level (the emitter's cascade
finder sees no counter), 14 derive at state level and need a port
(nested S1 6, avoid 3, unsupported 2, and 3 are never-QH by the lap).
So the ports unlock about a fifth of those rows, not the thousand
§7.3d guessed; the other four fifths are in the bouncers' bucket.
The box's `tr_lap_emit.sh` over the 1,246 rows: **75 LAPT boards**
(never-QH by the lap; the 10M-step scan had put them on the QH side
by a quiet instruction the lap does not contain), `ProvTr_Lap_12`,
unwired until the next cut.

**Populations by behaviour, v9** (`censustr_v9_scan_1e6.txt`, a
1M-step scan with the tape extent at 1e5 and 1e6; extent ratio < 1.8
log, < 5.5 sqrt, else linear): never-QH side 4,240 sqrt / 4,297 log /
230 linear; QH side (a fired instruction quiet since step 1e5) 2,998
sqrt / 2,017 log / 1 linear.  The never-QH sqrt class is 4,240 rows,
not the 1,036 open bouncers of §7.2a: the state-proven live rows and
the polynomial class grow the same way, so the route below runs over
all of them (`censustr_live_sqrt.txt`, `censustr_qh_bouncers.txt`,
tape-period rows from `rw_period_rows.py`).

**The closure was never the problem.**  On 40 sampled open bouncers
the Python mirror of RepWL.v builds a finite closure at one of the
tape-period block lengths for 13 of the first 19, 350-104K nodes,
median 4K, each in under a second.  The in-Coq tier's failure in
§7.2a was its parameters, not the search: at the finder's parameters
(the L, T, t that certify; fuel 8*nodes+64; M = max node size + 8)
Coq's own `rw_tier_tr` re-finds the certificate in 7 s / 30 s / 36 s
on 3K-7K-node closures and 709 s on a 25K one (Python 4-180 s, so
4-10x); a 52K-node search was OOM-killed at 15 GB after 980 s, so
closures past 30K nodes are not handed to Coq.

**The certificate-literal route is dead.**  `rw_check_neverqhtr`
takes the certificate as data, and the finder produces it -- but a
certificate is 23K-370K `(positive, nat)` entries per machine (a rank
component over every node per procedure round, per instruction),
4-10 MB of literals; the kernel check of four of them ran 21 min and
was killed for memory after two.  Storing certificates is out; the
route is **parameters**: `rw_cert_find.py find` (UNTRUSTED, the
Python mirror with the avoid filter moved from states to instructions
as `rw_procedure_tr` does) certifies a machine offline and writes the
row `spec L T t fuel M`; `gen_provtr_rw.py` probe/stage then runs
Coq's tier at exactly that row and stages with `rw_tier_tr_sound` --
the existing parameter-closed stage, no new Coq.  On the QH side the
same with `rw_tier_qhbtr` (pins from the scan's last fires, the
closure and the search on the wrapped machine; stage lemma
`QHConveyorTr.rwqh_stage`), `probe-qh` / `stage-qh` into
`ProvTr_QH_NN`.

**Sample yields (40 rows each).**  Never-QH open bouncers: 14/40
certified (10 "no certificate for one instruction" -- the abstraction
has a cycle avoiding that instruction with net tape growth, the same
instruction-vs-state gap as §7.1w; 8 no closure; 8 timeouts at 300 s);
a wider L/T grid on the misses found nothing in 400 s each, and the
FALLBACK_L ladder below nothing either (0/26: 8 no closure, 18
timeouts) -- the ladder is a QH-side gain.  QH
bouncers: 9/40 with the tape-period rows only, **25/40 with the
FALLBACK_L ladder** (a machine whose period detector said p=2 closes
only at L=3, 6; 14 instant "no closure" became certificates), the 15
left all timeouts.  The kernel accepts the QH rows: `rw_tier_qhbtr`
on the median certificate in 1 s.

**Box job:** `tools/censustr/overnight_rw.sh` -- both finders over
the full lists, Coq's tier at the found rows (12 probe jobs, 1,800 s
cap), stages `ProvTr_RW_11..` and `ProvTr_QH_16..`, wire (QH, Lap,
RW), cut v10, coqnative the box-emitted boards, re-walk.  Expected
from the sample rates: ~1,500 never-QH and ~1,800 QH rows.

### 7.3f The bouncer run on the box, and the residue at 1e8 steps (2026-09-22)

**Five WSL deaths in a day, none of them the census.**  The box's
first `overnight_rw.sh` run (2026-09-21) lost the VM five times:
clean teardowns and wedges with the WSL service itself hung, no
Hyper-V or memory event on the Windows side, C: low.  The 10 s memory
trace inside the VM (`census_probes/memlog.txt`) and `top` settled
it: a finder worker on a row that times out grows a closure toward
the mirror's own 400K-node cap and sits at ~4 GB for its whole 300 s,
and eight of them are the 32 GB VM; with the WSL swap image and the
pagefile sharing a nearly full C:, the VM stalls.  Fixes: the finder
stops a closure at `MAX_NODES` = 30K (nothing past it is usable by
Coq's tier anyway) and caps each worker's address space (`--mem-gb`,
default 2; a 29,644-node closure fits in 0.6 GB); `.wslconfig`
`swap=0`, the VHD sparse; 12 small workers instead of 14 large ones.

**First pass, 1,031 open bouncers: 348 certified.**  Failures: 270
timeouts, 12 closures past 30K nodes, 401 no closure / no certificate.
The cap changes the timeouts: a row that used to burn its 300 s on a
huge L=2 or L=4 closure now moves on to L=6 and closes small -- three
of the last pass's timeouts certify in 2-6 s.  **Retry pass over the
282 resource failures: 154 certified**, so **502 of 1,031 (49 %)**
have finder rows; Coq's tier confirms them in phase 3 (numbers in
§7.3g).  Residue after both passes: 44 timeouts at 300 s under the
cap, 251 no closure, 234 no certificate for one instruction.

**The residue at 1e8 steps.**  `censustr_v9_scan_1e8.txt` is the
1e6 scan re-run for 1e8 steps over the whole v9 list (`trcensus.c`,
2^26-cell tape; 22 linear machines run off it and are marked EDGE).
Per machine the earliest last fire among its fired instructions:
*dense* if within the last 10 % of the run, *sparse* if quiet for
10-90 % of it, *quiet* if silent for 90 %+.  A 110-row sample of the
open bouncers, judged by the capped finder and crossed with the scan:

| finder verdict | dense | sparse |
|---|---|---|
| certified | 47 | 0 |
| no closure | 28 | 2 |
| no certificate for one instruction | 2 | 21 |
| timeout (120 s) | 0 | 10 |

The two residue classes are two different machines:

* **Sparse hybrids** -- every "no certificate" and every timeout.  An
  instruction fires in bursts at geometric intervals (x4, x16, x64,
  x256 between bursts across the machines looked at) and is quiet for
  tens of millions of steps between them; in 16 of the 23 no-cert
  rows the blamed instruction is the quietest one.  RepWL forgets the
  counter that ends each quiet phase, so the tg-avoiding graph has a
  genuine cycle at every block length: not a tuning gap, a checker
  gap (a bouncer with a phase counter needs the lap/counter machinery
  composed with the bouncer abstraction).  Population: 260 of the
  1,031 open bouncers, **1,869 of the 4,240 sqrt-extent LIVE rows**
  (the state-proven live rows are half hybrids), 109 of the 1,246 QH
  counter rows (their pinned instruction fires again by 1e8: they are
  on the wrong side), 4,200 of the 8,767 LIVE deferred rows (the log
  class counts as sparse too: a carry that fires at 2^k is quiet for
  a third of 1e8).
* **Dense no-closure** -- tapes with two or three periods at once
  (one machine: blocks of period 5, 8 and a growing period-3 junk
  region) or a slowly growing counter-like cap.  A single block
  length collapses one period; a common multiple (60, 120) does not
  help because RepWL keeps up to 3L symbols verbatim around the head
  and the state space explodes there first.  The FALLBACK_L ladder
  does recover the ones whose period the detector missed: **5 of 28**
  certify at L=3 or 6 in 3-22 s (the tape-period rows had offered
  L=2, 4).  The ladder is back on the never-QH side (a miss costs a
  second under the cap; it was disabled when a miss cost 300 s), and
  `RETRY=2` re-judges the earlier passes' no-closure rows with it:
  worth about a fifth of them, ~50 machines.

**No hidden QH machines on the LIVE side; 14 hybrids on the QH
side.**  Of the 8,767 machines the 1e6 scan called LIVE, none has an
instruction dead at 1e8: 4,545 dense, 4,200 sparse, 21 EDGE, and 15
in one family whose quiet instruction last fires near 7.95M steps and
again near 127.3M (x16 phases; confirmed at 1e9 for all 15).  The
5,001 SUSPECT rows stay quiet (last fire < 1e6) -- the QH pins hold
-- except **14 of the 2,998 QH bouncers, whose pinned instruction
fires again** between 12M and 37M steps (`--qh` fails them soundly,
`wrap_pin_ok` cannot hold; they belong with the hybrids), and the 1
SUSPECT EDGE row, the linear QH machine.  The next QH run should pin
from the 1e8 scan (`--scan censustr_v9_scan_1e8.txt`: horizon 1e8,
pins = last fire < 1e7), which drops those 14 for free.

**Burn-down.**  The finder has taken most of what single-block RepWL
can take from the open bouncers: 502 rows plus ~50 from the ladder
pass.  The other half of the class is structural: ~1,900 sparse
hybrids across the sqrt class (a new checker), ~200 multi-period
dense rows (a multi-block abstraction, or a per-machine word list),
44 heavy rows (a 900 s pass).  The QH side's 2,998 bouncers run in
phase 4 of the same box job with the capped finder and the ladder.

### 7.3g v10: the bouncer run cut and walked (2026-09-24)

The box job's phases 2-5 finished: every machine the finder judged was
re-searched and confirmed by Coq's own tier, staged, wired, cut into
the v10 tables and walked.

| | v9 | v10 | new stages |
|---|---:|---:|---|
| `prov_tr` (never-QH) | 6,776 | 7,353 | `ProvTr_RW_11..16` (502 RepWL bouncers), `ProvTr_Lap_12` (75 `LAPT_*` counters) |
| `provqh_tr` (QH) | 3,233 | 5,534 | `ProvTr_QH_16..39` (2,301 wrapped-RepWL bouncers, `rwqh_stage`) |
| deferred (`DeferredTr_*`) | 13,783 | **10,924** | 2,859 rows cut, none added |

2,878 machines were staged in all; 2,859 of them were on the v9
list, so the cut removed 2,859 rows (20.7%).  `proven_specs.py`
counts 12,887 proven machines, which matches 7,353 + 5,534.

* **Never-QH RepWL**: 502 of the 1,031 open bouncers: 348 in the
  first pass plus 154 from `RETRY=1` over its timeouts (§7.3f).  The
  stage files are balanced by fuel (`gen_provtr_rw.py stage`, 40
  machines a file at most) so the prerequisite build's long pole is
  not one file.
* **QH wrapped RepWL**: 2,301 of the 2,998 quiet-instruction bouncers
  (77%), pinned from the 1e6 scan.  The 14 bouncers whose pin fails
  at 1e8 (§7.3f) are among the 697 that failed, as expected.
* **Walk**: 96/96 units, `census_tr : forall tm, QHBoundTr B_tr tm
  \/ Deferred D_tr tm` CHECKED.  `Print Assumptions census_tr` prints
  `functional_extensionality_dep` and nothing else.  The first try ran
  7 units at once and the kernel OOM-killed one (anon-rss 5.8 GB,
  `swap=0`); the rerun at `WALK_JOBS=5` (~29 GB peak), which only
  rebuilt the killed unit, went through.  5 is now the driver's
  default.

**What v10 leaves**, by the §7.3f classes.  These are approximate:
the 1e8 scan ran over v9, the classes overlap at the edges, and they
do not sum exactly to 10,924.

| Class | Rows | Route |
|---|---:|---|
| Sparse hybrids (a rare instruction in geometric bursts) | ~4,200 | a counter-aware recurrence checker (new) |
| Dense log counters | ~2,000 | the n-gram parameter route at window 4-6 (§7.1y) |
| QH counter rows | ~2,000 | diagnosis first: 56 of 70 sampled show no counter phase |
| Bouncer residue (529 never-QH + 697 QH finder failures) | 1,226 | `RETRY=2` with the ladder, a 900 s pass, QH re-pin from the 1e8 scan |
| Linear and the rest | ~250 | not looked at |

### 7.4 The census is frozen; the closeout takes over (2026-09-24)

Each cut so far meant a re-walk: every proven batch went into `RunTr.v`,
which rebuilt all 96 walk units (hours, the box, a memory budget) for
every few hundred rows.  From v10 on, the census stays as it is, and
the 10,924 deferred rows are settled outside it, the way the state-level
proof settled its 5,156 (`theories/Closeout/`).  The workflow is in
`docs/CLOSEOUT_TR.md`.

* **The kit is simpler than the state-level one.**  At instruction
  level, never-QH implies `QHBoundTr` at every bound, and `QHBoundTr`
  already moves across completion, swap and mirror (`TNF_QHTr`).  So
  the boarded predicate is just `QHBoundTr B_close`, the census's own
  left disjunct, and no new transport lemma was needed.
  `CloseoutKitTr.deferred_split_tr` is the state kit's `deferred_split`
  with that one change.
* **Membership had to get fast.**  The state kit's `row_inb` is a
  linear scan.  10,924 x 10,924 of those took 9 minutes of `vm_compute`,
  mostly because the map was rebuilt per row inside the `forallb`
  lambda.  Rows now go into a `PositiveMap` keyed by a base-17 reading
  of the row, built once under a `let`, and every hit is re-compared
  with `row_eqb`.  The whole `CloseoutTr.v` compiles in 1.6 s.
  Soundness needs no injectivity proof: a collision can only fail the
  check.  (Base 16 collided, since slot codes run 0..16, and the check
  duly failed.)
* **The first batch.**  The RepWL finder with the block-length ladder,
  run on the first 80 remaining rows at 20 s each (the container, 4
  jobs), certified 17, and `CBT_RW_00` boards them (3 s to compile).
  By class: DN 11 of 20, ED 6 of 9, QH 0 of 44, SP 0 of 7.  A random
  40 of the QH class through the `--qh` finder (pins from the 1e8
  scan): 1 certifies (`CBT_QH_00`), 27 have no closure, 12 time out.
  The QH class is counters, not bouncers.
* **Correction: the dense class is not the cheap half.**  The DN 11 of
  20 above came from the head of the list: small machines with
  undefined transitions, which the census orders first.  A random 40
  of the 4,022 remaining DN rows at 60 s: **3 certify**, 30 have no
  closure, 7 time out (the container, 2026-09-24).  The box's full DN +
  ED run agrees: 3 of the first 238.  RepWL takes about 7% of the class,
  ~300 rows.  The rest of DN is for the n-gram route (window 4-6) and
  whatever comes after it.
* **Classes** (`closeouttr_classes.tsv`, by the quietest instruction's
  last fire at 1e8): DN 4,033 dense, SP 4,154 sparse, QH 2,715 quiet,
  ED 22 edge.

### 7.4.NG The dense rows RepWL misses: the n-gram rank tier at window 4-6 (2026-09-24)

Class DN, batch tag `NG`.  The route is §7.1y's finding put to work:
[DecideTr.rank_tier_tr tm n t 200000 512] (grow the gram sets, explore
the closure, search a per-instruction rank/lex certificate, check it with
the verified lex checker) at windows the census ladder never used for
the never side (`rank_rungs_tr` stops at n = 3).  The driver is Coq
itself: `tools/closeouttr/ng_batch.py probe` compiles one
`Eval vm_compute in rank_tier_tr (row_to_tm ROW) n t 200000 512.` per
(row, rung) under a timeout, so a probe verdict is exactly what the
batch's `vm_cast_no_check` gets.  No finder, no certificate literal:
`ng_batch.py batch` writes `apply coversTr_nqh, (rank_tier_tr_sound _ n t
200000 512). vm_cast_no_check (eq_refl true).` per row.

**Yield on the sample** (`classes.py shard DN 0 40`, 100 rows; every
rung run on every row, 300 s cap, 2 jobs in the container; times are
coqc wall time including ~0.8 s of library loading):

| rung (n, t) | checker | true | false | timeout | median s (true) | median s (all) | max s |
|---|---|---:|---:|---:|---:|---:|---:|
| (4, 0) | rank | 20 | 80 | 0 | 0.9 | 1.1 | 20 |
| (5, 0) | rank | 25 | 75 | 0 | 1.0 | 1.6 | 129 |
| (6, 0) | rank | 29 | 67 | 4 | 1.7 | 3.5 | 300 (cap) |
| (7, 0) | rank | 30 | 55 | 15 | 2.3 | 6.8 | 300 (cap) |
| (4, 64), (4, 1024), (5, 64) | rank | 20, 20, 25 | | | | | |
| (4, 0), (5, 0), (6, 0) | plain `ngram_check_neverqhtr` | 1, 1, 1 | | | 0.6-0.9 | 1.0-1.2 | |

* **The window is the knob, the prefix is not.**  t = 64 and t = 1024
  accept exactly what t = 0 accepts.  The windows nest: every row (4, 0)
  takes, (5, 0) takes, and (6, 0) takes all 29 (first accepting window:
  4 for 20 rows, 5 for 5, 6 for 4).  Window 7 takes 3 more (3 of the
  71 window-6 rejections), 32 of 100 in all, at 15 timeouts.
* **The plain checker is not the route.**  Without the lex certificate
  the closure's instruction-avoiding subgraphs are cyclic on counters:
  1 row of 100 at each of windows 4, 5 and 6 (the same row).
* **Against RepWL.**  The RepWL finder (`rw_cert_find.py find --jobs 2
  --timeout 60`) certifies 12 of the 100.  Of the 88 it fails, the rank
  tier takes 25 (18 at window 4, 21 at 5, 25 at 6); of RepWL's 12 it
  takes 4.  Together: 38 of 100, RepWL alone 8, rank alone 26, both 4.
  So the two routes are nearly disjoint: RepWL takes the bouncers, the
  rank tier the log counters.
* **Cost.**  The ladder (4, 0) -> (5, 0) -> (6, 0) stopping at the first
  true costs ~40 s per row on average, dominated by window-6 failures
  (17 of 100 rows over 60 s at window 6, 4 at the 300 s cap).  The
  slowest accepted window-6 row took 180 s.  `CBT_NG_00` (30 rows, each
  at its cheapest accepting rung) compiles in 60 s.
* **Boarded.**  `CBT_NG_00`: the 30 sample rows (29 at windows 4-6, 1
  at window 7); 4 of them RepWL also certifies, so the box's `RW` batches
  may carry duplicates of those four (harmless, §CLOSEOUT_TR).

**The rest of the class, probed ahead of the box** (the other 3,922 DN
rows, the ladder stopping at the first true, 300 s cap, 2 then 4 jobs;
results committed as `tools/closeouttr/ng_probe_dn.tsv`, the sample's as
`ng_probe_dn_sample.tsv`, both readable by `ng_batch.py batch`):

| rung | run | true | false | timeout |
|---|---:|---:|---:|---:|
| (4, 0) | 3,922 | 641 (16.3%) | 3,281 | 0 |
| (5, 0) | 3,281 | 202 | 3,057 | 22 |
| (6, 0) | 3,079 | 126 | 2,662 | 291 |

So the ladder takes **969 of 3,922 (24.7%)**, against the sample's 29%:
windows 4-5 take 843 (21.5%), window 6 adds 126 (4% of what window 5
rejected, against 4 of 75 on the sample).  Cost: window 4 ~1 h at 2
jobs, window 5 ~5 h, window 6 43 CPU-hours (~11 h at 4 jobs), 24 of
them in its 291 timeouts at the 300 s cap.  With the sample, class DN
has 999 rows the rank tier certifies (969 + the 30 of `CBT_NG_00`).
**Boarded (PR #148, merged after the box's `RW` batches):** of the 1,001
DN rows the rank tier certifies at any window (969 + the sample's 32),
921 are in `CBT_NG_00..18` and the other 80 were boarded first by the
box's `RW` batches, so the RepWL / rank-tier overlap on the whole class
is 80 rows (8% of the rank tier's take).  No certified row is left in
`closeouttr_remaining.txt`; class DN stands at 1,114 boarded, 2,919
remaining.

**Dry run of the boarding.**  `ng_batch.py batch` over the two TSVs
writes 20 batches of 50 (971 rows: the 969, plus the 2 sample rows that
only window 7 takes and that `CBT_NG_00` predates); every row
kernel-checks (1,224 s wall at `-j4`, ~4 core-minutes per 50-row
batch), and the split `CloseoutTr.vo` over them
compiles in 10 s.  The committed batches were regenerated after the
`RW` merge, which dropped the rows RepWL boards first.

**Next lever: window 7.**  On the sample it takes 3 of the 71 rows
window 6 rejects; on the full class's ~2,950 window-6 rejections that is
of the order of 100 rows, at a window-6-like bill (tens of CPU-hours,
mostly timeouts).

A note for anyone running a long probe in the container: a detached
(`nohup`/`setsid`) probe dies when the idle container is reclaimed; run
it as a tracked background task.  The probe resumes from its JSON.

Where the route stands: every DN row has been through windows 4-6, so
the 2,919 remaining DN rows are rank-tier failures at those windows
(plus the RepWL finder's).  Window 7 (above) is the only untried rung
on this route.

### 7.4.SP Class SP: the rare instruction is an overflow, and two landed checkers already prove it recurs (2026-09-24)

**The class, measured.**  Over all 4,154 SP rows (the 1e8 scan), the
rarest instruction fires a median of 23 times in 1e8 steps: 1,354 rows
at most 16 times, 3,086 at most 32, 3,314 at most 1,000; the rest
(840) fire thousands to 8.4M times, in bursts.  A 50-row sample
(`sp_char.py sample 50 4154`, then `sp_char.py char` with
`sp_burst.c`, every fire of the rarest instruction over 1e8 steps):

| measurement | rows of 50 |
|---|---:|
| visited extent at 1e8 under 200 cells (log: counters) | 32 |
| visited extent at 1e8 of 8K-25K cells (doubling bouncers) | 18 |
| every fire of the rare instruction at the visited extent's edge | 35 |
| some fires at the edge | 12 |
| no fire at the edge | 3 |
| one fire per burst (the other 10: bursts that double too) | 40 |
| burst period ratio 2 | 25 |
| burst period ratio 4 | 20 |
| ratio 2.25 / 1.41 / 9 / other | 2 / 1 / 1 / 1 |

Two machines, then, and in both the rare instruction is the one that
ends a phase by growing the tape:

* **binary counters** (ratio 2, log extent), the rare instruction is
  the overflow.  `0RB1LC_1LA1RB_0LA1LD_0RB0LA`, C0, at each fire:
  `[C0]10110110...110111`; between fires the digits read `110` = 0 and
  `111` = 1 and count up to all-`111`, one digit more per overflow, the fires at 6, 29, 80, 187, ..., 229,289: the
  period doubles and nothing else fires C0.
* **doubling bouncers** (ratio 4, width doubling).
  `1RB1LA_0LA1RC_1LA0RD_1RB1RD`, C0, at each fire: `1^w [C0]` with
  w = 2, 6, 14, 30, 62, ... (w' = 2w + 2); between fires a single 0
  marker walks across the block, one cell per sweep, and the phase ends
  when it reaches the edge.  RepWL abstracts the marker's distance to
  `1^{>=k}` and so has a genuine C0-avoiding cycle at every block length
  (the "no certificate for one instruction" of §7.3f).

**The existing inductive checkers already prove these.**  The rare
instruction needs an argument over an unbounded parameter (the width,
or the marker's distance), and the repo has three landed checkers that
make one and conclude `NeverQuasiHaltsTr`:

* `Checkers/IRules/MetaBlkPfxTr.v` (`irulesblkpfx_check_neverqhtr_sound`):
  BBB's `bin/irules` certificates, rules with symbolic counts applied a
  symbolic number of times, and an affine meta map C(k) ->* C(a k + b)
  from an anchor C(k0) the concrete prefix reaches;
* `Counters/LapGlueTr.v` (`glue_neverqhtr`): the lap certificates of
  `emit_lapcert.py --tr` (digit-alphabet counters, `LAPT_*` boards);
* `Checkers/TCyclerTr.v`: translated cyclers (none in the sample).

The soundness argument that makes the rare instruction recur is the same
in the first two, and it is the one the state level used: an anchor
sequence C(k0), C(f(k0)), ... that the machine visits in order (one
induction, proved once for every k), and a fired set F of the symbolic
segment between two anchors.  Every instruction in F fires between any
anchor and the next, so it fires after every N.  The anchor sits at the
phase boundary -- the irules meta cycle is a whole burst period, the lap
certificate's overflow branch is the carry into a new digit -- so the
rare instruction is in F by construction: in `MetaBlkPfxTr` because the
symbolic replay of the meta cycle fires it, in `LapGlueTr` through
`fire_via_ovf` (every anchor reaches an overflow, and the overflow chain
has a prefix ending on the instruction).  The instruction-level gate is
what the state level did not need: `MetaBlkPfxTr` checks that every
instruction fired in the concrete prefix is in F (the `tvis` mask), and
`LapGlueTr` runs the laps on the machine wrapped at the never-fired
instructions, so an instruction outside F cannot fire at all.

So for these rows SP was a conveyor gap, not a checker gap.  Nobody had
run `bin/irules` over SP (the one irules sweep of the LIVE side was a
500-row sample, 23 SP rows among its certificates), and the lap emitter
never saw 2,421 of the 4,154 SP rows (it ran over the v6 log-extent
list; the other 1,733 it saw all failed, 1,325 of them "no anchor").

**Yields on the 50-row sample:**

| route | derived | kernel-accepted | shape |
|---|---:|---:|---|
| `bin/irules --max-steps 1000000` | 12 | 10 | 12 of the 18 doubling bouncers |
| `bin/irules --max-steps 200000` | 11 | 9 (1 false, 1 timeout) | the same rows minus one |
| `emit_lapcert.py --tr` (derive) | 7 | not yet compiled | 7 of the 32 counters, all from the 2,421 never-seen rows (7 of 26) |
| both (disjoint) | 19 | | |
| neither | 31 | | 25 counters ("no anchor" 18, "no overflow chain: nested route is S0-only" 7), 6 bouncers |

A rejected irules certificate can run its full fuel in the kernel
(470 s measured, against under 1 s for an accepted one), so the probe
runs one `coqc` per certificate under a timeout, and a batch only ever
holds accepted ones.

**The irules route over the whole class: 1,266 rows, `CBT_SP_00..03`,
`05..26`.**  `bin/irules --max-steps 200000` over all 4,154 SP rows
(the container, four jobs, about 2.5 h): **1,339 certificates (32%)**,
of which the probe accepts **1,266** (9 false, 64 timeouts at 30 s).
`sp_batch.py batch` stores the certificate literal in the row's proof (a
few hundred bytes; the RepWL route could not, §7.3e) and closes it with
`irulesblkpfx_check_neverqhtr_sound`; 50 rows compile in about 7 s, the
27 batch files in under two minutes on two cores.  The first four
batches (173 rows) came from the first 559 rows, the other 22 (1,093)
from the rest.  The 64 timeouts are not cheap rows after all: re-probed at 300 s,
28 say false and 36 time out again, none accept.

**The lap route over the never-seen rows: 637 rows, `CBT_SP_27..39`.**
`emit_lapcert.py --tr` over the 1,314 SP rows it had never seen and
irules does not take (three jobs, ~50 min derive): of the first 1,132,
**545 derive** (48%, against 7 of 26 in the sample; failures: no anchor
299, "no overflow chain (nested route is S0-only)" 132, nested with no
overflow phase 10, no interior chain 9, no visit witness 8, ...).
`--emit` then writes and compiles one `Machines/CountersTr/LAPT_*` board
per row: **541 compile** (3 more stop at the nested-overflow route, 1 was
a missing alphabet library).  A board compiles in about a second;
`sp_lap_batch.py` lists them in `_CoqProject` and batches them with
`coversTr_nqh_at` on the board's `nqhtr_*`.  The last 182 rows: 96 more
boards (`CBT_SP_38..39`), so **637 lap rows** in all.  One row,
`1RB0RD_1LB1LC_1RC0RA_0LB1RD`, drives the emitter to 14 GB and the
container's OOM killer; it is skipped (run the emitter under `ulimit -v`).

**The residue is counters, and the third checker is the ladder's
transition-level twin: `Checkers/LadderCheckTr.v` (built).**  The 25
sampled counters neither route takes are clean binary counters (the
`110`/`111` machine above is one) whose digit words the lap emitter does
not anchor.  The repo's alphabet-free counter checker is the state
level's value-family ladder (`Checkers/LadderCheck.v`, the `LDR_*`
boards, `tools/ladder/valfam.py`): the digits, the fill law and the arms
are data, so a new alphabet costs nothing.  It concludes
`NeverQuasiHaltsSt`, and its visit premise already had the right shape:
a prefix of the FILL arm (the overflow) ending on the state, at every
counter top, and the tops are cofinal (`tops_cofinal_at`, a theorem, not
a measurement).  The port is the one `LapGlueTr` made of `LapGlue`:

1. `glue_neverqhtrN`: `LadderCheck.glue_neverqhN` on `tm_wrap_trs tm pins`
   (pins = the instructions the machine never fires), with the premise
   "for every unpinned instruction t and every N, some anchor past N
   reaches a configuration whose instruction is t".  Laps chaining forever
   on the wrapped machine say it never halts, `WrapTr.wrap_trs_agree` then
   says its run is `tm`'s and no pin fires, so every instruction that
   fires is unpinned and recurs.
2. `board_fire`: `LadderCheck.board_visit` with `LapGlueTr.srun_instr` /
   `fire_of_run_instr` in place of `srun_st` / `vis_of_run`: the prefix
   chain's end configuration has a concrete (state, head symbol) for every
   width and every tail.  The fill arm is the overflow, so this is where
   the rare instruction is witnessed.
3. `boardph_neverqhtr`: `boardph_neverqh` with (1) and (2); every arm
   hypothesis is stated on the wrapped machine, so the `LDR_*` board body
   is reused verbatim once `tm` is re-pointed (the `LAPT` trick).

`LadderCheck.v` is not touched (it is in the state census's closure); the
twin calls only lemmas it exports (`tops_cof_pv`, `board_lap`,
`iter_total`, `cells_top`, `cden_cls_conf`, ...).  It compiled first try,
axioms `functional_extensionality_dep` only.  `emit_ladder.py --tr` emits
`Machines/LadderTr/LDRT_*` boards: pins from a 10^6-step run (a wrong pin
only halts the wrapped machine and fails the board), visit chains keyed
by (state, head symbol), the `boardph_neverqhtr` closer; the default mode
is byte-identical to before.  `sp_ladder_batch.py` emits, compiles and
batches them (`coversTr_nqh_at` against the board's own `tm`).

Measured on the 31 residue rows (`valfam.py --cap 150`): **15 close**
(the finder), 16 do not ("families found but none closed" 12, "no value
family" 4).  Of the 15, **6 board** (`CBT_SP_04`, about 1 s a board);
the other 9 stop in the emitter's closure, 8 of them for reasons the state
level shares ("interior arm: no chain ... the carry ripple is not affine
in the run length" 7, a fill arm with no chain 1) plus one family whose
fill widens by 1 but names 3 digits.  One is instruction-specific: no
phase's fill anchors reach every instruction (D0 or B0 missing in each);
an interior-arm witness would close it, and is the obvious next piece.
Sample tally, all three routes: irules 10 + lap 7 (derived) + ladder 6 =
23 of 50.  The finder costs about a minute a row, so the ladder pass over
the class residue (after irules and lap, ~2,700 rows) is a box job.

**Loop** (container; `bin/irules` from the BBB repo, `make bin/irules`):

```
python3 tools/closeouttr/classes.py shard SP 0 1 > sp_rows.txt
bin/irules --max-steps 200000 --cert-dir certs sp_rows.txt > sp_irules.csv
python3 tools/closeouttr/sp_batch.py probe certs probe.tsv --jobs 4 --timeout 30
python3 tools/closeouttr/sp_batch.py batch probe.tsv --tag SP
# the ladder route, on what irules and lap leave
(cd tools/ladder && python3 valfam.py --list ../../rest.txt --cap 150 --json ../../vf.jsonl)
python3 tools/closeouttr/sp_ladder_batch.py vf.jsonl --tag SP
```

#### 7.4.QC Class QH diagnosed: counters, sweep counters, hybrids (2026-09-24)

Workstream QC (batch tag `QC`), over the 2,714 open QH rows (2,715 minus
the one in `CBT_QH_00`).  Per-row results are in
`closeouttr_qc_subclasses.tsv`.

**Diagnosis.**  Every row was run for 1e8 steps (a scratch C simulator:
the tape extent at 10^k steps and the step of every new leftmost and
rightmost cell).  The growth exponent of the extent between 1e6 and 1e8
splits the class cleanly, with nothing between the peaks:

| sub-class | rows | growth | what it is |
|---|---:|---|---|
| exponential counters, never given to the lap emitter | 1,405 | ~0.05 (log) | binary-style counters; a new cell every 1-4 doublings of time.  The v8/v9 log list (`censustr_qh_log_rows.txt`) was classified at 1e6 over the in-walk rows, and these came from elsewhere, so the emit never saw them |
| exponential counters the box's `--qh` emit failed | 605 | ~0.05 | in `censustr_qh_counter_fail_rows.txt` |
| **sweep counters** (quadratic laps) | 485 | 1/3 exactly | a block `1^n` with one travelling hole; each hole step is one full sweep, and the block grows by a cell when the hole reaches the end.  Lap n costs ~n^2 steps, so the extent is ~t^(1/3).  481 of them are in the box's counter-fail list: they are most of §7.3e's "56 of 70 have no counter phase" |
| bouncer hybrids | 198 | ~0.5 | a sqrt-extent bouncer with an instruction in geometric bursts (one looked at: A1/B0 fire near 16.2M, then 145.4M, x9); the §7.3f sparse hybrids |
| dense bouncers | 15 | ~0.5 | never given to RepWL |
| in-place cyclers | 6 | 0 | e.g. `0RB---_0LC---_0RB---_------`: period 2, from step 1 |

A random 100 (seed 20260924): 72 counters (42 never-tried rows that
derive, 5 never-tried that fail, 25 box-fail rows that fail), 18 sweep
counters, 9 hybrids, 1 cycler.  In the 1e8 scan, 2,253 rows have one quiet
instruction (almost always A0 at step 0-7), 207 have two and 254 have
three; 909 also have a live instruction that is sparse at 1e8 (the
hybrids, and counters whose overflow instruction fires once per
doubling).  90% of rows are quiet by step 7; the latest quiet last fire
in the class is 7,972,431, a quarter of `B_close`.

**Routes tried, with yields.**

* **Lap certificates** (`emit_lapcert.py --qh`, `LapGlueQHTr`,
  `lap_qh_stage`) on the 1,405 never-tried counters: **1,276 derive
  (90.8%)**; 66 have no overflow chain (the nested route is S0-only), 51
  no interior chain, 12 no anchor.  All 1,276 kernel-check.  On the
  box-fail rows the sample confirms the box: 0 of 25 derive.
* **Quiet-instruction cyclers** (`TCyclerQHTr`): `tc_find.py` skips
  in-place laps (d = 0) as "the cycle checker's business", but
  `tcycler_check_qhboundtr` takes them unchanged (`gmatch` compares the
  exact right half-tape).  6 of 6 check.
* **Wrapped RepWL** with L=1 added in front of the ladder (the finder's
  `FALLBACK_L` starts at 2), 30 s: **0 of 80** sampled rows (61 counters
  with no closure; 10 sweep counters time out, 2 have no closure, 2 have
  no certificate; 5 hybrids time out).  On a sweep counter L=1 closes at
  97 nodes, but B0 (the grow step) gets no certificate.  The hole-transit
  loop avoids B0 and has no head-relative measure that decreases: the
  quantity that decreases is the hole's distance to the block's end.  The
  real `--qh` finder at 120 s on the 15 dense bouncers: 0 of 15 (all
  timeouts).
* **Wrapped n-gram** (`qh_plain_at`, n in {2,3,4}, t = last quiet fire
  + {1, 65, 1025}): 0 of 12 (4 sweep counters, 4 box-fail counters, 4
  hybrids).

**Boarded: 1,282 rows**, `CBT_QC_00` (the 6 cyclers) and `CBT_QC_01..32`
(the 1,276 counters, 40 per file).  Class QH: 2,714 open to **1,432**.
The boards go inside the batch file, one `Module` each
(`tools/closeouttr/qc_batch.py lap`).  The board's BBB4 imports become a
top-level `Require` and an `Import` local to its module, and the row
lemma is `coversTr_qh3_at` at the board's machine with an 8-way case
split.  Nothing is added under `theories/Machines`, and no `_CoqProject`
line depends on the shared files (a regenerate on a merge conflict would
drop one).

One cost trap: the closer's last goal `(t0 <=? 32779478) = true` makes
the VM build the unary 32779478 once per board.  That is 1-2 s per board,
and a 40-board file peaked at 3.3 GB (OOM-killed at -j4).  Each file now
proves `qcleb_<file> : (n <=? 1024) = true -> (n <=? 32779478) = true`
once, and the boards close with `apply qcleb_<file>. reflexivity.` (the
boots are at most 64).  The same file then takes 8 s and 0.9 GB, and all
33 batches plus `CloseoutTr.v` build in 91 s at -j4.

**What is left (1,432), and the route for each:**

| rows | sub-class | route |
|---:|---|---|
| 605 + 129 | counters the lap emitter does not derive | the emitter ports §7.3e already names (nested S1 overflow, peel, avoid).  The largest new bucket is "no overflow chain (nested route is S0-only)" (§7.4.QE: 340 boarded by three emitter ports, 394 left) |
| 485 | sweep counters | **new Coq**: a two-index lap glue.  The anchor `Cc (n, i)` is the block `1^n` with the hole at i; the inner lap `(n, i) -> (n, i+1)` is one sweep, a linear `srun` chain with `SCyc` over the rest of the block; the outer lap `(n, n) -> (n+1, 0)` is the grow step.  Both are `LapDecider` chains already, and the missing piece is the glue that runs the inner lap by induction on the hole's distance (the counter alphabets are positional, so `cview` does not express it).  One shape covers all 485 |
| 198 | bouncer hybrids | the counter-aware recurrence checker of the SP class (same machines, one quiet instruction more) |
| 15 | dense bouncers | a longer `--qh` RepWL pass (900 s) |

#### 7.4.QE The QH counters the lap emitter did not derive: three emitter ports, 340 boarded (2026-09-28)

Workstream QE (batch tag `QE`), over the 734 open rows of §7.4.QC's
`counter_boxfail` (605) and `counter_new` (129) sub-classes.  The 485
`sweep_counter` rows are workstream QS's and were not touched.  Per-row
results: `tools/closeouttr/qe_probe.tsv`.

**Bucketing.**  `emit_lapcert.py --qh` reports only the LAST anchor's
failure, and the last anchor it tries is the mirrored S1-head one, so its
"no overflow chain (nested route is S0-only)" line (§7.3d, §7.4.QC) says
little about why the S0 anchors failed.  `tools/closeouttr/qe_probe.py`
runs the same search (both orientations, both head symbols, every anchor
family) and records every attempt: the derive's reason or, for a derived
certificate, the `--qh` renderer's.  On the first 67 rows the blockers
that mattered were in the TRANSITION-level path, not in the lap search:
26 rows derived a certificate that `render_tr` then refused.  45 rows hit
the S1 refusal, and every one of them also failed at an S0 anchor at the
overflow stage or later.  Hence two ports in the renderer path, and the
S1 port third:

* **the per-STATE visit gate** (`no visit witness for state X`, and `avoid
  route: only flat exact boards are wired`).  `derive` insisted that every
  state fire inside the lap, or that the missing one be closed by
  `glue_qh`, an absorbing set or the avoid route.  At instruction level
  none of that is needed.  `render_tr` drops the state board from `viso_*`
  on and proves per-INSTRUCTION fires; an instruction that fired only
  before the boot is pinned, and the kernel re-runs every chain on the
  machine wrapped at the pins.  A state that the lap never reaches has no
  fired instruction after the boot, so it only adds pins.  In `TR_MODE`
  the gate is now skipped.  State-level behaviour is unchanged.
* **the reindexed routes in `render_tr`** (offset-nested overflow and the
  peeled overflow), which state the overflow branch at `j = S j'` with
  `p = 1` as one concrete lap.  The renderer refused them.  It now
  destructs the outer index in each overflow-side fire bullet and
  discharges `p = 1` with a concrete `firez_<instr>_<ID>` run from `Cc 1`
  (the state board's `visz_*`, per instruction).  Offset nests with an
  instruction that fires only in the exit half are still refused.  After
  the ports no row in this population hits a renderer refusal.  All 18
  reindexed boards are offset nests; the peeled path shares the code but no
  row here exercised it.

The third port is the one §7.3e/§7.4.QC named: **the nested overflow at an
S1 anchor head**.  `nestcert` hard-coded the OUTER anchor's head as blank
in `phase_mid`, `validate`, `derive_offset` and `validate_offset`.  The
outer head is now `NC.OHD`, which the emitter sets to its `HD`.  The Coq
side needed nothing, since the inner anchors keep their literal `S0` and
the outer glue is the flat `@AHD@` template.

**Yields** (probe: 734 rows, 4 jobs, 400 s cap, ~8 s a row; then
`--qh --emit`, every board kernel-checked by the emitter's `coqc`):

| port | rows boarded | from |
|---|---:|---|
| per-state visit gate skipped at instruction level | 320 (11 of them with lift slack) | 319 box-fail, 1 new |
| reindexed (offset-nested) overflow in `render_tr` | 18 | all `counter_new` |
| nested overflow at an S1 head | 1 | box-fail |
| none (flat; a box board already exists, `ProvTr_QH_09`, but the row is still deferred) | 1 | box-fail |
| **total** | **340** | 321 of 605 box-fail, 19 of 129 new |

No derived certificate failed to compile.  Boarded as `CBT_QE_00..08`
(40 boards a file, inline, through `qc_batch.py lap --tag QE`; no new Coq).
Closeout: 4,320 boarded before, **4,660** after, **6,264** remaining.

**The residue (394), by blocker and by growth.**  Growth is the tape
extent's dominant side over 1e8 steps (`log2` of the time ratio per new
cell over the last third of its new cells): 1.00 is a binary counter with
one cell per digit, 0.50 two cells per digit, 0.694 the golden ratio.

| best blocker | rows | growth | what it is |
|---|---:|---|---|
| no interior chain | 74 | 0.694 | **Fibonacci counters** (Zeckendorf-style: x1.618 a cell).  No binary digit alphabet fits.  They need a Fibonacci counter theory (`FIB_ELEVEN` in `tools/counters/` is the state-level precedent) |
| no interior chain | 66 | 1.00 | **binary, parity carry.**  One looked at, `0RB0LB_0RC0LA_1LB1RD_1LA1RC` (mirrored, anchor `C` at head 1, `Kp`): the carry crosses the run of ones alternating two states (`D1 -> 1RC`, `C1 -> 1RD`), so the state that ends the carry depends on the parity of `j`.  No single `srun` chain covers both parities.  The port is a parity split of `cview` (`j = 2i`, `j = 2i+1`, two chains).  That is new Coq glue |
| no interior chain | 28 / 57 | 0.79 / other (0.64, 0.67, 0.72, 0.86, 0.89) | other radices (x1.73 a cell and others) |
| no overflow chain (nested: no exit chain) | 40 | 1.00, **two-sided** | one family (5 cores times the quiet A-transitions): a binary counter that grows one cell per doubling on BOTH ends.  The nested route (S0 and, now, S1) finds the boot but no exit chain |
| no overflow chain (nested: boot / inner family / inner interior) | 55 | 0.50 (30) or 0.47 (25) | two-cell-digit binaries whose overflow phase the nested search cannot split |
| no anchor | 74 | 1/3 (25), 0.50 (29, 5 two-sided), 0.47 two-sided (16), 0.694 (2), 0.47 (2) | no anchor family with a long run of consecutive values |

The two largest pieces of residue (74 Fibonacci, 66 parity carries) are
both new counter shapes, not search gaps.  The parity split is the smaller
Coq change: it reuses every chain and glue lemma per parity.

```
python3 tools/closeouttr/qe_probe.py rows.txt probe.jsonl --jobs 4 --timeout 400
(cd tools/counters && python3 emit_lapcert.py --qh --emit --list ok.txt --json emit.json)
python3 tools/closeouttr/qc_batch.py lap theories/Machines/CountersTr/LAPQ_*.v --tag QE --chunk 40
```

#### 7.4.QS The sweep counters: a two-index lap glue (2026-09-28)

Workstream QS (batch tag `QS`), over the 485 `sweep_counter` rows of
§7.4.QC (`closeouttr_qc_subclasses.tsv`).  All 485 are quasihalting
(their quiet instructions stop by step 133), so the route ends in
`coversTr_qh3`.

**The glue** (`theories/Counters/SweepGlueTr.v`, axiom-free beyond
`functional_extensionality_dep`).  The anchor is
`swC i k = (q, (Lpre ++ uL^i ++ Lpost, h, Rpre ++ uR^k ++ Rpost))`: `i`
units behind the hole, `k` ahead.  The inner lap `(i, k+1) -> (i+1, k)`
never touches the units behind, so they are the chain's OPAQUE left tail
and one `srun` with index `k` covers every `i`.  The outer lap
`(i, 0) -> (e, i + d)` is a chain with index `i` and both tails empty.
The glue proper is the enumeration: `swCf p` is the `p`-th anchor along
`sw_nxt`, which turns the two laps into the single `Hlap` of
`LapGlueQHTr.glue_qhboundtr`.  Per-instruction fires come from chain
prefixes of either lap.  An inner-lap fire is reached from any visited
anchor by growing the block until enough units are ahead (the block grows
by `e + d >= 1` per round).  An outer-lap fire is reached through `k`
inner laps.  A certificate is data (`swcert`), and `sweep_check` is one
boolean under `vm_compute`, so a row is one line:
`apply coversTr_qh3, (sweep_sound _ (mkSW ...))` (`sweep_sound_mirror`
when the hole moves left).  There are no per-machine definitions or
modules, and a 40-row batch compiles in 1.6 s.

Two things the first cut (one unrolled unit, near end) missed:

* **Turning on the block's last unit.**  In ~70 rows the return sweep
  changes state on the far unit of the block ahead (D reads the last 1,
  then A sweeps back).  `SCycL` needs the same state at every unit, and a
  count `k` that may be 0 has no unit to peel, so the inner start unrolls
  `na` units at the near end and `nb` at the far end.  The last
  `na + nb - 1` inner laps become concrete `sw_base` chains.
* **The same on the grow step.**  The outer start unrolls `ma`/`mb` units
  of the block behind.  Instead of concrete short outer chains, an
  invariant: every visited anchor has `i + k >= ma + mb` (`sw_good`,
  checked at the boot and kept by both laps).

**Emitter** (`tools/closeouttr/qs_batch.py find`, untrusted).  It runs
the machine and its mirror for 60,000 steps and pins the instructions
silent over the last two thirds, plus the undefined ones.  For each
instruction and small prefix/unit lengths (unit 1-3, prefix 0-3), it
splits the late configurations as `Lpre uL^i Lpost | h | Rpre uR^k Rpost`
and keeps a split whose `(i, k)` sequence steps as a sweep with constant
`(e, d)`.  It then derives the chains with `lapcert.derive_chain` on the
wrapped table (trying `(na, nb)` and `(ma, mb)` up to 2).  The boot is
the first fitting anchor after the last quiet fire; the latest is step 41.

**Yield: 410 of 485 (84.5%) boarded**, `CBT_QS_00` (the 20-row sample)
and `CBT_QS_01..10`.  All 410 kernel-check (a 40-row file: 1.6 s).
QH open: 1,432 to **1,022**; all rows: 6,604 to **6,194**.

| certificate shape | rows |
|---|---:|
| one unit near end (`na,nb,ma,mb = 1,0,0,0`) | 339 |
| + one at the far end (`1,1,0,0`) | 56 |
| + outer unrolling (`1,1,1,0` / `1,1,1,1`) | 11 / 4 |
| units of 1 / of 2 cells (`uL = uR`) | 314 / 96 |
| hole moves left (certified on the mirror) | 236 |
| grow step `(e, d)`: (0,1) / (1,1) / (1,0) / (0,2) / (1,2) | 178 / 106 / 81 / 32 / 13 |

The search took 37 min for the 485 at 8 jobs on 4 cores (a failing row
tries every candidate split).

**Residue (75), two shapes, both three-index:**

| rows | shape | why the glue misses it |
|---:|---|---|
| 58 | **two converging holes**: `1^a 0 1^b 0 1^c`, `c` in `{a, a+1}`; the holes step inward alternately, the middle block shrinks by one per half-lap, and the block regrows when they meet | no single-hole split fits ("no sweep anchor").  The natural anchor has the SAME count `a` on both outer blocks, so a half-lap is a chain over the middle block with both tails opaque, and the glue would enumerate `(a, b)` with `c` tied to `a` |
| 17 | **travelling gap**: `1^a 0^b 1^c`, a run of blanks that grows as it moves through the block | 15 have no outer chain and 2 no inner chain at any unrolling up to 2; the hole is a run whose length is itself a count |

Both look like the same glue with a third, tied count.  The anchor
would become `L ++ uL^i ++ M ++ uR^k ++ N ++ uL'^i ++ R`, and each lap
would still be a single-index chain between two opaque tails.  That is
the next step for these 75.

#### 7.4.DX Class DN after RepWL and the rank tier: four landed routes take half, bouncer + counter hybrids are the rest (2026-09-28)

Workstream DX (batch tags `DX0`..`DX3`, `DXQ`, `DXS`), over the 2,919
open DN rows plus the 213 `bouncer_hybrid`/`bouncer_dense` QH rows of
§7.4.QC.  The per-row data is under `tools/closeouttr/dx/`.

**Diagnosis.**  `tools/closeouttr/dx_sim.c` + `dx_char.py` run every row
for 1e8 steps.  They record the extent at each power of 10, each end's
growth exponent between 1e6 and 1e8, the record gaps, edge-to-edge
sweeps and the tape's periodic blocks at the end.  The table covers all
3,132 rows (`dx/char_all.tsv`), with a random 100 (seed 20260928) in
`dx_char_sample.tsv`.  The classes separate cleanly by exponent:

| kind | exponent | rows (of 3,132) | sample of 100 | what it is |
|---|---|---:|---:|---|
| counter | ~0.05 (log) | 1,246 | 48 | binary-style counters, the extent under ~120 cells at 1e8 |
| sweep counter | 1/3 | 887 | 21 | a block `1^n` with one travelling hole (§7.4.QC's sweep counters, never-QH side) |
| bouncer + counter hybrid | 1/2 on one end, log on the other | 672 (462 DN + 210 QH) | 22 | a bouncer block, typically `(10)^n`, on one side and a binary counter on the other, with digits such as `00`/`01`.  Each sweep increments the counter once |
| two-sided bouncer | 1/2 both ends | 164 | 5 | multi-period tapes, the RepWL no-closure rows of §7.3f |
| one-sided bouncer | 1/2, other end fixed | 43 | 0 | |
| linear | 1 | 110 | 4 | translated cyclers |
| other | | 10 | 0 | |

**Routes, all existing checkers except one twin:**

| route | tried on | certified | kernel-accepted | boarded |
|---|---|---:|---:|---|
| `tc_find.py --steps 200000 --maxp 20000` -> `TCyclerTr` | all 3,132 | 123 | 109 (the 14 rejects: "periodic" only at the end of the budget, and at 2e6 steps the same) | `CBT_DX0_00..02` |
| `bin/irules --max-steps 200000` -> `MetaBlkPfxTr` | all 3,132 | 940 (761 DN) | 682 (61 false, 18 timeouts at 30 s; none of the timeouts accepts at 300 s) | `CBT_DX1_00..12` (629; the other 53 are also translated cyclers) |
| the same certificates, `claim_qh T` -> **`MetaBlkPfxQHTr` (new)** | the 213 QH bouncers | 179 | 176 (3 time out at 30 s and at 300 s) | `CBT_DXQ_00..03` |
| `emit_lapcert.py --tr --emit` -> `LapGlueTr` | the 1,246 counters | 704 | 704 | `CBT_DX2_00..14` |
| `valfam.py --cap 150` -> `LadderCheckTr` | 40 of the 542 lap failures | 19 closed | 4 boards | `CBT_DX3_00` |
| `bin/irules --max-steps 1000000` | the 465 open sweep counters and bouncers | 75 | 1 (57 false, 17 timeouts) | `CBT_DX1_13` |

* **The sweep counters were an irules conveyor gap.**  `bin/irules` takes
  600 of the 887 (68%).  Its meta cycle `C(k) -> C(a k + b)` with a rule
  applied a symbolic number of times is the hole's inner loop.  The
  never-QH side needed nothing new.
* **The counters were a lap conveyor gap.**  The lap emitter had never
  run on the DN log counters.  It derives 704 of the 1,246 (57%), and all
  704 boards compile (about a second each).  Failures: "no interior
  chain" 273, "no anchor" 237, "no overflow chain (nested route is
  S0-only)" 28, "no visit witness" 4.
* **`MetaBlkPfxQHTr` is the transition-level twin of `MetaBlkPfxQH`.**
  It reuses `MetaBlkPfxTr`'s engine, but where the prefix gate required
  every fired instruction to be in F, it takes a witness instruction
  `tz` that fires at `nz` and is not in F.  The bound is the anchor
  (nothing outside F fires after it), lifted once to `B_close` for
  anchors up to 2^20.  It gives `NonHalt /\ QHBoundTr 32779478 /\
  QuasiHaltsTr`, the `coversTr_qh3` shape; the only axiom is
  `functional_extensionality_dep`.  It takes 176 of the 213 QH bouncers.
  It also takes all 485 of §7.4.QC's QH sweep counters (irules certifies
  485 of 485 in under a minute, and the kernel accepts 485 of 485).  The
  QS workstream's `SweepGlueTr` had already boarded 410 of those, so
  `CBT_DXS_00..01` carry only the other 75, QS's "two converging holes"
  and "travelling gap" residue.  Over the rest of the open QH rows (771)
  irules certifies 3, all of which time out in the kernel.
* **Why irules misses the DN hybrids.**  It takes 176 of the 210 QH
  hybrids and none of the 462 DN ones.  On the DN side, the certificates
  it does emit for the bouncers fail the prefix gate (57 of 75 false at
  1e6): the meta cycle is one sweep, and the counter's carry instruction
  is not in the sweep's fired set F.  On the QH side the carry
  instruction is exactly the quiet one, so the same sweep cycle is a
  valid QH certificate.

Class DN, 2,919 open to **1,472**; the QH bouncers, 213 to **37**; with
`DXS`, QH 1,432 to 1,181.  All rows: 6,604 to 4,906 (alone on `main`;
with QS's 410 on top of it, 4,496).

**What is left (1,509: 1,472 DN + 37 QH), and the route for each:**

| rows | kind | route |
|---:|---|---|
| **496** (462 DN + 34 QH) | **bouncer + counter hybrids** | **new checker: a lap certificate whose tail is a growing bouncer block.**  The anchor is `Cc p = (E, (Enc p ++ w^(a p + b) ++ tail, hd, far))`: `LapGlueTr`'s counter anchor with the block between the counter and the far side.  One lap is one sweep: a `SCyc` chain over `w^n` (the inner loop §7.4.QS's glue already runs over an opaque tail) and one counter increment, whose overflow arm is the carry instruction.  That is `LapGlueTr`'s `fire_via_ovf`, the piece the irules sweep cycle lacks.  The QH side (34) is the same through `LapGlueQHTr`.  The same checker is the likely route for the SP class's sparse hybrids (§7.3f, ~1,900 rows there) |
| 538 | counters the lap emitter does not derive | the ladder takes ~10% (4 of 40; 15 of 19 closed rows stop at "interior arm: no chain ... the carry ripple is not affine", SP's blocker too).  The emitter ports §7.3e names ("no interior chain" 271, "no anchor" 235) |
| 287 | sweep counters irules does not take (261 undecided, 26 false/timeout) | **a never-QH twin of QS's `SweepGlueTr`**: the same two-index glue through `LapGlueTr.glue_neverqhtr` instead of `LapGlueQHTr`; the finder is `qs_batch.py`'s without the pins.  Done in §7.4.SW: the plain twin takes none, a multi-family glue with behind sweeps takes 239 |
| 177 | two-sided (137) and one-sided (40, 3 of them QH) bouncers: irules undecided, false, or (18) timing out in the kernel | RepWL at 900 s, or a multi-block RepWL (§7.3f) |
| 11 | other (8 sqrt rows whose ends fit neither shape, 2 unclassified, 1 linear that is not a cycler) | |

The loop, for the next session:

```
python3 tools/closeouttr/dx_char.py char ROWS dx.tsv --jobs 2          # the kinds (0.5 s a row)
python3 tools/censustr/tc_find.py ROWS --steps 200000 --maxp 20000 > tc.tsv
python3 tools/closeouttr/dx_tc_batch.py probe tc.tsv tcp.tsv && python3 tools/closeouttr/dx_tc_batch.py batch tcp.tsv --tag T
bin/irules --max-steps 200000 --cert-dir certs ROWS > ir.csv         # BBB repo, make bin/irules
python3 tools/closeouttr/sp_batch.py probe certs irp.tsv --timeout 30 && python3 tools/closeouttr/sp_batch.py batch irp.tsv --tag T
python3 tools/closeouttr/dx_irqh_batch.py probe certs ROWS irq.tsv && python3 tools/closeouttr/dx_irqh_batch.py batch irq.tsv --tag T
(cd tools/counters && python3 emit_lapcert.py --list COUNTERS --tr --emit --json lap.json)
python3 tools/closeouttr/sp_lap_batch.py lap.json --tag T
```

The probe TSVs name certificates as `certs/<spec>.cert`; the
certificates are in `dx/irules_certs.tgz`, `dx/ir1m/irules_certs.tgz` and
`dx/qsweep/irules_certs.tgz` (untar next to the TSV).  Cost in the
container: the 2e5 irules search took ~100 min at 2 jobs for 3,132 rows,
the lap derive + emit ~2 h at 3 jobs for 1,246 rows, and the rest took
minutes.

CI: with the QS and DX batches, the `core` job's closeout step runs
32-40 min at `-j4`, and runs were cancelled at the old 45-minute limit.
`timeout-minutes` is now 90.

#### 7.4.BR The plain bouncers: RepWL at 900 s takes a sixth, the rest is not a budget problem (2026-09-29)

Workstream BR (batch tag `BR`), over the §7.4.DX rows RepWL was named
for: the 137 two-sided and 40 one-sided bouncers (3 of them QH) and the
11 "other" rows of `dx/char_all.tsv`, plus the 15 `bouncer_dense` QH rows
of `closeouttr_qc_subclasses.tsv`.  All 203 were still open: 185
never-QH, 18 QH.  Per-row data in `tools/closeouttr/br/`.

| route | tried on | certified | kernel-accepted | boarded |
|---|---:|---:|---:|---|
| `rw_cert_find.py find --timeout 900` (the FALLBACK_L ladder L=2..10,12; MAX_NODES 30K) | 185 never-QH | 33 (L=6..10) | 33 | `CBT_BR_00..06` |
| the same with `--qh --scan censustr_v9_scan_1e8.txt` | 18 QH | 0 (14 no closure at 770-810 s, 4 timeouts) | | |
| RepWL at the rows' own block periods and pairwise LCMs outside the ladder (L=11, 13..40, from `dx/char_all.tsv`), 600 s | the 135 misses with such an L | 4 (L=11, 14, 15, 15) | 4 | `CBT_BR_07..08` |
| `ng_batch.py probe --rungs rk:7:0`, 300 s | all 149 never-QH misses (a random 30 first: 1 of 30) | 4 (73+19 false, 53 timeouts) | 4 | `CBT_BR_09` |

**41 of 203 boarded** (all 185+18 judged); all rows: 4,156 to 4,115 open.

* **The budget was never the limit.**  Of the 152 never-QH misses at
  900 s, 148 are "no closure": every rung of the ladder passes the 30K
  node cap, in 6-30 s for the whole ladder.  Only 4 time out.  The
  certified rows take 10-148 s.  A longer budget buys nothing; raising
  MAX_NODES is not an option either (Coq's tier OOMs past ~30K, §7.3e),
  and the three rows that hit the 2 GB worker cap do not close at 4 GB.
* **Kernel cost.**  Coq re-runs the search at the finder's parameters,
  and the closures here are big (up to 29.7K nodes).  Batch compile times
  in the container, sharing 4 cores with the probes: BR_00 47 min, BR_02
  43, BR_03 38, BR_04 25, BR_08 22, BR_07 12, BR_05 7.5, BR_01 6, BR_09 1.
  The batches are cut at 5 rows (2 for the L=14/15 rows) so the heavy
  rows spread across `-j4`.
* **The rank tier at window 7** takes 4 of 149 (2.7%), a tenth of its
  window 4-6 yield on DN (§7.4.NG).  Window 4-6 had already rejected or
  timed out on 180 of these rows.

**The residue: 162 rows (144 never-QH + 18 QH)**, in
`tools/closeouttr/br/residue.txt`, by the 1e8-step tape shape of
`dx/char_all.tsv`:

| rows | shape at 1e8 | what it says |
|---:|---|---|
| 47 | more than 100 aperiodic ("junk") cells | not a bouncer in RepWL's sense: the tape grows material no block describes.  All 33 finder-certified rows have <= 100 junk cells (31 of them <= 20).  Route: re-characterise (the growth exponent put them with the bouncers, but the junk is counter- or Fibonacci-like); likely the hybrid checker of §7.4.DX, or a per-machine word list |
| 45 | several block periods whose LCM is past 12 (e.g. 5 and 8, 10/12/14/16) | the multi-period tapes of §7.3f.  A single block length at the LCM does not close (4 of 135 above): RepWL keeps up to 3L symbols verbatim around the head and the state space explodes there |
| 25 | several periods, LCM <= 12 | the ladder tried the LCM and failed; the periods are there but the blocks sit in separate growing regions |
| 27 | one period | three or more growing runs of one word (e.g. `0^a 0^b 1^c`, `(01)^a ... (01)^b`); fails like the row above |
| 18 | QH (15 `bouncer_dense` + 3 one-sided) | the wrapped closure grows to the cap slowly (770-810 s per row); irules also missed them (§7.4.DX) |

**Is a multi-block RepWL (§7.3f) worth building?**  Its target is the
97 low-junk never-QH rows (45 + 25 + 27), plus perhaps some of the 18
QH rows: blocks of different lengths per tape region, so that a node
stores the word and its count per region instead of 3L verbatim cells at
L = LCM.  That is a new abstraction in `RepWL.v`'s soundness proof (the
block split is no longer uniform) and a new finder, for at most ~100 rows,
with an unknown hit rate: the single-block evidence says little, since
the LCM rungs that would be its degenerate case fail by node count, not
by a cycle.  Recommendation: **not before** the bouncer + counter hybrid
checker (496 rows, §7.4.DX) and the never-QH sweep glue (287 rows).  If it
is built, a cheaper first step is to measure the node count a two-length
abstraction would reach on the 45 LCM>12 rows with the Python mirror
before touching Coq.

#### 7.4.HY The bouncer + counter hybrids: a counter lap whose far side is a growing block (2026-09-28)

Workstream HY (batch tag `HY`), over the 496 open `sqrt+log` rows of
§7.4.DX (`dx/char_all.tsv`, column `hybrid`): 462 DN and 34 QH.

**Five by hand.**  In `1RB0RA_1LC0RA_1LD0LB_1RB1LD` the tape is a binary
counter at the left end, one cell a digit with the low end next to the
block, and a block beside it: `1101110010 (01)^n 1`.  Each lap the head
comes back over the block and runs into the counter (`D` walks left over
the carry of ones, `D0` sets the first zero, `A` walks back clearing the
ones).  It then sweeps right over the block, writes one more unit at the
far end and comes back.  Three of the five rows have this shape.  The
other two are what most of the residue turned out to be: a counter that
steps once every three sweeps with a 3-cell unit growing 2 cells a sweep
(`0RB0RA_1LC1RA_0LD0LA_1LA1LB`), and a tape of several blocks
(`1RB1LA_0LA0RC_1LC1LD_1RB0LA`).

**The checker** (`theories/Counters/HybridGlueTr.v`, axiom-free beyond
`functional_extensionality_dep`).  The anchor is two-index:
`hyC p n = (q, (Lpre ++ E p, h, Rpre ++ w^n ++ Rpost))`.  `E` is the counter
word, generic in its digit words (`E xH = C`, `E (xO r) = A ++ E r`,
`E (xI r) = B ++ E r`, the shape of every inferred alphabet); its `cview`
decompositions are proved once for all `A`, `B` and `C`, so a board needs
no per-alphabet file.  One lap is two chains through a mid configuration
`hyM p n = (q2, (Mpre ++ E p, h2, w^n ++ Rpost))`:

* the **counter half** `hyC p (m + n) -> hyM (p+1) n` is a `LapDecider`
  chain indexed by the carry length, with the block as its opaque right
  tail (`m` units of it concrete).  It has an interior branch (high part
  `E r` opaque) and an overflow branch (far left empty).  Each unrolls
  `nu`/`no` carry units and takes the shorter carries as concrete
  chains.  The overflow branch carries the carry instruction: the piece
  §7.4.DX found the irules sweep cycle lacks;
* the **sweep half** `hyM p (na + k + nb) -> hyC p (k + c)` is a chain
  indexed by the block length, with the counter as its opaque left tail
  (§7.4.QS's inner loop).  It may cross the block several times, which is
  how a counter that steps once every 2 or 4 sweeps is expressed: the
  partial units the sweeps add fold back (`SFold`) by the end of the lap.

A certificate is a list of anchor **phases**: when the block grows by a
number of cells its unit does not divide, the junction sees the unit at a
different offset each lap.  Each phase's sweep lands on the next phase's
anchor, so the lap is `(p, n, i) -> (p+1, n - nmin_i + c_i, i+1 mod L)`.
The anchors along the run are the `(p - p0)`-th iterates from the boot,
which is the single-index `Hlap` of `LapGlueTr.glue_neverqhtr` (DN) or
`QHConveyorTr.lap_qh_stage` (QH).  Fires come from chain prefixes of any
phase's three chains.  An interior or overflow fire needs a counter value
with the right carry shape in that phase.  The certificate names a
family for it (`ones_on j (xO (r0 + L s))`, or `ones_on (k0 + T s) xH`),
and the checker computes the family's phase mod `L`.  The QH bound
reads `Nat.log2 t0 < 24`, so no unary `2^24` is built per row.  A row is
one line, `apply coversTr_nqh, (hy_sound_nqh _ (mkHY ...))` (`_mirror`
when the counter is on the right), and a 40-row batch compiles in 1-2.3 s.

**Finder** (`tools/closeouttr/hy_batch.py find`, untrusted).  It runs the
row and its mirror for 4e5 steps.  It pins the undefined instructions
(DN; a carry instruction may be silent for the whole run), or those
silent since the 1e8 scan's quiet point (QH).  Two kinds of anchor
sequence are tried:

* the fires of one instruction at one cell whose six left neighbours
  change between visits (the counter's low end);
* the k-th visit of a cell after each sweep, sub-sampled every `S` sweeps
  (`S` = 1..4) and split into `L` = 1..4 phases, with one counter prefix
  for all phases or one per phase.

It reads the counter family (`Lpre`, `A`, `B`, `C`, digits of 1-4 cells)
and the block (`Rpre`, `w`, `Rpost`, units of 1-8 cells) off the anchors.
It reads the mid off the simulation (the counter incremented, the head
about to leave `Rpre ++ w^m`).  Then it derives the chains with
`lapcert.derive_chain`, the earliest boot, and a fire witness per
instruction.  4e5 steps, 240 s a row; the 496 took ~40 min at 4 jobs.

**Yield: 170 of 496 (34%), all DN**, `CBT_HY_00..04`; all 170 compile.
DN open 1,472 -> **1,302**; all rows 4,156 -> **3,986**.

| certificate shape | rows |
|---|---:|
| one phase / two phases | 169 / 1 |
| sweeps per lap (counter steps once every 1 / 2 / 3 / 4 sweeps) | 66 / 52 / 1 / 51 |
| digits of 1 / 2 / 3 / 4 cells | 58 / 82 / 29 / 1 |
| top alphabets `(A, B, C)`: `(0,1,1)` / `(00,11,11)` / `(00,10,1)` / `(00,01,01)` | 58 / 50 / 17 / 15 |
| block unit of 1 / 2 / 3 / 4 / 7 cells | 54 / 103 / 5 / 4 / 4 |
| carry unrolled `nu` = 0 / 1 (no = 0 in all) | 148 / 22 |
| counter on the right (certified on the mirror) | 77 |
| fire witnesses: sweep only / + interior / + overflow | 92 / 66 / 12 |

The boots are short (the latest at step 285).

**Residue (326: 292 DN + 34 QH).**  From the tape at the last far-side
record before 4e5 steps (`hy_residue.py`, `tools/closeouttr/hy/residue.tsv`; a block is a
run of a unit of at most 4 cells over at least 8 repetitions, a long block
one over 40 cells):

| rows | tape | what the glue misses |
|---:|---|---|
| 130 (115 DN + 15 QH) | one long block (unit of 3 cells: 67, 2: 42, 1: 14, 4: 7) and a short end | the short end is not a counter of the `E` shape read from one cell.  Seen by hand: a digit under the MSB written differently until the next overflow (`0RB0LB_1LC1RA_0LD0LC_1RD1LB`: `...1101 0110 01101` before 192, `...1101 01101` after); 3-cell units growing 2 cells a sweep, where the junction cells rotate with the unit and anchors that fall mid-carry defeat the per-phase family (`0RB1LC_1LC1RD_1LA0LC_0RD1RB`); a low digit that cycles through three values (`0RB0RA_1LC1RA_0LD0LA_1LA1LB`: `100 -> 010 -> 000`) |
| 190 (171 DN + 19 QH) | several long blocks | two-block sweeps with a counter at one end (§7.4.QS's sweep counter plus a counter: three indices), doubling multi-block tapes (`0RB0LB_1LC0RD_1LA1RB_1LC1RD`: `(111)^13 0 (111)^26 00 (111)^52 ...`), block-digit counters (`(001)^159 011 0 (001)^61 ...`), and the QH rows' `(111)^a (01)^b (111)^c` |
| 6 | no long block | |

None of the 34 QH rows fits.  Their quiet instruction stops as late as step
7.97M (the finder runs past it for QH rows), and their tapes are two- and
three-block sweeps, not counter + block.

**The SP class (stretch).**  The same finder over all 2,245 open SP rows
(90 s a row, 3 jobs, ~2 h) certifies **12**, boarded in `CBT_HY_05`
(`hy/sp_find.jsonl`): all one-phase, and all found from single-instruction
anchors.  The rest fail before any chain is derived: 1,213 find no
growing block beside the counter from either end (the log counters of
§7.4.SP), 1,018 find no anchor cell or no counter family, and 2 time out.
So §7.4.DX's guess that this checker is the route for SP's sparse hybrids
holds only for these 12; the other sqrt-width SP rows (not characterised
further here) are not a counter beside one block.  SP open 2,245 -> **2,233**; all rows
-> **3,974**.

**Next.**  Most of the 190 multi-block rows are the three-index
shape §7.4.QS left open: a sweep counter's `(i, k)` glue with a counter
(or a third tied block) as its far tail.  `HybridGlueTr`'s phase list and
`SweepGlueTr`'s two-index enumeration compose: the sweep half becomes
`SweepGlueTr`'s inner and outer laps with the counter opaque.  The
130 single-block rows need counter alphabets beyond `E`: a top digit
that differs from the body digits, and base-3 digits (a `cview` for base 3).

#### 7.4.CE The counters the lap emitter did not derive: a parity split and 18 inferred alphabets, 214 boarded (2026-09-29)

Workstream CE (batch tag `CE`) covers two groups.  The first is the 538 DN
log counters of §7.4.DX that `emit_lapcert.py --tr` did not derive.  The
second is QE's QH residue, the 394 rows of §7.4.QE still open.  The bouncer +
counter hybrids, the sweep counters and the plain bouncers belong to other
workstreams and were not touched.

**Bucketing.**  `tools/closeouttr/qe_probe.py --tr` is QE's probe for the
never-QH side: every anchor, both orientations, both head symbols.  On the
DN side the buckets are §7.4.DX's: "no interior chain" 271, "no anchor"
235, "no overflow chain (nested route is S0-only)" 28, and "no visit
witness" 4.  On the QH side they are QE's best blockers over the 394 open
rows: no interior chain 225, no anchor 74, and the nested-overflow failures
95.  The two ports below address the two largest buckets, which are the
same on both sides.

**Port 1: "no anchor" is mostly missing digit alphabets.**
`alphabet_infer.py` over the 309 no-anchor rows (235 DN + 74 QH) reads a
consistent `E xO = A ++ E`, `E xI = B ++ E`, `E xH = C` family on 205 of
them.  181 of those are 20 families that no existing alphabet covers.  The
biggest is `A=110 B=111 C=111` on 77 rows: a binary counter with 3-cell
digits whose overflow rewrites the whole run.  The 24 others read as
alphabets the table already has (`Bp` 22, `Dp` 2), so their failure is
elsewhere.  `gen_alphabet.py` wrote the 18 new modules
(`theories/Counters/Alph_*.v`, 3-5 cells a digit, each proved by the
standard induction with no axioms).  They were appended to
`alphabets_gen.FAMILIES`.  Two of the 20 inferred triples are already in
the table and were left untouched.  Nothing else changed: the existing
routes derive these rows once the alphabet exists, mostly through the
nested overflow (`NestedLapLift`).  Census cache: MATCH.

**Port 2: the parity split (`emit_lapcert.py`, TR boards only).**  QE's
example `0RB0LB_0RC0LA_1LB1RD_1LA1RC` shows the problem.  The carry crosses
the run of ones in two states that alternate per digit, so the carry ends in
a state that depends on the parity of `j`.  The lap LENGTH is still affine
(`2j+2`), so only the state path differs.  The fix is to split `j` by its
residue mod M (M = 2, then 3):

* A class case covers `j = M*i + c`.  It carries `c1` copies of `uS` in the
  chain's prefix and `c2` in its postfix, over the unit `uS^M`.  One period
  is peeled (`c = r + M`) when the unpeeled form does not derive.  Each
  `j < c` is one concrete lap.
* The same split applies on the overflow side (`cview p = (S j, None)`).
  There a case may close up to `lift`: the `p = 1` lap writes over the
  tail's blank.  The prefix is kept maximally concrete, so the fire-witness
  search can run past the lap into the next small laps.  An instruction
  that fires only for one parity of the carry is then still witnessed in
  every case.
* A lap-length pre-filter keeps failing anchors cheap.  Measured interior
  and overflow laps for `j <= 3M+1` must not depend on the high part, and
  must be affine along each residue class.

The Coq side is per-board: `repeq_*`, `repmul_*` and `repm_*` (`rep u (m*i +
(c1+c2)) = rep u c1 ++ rep (rep u m) i ++ rep u c2`), one glue lemma per
case, and `lapi_*`/`lapo_*`/`fireo_*` by a `Nat.div_mod_eq` /
`Nat.mod_upper_bound` split on `j`.  These feed the unchanged
`LapGlueTr.glue_neverqhtr` / `QHConveyorTr.lap_qh_stage` (via
`fire_via_ovf`).  There is no new theory file.  `Print Assumptions` on a
parity board shows only `functional_extensionality_dep`.  A board compiles
in ~3 s.

**Yields** (probe at 3 jobs, 300 s cap; then `--tr`/`--qh --emit`, where
every board is kernel-checked by the emitter's `coqc`):

| bucket (before) | rows | boarded | by |
|---|---:|---:|---|
| DN no anchor | 235 | 128 | new alphabets (108 through the nested overflow, 20 flat) |
| DN no interior chain | 271 | 14 | parity split 12, flat 2 (an anchor the DX run did not reach) |
| DN no visit witness | 4 | 4 | QE's instruction-level gate (no port needed) |
| DN nested route is S0-only | 28 | 2 | QE's S1 nest / gate |
| QH no interior chain (QE: parity 66, Fibonacci 74, other radices) | 225 | 34 | parity split (M = 2 on all 34) |
| QH no anchor | 74 | 32 | new alphabets (flat) |
| QH nested-overflow failures | 95 | 0 | |
| **total** | **932** | **214** | 148 DN + 66 QH |

Three DN rows derive in the probe but not in `emit_lapcert.py`'s own
anchor walk, which tries anchors in a different order.  They are still
open.  All boards that derived compiled.  Batches: `CBT_CE_00..04` (148 DN,
LAPT boards through `sp_lap_batch.py`) and `CBT_CE_05..06` (66 QH, inline
through `qc_batch.py lap`), 43 s for the last three at `-j3`.  Closeout:
6,768 boarded before, **6,982** after, **3,942** remaining.

**The residue (718: 390 DN + 328 QH), by blocker.**  DN growth is §7.4.DX's
record-gap ratio; QH growth is QE's `log2` ratio per cell.

| blocker | DN | QH | what it is |
|---|---:|---:|---|
| no interior chain | 255 | 199 | Measured interior lap lengths on the DN rows: over j = 0..5 at the first six anchors of the 271 open DN rows with this blocker, 82 grow exponentially in j (a nested interior); 121 are neither affine nor exponential (the Fibonacci counters and the other radices); 35 never return to the next anchor within 5,000 steps; 21 are affine, which is a chain-search gap; and 12 depend on the high part.  Fibonacci counters: DN gap ratio 1.62 on 41 rows, QH growth 0.694 on 69.  QH also has other radices: 0.79 (26), 0.64 (24), 0.67 (20).  30 QH parity-looking rows (growth 1.00) survive M = 2 and 3 |
| no anchor | 102 | 32 | Rows with no inferable family (104 of the 309 had none), or with a family whose anchor still does not fit.  The largest DN group is two-sided with gap ratio 1.0 (23 rows) |
| nested overflow: no exit / boot / inner interior / inner family | 28 | 95 | QE's two-sided binaries (40 QH, growth 1.00) and two-cell-digit binaries (55 QH) are unchanged.  On DN, the no-exit rows (8) are all two-sided |
| other | 5 | 2 | 3 emit-order misses, 2 "no overflow phase at K=6"; 2 QH offset nests with no `p = 1` fire |

The next routes, by size:

1. **Nested interior laps.**  The exponential class (82 DN rows) has an
   interior lap that is itself a counter run, for example
   `0RB0RB_0LC1RA_1RB1LD_1LC0RA`, where the lap at `j` costs 4, 12, 44, 172
   steps.  `NestedLapLift` already composes such a run on the overflow side.
   The interior would need the same boot + inner + exit composition, per
   `j`.
2. **A Fibonacci counter theory.**  About 110 rows (41 DN + 69 QH) are
   Zeckendorf counters.  `FIB_ELEVEN.txt` is the state-level reading; there
   is no Coq module.
3. **Two-sided counters.**  These are the no-anchor rows with gap ratio
   1.0 or 1.4, and QE's 40 no-exit rows.  They need an anchor with a
   counter on each side.

```
python3 tools/closeouttr/qe_probe.py ROWS probe.jsonl --jobs 3 --timeout 300 [--tr]     # per-row results: tools/closeouttr/ce_probe.tsv
python3 tools/counters/alphabet_infer.py --list NOANCHOR_ROWS          # then gen_alphabet.py --abc A,B,C
(cd tools/counters && python3 emit_lapcert.py --tr --emit --list ok.txt --json lap.json)   # --qh for QH
python3 tools/closeouttr/sp_lap_batch.py lap.json --tag CE --chunk 40
python3 tools/closeouttr/qc_batch.py lap theories/Machines/CountersTr/LAPQ_*.v --tag CE --chunk 40
```


#### 7.4.CE2 CE's residue: the value-family ladder on the QH side, in base 3/4, Fibonacci and Gray, 212 boarded (2026-09-29)

Workstream CE2 (batch tag `CE2`), over the 718 rows §7.4.CE left (390 DN +
328 QH), all still in `closeouttr_remaining.txt` at the start.  Class SP was
not touched (session SPC).

**Re-bucketing: measure the radix first.**  `tools/counters/radix_clock.py`
(per-cell toggle ratio, no anchor needed; 2e6 steps) over the 718 rows:
base 2 341, Fibonacci (phi) 126, base 4 82, base 3 46, flat 23, unreadable
100.  On a sample of 94 base-2 "no interior chain" rows, the interior lap at
the emitter's anchors is QUADRATIC in the carry length on 48 (for example
`2(j+2)^2`: the carry walks back to the anchor once per digit), affine on 11
(a chain-search gap), exponential or non-returning on 8, and 18 have no
anchor.  So the §7.4.CE buckets were mostly not emitter gaps but other
numerations, and the tool that reads numerations as data is the ladder's
`valfam.py`.  It had been run at instruction level only on a 40-row DN
sample (§7.4.DX), and never on the QH side, because there was no QH closer.

**The three DN "derived, emit missed" rows** derive in `emit_lapcert.py`'s
own anchor walk.  The miss was an uncompiled `Alph_000_111_111.vo`, not the
anchor order.  They are `CBT_CE2_00` (LAPT boards).

**Ports (all generic, per numeration, not per board; axioms:
`functional_extensionality_dep` only):**

* `Checkers/LadderCheckQHTr.v`, **the ladder on the QH side.**
  `LadderCheck`'s `(Binary, 1)` board with the boot on the ORIGINAL machine
  (up to `lift`) and the laps and fires on the machine wrapped at the quiet
  pins, closed by `QHConveyorTr.lap_qh_stage`.  The anchors are re-indexed by
  `positive`; a fire from every anchor comes from `board_fire`'s cofinal
  fires plus the exact laps.  `emit_ladder.py --tr --qh` pins the
  instructions the 1e8 scan saw go quiet (every QH row here has its last
  quiet fire below step 100) and boots at the first family member past it.
  Boards `LDRQ_*`.
* `Checkers/LadderCheckLiftTr.v`, **fill arms up to `lift`.**  The base-4
  counters (a binary counter whose bits alternate a two-cell and a one-cell
  word, so a base-4 digit is `000/110/001/111`) run the fill `111^k ->
  000^k 110` and stop one blank short: the machine never writes the last
  `0`.  The fill arm is stated to what the machine writes, plus a per-arm
  count of trailing blanks (`cpad`, `lift_cpad`), and `LadderCheck.board_arm`
  (generic over the arms' property) runs unchanged over a virtual arm stated
  to the target.  Both closers (`boardphL_neverqhtr`, `boardphL_qhtr`).
  `valfam.py`'s digit alphabet cap went from 3 to 4 words (`MAX_ALPHA`),
  without which base 4 read as "no value family".
* `Checkers/LadderCheckFibTr.v`, **the Fibonacci question.**  A
  Zeckendorf-style family does not fit `MonoCounter.cview`: `cview` splits a
  `positive` at its low run of set bits, which IS the binary carry.  A
  Fibonacci counter has no `positive` to index by, and its increment folds
  `F(k) + F(k+1) -> F(k+2)`, so a per-board `cview` glue would re-prove the
  numeration on every board.  It also needs no new lemma:
  `LadderFam`/`LadderCheck` §11 already state `(Fib, 1)` once (`fib_split`,
  `fib_class`, `topsF_cofinal`), so the port is `LadderCheckTr`'s shape for
  that section, both closers.  `valfam.py --numeration` finds the families.
* `Checkers/LadderCheckGrayTr.v`: `LadderCheck` §10 (`(Gray, 2)`), both
  closers, for the DN families valfam reads in reflected binary.
* `valfam.py --json` now writes one row at a time and resumes past done
  rows.  The container is reclaimed when the session idles, which cost two
  multi-hour runs before this.

**Yields** (valfam at 120-150 s a row, 4 jobs; boards emitted and compiled by
`sp_ladder_batch.py [--qh]`, ~2-5 s a board):

| radix (radix_clock) | DN rows | DN boarded | QH rows | QH boarded |
|---|---:|---:|---:|---:|
| base 2 | 208 | 21 | 133 | 75 |
| base 3 | 10 | 7 | 36 | 26 |
| base 4 | 36 | 19 | 46 | 37 |
| phi (Fibonacci) | 55 | 7 | 71 | 17 |
| flat | 21 | 0 | 2 | 2 |
| unreadable | 60 | 1 | 40 | 0 |
| **total** | **390** | **55** | **328** | **157** |

By closer: `(Binary, 1)` exact 112 (101 QH), lift-tolerant fills 54 (39 QH),
Fibonacci 25 (17 QH), Gray 18 (all DN), LAPT 3.  So **212** rows, in
`CBT_CE2_00..19`.  Closeout: 3,480 remaining before, **3,268** after.  The
QH side gains most: when valfam closes a QH row, the new closer boards it
(157 of 171).

**The residue (506: 339 DN + 167 QH), by where it stops:**

| stops at | DN | QH | radix | what it is |
|---|---:|---:|---|---|
| valfam: families found, none closed | 95 | 123 | base 2 89, phi 42, base 4 11, base 3 9, ? 62 | an anchor family decodes, but its arms do not close (the rule ladder cannot state the carry) |
| valfam closes; the interior arm has no chain | 133 | 8 | base 2 102, base 4 13, flat 8, ? 14 | **the carry costs time quadratic in its length.**  `LadderKernel.LRule` states a step count affine in the run (`lr_ca * j + lr_cb`), so no arm index scheme expresses it.  This is RULE_LADDER §5's count language: a kernel extension (a rule whose cost is a sum over the run), not an emitter gap |
| valfam: no value family | 94 | 18 | base 2 51, phi 30, flat 8, ? 23 | no anchor decodes over ladder-named digits (§7.4.CE's "no anchor", unchanged) |
| valfam: time cap | 10 | 15 | phi 21 | Fibonacci rows whose numeration pass does not finish at 120 s |
| valfam closes; shifted Fibonacci numeration | 2 | 4 | phi | weights `1, 2, 3, 5` (Zeckendorf), which `LadderFam` does not state (§11 is `1, 1, 2, 3`) |
| other | 1 | 3 | | a fill anchor that reaches no A1; 2 Fibonacci boards whose `vis_ok` fails in the kernel; 1 row not run |

The largest piece of residue with a named fix is the 141 quadratic-carry
rows (133 DN).  The QH nested-overflow rows of §7.4.QE/§7.4.CE (95) mostly
went to the QH ladder: 75 of the 133 QH base-2 rows boarded.

```
python3 tools/counters/radix_clock.py ROWS --steps 2000000                  # the re-bucketing
(cd tools/ladder && python3 valfam.py --list ROWS --cap 120 --json vf.jsonl)  # add --numeration for phi rows
python3 tools/closeouttr/sp_ladder_batch.py vf.jsonl --tag CE2 --chunk 40       # DN: LDRT boards
python3 tools/closeouttr/sp_ladder_batch.py vf.jsonl --tag CE2 --chunk 40 --qh  # QH: LDRQ boards
```

#### 7.4.CE3 CE2's residue: nested arms for the quadratic carry, and closing from the family alone, 153 boarded (2026-09-29)

Workstream CE3 (batch tag `CE3`), over the log counters §7.4.CE2 left: 335 DN
(`dx/char_all.tsv` shape `log`, kind `counter`) and 171 QH
(`counter_boxfail` / `counter_new`), 506 rows.  Hybrids (HY2), bouncers and
edge rows (BX) and class SP (SPB) were not touched.

**The quadratic carry is a loop of rounds, and needs no count.**  On
`0RB0LA_0LC0RD_1LA1LC_1RC1RD` the interior lap costs `2(j+2)^2`.  The carry
is `j` ROUNDS of `A[0] 1^(2i+1) 01 X -> A[0] 1^(2i+3) X`, each an ordinary
kernel rule whose cost is affine in its OWN index `i` (the run it sweeps).
The number of rounds is affine in the arm's index.  Every row traced has one
of two shapes: UP, where the swept run grows and each round consumes a word
from a tail, or DOWN (`0RB0LA_1LA0RC_0LD1RC_1RB1LD`), where the swept run
shrinks and each round pushes a word onto the other side.  The closers only
need SOME positive number of steps per lap, so the sum never has to be
stated.

**Ports (generic; axioms `functional_extensionality_dep` only):**

* `Checkers/LadderNest.v`.  An arm is a SEGMENT program: kernel chains
  (`NCh`) and iterations `NUp`/`NDn` of an inner rule over `al*j+be` rounds.
  The proof is by induction on the round count (`iter_up`, `iter_down`), and
  each round is linked to the next by a syntactic check (`link_up`,
  `link_down`).  Segments meet at configurations built by `sidx` (a side at
  an affine index), `srep` (a repeated word) and `sapp` (concatenation, with
  at most one side depending on `j`).  Sides are compared on a normal form
  (`snf`: fold the constant into the prefix and the multiplier into the
  unit, then unrotate), because chains land on different spellings of the
  same side (`0 ++ 0^(2j+2)` against `0000 ++ (00)^j`).  The end of an arm
  is compared up to trailing blanks beside an empty tail (`ceqL`).  The
  result is `ReachL`: a positive run to a configuration that lifts to the
  right-hand side's.  `narm_reach` is the one theorem.
* `Checkers/LadderCheckNestTr.v`.  The `LadderCheckTr`/`QHTr` board over such
  arms (`boardN_neverqhtr`, `boardN_qhtr`).  `LadderCheck`'s `board_arm` and
  `LadderCheckTr`'s `board_fire` carry the interior arms' `RuleSound` as a
  section hypothesis, so they are restated here without it.  A fire may be
  witnessed after the rounds: `nfire` runs a program prefix, then a base
  chain.  The file also has a lookahead split (`boardK_*`: interior arms per
  NEXT digit, plus end arms per phase for the last digit), for carries that
  turn back on the next digit's first cell.  It is built and checked but has
  boarded nothing: on the rows tried, the carry runs across the whole next
  run, which is a misread family rather than a lookahead.
* `tools/ladder/nest.py`.  It simulates the arm at several `j` with a marker
  in every opaque tail, takes the state/symbol whose visit count is affine
  in `j`, fits UP/DOWN rules to consecutive visits, proves them with
  `lapcert.derive_chain`, fits the round count, and glues the pieces with
  chains.  The chain engine can fold copies into a count but never unfold
  one, so an inner rule carries its constant copies in `s_pre`.
  `emit_ladder.py` tries it only when an arm has no kernel chain (plus arm
  thresholds 4..6 last, since a round count `j - 1` needs `r >= 2`), and
  emits the nested closure only for such rows.  Every other board is
  byte-identical.
* `tools/ladder/famclose.py`.  It closes from valfam's FAMILY alone.
  `emit_ladder.closure_data` builds its class arms from the family and never
  uses the arms valfam mines, and valfam's own miner is affine too.  So for
  a row filed as "families found but none closed", each family (with its
  fill laws and boot) is handed straight to the emitter.

**Yields** (valfam at 150 s a row over all 506; famclose on the unclosed
rows, 2 jobs; every board compiled by `sp_ladder_batch.py`):

| bucket (valfam, this run) | DN | QH | boarded DN | boarded QH | by |
|---|---:|---:|---:|---:|---|
| valfam closes | 138 | 24 | 96 | 16 | nested arms on 90 of the 94 in `CBT_CE3_00/01`; the others are plain arms the old emitter refused only because they land a blank off the rhs (`ceqL`) |
| families found, none closed | 76 | 96 | 12 | 29 | famclose (of 85 DN and 57 QH run so far) |
| no value family | 94 | 18 | 0 | 0 | |
| time cap | 27 | 33 | 0 | 0 | |
| **total** | **335** | **171** | **108** | **45** | 96 boards nested |

Batches `CBT_CE3_00..05`.  Closeout: 8,152 boarded before, **8,305** after,
**2,619** remaining.  famclose was still running on the rest of both
unclosed lists when this was written (container restarts cut it twice).

**The residue, by where it stops.**  Among the 42 DN rows valfam closes and
the emitter still cannot: the interior arm fails on 10, and 7 of those have
AFFINE laps.  Those carries read past the incremented digit into the next
run (a family misread, not a cost problem).  Most of the rest fail on the
fill arm or the visit phase.  Over the first 60 unclosed rows, the
interior-lap growth of the first family is: no one-parameter family with a
boot 30, affine 16, family step lands off the next member 9, quadratic 3,
exponential 2.  An exponential lap (`0RB0LA_1LC1RD_0RD0LC_1RB1LA`: 16, 36,
72, 140, 272, 532) runs a whole inner binary counter inside the carry.  It
would need an arm that invokes itself at a smaller index; it is too rare
here to pay for.  famclose closes 5 of the 16 affine rows; 8 fail on the
fill arm.  The QH rows were blocked by valfam's arm miner, not by cost:
only 1 of the 45 QH boards needs a nested arm.

```
(cd tools/ladder && python3 valfam.py --list ROWS --cap 150 --json vf.jsonl)
(cd tools/ladder && python3 famclose.py --list UNCLOSED --json fc.jsonl --jobs 2 [--qh])
python3 tools/closeouttr/sp_ladder_batch.py vf.jsonl fc.jsonl --tag CE3 --chunk 50 [--qh]
```

#### 7.4.SW The DN sweep counters: a multi-family two-index glue, 239 of 287 boarded (2026-09-29)

Workstream SW (batch tag `SW`), over the 287 `sweepctr` rows of
§7.4.DX (`dx/char_all.tsv`) that irules does not take.  All 287 are
class DN, so every row needs `NeverQuasiHaltsTr`.

**QS's residue (part b of the brief) was already done.**  The 75 rows
§7.4.QS left ("two converging holes" 58, "travelling gap" 17) are all
boarded by `CBT_DXS_00..01` (irules → `MetaBlkPfxQHTr`, §7.4.DX).  No
three-index glue is needed for the QH side.

**The plain never-QH twin takes none.**  `SweepGlueTr`'s anchor, laps
and enumeration, with the boot on the wrapped machine and
`glue_neverqhtr` at the end: 0 of a 20-row sample (seed 20260928).  The
DN sweep counters are not QS's shapes:

* **Behind sweeps** (the `1 01 1` rows, `1^a (01)^b 1^c`).  The machine
  turns at the hole and sweeps the units BEHIND it, out to the tape's end
  and back, toggling `11 <-> 01` as it goes.  The units ahead are never
  touched.  QS's inner lap sweeps the side that shrinks, and this one
  sweeps the side that grows.  It is not the mirror of the other either:
  mirroring swaps the sides, but not which side is swept.
* **Parity** (most `1 1` rows).  The block grows by one cell a round, but
  the sweep alternates two states per cell, so the units are two cells.
  Consecutive rounds then split differently (`Rpost = [1]`, then `[]`),
  and no single anchor split covers both.

**The glue** (`theories/Counters/SweepGlueNeverTr.v`, only axiom
`functional_extensionality_dep`).  A certificate (`swncert`) is a cycle
of anchor families `fC f i k = (q, (Lpre ++ uL^i ++ Lpost, h, Rpre ++
uR^k ++ Rpost))`.  Each family has:

* an inner lap `(i, k+1) -> (i+1, k)` that stays in the family.  An
  AHEAD lap is `SweepGlueTr.sw_inner_lap`, reused as it stands through
  `fam_sw`.  A BEHIND lap (`sb_inner_ok`) is a chain from `swAb` with
  index `i`, the first unit ahead concrete and the rest of the right side
  the opaque tail.  The anchors with fewer than `na + nb` units behind
  take the concrete `f_base` chains;
* an outer lap `(i, 0) -> (e, i + d)` onto family `j+1 mod P`
  (`sn_outer_ok`, both tails empty, index `i`).

The anchors `(j, i, k)` are enumerated along `sn_nxt` into
`glue_neverqhtr`'s single `Hlap`.  The block size `i + k` never shrinks,
and `sweep_nqh_check` requires family 0 to grow it (`1 <= e_0 + d_0`).
So from any visited anchor, cycling the families reaches any family with
as many units ahead as a fire witness needs (`reach_big`, `reach_fam`,
`reach_ahead`).  That turns every chain-prefix fire, of any family's
inner or outer lap, into a fire from every anchor.  A row is one line,
`apply coversTr_nqh, (sweep_nqh_sound _ (mkSWN ...))`
(`sweep_nqh_sound_mirror` when the hole moves left).  A 40-row batch
compiles in about 1.2 s.  `Tests/SweepNqh_Corruption.v` holds a real
two-family certificate and 7 controls that must fail: the families
swapped (the growth gate), a wrong cross-family `d`, the lap-side flag
flipped, a live pin, no fire witnesses, the unmirrored machine, and a
one-transition mutant.

**Finder** (`tools/closeouttr/sw_batch.py find`, untrusted).  It runs 6e4
steps of the machine and its mirror, and pins the instructions that
never fire (the undefined ones).  For each instruction and each small
prefix/unit length (units 1-4), it groups the late configurations by
split key, one key per family.  It follows the outer transitions
(`k = 0` -> the next key at `(e, i + d)`) around a cycle whose total
growth is positive.  Then it derives each family's inner chain (ahead
first, then behind) and outer chain with `lapcert.derive_chain`.  Three
passes, each run only on what the one before left:

| pass | what changes | rows |
|---|---|---:|
| all late fires of the instruction | | 190 |
| only the steps where the head reverses | the anchor instruction also fires inside the sweeps; those fires hid the anchor's units (they are cut from the longest configuration) | 21 |
| keys read one at a time | the hole moves one cell a sweep with two-cell units, so the key alternates every lap; a family's inner lap is then two sweeps, and its outer transition goes to the next round's start | 28 |

**Yield: 239 of 287 (83%) boarded**, in `CBT_SW_00` (the sample, 13)
and `CBT_SW_01..07`.  All 239 kernel-check; each batch takes about 1 s.
All rows, 4,156 -> **3,917**.

| certificate shape | rows |
|---|---:|
| one family, behind lap | 122 |
| one family, ahead lap | 15 |
| two families (parity), ahead laps | 96 |
| three / four families, behind laps | 2 / 4 |
| units of two cells / four cells | 233 / 6 |
| hole moves left (certified on the mirror) | 112 |

Cost in the container (4 cores, shared with a full `make closeout-tr`):
the first pass took about 2 h at 4 jobs (~12 s a row, and a failing row
tries every candidate).  The two later passes took about 25 and 40 min
on the rows left before them.

**Residue (48):**

| rows | shape | failure |
|---:|---|---|
| 31 | two or three holes in a block of 1s (`1 1 1`, `1 1 1 1`): the converging-holes shape of §7.4.QS's residue, never-QH side | 22 no outer chain (a one-hole split fits the anchors inside a round, but no chain closes the round); 8 no sweep anchor; 1 no inner chain |
| 8 | long `(01)^n` trains with a `0010101` head (`01 01 ... 01 0010101`) | no sweep anchor |
| 9 | one-hole shapes (`1 1`, `1 01 1`, `1 01`) | 5 no sweep anchor, 4 no outer chain |

The 31 multi-hole rows are the next step.  They need the three-index
anchor §7.4.QS sketched, `L ++ uL^i ++ M ++ uR^k ++ N ++ uL'^i ++ R` with
the two outer blocks tied.  Each lap is still a one-index chain between
opaque tails, so the glue here would carry over with a third, tied
count.  On the QH side, irules took all 75 of these shapes (§7.4.DX), but
on the DN side it leaves them undecided.

#### 7.4.TI The multi-block sweeps: a block-family glue with rankings, 48 boarded (2026-09-29)

Workstream TI (batch tag `TI`), over §7.4.SW's residue (48 rows, 31 of
them the multi-hole shape) and §7.4.HY's residue (326 rows: 171 DN + 19 QH
multi-block, 121 DN + 15 QH single-block).

**The three-index anchor is not enough.**  Read by hand, the multi-hole
rows are not converging holes with tied outer blocks.  In
`1RB1LA_0RC0RD_1LC0LA_1LB0RC` the anchor `1^i 0 [D1] 1^m 0 1^k` laps as
`(i, m+3, k) -> (i+1, m, k+2)`, and what happens when the middle block
runs out depends on `m mod 3`.  Remainder 1 or 2 merges everything into a
new round `(1, i+k(+1), 2)`.  Remainder 0 starts a sub-round
`(1, i-3, k+3)` on a block a third the size, and that recursion has no
bounded depth.  The anchors of one round are three-index, but the ties
between rounds are not fixed (at sub-round depth `d` the right block is
about `4^d` times the middle one), so no fixed `L uL^i M uR^k N uL'^i R`
closes.  What does close is a finite set of anchor FAMILIES, each a
symbolic tape, with the remainder cases as separate leaves.

**The glue** (`theories/Counters/TriGlueTr.v`, 1,790 lines, only axiom
`functional_extensionality_dep`).  A family is a whole tape `q, h, L, R`,
each side a list of literal words and blocks `u^e`, with `e` affine in the
family's variables.  Three variables is the common case, but the glue
takes any number.  A family carries a dispatch tree.  A split on variable
`k` takes the values `0..n-1` one by one and the rest by residue mod `p`,
so its leaves are regions `x_k = M_k z_k + c_k`.  Each leaf has ONE
`LapDecider` chain whose index is one `z_j`.  The other blocks are
concrete in the region or inside the opaque tails.  The chain lands (up to
`lift`) on a family at values affine in `z`.  Both ends are compared with
the families by a verified one-pass normalizer on segment lists (merges,
absorption of unit copies into blocks, primitive roots, trailing blanks).
The anchors are the iterates of `tnxt` (walk the tree, jump to the
target): the single `Hlap` of `glue_neverqhtr` (DN) or `lap_qh_stage`
(QH).  The FIRES need a liveness argument, because an instruction may fire
in some leaves only (D0 above fires only when a round ends on remainder
0).  So a certificate also carries:

* a residue modulus `P`;
* a node set `S` of pairs (leaf, values mod `P`), which contains the boot
  and is closed under every step into a leaf whose region is compatible
  with the target values;
* per instruction, an affine ranking on the nodes that drops by 1 at every
  step out of a leaf that does not fire it into another leaf that does
  not.

Every chain prefix of a leaf fires its end instruction (`leaf_fired`, no
witness data), and every check is coefficient-wise.  A row is one line,
`apply coversTr_nqh, (tri_sound _ (mkTC ...))`, or `coversTr_qh3` of
`tri_sound_qh` for QH rows (boot on the machine, `t0 <= 4096`).  The
`_mirror` variants exist but no boarded row needs them.  Corrupting a
chain step, a target constant or a ranking entry makes the row fail to
compile (checked by hand on the first row).

**Finder** (`tools/closeouttr/ti_batch.py`, with `ti_coq.py`, an exact
Python transcription of every decidable function of the checker).  The
boot is the tape at step 3000, with every run of at least two copies of a
primitive unit of 1 to 4 cells read as a block.  Each family is explored
from its generic instance:

1. run concretely until the head is about to enter a block;
2. cross the start block with `SCycR`/`SCycL` (with carried cells) when
   its traversal cycles, at unit powers up to 4 (a residue split);
3. otherwise peel it (a split on its variable, small values one by one);
4. cut when the head is about to enter any other block, or comes back to
   the start block after an excursion.

The end configuration, normalized exactly as the checker does, is an
instance of a new or known family, and lower bounds drop until they are
stable.  The rankings come from an integer LP (scipy's `milp`, finder
side only) over the reachable nodes, for `P = 1, 2, 3, 4, 6`.  Every check
of `tri_check` is replayed in Python before a certificate is written.  QH
rows pin the instructions silent after the 1e8 scan's quiet point.  Cost:
~7 s a row for the SW rows (8 min for the 48 at one job), well under a
second for most HY rows.

**Yield: 48 boarded**, in `CBT_TI_00..03`.  All 48 kernel-check.  Compile
times: 16, 11, 19 and 2 rows in 6.3, 8.9, 5.1 and 2.7 s (measured under
load), `TriGlueTr.v` itself ~5 s, so the CI `closeout-tr` job grows by
well under a minute.  All rows: 3,480 -> **3,432**.

| source | rows | boarded | certificate shape |
|---|---:|---:|---|
| SW residue, multi-hole | 31 | 11 | 9-41 families, 13-56 leaves; `P = 1` for 15 of the 19 SW rows, `P = 2` for 4 |
| SW residue, other (`(01)^n` trains, one hole) | 17 | 8 | |
| HY multi-block, DN | 171 | 8 | `P = 1, 2, 3`: 4, 3, 1 |
| HY multi-block, QH | 19 | 19 | quiet by step 2; 7-8 families, `P = 1` |
| HY single-block, DN | 121 | 2 | |
| HY single-block, QH | 15 | 0 | |

**Residue (in my scope, 326 of 374):**

| rows | failure | what it is |
|---:|---|---|
| 271 (144 HY multi + 114 HY single + 13 SW) | too many families (cap 120) | the block count grows without bound: doubling tapes (`1^6 0 1^12 0 1^24 0 1^48 ...`), block-digit counters, `(10)^n` trains with doubling blocks.  They need a counter segment in the family language (HybridGlueTr's `E p`) for the part that is not blocks; the rest of the glue carries over |
| 24 (15 SW + 9 HY) | no ranking at any `P <= 6` | the instruction fires in one remainder case only, and a (leaf, residue) node cannot see why that case recurs.  In the `-3/+2` rows the argument is relational: `3i + m >= C` holds through the rounds, so a round never ends small enough to take the other branch.  Next step: per-node linear invariants with Farkas multipliers in the certificate, checked coefficient-wise like the rankings |
| 16 (1 SW + 10 HY multi + 5 HY single) | leaf too long | a leaf runs 4,000 steps without meeting a block (a bouncer whose sweep region is all literal at the boot) |
| 15 | HY QH, quiet point past the boot cap | the quiet instruction stops at ~7.95M steps.  In the generic instance the pinned instruction fires inside a leaf, so the regions need the same relational invariants |

The composition §7.4.HY proposed ("the sweep half becomes `SweepGlueTr`'s
inner and outer laps with the counter opaque") is, in this glue, a family
whose far side is a counter segment.  The DN hybrids that close here are
the ones without a counter.  Adding a counter segment type and its
`cview`-style leaves is the next step for the 271.

#### 7.4.MB BR's residue: a multi-block RepWL, 17 of 162 boarded (2026-09-29)

Workstream MB (batch tag `MB`), over the 162 rows of
`tools/closeouttr/br/residue.txt` (§7.4.BR).  All 162 were still open:
97 low-junk never-QH bouncers, 47 never-QH rows with more than 100 junk
cells, 18 QH.  Per-row data in `tools/closeouttr/mb/`.

**The design.**  The multi-block node is RepWL's own `rconf`.  RepWL never
needed its item words to share a length: `items_den`, `push_side_den`,
`pop_den` and the five measures of `rw_meas_exact` hold for any non-empty
words.  The only thing tied to one length L is the fold, which cuts the
departed buffer into L-blocks once it reaches 3L cells.  So the new
checker changes the fold and nothing else.  Each side has a word list
(`mb_DL`, `mb_DR`, nearest-first).  When the head walks off the arrival
end, `mb_fold` cuts the far end of the departed buffer at a listed word.
It prefers, in order:

1. the nearest item's word, if it is listed (a run keeps its phase);
2. a listed word the far end holds twice (so a rotation of a long word
   does not cut into a short-period run);
3. any listed word.

A word fold starts once the buffer holds `Y` cells and leaves at least
`K` cells.  With no word matching, past `X` cells the farthest single
cell is folded as an exact, unmerged item (`push_raw`).  Popping from an
empty side gives `B` blank cells, and counts saturate at `T`.  The seed
puts each concrete side into the buffer and folds it.

Soundness does not depend on the policy at all.  The pushed block is
literally `skipn c buf`, so `mb_fold_den` holds for any cut, and the
parameters (`mbpar`) are plain data.  The checker is
`theories/CensusTr/RepWLMBTr.v` (a new file; `RepWLTr.v` is untouched):

* `mb_tier_tr` (never-QH) and `mb_tier_qhbtr` / `mbqh_stage` (wrapped,
  QH) are parameter-closed like `rw_tier_tr`: the kernel re-runs the
  closure and the certificate search at the finder's parameters;
* the certificate syntax, the engine, the measures and the search are
  RepWL's;
* `Print Assumptions` shows `functional_extensionality_dep` only.

A row is one line:
`apply coversTr_nqh, (mb_tier_tr_sound _ (MbPar DL DR K Y X B T) t fuel M)`.

**Two rules came from the design rows.**  A forced single-cell fold
first merged like any other push.  A bounded run of `1`s folded cell by
cell then became an unbounded `1^2+` item, and the abstraction walked
off it forever (row 4 below).  Hence `push_raw`.  Longest-first matching
also let a rotation of a period-5 word (`01101`) cut into a transient
period-3 run (`011011...`), leaving `1` junk between the 5-words.  Hence
the double match.  On 25 failing rows the double match gains nothing at
40 s, but all 13 first hits re-certify under it with smaller closures
(for example 11,426 → 4,449 nodes).

The five design rows:

| row | tape | multi-block |
|---|---|---|
| `0RB0RC_0LC1RA_1LD1RC_1LA0LB` | `(001)^a (0110)^b [h] (01)^c`, periods 3/4/2 (LCM 12) | 452 nodes; RepWL: no closure at any L |
| `0RB1LB_1LC1RC_1RD0LA_0RC1RB` | `(01111)^a (01)^b 0^c` (LCM 10) | 1,102 nodes |
| `1RB0RD_1LC0RA_1LA1LC_1LD0LC` | two period-14 regions | 3,660 nodes |
| `0RB0RC_1LC1RC_1LD1RA_1RA0LD` | `(10110)^a .. (11110)^b` and a right-end run of `1`s of varying length | no closure: the run is bounded but not a word, and the abstraction over-grows it |
| `0RB0LA_1LC1LD_1RD0RD_1LA0RC` | `1^k 01 0^a [h] 1^b`, k growing slowly | no closure: a unary counter at the edge, a hybrid |

**The finder** is `tools/censustr/mb_cert_find.py` (untrusted, the Python
mirror of `RepWLMBTr.v`).

* Word lists: the periodic runs (period at most `--pmax`, default 16) of
  82 tape snapshots from one run of 2^12..2^22 steps, heaviest first.
  The finder tries the top 2..8 period classes, every rotation of each,
  longest first, with the left side mirrored.
* Candidates: `K` in {1, 2, longest word}, `Y` = `K` + longest (+2),
  `X` = `Y` + max(4, longest), `T` in {2, 3}, `t` in {0, 1024, 4096}.
  Closures are capped at 30K nodes.
* After the first hit it spends `--polish` seconds (default 60) looking
  for a smaller closure, with the cap set just under the best so far.
  The kernel's cost grows steeply with the closure.
* `--qh` is the wrapped mode (pins from the 1e8 scan, as in
  `rw_cert_find.py`).

`probe` writes `Time Eval vm_compute` files.  `tools/closeouttr/mb_batch.py`
writes the batches and spreads the heavy rows across them.

**Yields.**

| rows | tried | certified | boarded |
|---|---:|---:|---:|
| never-QH, the 97 low-junk and the 47 junk rows, 240 s | 144 | 13 (all low-junk) | 13, `CBT_MB_00..03` |
| the 20 long-period junk rows (below), `--pmax 64`, 300 s | 20 | 8 | 4, `CBT_MB_04..05` |
| QH, `--qh`, 240 s | 18 | 0 (15 time out growing wrapped closures, 3 no closure) | |

**17 of 162 boarded.**  All rows: 3,480 → **3,463**.  The 13 low-junk hits
are mostly two long-period regions (periods 14 and 14, 11 and 6, 15 and
15, 5 and 2), which is what a single L at the LCM could not hold.

**Kernel cost.**  Per row (probe, container, CPU shared with the finders):
452 nodes 0.8 s, 1,102 nodes 3-4 s, 3.2K-3.7K nodes 8-10 s, 4,449 nodes
23 s, 5,551 nodes 56-60 s, 16,578 nodes 62 s.  The long-period rows run
about 20 s at 5.1K-5.5K nodes and **about 7.7 min at 15.8K** (20-cell
words, 41-cell buffers).  The four 15.8K rows (`1RB0LA_1LC0RD_1LA0LC_1RB0RD`
and its three twins) certify, but 31 kernel-minutes for 4 rows is BR's
cost again, so they are left out.  They are one `mb_batch.py` call away
if the CI budget allows.

Per batch, at 4 or 2 rows a batch: MB_00 131 s, MB_01 89 s, MB_02 81 s,
MB_03 78 s, MB_04 83 s, MB_05 53 s.  That is **about 8.6 CPU-minutes in
all, 2-3 minutes of wall time on CI's `-j4`**, against BR's ~48.

**The 47 junk rows, re-characterised** (`dx_char.py junk`: junk at 1e6, 1e7
and 1e8, its growth exponent, where it sits, and the long periods 17..64
over the whole tape; `tools/closeouttr/mb/junk47.tsv`):

| rows | class | what it is | workstream |
|---:|---|---|---|
| 20 | `longper` | ≥ 60% of the tape is periodic with one period of 17-54, fixed from 1e7 to 1e8.  Mostly level-2 words `A (011)^k` with k fixed.  BR's detector stops at 16, so no RepWL L ever matched | MB with long words: 8 certify (4 boarded, 4 heavy), 12 no closure |
| 26 | `spread` | junk grows with the extent (exponent 0.41-0.79), in 1-750 segments, and no long period covers it.  Irregular tapes (e.g. `0RB0RA_0LC1RA_1RB1LD_1LC0LD`) | none landed; the n-gram / CPS family at wider windows is the nearest route.  Not a bouncer or counter workstream |
| 1 | `inner_log` | bounded junk inside the tape (`1RB0RA_1RC0RD_1LD1LC_1RA0LC`) | HY |

None of the 47 is a counter at the tape's edge (no `edge_log`), so the
counter workstreams (CE, SW) do not own them.

**Residue: 145 rows** (`tools/closeouttr/mb/residue.tsv`):

| rows | what | route |
|---:|---|---|
| 84 | low-junk never-QH with no closure.  The sampled failures are hybrids: a slowly growing edge run (`1^k 01 ...`), a `{01, 001}` token counter at one end, or a bounded non-word run the abstraction over-grows | the bouncer + counter hybrid checker (HY), not a larger word list |
| 26 | `spread` junk | none |
| 16 | `longper`: 12 no closure, 4 certified but 7.7 kernel-minutes each | MB if the CI budget allows the 4 |
| 18 | QH | none landed; the wrapped closures grow for the whole budget |
| 1 | `inner_log` | HY |

**Verdict.**  The multi-block RepWL works where BR said it would: bouncers
whose regions have different periods.  On this residue that is a
seventh, because most of the 97 "low-junk bouncers" are hybrids at the
edge.  It stays as a landed tier for other classes: it is cheap to try
(the finder costs about 30 s a row on a miss), and a single-region row
is its L = period special case.

#### 7.4.SPB The SP log counters: CE's lap ports take 775, the ladder the next slice (2026-09-29)

Workstream SPB (batch tag `SPB`), over all 2,233 open SP rows (class SP,
`classes.py shard SP 0 1`).  HY's stretch run (§7.4.HY) had split them
into 1,213 log counters with no block beside them and 1,020 with no
anchor cell or no counter family.  Nobody had run the emitter ports of
§7.4.QE/§7.4.CE (the per-instruction visit gate, the reindexed and S1
nested overflows, the parity split, the 18 inferred alphabets) or CE2's
ladder ports on class SP.  No new Coq: every board is a landed
`LapGlueTr` (`LAPT_*`) or `LadderCheckTr` (`LDRT_*`) board.  Per-row
results: `tools/closeouttr/spb/` (`probe.tsv`, `lap_c*.json`,
`ok_c*.txt`); `tally.py` recomputes every count below.

**The lap route: 791 derive, 775 boarded, `CBT_SPB_00..15, 18..21`.**
`qe_probe.py --tr` over the 2,233 rows (3 jobs, 120 s cap, ~4 h
including a container restart; 1 timeout) derives **791** (35%).
`emit_lapcert.py --tr --emit` on them in chunks of ~200 derives and
compiles **775** (16 misses: the emitter's own anchor walk stops at a
nested-overflow failure for 11, "no interior chain" for 4, and one board
fails `coqc`).  A board compiles in about a second; a 40-row batch in
about 7 s.

| port the board needed | rows |
|---|---:|
| a CE-inferred alphabet, flat | 459 |
| a CE-inferred alphabet, nested overflow (`NestedLapLift`) | 241 |
| a pre-CE alphabet (QE's per-instruction gate 39, reindexed offset nest 36, S1-head nest 22; overlapping) | 75 |
| the parity split | 0 |

`Alph_110_111_111` alone (the `110` = 0 / `111` = 1 counter of §7.4.SP)
carries 436 boards; then `Alph_111_101_1` 84, `Alph_101_111_11` 80,
`Alph_011_111_1` 68, `Alph_10_11_11` 39.  412 boards are certified on
the mirror, 305 at an S1 head.  So the SP log counters were almost all
an alphabet gap: §7.4.SP's "no anchor" (1,325 of the 1,733 SP rows the
emitter saw before) was CE's port 1 on a larger scale, and none of them
needs the parity split.

By HY's split: **755 of the 1,213 log counters** board, and 20 of the
1,020 no-anchor/no-family rows.

**The lap route's residue: 1,442 probe failures + 16 emit misses.**

| best blocker (over every anchor) | HY log counter | HY no anchor/family | all |
|---|---:|---:|---:|
| no anchor | 37 | 609 | 646 |
| nested overflow: no overflow phase at K=6 / no inner family at pow2 j / no boot / no exit / other | 322 | 170 | 492 |
| no interior chain | 79 | 212 | 291 |
| renderer: no lap witness for one instruction | 4 | 8 | 12 |
| timeout (120 s) | 0 | 1 | 1 |

**The ladder route: 351 rows, `CBT_SPB_16..17, 22..31`.**  CE2's
value-family finder, `valfam.py --cap 150` (1 job, then 3, then 4
shards; ~48 s a row, ~6 h wall), over every lap-probe failure and the 16
emit misses: **578 of 1,458 close** (40%).  `sp_ladder_batch.py` emits
an `LDRT_*` board for each (`emit_ladder.py --tr`, pins from a 10^6-step
run) and keeps it only if its closure builds and it compiles: **351
board** (343 lap-probe failures + 8 emit misses), ~1 s a board, a
40-row batch in 30-50 s on CI's cores.  The ladder takes rows the lap
route cannot: of the 343, the lap probe's best blocker was a nested
overflow for 200, "no interior chain" for 137 and "no anchor" for 6.
By HY's split, 193 are log counters and 158 no-anchor/no-family rows.

| ladder outcome (1,458 rows) | rows |
|---|---:|
| closed and boarded | 351 |
| closed, closure not built: interior arm, no chain at any threshold | 103 |
| closed, closure not built: fill arm, no chain at any threshold | 54 |
| closed, closure not built: no phase whose fill anchors reach every instruction | 29 |
| closed, closure not built: phase-0 fill names 3-5 digits but widens by 1 | 17 |
| closed, board fails `coqc` | 24 |
| not closed: families found but none closed | 468 |
| not closed: no value family (no anchor whose counter side decomposes) | 349 |
| not closed: no local rules | 4 |
| not closed: time cap (150 s) | 59 |

The not-built reasons are the ones §7.4.SP met on its six-row sample:
the state level shares the interior- and fill-arm gaps, and the
instruction-specific one (no phase reaching every instruction) is still
the smallest.  Of the 24 `coqc` failures, 4 are a `nat`-typed term the
emitter writes where an expression is expected, and the others fail a
concrete-configuration `reflexivity`; none was investigated further.

**Totals.**  SPB boards **1,126** of the 2,233 open SP rows (50%): 775
lap + 351 ladder, `CBT_SPB_00..31`.  SP open 2,233 -> **1,107**; all
rows (with `main`'s CE2 integration) -> **2,077** of 10,924.

**The residue (1,107), characterised.**  `sp_char.py char` at 1e8 steps
on every residue row (`tools/closeouttr/spb/residue_char.{txt,json}`)
splits it cleanly by the visited extent:

| rows | extent at 1e8 | burst period ratio | what it is | where it stops |
|---:|---|---|---|---|
| 605 | >= 1,000 cells (HY: all no anchor / no family) | 4: 258, 2.25: 183, 9: 38, other 114, 2: 12 | §7.4.SP's doubling bouncers (width w' = 2w + c), not counters | no value family 333, families none closed 272.  `bin/irules` (§7.4.SP) is their route; these are the ones its 200K-step certificates missed |
| 502 | < 200 cells (HY: 257 log counter, 245 no anchor / no family) | 2: 233, other: 123, 4: 123, 1.41: 14, 2.25 / 9: 9 | counters the lap emitter does not derive | ladder closed but not built or rejected 227; families none closed 196; time cap 59; no value family 16; no local rules 4 |

So every SP counter the ports reach is boarded, and the counter
residue is 502 rows in three pieces:

1. **227 ladder closures the emitter cannot close** (interior arm 103,
   fill arm 54, no phase reaching every instruction 29, wide fill 17,
   `coqc` 24).  These are emitter work, not finder work: an
   interior-arm witness (§7.4.SP's "obvious next piece") and a fill arm
   whose chain is not affine in the run length would take most of them.
2. **196 + 16 + 4 rows the finder does not close.**  Over all 502 log
   rows the burst ratio is 2 for 233, 4 for 123 and no clean ratio for
   123, so they are not all binary counters: the ratio-4 rows look like
   base-4 or two-digit-per-overflow counters, and the unclean ones like
   §7.4.CE's Fibonacci and other-radix counters (not checked row by row).
3. **59 time caps**, re-run at 400 s below.

The lap route's own residue is dominated by the nested overflow (492)
and "no interior chain" (291), which is where the ladder took its 343;
its "no anchor" rows still open (640) are the 605 wide rows and 35
counters.

TIME-CAP RE-RUN: IN PROGRESS.

```
python3 tools/closeouttr/classes.py shard SP 0 1 > sp_rows.txt
python3 tools/closeouttr/qe_probe.py sp_rows.txt probe.jsonl --jobs 3 --timeout 120 --tr
tools/closeouttr/spb/drive_emit.sh          # emit_lapcert.py --tr --emit per ~200 derived rows (resumes after a restart)
tools/closeouttr/spb/board_chunk.sh cN      # sp_lap_batch.py --tag SPB, gen, build, checks, stage
tools/closeouttr/spb/verify_head.sh         # the invariant checks on a clean worktree of HEAD
(cd tools/ladder && python3 valfam.py --list lad_sK.txt --cap 150 --json vf_sK.jsonl)   # per shard
python3 tools/closeouttr/sp_ladder_batch.py vf_s*.jsonl --tag SPB --chunk 40
python3 tools/closeouttr/spb/tally.py       # the counts above
```

#### 7.4.BX The small classes: class ED closed, the cube counters need a non-linear liveness (2026-09-29)

Workstream BX (batch tag `BX`), over the small classes of
`dx/char_all.tsv` still open: 89 DN multi-block bouncers (`bouncer` /
`bouncer_part`, hybrid `sqrt+sqrt`: the residue of BR, MB and TI), 29 DN
cube sweep counters (`sweepctr`, shape `cube`: SW's residue), the 8 class-ED
edge rows, and the 3 DN `linear` / `other` rows.  Row lists and per-row
data are in `tools/closeouttr/bx/`.

**Class ED: 8 of 8 boarded, the class is closed (22 of 22).**

| rows | what they are | route | batch |
|---:|---|---|---|
| 6 | `xRB---_xRC---_xRA---_------`: three right-moving instructions on blank tape, the other five undefined | translated cyclers (`tc_find.py`, `dx_tc_batch.py`; period 3, 0.7-0.9 s a probe) | `CBT_BX_00` |
| 1 | `1RB1LD_1RC1RB_1LC1LA_0RC0RD`, **the BBB(4) champion** | blank tail: at step 32,779,478 = `B_close` the tape is blank, the head is in C, and `C0 = 1LC` marches left forever | `CBT_BX_01` |
| 1 | `1RB0LD_1LC0LA_1LA0LC_1RD1RC`, the previous champion | blank tail at step 66,349, `D0 = 1RD` | `CBT_BX_01` |

RepWL at 900 s did not certify the champion ("no cert for A0 at L=5",
11,232 nodes): it quasihalts, and the never-QH tier is the wrong route.
The scanner calls it EDGE because its terminal march runs off the 2^26-cell
tape.  `theories/Counters/BlankTailTr.v` (new, generic, 180 lines) is the
instruction-level twin of `Counters/BlankTail.v`.  After the prefix the
march keeps a blank under the head, so only `(q, S0)` fires from `N0` on.
That gives `NonHalt /\ QHBoundTr B /\ QuasiHaltsTr` for every `B >= N0`
(`q <> StA`).  The prefix runs on `TCyclerN.cstepsN`'s binary fuel.  The
bound `N.to_nat N0 <= 32779478` is discharged by `N_le_dec`, which compares
the binary numerals.  The literal `32779478` stays `Nat.of_num_uint` and is
never forced to 32.8M constructors.  Finder and writer:
`tools/closeouttr/bx_bt_batch.py`.  Compile times (container, 4 cores):
`BlankTailTr.v` ~3 s, `CBT_BX_00` ~5 s, `CBT_BX_01` ~20 s (the champion's
prefix is one `vm_compute`).  `Print Assumptions` shows
`functional_extensionality_dep` only.

**The 29 cube sweep counters: none boarded.**  TI had failed all 29 on "too
many families" at the cap of 120.  `ti_batch.py find` now takes the
exploration limits as flags (`--maxfam --maxleaf --maxsteps --maxna --t0
--plist --force`).  At `--maxfam 600 --maxleaf 3000`, 600 s a row:

| rows | TI verdict | what it is |
|---:|---|---|
| 13 | too many families (at 600) | doubling tapes: `(01)^5 1 (10)^10 0 (01)^20 1 (10)^39 0 (01)^77 ...`, a block count that grows without bound.  They need TI's counter segment (§7.4.TI, the 271) |
| 15 | exploration closes (13-24 families, 20 leaves), no ranking | see below |
| 1 | leaf too long (also at `--maxsteps 40000`) | |

The 15 rows that close are TI's "no ranking" failure, and a wider `P` does
not fix it.  `P` = 5, 8, 9, 12, 18 and 27 all fail, and the node set grows
about 7x per doubling of `P` (82, 434, 2,722, 19,010, 141,442 nodes for
`P` = 2..32).  10 of the 15 are one machine up to `D0`:
`1RB1LA_0RC0RD_1LC0LA_??0RC`, with `D0` the rare instruction.  In
`1RB1LA_0RC0RD_1LC0LA_0LB0RC`, the inner lap `F4 (a, b, c) -> (a+1, b-2,
c+2)` ends on the parity of `b`.  Only the even end fires `D0`, and the next
round's start is affine in `a` and `c`, where `a` has counted the `b/2`
laps.  So the parity at the end of the next round depends on `b mod 4`, the
one after that on `b mod 8`, and so on.  A node that keeps values mod a
fixed `P` cannot tell whether the next round fires, and the abstract graph
has a `D0`-free cycle at every `P`.  The concrete dynamics has no such
cycle.  On the certificate's own leaf maps, from 3,000 random starts in
every family, `D0` fires before the round-end family is visited 7 times
(starts below 2,000) or 4 times (starts below 10^6).  The argument this
needs is 2-adic, like a Collatz-type map: a `D0`-free run is bounded by a
2-adic valuation of the start values, which is finite for each start but
not bounded over all of them.  A certificate for it would be a
lexicographic ranking `(level, nu_2(e), V)` per node.  Here `e` is affine,
every non-firing edge inside a level satisfies `2^j e' = a e`
coefficient-wise with `a` odd, `nu` drops when `j >= 1`, and `V` must drop
when `j = 0`.  That is checkable coefficient-wise like the present
rankings, and sound by Gauss's lemma.  A prototype MILP finder (big-M over
15 ratio options per edge) found no such certificate in 300 s.  The
non-firing node graph at `P = 1` is one strongly connected component (16
nodes, 20 edges) that includes the paths after the fire.  On those paths
the exact ratio fails (the edge `F12 (0, y) -> F11 (2, y)`), and splitting
small values off every variable (`--force 2`: 53 nodes, still one
component) does not separate them.  So the 2-adic argument needs a
per-path invariant, not just a per-node one.  This
is research, and it likely also covers the 24 "no ranking" rows of §7.4.TI.

**The 89 multi-block bouncers: none boarded.**

| route | result |
|---|---|
| TI, `--maxfam 400 --maxleaf 3000 --maxsteps 20000`, 300 s | 86 too many families, 3 leaf too long |
| (earlier) RepWL 900 s with the ladder and wide L (BR), rank tier at window 7 (BR), multi-block RepWL at 240 s (MB) | all missed |
| n-gram rank tier `rk:8:0` and `ng:7:0`, 600 s, a 12-row sample plus the 3 misc rows | NGRESULT |

Read by hand, the clean-looking ones (e.g. `(0111)^a 0^4 (1100)^b (110)^c`,
`(01001)^a 0 1^4 (01011)^b`) have a middle region whose phase changes
between snapshots (`1100` at 1M and 4M steps, `1001` at 8M), and junk
cells at the edge that grow slowly.  They are §7.4.MB's "hybrids at the
edge": a word list does not describe them, and a block-family glue needs
the counter segment.

**The 3 `linear` / `other` rows: none boarded.**  Translated cyclers (2M
steps), TI (2 too many families, 1 leaf too long), multi-block RepWL at
900 s with `--pmax 32` (no closure, 204-216 candidates each) and the
n-gram sample above all miss.  `1RB1RC_1LC0RA_0LB0LD_1LA1LD` is a
multi-block tape of growing `1^n` and `(01)^n` runs (extent 34,312 at 1e8),
and the other two have tens of thousands of junk cells.

**Yield: 8 of 129 boarded** (`CBT_BX_00..01`).  All rows: 2,772 ->
**2,764**.  Residue: 121 rows (`bx/bnc.txt`, `bx/cube.txt`, `bx/misc.txt`).
Two routes would take most of it, and both are research: TI's counter
segment (13 cube rows and most of the 89 bouncers, which TI reports as
"too many families") and the 2-adic lexicographic liveness above (15 cube
rows, and probably TI's 24).

## 8. What we deliberately do NOT redo

* The state-level theorem and its census `.vo` stay frozen and untouched;
  the new development builds beside, not on top.
* No strengthening of in-walk tiers to rescue deferrals (PLAYBOOK Rule 4
  survives verbatim: prove machines, keep the walk light).
* No hand-porting of generated layers (`Machines/` ~2.6M lines,
  `Closeout/CB_*`, census lists): they regenerate from tools once the
  checker layer lands.
