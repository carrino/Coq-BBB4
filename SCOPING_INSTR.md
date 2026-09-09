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

## 8. What we deliberately do NOT redo

* The state-level theorem and its census `.vo` stay frozen and untouched;
  the new development builds beside, not on top.
* No strengthening of in-walk tiers to rescue deferrals (PLAYBOOK Rule 4
  survives verbatim: prove machines, keep the walk light).
* No hand-porting of generated layers (`Machines/` ~2.6M lines,
  `Closeout/CB_*`, census lists): they regenerate from tools once the
  checker layer lands.
