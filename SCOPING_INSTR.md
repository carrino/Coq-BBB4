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
rows (with `main`'s CE2 integration) -> **2,077** of 10,924.  The box's
SP2 ladder run (integrated in #171) boarded many of the same rows.
`closeouttr_boarded.tsv` credits a row to its alphabetically first batch
(`CBT_SP2_*` sorts before `CBT_SPB_*`), so it credits only 643 rows to
SPB.  SP2 also took 14 of the 502 log-width residue rows below.  After
the merge, SP has **1,093** open rows and all classes 1,957.

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
3. **59 time caps.**  Re-run at `--cap 400` (4 jobs, ~2 h): none closes; 37
   time out again and 22 find families but close none.

The lap route's own residue is dominated by the nested overflow (492)
and "no interior chain" (291), which is where the ladder took its 343;
its "no anchor" rows still open (640) are the 605 wide rows and 35
counters.

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

#### 7.4.SPW The wide SP rows: the missing v5c port, then the block-family glue (2026-09-30)

Workstream SPW (batch tag `SPW`), over the 605 wide rows of §7.4.SPB's
residue.  These are the class-SP rows whose visited extent at 1e8 steps
is at least 1,000 cells.  Their burst-period ratios are 4 (254 rows),
2.25 (183), 9 (33), 2 (8) and other (127), as grouped by
`tools/closeouttr/spw/tally.py`.  The prompt's 258/183/38/12/114 used a
slightly different binning.  Per-row data is in `tools/closeouttr/spw/`.

**Why the 200K-step irules sweep missed them.**  It is mostly not the
budget.  The row list is `spw_rows.txt`.  On a 40-row sample
(`sample40.txt`, spread over the ratio groups; `sample_table.tsv`),
`bin/irules --why` was run at 2M, 10M and 50M steps, one process per row
under a timeout (`run_irules.sh`).  Each certificate was then probed with
one `coqc` under a timeout.

| budget | certificates | kernel-accepted | failures (`--why` stage) | timeouts | CPU |
|---|---:|---:|---|---:|---:|
| 2M | 16 | 16 (6 need v5c) | `nofit` 23, `noproof` 1 | 0 | 0.5 h |
| 10M | 16 | 16 | `nofit` 20, `noproof` 1 | 2 (30 min) | 2.2 h |
| 50M | 16 of 37 finished | 16 | `nofit` 20, `noproof` 1 | 3 unfinished (container reclaimed) | 1.0 h for the 37 |

By ratio, every ratio-9 and ratio-2 row certifies at 2M, and so do half
of the ratio-4 rows.  No ratio-2.25 row certifies at any budget, and
only a few "other" rows do.  10M adds one row over 2M, and 50M none so
far.  The failures are structural (`nofit`: the anchor sequence is not
one affine map), so the budget is not what limits these rows.  Two gaps
on the Coq side were:

1. **The engine.**  §7.4.SP probed every certificate with
   `MetaBlkPfxTr`, the plain replay.  On the SPW sample, 6 of the 16
   certificates at 2M are ones that BBB's `bin/verify` passes but whose
   plain replay stalls at a block boundary: 5 probe "false" after
   ~40 s, 1 times out.  §7.4.SP's 9 "false" and 64 "timeout" rows are
   probably the same gap, but they were not re-probed.  The state-level
   `MetaBlkPfxV5c` gets past those stalls: it closes the block table,
   re-blocks after every step and uses the multi-run cell-stream
   end-match.  But it had no transition-level port.  On the 2M sample
   it accepts all 16 certificates (1-3 s each), including the 6 that the
   plain engine rejects after burning its fuel.
2. **The v4 matrix meta map.**  `bin/irules` also emits certificates
   with 2-3 meta variables and a map x -> M x + c (`nvar`, `mmrow`,
   `xmin`, `x0`, `tplrunmv`).  `sp_batch.py`'s parser skipped those
   lines, so such a certificate read as a v1 certificate with empty
   templates and failed.

**New Coq** (axioms: `functional_extensionality_dep` only):

* `Checkers/IRules/MetaTileTr.v`: `meta_tile_neverqhtr`, the
  transition-level recurrence argument of the irules meta checkers.  It
  needs an anchor, a cycle from every admissible parameter to the next
  one firing exactly the set F, and the prefix gate.  It is stated once
  over an arbitrary parameter type.
* `Checkers/IRules/MetaBlkPfxV5cTr.v`: `MetaBlkPfxV5c` at transition
  level (`irulesblkpfx_check_neverqhtr_v5c_sound`).  It proves only the
  anchor and the cycle.
* `Checkers/IRules/MetaBlkPfxMVTr.v`: the matrix meta map, for both
  engines (`irulesblkmv_check_neverqhtr{,_v5c}_sound`).  The rule
  engine, `breplayKP`/`breplayRB` and the end-matches are all generic in
  the bounds vector and the valuation, so only the scalar layer is new.
  A valuation replaces `fun _ => K`, `mstep` gives the next valuation,
  and `mvwant_shift` says the want template is the start template with
  each run's variable replaced by its row.  `mstep_bge` shows the bounds
  are invariant, given M >= 0 and xmin <= M xmin + c.

`sp_batch.py` now parses v4 certificates.  Its `probe` tries the v5c
engine first and then the plain one (`--engines`), recording the engine
per row, and `batch` writes the matching Requires.  A plain-engine batch
still gets the old Require line byte for byte.  Every certificate in the
SPW sweeps was accepted under v5c.

**The routes over all 605 rows:**

| outcome | ratio 4 | 2.25 | 9 | 2 | other | all |
|---|---:|---:|---:|---:|---:|---:|
| boarded, `TriGlueTr` (`CBT_SPW_01..14`) | 45 | 143 | 22 | 1 | 49 | 260 |
| boarded, irules at 2M (`CBT_SPW_00, 15..18`) | 77 | 0 | 10 | 7 | 6 | 100 |
| open, TriGlue "no ranking" | 61 | 36 | 1 | 0 | 56 | 154 |
| open, TriGlue "too many families" | 66 | 4 | 0 | 0 | 14 | 84 |
| open, TriGlue "leaf too long" | 5 | 0 | 0 | 0 | 2 | 7 |

* **irules at 2M** went over the first 118 rows (23 certificates,
  `CBT_SPW_00`), then over the 322 rows TriGlue leaves (77 certificates,
  `CBT_SPW_15..18`).  Every certificate was accepted.  A row costs under
  a second when it fails at the fit, and up to minutes when the prover
  runs.  The 600 s timeouts (27 of 402 rows) are three quarters of the
  5.6 CPU-hours.
* **The block-family glue** (`ti_batch.py find`, §7.4.TI) was the big
  surprise.  It was run over the 572 rows open after the first two
  batches, at about 20 s a row on one core.  It returned 250
  certificates: no ranking 164, too many families 149, leaf too long 9.
  Every certificate compiled.  TriGlue's dispatch trees split a family
  variable by residue, which is exactly what irules' single affine map
  cannot do.  So it takes 143 of the 183 ratio-2.25 rows, which are
  Collatz-like 3/2 maps.  One example is `1RB1LB_0RC0LA_1LC0LD_1RA1LD`,
  whose tape at every C0 fire is `1^a 0 [C0] 1^(2j)`.  For a odd it
  maps to ((3a-1)/2, j+1), and for a even to (3(a+2j)/2 + 3, 0).  Both
  branches fire every instruction.
* **Tried, nothing taken.**  The n-gram rank tier at windows 6, 7 and 8
  (`ng_batch.py probe --rungs rk:6:0,rk:7:0,rk:8:0 --all`, 120 s per
  probe) went over the 24 sample rows irules leaves at 2M.  None
  certified: 21 false, 7 timeouts over 28 probes.  TriGlue at larger
  residue moduli (`--plist 1,2,3,4,6,8,12`) on 12 no-ranking rows
  certified none.  `RepWLMBTr` and the hybrid glues were not run.  The
  open rows have no counter beside the bouncer (HY's split already
  marks all 605 "no anchor / no family"), and `RepWLMBTr` is the RepWL
  abstraction, which §7.4.SP showed has a genuine rare-instruction-free
  cycle on these rows.

**Totals.**  SPW boards **360** of the 605 rows (`CBT_SPW_00..18`),
which is 260 TriGlue and 100 irules.  All classes: 1,830 -> **1,470**
open.  Compile times on the container (4 cores, loaded): irules batches
of 25 take 20-60 s, TriGlue batches of 20 take 11-48 s.  On CI's
`closeout-changed` job each batch takes 1-3 s.  `ci_costs.tsv` carries
the slowest of each kind at 80-110 s.

**The residue (245), characterised.**

1. **Multi-block doubling tapes (84, TriGlue "too many families").**
   The number of blocks grows by one per burst, so no finite family set
   exists.  Examples: `1RB1RA_1LC0RA_1LD1LC_1RD0LB` at D0 has
   `1^(2|3) (0 1^2)^n 0 1^m`, where the last block runs 4, 6, 10, 14,
   22, 30, 46, 62 and one `0 1^2` is added every other burst.
   `1RB1LD_1LC0RB_1RA1LA_1LC0LC` has the nested
   `1^2 0 1^2 0 1^4 0 1^2 0 1^8 0 ... 1^(2^n-1) 0 1`, and
   `1RB0LA_1LC1RC_1LA1RD_0RB0RB` has
   `1 0 1^(2^n-1) 0 1^2 0 1^(2^(n-1)-1) ...`, where a new doubled block
   is prepended every burst and the rest is untouched.  A checker for
   these needs an inductive family over a list of blocks: a regular
   invariant on the block sequence plus a meta rule for the new head
   block.  Nothing landed does that.
2. **No ranking (154).**  The families close, but some instruction
   (usually the rare one) has no affine ranking at moduli up to 12.  On
   the rows looked at, the extent follows an irregular 3/2-type map
   (`0RB1LD_1RC1RB_1LA1LC_0RD0LA`: 14, 114, 278, 652, 990, 1,498, ...;
   `1RB1LA_1LC0RC_1LC1LD_0RA0LA`: block 36, 57, 135, then extents
   457, 693, 1,579, ...), and the
   rare instruction fires only in some parity branches.  Its recurrence
   is then a statement about the orbit's parity sequence, the
   Collatz-type obstacle of the cryptids.  This is a characterisation of
   a few rows, not a proof that all 154 are like this.
3. **Leaf too long (7):** a TriGlue leaf chain over its step cap.
4. **Not run to the end here: irules at 10M over the 245.**  The
   container is reclaimed when the session idles, and background runs
   die with it (twice on 2026-09-30).  26 of the 245 rows finished, all
   `undecided`.  On the sample, 10M added one row over 2M.  To finish it
   on the box, see the commands below; they resume from
   `tools/closeouttr/spw/all10M/res` if that directory is copied over.

**Loop** (container; `bin/irules` from carrino/bbb, `make bin/irules`):

```
cd tools/closeouttr/spw
./run_irules.sh 2000000 600 open.txt all2M 3          # one irules per row, resumable
cd ../../..
python3 tools/closeouttr/sp_batch.py probe tools/closeouttr/spw/all2M/certs probe.tsv --jobs 3 --timeout 90
python3 tools/closeouttr/sp_batch.py batch probe.tsv --tag SPW --chunk 25
python3 tools/closeouttr/ti_batch.py find open.txt ti.jsonl --jobs 1 --timeout 180   # needs numpy + scipy
python3 tools/closeouttr/ti_batch.py batch ti.jsonl --tag SPW --chunk 20
python3 tools/closeouttr/spw/tally.py                 # the route table above
python3 tools/closeouttr/spw/sample_table.py          # the budget sample
```

**For the 14-core box** (the passes this container could not finish):

```
cd tools/closeouttr/spw
comm -12 <(sort spw_rows.txt) <(sort ../../../closeouttr_remaining.txt) > open.txt
./run_irules.sh 10000000 1200 open.txt all10M 12      # ~245 rows; ~1-2 h wall (~10% hit the 20 min timeout)
./run_irules.sh 50000000 3600 open.txt all50M 12      # optional; ~2-3 h wall, expected yield ~0 on the sample
cd ../../..
python3 tools/closeouttr/sp_batch.py probe tools/closeouttr/spw/all10M/certs p10.tsv --jobs 12 --timeout 90
python3 tools/closeouttr/sp_batch.py batch p10.tsv --tag SPW --chunk 25
```

Wall times: TriGlue took about 2 h on one core for 572 rows.  irules at
2M took about 1 h on three cores for 322 rows.  A 50M pass over the
residue is bounded by its timeouts: at 3,600 s a row, about 245 x 0.1 x
1 h / 14 cores, so 2 h on the 14-core box, since roughly 10% of rows
time out.  It is not worth it on this evidence.

#### 7.4.BX The small classes: class ED closed, the rank tier at window 8 takes 12 bouncers, the cube counters need a non-linear liveness (2026-09-29)

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

**The 89 multi-block bouncers: 12 boarded, by the rank tier at window 8.**

| route | result |
|---|---|
| TI, `--maxfam 400 --maxleaf 3000 --maxsteps 20000`, 300 s | 86 too many families, 3 leaf too long |
| (earlier) RepWL 900 s with the ladder and wide L (BR), rank tier at window 7 (BR), multi-block RepWL at 240 s (MB) | all missed |
| n-gram tier `ng:7:0`, 600 s, a 12-row sample | 0 of 12 (all false in 3-30 s) |
| **rank tier `rk:8:0`** (`DecideTr.rank_tier_tr tm 8 0 200000 512`), 600 s, all 89 | **12 certified** (4 of the 12-row sample, 8 of the other 77); 40 false, 37 timeouts |
| the same rung on the 29 cube counters | 0 (all false) |

The 12 are boarded in `CBT_BX_02..08` (2 rows a batch, 1 in `BX_08`).  The
kernel re-runs the search: 33-119 s a row in the probe, and 1.7-3.4 min a
batch in the container with 3 probes running.  All seven batches are in
`ci_costs.tsv`.  Window 7 had taken none of these 89 rows (§7.4.BR's 4 hits
were other rows), so window 8 is the rung that pays here.  37 rows time out
at 600 s, so a longer budget or window 9 is the next cheap thing to try on
this class.

Read by hand, the clean-looking ones (e.g. `(0111)^a 0^4 (1100)^b (110)^c`,
`(01001)^a 0 1^4 (01011)^b`) have a middle region whose phase changes
between snapshots (`1100` at 1M and 4M steps, `1001` at 8M), and junk
cells at the edge that grow slowly.  They are §7.4.MB's "hybrids at the
edge": a word list does not describe them, and a block-family glue needs
the counter segment.

**The 3 `linear` / `other` rows: none boarded.**  Translated cyclers (2M
steps), TI (2 too many families, 1 leaf too long), multi-block RepWL at
900 s with `--pmax 32` (no closure, 204-216 candidates each), `ng:7:0`
(false) and `rk:8:0` (all three time out at 600 s) all miss.  `1RB1RC_1LC0RA_0LB0LD_1LA1LD` is a
multi-block tape of growing `1^n` and `(01)^n` runs (extent 34,312 at 1e8),
and the other two have tens of thousands of junk cells.

**Yield: 20 of 129 boarded** (`CBT_BX_00..08`: 8 ED, 12 bouncers).  All
rows: 2,772 -> **2,752**.  Residue: 109 rows (77 bouncers, 29 cube
counters, 3 misc; the lists are `bx/bnc.txt`, `bx/cube.txt`, `bx/misc.txt`
less the boarded rows, per-row verdicts in `bx/ng_rk8.json`).  The cheap
next step is `rk:8:0` or `rk:9:0` at a longer budget on the 37 bouncers
that timed out.  Beyond that, two routes would take most of the residue,
and both are research: TI's counter segment (13 cube rows and most of the
bouncers, which TI reports as "too many families") and the 2-adic
lexicographic liveness above (15 cube rows, and probably TI's 24).

#### 7.4.HY2 HY's residue: a hybrid glue over any positional counter with a top table, 54 boarded (2026-09-29)

Workstream HY2 (batch tag `HY2`), over the DN rows still open whose
`dx/char_all.tsv` kind is `bouncer_part` with hybrid `sqrt+log` (282),
`sqrt+fix` (26) or `other` (8): 316 rows (`tools/closeouttr/hy2/rows.txt`).
The 18 QH rows of these hybrid kinds and the `sqrt+sqrt` rows were not
touched.

**The sample (20 rows, by eye).**  Only about 5 are a counter beside ONE
growing block (base 4 with 3-cell digits and a 3-cycle at the junction; a
binary counter whose top is a 10-cell word; a counter end that shifts into
a `(10)^k` buffer at each overflow).  About 11 are tapes whose block COUNT
grows (doubling `010110 1^4 0 1^8 0 1^16 ... 0`, x4 runs
`(001)^12 00010 (001)^52 00010 (001)^213`), and the rest two-block transfer
bouncers (`1^216 0 1^403`, one block +2 and the other -1 a round).  A
block census at 2.5e5 / 1e6 / 4e6 steps over all 316
(`hy2/blocks.jsonl`): one long block and a short end 125, block count
growing 75, several blocks with a fixed count 116.  So only the first
group has a counter end at all, and it is the target.

**What the counter ends are.**  Reading the short end at consecutive
anchors against every (digit width 1-6, base 2-4) and fitting the values:
of the 54 rows boarded below, 26 are base 3 and 23 base 4 (3- or 4-cell
digits, e.g. `001/101/000/100`), 5 binary.  None of these is `E`'s shape,
and not because of the digits alone: in 43 of the 54 the counter has NO
top digit, only a terminator (all digits at `b - 1` widen to one more
digit of `0`, the bijective numeration), and in 11 the top steps through
two words before the counter widens.  That is what HY's residue note
called "a digit under the MSB written differently until the next
overflow": the top is a small cycle of words, not a digit.  The ladder's
value families do not fit either: their numeration is on the whole tape,
with no opaque block tail.

**The checker** (`theories/Counters/HybridCtrTr.v`, a sibling of
`HybridGlueTr`; `Print Assumptions`: `functional_extensionality_dep`
only).  The counter is a pair `(low, tv)`: low digits in base `b`, one
word each (`D`), and a top value `lo <= tv < hi` read through a word table
(`T`).  Its word is `concat (map D low) ++ T tv`, its value the RANK
`(hi - lo) G |low| + vl low + b^|low| (tv - lo)` with
`G k = 1 + b + ... + b^(k-1)` (successor, injectivity and existence are
proved once, `canon_succ`, `canon_inj`, `canon_exists`).  The increment
is one generic carry chain per shape: per digit `d < b - 1`
(`Dm^j D d X -> D0^j D(d+1) X`, `X` opaque), per top step
(`Dm^j T tv -> D0^j T (tv+1)`), and the overflow
(`Dm^j T(hi-1) -> D0^(j+1) T lo`).  `hi = b lo` is a positional counter
with a top window, `lo = 0, hi = 1` a terminator-only counter, and
`b = 2, lo = 1, hi = 2` is exactly HY's `(A, B, C)`.  Each carry case
names an EXIT (its own mid and sweep), so an overflow that leaves the
counter in another state is expressible; the lap's block count follows
the exit taken.  Sweep fires are reached through a carry family (the
rank families of interior and top shapes, whose phase mod `L` the checker
computes; the top family's phase by the recurrence `y (j+1) = (hi - lo) +
b y j`, so no large power is built).  The phase list, the two-index
anchor and the sweep half are HY's.  A row is one line,
`apply coversTr_nqh, (hc_sound_nqh _ (mkHCC ...))` (`_mirror` when the
counter is on the right); a corrupted boot index fails to compile.

**The finder** (`tools/closeouttr/hy2_batch.py`, on `hy_batch.py`'s runs,
anchors, blocks and chain search).  It reads `(Lpre, b, D)` and a first
rank off the anchors (rejecting fits whose first rank is below `b^2`:
a first prototype without that floor read overfitted "families" with first
values of 4-9), then
LEARNS the top cycle by simulation: from an observed top word it runs one
counter half from a constructed anchor and reads what top word the carry
leaves; when that is `D0` followed by a word already met, the cycle is
closed and its length is `hi`.  It refits the rank against the anchors,
reads the mid off interior laps only (an overflow lap may leave by another
exit), derives one carry chain per case (and the case's own exit by
simulation when the main mid does not fit), the sweeps, the boot and the
fire witnesses.  240 s a row, then 600 s for the timeouts; ~1.3 h for the
316 at 4 jobs.

**Yield: 54 of 316**, `CBT_HY2_00` (38) and `CBT_HY2_01` (16), all 54
compile (~30 s a batch).  All rows: 2,772 -> **2,718**.

| certificate shape | rows |
|---|---:|
| base 3 / 4 / 2 | 26 / 23 / 5 |
| top cycle length `hi - lo` = 1 (terminator only) / 2 | 43 / 11 |
| digit width 3 / 4 / 2 cells | 41 / 8 / 5 |
| one phase / four phases (block unit rotating at the junction) | 46 / 8 |
| block unit 3 / 2 / 4 cells | 45 / 8 / 1 |
| counter on the right (certified on the mirror) | 28 |
| exits per phase | 1 on all 54 |

The boots are short (the latest at step 218).  No boarded row needed a
second exit; the exit mechanism is there for the two-state overflows seen
by hand (below), which fail earlier.

**Residue (262)**, per row in `tools/closeouttr/hy2/residue.tsv`:

| rows | tape | where it stops | what it is |
|---:|---|---|---|
| 75 | block count grows | no anchor 48, no family 27 | doubling / x4 multi-block tapes: TI's "too many families" rows.  The part that is not blocks is a list of blocks of exponential length, not a counter end: it needs a block-list numeration (a counter whose digits are blocks), not a wider alphabet |
| 116 | several blocks, count fixed | no anchor 56, no family 57, other 3 | two-block transfer bouncers and three-block sweeps (TI's and BX's shapes); no counter end |
| 36 | one long block | no counter family | read by hand: two blocks of one unit, one growing linearly and one slowly (a UNARY counter, e.g. `1RB0LC_1LC0RA_1RA1LD_1LA1LA`: `(011)^n ... (011)^k`), or a counter that shifts its low end into a `(10)^k` buffer at each overflow so no fixed anchor cell exists (`0RB0LB_1LC1RA_0LD0LC_1RD1LB`) |
| 19 | one long block | later: no top cycle 7, no mid 6, no block 4, other 2 | the two-lap overflow: `0RB0LC_1LC1RD_1LA1LB_1RC0RB` (binary, 2-cell digits `01/11`) at an all-ones counter first writes a marker past the MSB and sweeps the block WITHOUT carrying (exit state 2 instead of 0), and carries on the next lap.  A lap that does not increment is outside the one-rank-per-lap anchor; it needs a non-incrementing top step (a top word that keeps the low digits) in the numeration |
| 14 | one long block | timeout at 600 s | families read; the chain searches do not finish |
| 2 | one long block | no anchor | |

**Next.**  (1) The two-lap overflow: a top step that keeps the low digits
(rank arithmetic changes: the widths get extra states); 19 rows plus some
of the 14 timeouts.  (2) The 75 growing-count rows are one family by eye
(a counter whose digits are blocks, `1^(2^k)`); a checker for them is the
TI residue's "counter segment in the family language", in its block-list
form.  (3) The unary-counter rows are a two-block sweep with a slow block,
closer to SW's two-index glue than to a counter.

```
python3 tools/closeouttr/hy2_batch.py find tools/closeouttr/hy2/rows.txt hy2/find1.jsonl --jobs 4
HY2_BUDGET=600 python3 tools/closeouttr/hy2_batch.py find hy2/timeouts1.txt hy2/find2.jsonl --jobs 4
python3 tools/closeouttr/hy2_batch.py batch hy2/find1.jsonl hy2/find2.jsonl --tag HY2 --chunk 50
```

#### 7.4.BL The block-list rows: what they are, a lattice TriGlue finder, 19 boarded (2026-09-30)

Workstream BL (batch tag `BL`), over the still-open rows whose tape is
blocks plus something that grows.  There are 680 rows
(`tools/closeouttr/bl/rows.txt`):

* 281 DN/QH bouncer + counter hybrids (`dx/char_all.tsv`: `bouncer_part`,
  hybrid `sqrt+log` / `sqrt+fix` / `other`; HY2's residue);
* 77 DN multi-block bouncers (`sqrt+sqrt`; the residue of BR, MB, TI and
  BX);
* 322 wide SP rows that TriGlue left as "too many families" (149), "no
  ranking" (164) or "leaf too long" (9) (SPW's residue).

While this ran, SPW boarded 75 of these by irules at 2M steps
(`CBT_SPW_15..18`, §7.4.SPW).  The pure counters (LE) and the 29 cube
sweep counters were not touched.

**The sample, and the whole set classified.**  About 40 rows were read
by hand: tape snapshots at 1e5 to 8e6 steps, the last-visit age of every
cell, the tape at every fire of the rare instruction, and the tape at
every head turn through one round.  Then
`tools/closeouttr/bl/classify.py` (with `bl_sim.c`) measured two things
on all 680 rows (`bl/classify.tsv`):

* whether the rarest instruction fires at a REGULAR ratio (the last five
  fire-interval ratios agree within a factor 1.3), IRREGULARLY, or at
  sweep rate (every instruction fires 64+ times in 1e8 steps);
* whether the number of blocks grows between the rare fires nearest 1e6
  and 6.4e7 steps.

| rows | group | fires | block count | what they are (by hand) |
|---:|---|---|---|---|
| 157 | SPW | irregular | 143 flat, 14 grow | **Collatz-like rounds.** A two-block transfer ends on a residue, and only one residue case fires the rare instruction (`0RB0LB_1RC1LB_0RD0RD_1LD1LA`: C0 at rounds of 9, 15, 24, 90, 207, 312, 1062).  Many rows share one non-periodic ratio sequence (1.38, 7.33, 5.07, 12.96, 1.37, ...).  This is BX's 2-adic liveness problem; no per-node ranking or relational invariant sees why the firing case recurs |
| 81 | SPW | regular | flat | doubling / x4 bouncers with a bounded block count.  This group is where TriGlue, or irules at 2M, closes.  Of the 81, SPW's irules batches and `CBT_BL_*` boarded 38; the rest are TriGlue "too many families" (below) |
| 42 | SPW | regular | grow | **block-list counters** (below) |
| 42 | SPW | sweep rate | flat | wide one- and two-block rows whose rare instruction fires every sweep |
| 151 + 46 | hybrids + bouncers | sweep rate | grow | block-list counters, and x4 lists such as `(100)^197 001 (010)^50 (0)^3 1 (010)^13 ...` |
| 130 + 31 | hybrids + bouncers | sweep rate | flat | HY2's single-long-block shapes (the two-lap overflow, unary counters, a low end that shifts into a `(10)^k` buffer), long-period blocks, and irregular "spread" tapes |

**The block-list counters are relational.**  `0RB1LB_1RC0LD_1LA0RD_1RA1LD`
at every C0 fire is exactly

    (1)^(2^k+1) 0 (1)^(2^(k-1)+3) 0 ... 0 (1)^11 0 (1)^7 0 (1)^5 0 (1)^4 (01)^3 [C0]

so `b_(i+1) = 2 b_i - 3`.  Within a round the list is a binary counter.
The digits are the separators (`0` / `010`), and each carry is a
two-block transfer between NEIGHBOURING blocks, whose length it
compares: `(1)^21 0 (1)^41 -> (1)^41 0 (1)^21`, in steps of the top
block's width.  The first phase of the round, a leftward sweep, does
cross every item the same way (`(1)^n 0 -> (1)^n 0` shifted one cell).
But the carries do not, so a list segment of FREE items (a Kleene star
of `u^(c + x_i) w`, crossed item by item) does not close.  The same
holds for the separator-digit lists `00100 (1)^3 00 (1)^7 00 (1)^15 0
(1)^31 ...` (`0RB0LB_1LC0RD_1LA1RB_1LC1RD`: `L_(i+1) = 2 L_i + d_i`) and
the halving lists `(1)^932 0 (1)^612 010 (1)^306 0 (1)^155 ...`.  None
of the sampled lists has a frozen history (a tail never revisited):
`lastvis` shows every block revisited at a rate halving along the list.
So piece (a), a block-list numeration, is a checker whose segments carry
a list of blocks WITH an affine recurrence between neighbours
(`b_(i+1) = a b_i + d_i`, `d_i` a finite digit), and whose carries are
proved by induction along the list.  That is a new glue with its own
liveness, and it is research: nothing landed here.

**What the existing checkers take, with wider parameters.**

| checker | run | result |
|---|---|---|
| `TriGlueTr` via the new finder `bl_ti.py` (below) | all 680; t0 3000 / 12000 / 50000 x start lattice 0 / 1, 240 s a row, 4 jobs, ~3.5 h | **50 certify**: 10 hybrids, 40 SPW.  38 of the SPW ones were boarded meanwhile by SPW's irules, so 14 are new (`CBT_BL_00`, `CBT_BL_04`) |
| the same, `--maxfam 300 --plist 1,2,3,4,6,8,12`, 400 s | the 63 open REGULAR rows | 0 |
| `RepWLMBTr` (`mb_cert_find.py --pmax 64`, 300 s) | the 18 hybrids whose tape is at least 50% one period of 7-64 cells; MB never tried them | **3 certify** (15.8K-20.6K nodes), `CBT_BL_01..03` |
| rank tier `rk:4:0`, `rk:5:0` (`ng_batch.py probe`, 120 s) | the 322 SPW rows; SP was never put through the rank tier (§7.4.NG probed DN only) | 0 of 322 at window 4, and 0 of 63 at window 5 (57 false, 6 time-outs) before it was stopped |
| `HybridCtrTr` (`hy2_batch.py`, `HY2_BUDGET=1800`) | the 15 HY2 rows that timed out at 600 s and are still open | **2 certify** (`1RB1RC_0LC0LB_1RD1LB_0RA0LA` and `..._0RA0RB`, `CBT_BL_05`); 10 no counter family, 1 no top cycle, 2 time out again |

**The finder** (`tools/closeouttr/bl_ti.py`; untrusted, on top of
`ti_batch.py`, no new Coq).  TI gives each family variable the domain
`[lb, oo)`.  On a doubling bouncer that is what makes the exploration
diverge.  A block that is always `2 mod 4` long at a family's anchor is
explored at every length.  The odd lengths, which the machine never
produces, open new block shapes (`(1)^a 0 (10)^b (1)^c (01)^d ...`), and
those open more, until the cap (`1RB1RC_0LC1RA_1LA1LD_1LA0LC`: TI "too
many families" at any cap, `bl_ti` 6 families).  Here a family variable
is a LATTICE `c + g*x`, and TriGlue's exponents are affine, so the
checker takes it unchanged:

1. **A concrete pass.**  From the boot, follow the real run leaf by
   leaf through TI's own leaves (3,000 leaf steps).  Explore generically
   only the families the run reaches, and record the exponents met in
   each.  The seed of a variable is `c` = the least value met and `g` =
   the gcd of the differences.
2. **The exploration**, TI's, with the seeds.  A leaf landing at `e(z) =
   e0 + sum m_i z_i` widens the target to `c' = min(c, e0)`, `g' =
   gcd(g, m_i, e0 - c)` and re-explores it.  The target value is
   `(e(z) - c') / g'`.  Lattices only coarsen.
3. Rankings and every replayed check are TI's.  A row is one
   `tri_sound` line, exactly as in `CBT_TI_*`.

A variable seen once starts as the one value (`G0 = 0`) or as `[c, oo)`
(`G0 = 1`), and the finder tries both at each boot time.  Where it
fails, the failure is one of two kinds.  The first is `G0 = 0` "leaf
too long": the families of a growing tape are each met once, so their
blocks stay concrete.  The second is `G0 = 1` "too many families": the
block count really grows.  A mixed start (constant only for families
the pass met) gained nothing on a 24-row sample of those failures.

**Yield: 19 rows** in `CBT_BL_00..05`, all kernel-checked (container, 4
cores, under load):

| batch | rows | route | compile |
|---|---:|---|---:|
| `CBT_BL_00` | 6 | `TriGlueTr`, lattice finder (4-96 families; boots at 3000, 12000, 50000) | 45 s |
| `CBT_BL_01` | 1 | `RepWLMBTr`, 20-cell words (`1RB0LA_1LC0RD_1LA0LC_1RB0RD`) | 656 s |
| `CBT_BL_02` | 1 | `RepWLMBTr` (`1RB0RA_1LC0RA_1LD0LC_1RB0LD`) | 378 s |
| `CBT_BL_03` | 1 | `RepWLMBTr` (`1RB0RA_1LC0RB_1RA0LD_1LC0LD`) | 373 s |
| `CBT_BL_04` | 8 | `TriGlueTr`, lattice finder | 45 s |
| `CBT_BL_05` | 2 | `HybridCtrTr` (`hy2_batch.py` at `HY2_BUDGET=1800`) | 35 s |

`CBT_BL_00..03` are in `ci_costs.tsv` at about twice the container time.
With them, `ci_shard.py --plan 6` keeps the slowest shard at `CBT_BR_02`
alone (2,764 s).  `Print Assumptions` on `cv_BL_00_0000` and
`cv_BL_04_0000` shows `functional_extensionality_dep` only.

**Residue: 586 of the 680 rows are still open** (75 were boarded by SPW,
19 here).  Per-row verdicts are in `bl/find1.jsonl`, classes in
`bl/classify.tsv`:

| rows | class | where every route stops | why |
|---:|---|---|---|
| 152 | SPW, irregular fires (138 flat, 14 grow) | TriGlue "no ranking" / "too many families", rank tier false | Collatz-like rounds: the 2-adic liveness of §7.4.BX |
| 234 | block count grows (SPW regular 42; hybrids and bouncers 192) | TriGlue "too many families" (`G0 = 1`) or "leaf too long" (`G0 = 0`) | block-list counters with a neighbour recurrence: piece (a) above |
| 136 | hybrids and bouncers, flat block count | the same | HY2's pieces (b) two-lap overflow and (c) unary / shifting-anchor counters, long-period blocks MB does not close (15 of 18), irregular "spread" tapes |
| 49 | SPW, flat (18 regular, 31 sweep-rate) | TriGlue "no ranking" / "too many families" | bounded-block rows the lattice does not rescue; not read further |
| 15 | QH hybrids | TriGlue "quiet point past the boot cap" | the quiet instruction stops after step 4,096 (as late as ~7.97M), past `tri_sound_qh`'s boot cap |

**Next.**  (1) Piece (a) is the lever and it is research: a list segment
whose items carry an affine recurrence to their neighbour, a carry proved
by induction along the list, and a liveness argument for the overflow
(the list read as a number increases).  (2) The Collatz-like SPW rows
need BX's 2-adic ranking and are probably out of reach.  (3) HY2's (b)
and (c) remain as HY2 described them.  They need a `HybridCtrTr`
extension (a top step that keeps the low digits), which BL did not
build.

Commands (resumable: `find` skips rows already in its output):

```
python3 tools/closeouttr/bl_ti.py find tools/closeouttr/bl/rows.txt bl_find1.jsonl --jobs 4 --timeout 240
python3 tools/closeouttr/bl_ti.py batch bl_find1.jsonl --tag BL --chunk 20
cd tools/censustr && python3 mb_cert_find.py find ../closeouttr/bl/mb_long.json --list LONGPER_ROWS --jobs 2 --timeout 300 --pmax 64
python3 tools/closeouttr/mb_batch.py tools/closeouttr/bl/mb_long.json --tag BL --chunk 1
cc -O2 -o /tmp/bl_sim tools/closeouttr/bl/bl_sim.c
python3 tools/closeouttr/bl/classify.py tools/closeouttr/bl/rows.txt > classify.tsv
```

On the 14-core box, the `bl_ti.py` sweep is ~1 h at `--jobs 12`.  The
rank-tier rung BX recommends, `rk:8:0` at a 1,800 s cap on the 37
bouncers that timed out at 600 s (`bx/bnc_rk8_timeout.txt`), is at most
~18.5 CPU-hours, so ~1.5 h at 12 jobs:

```
python3 tools/closeouttr/ng_batch.py probe tools/closeouttr/bx/bnc_rk8_timeout.txt rk8.json --rungs rk:8:0 --jobs 12 --timeout 1800
python3 tools/closeouttr/ng_batch.py batch rk8.json --tag BL --chunk 2
```

#### 7.4.BLC BL's closeout: the 15 QH hybrids are never-quasihalting and are boarded; a list-glue checker lands, but its finder does not converge (2026-09-30)

Workstream BLC (batch tag `BLC`).  There were two parts: piece (a) of
§7.4.BL, the block-list counters, and BL's 15 "QH hybrids", the rows
past the boot cap.  The open count went from 1,324 to 1,309 (DN 546,
SP 640, QH 123).  The Collatz-like SPW rows, HY2's pieces (b) and (c)
(owned by HY3) and the pure counters (LE) were not touched.

**Part 2: the 15 QH hybrids, all boarded.**  BL listed them as TriGlue
"quiet point past the boot cap": the instruction the 1e8 scan calls
quiet stops firing late, as late as ~7.97M steps.  Run further, every
one of the 15 (`blc/qh15.txt`) fires that instruction AGAIN, at about
127.2M steps (`bl_sim.c` with a 2^27-cell tape).  So these rows are not
quasihalting at all.  They are never-quasihalting bouncer + counter
hybrids that the scan misclassified, and the right route is
`coversTr_nqh` with no pins, not a raised QH boot cap.  So neither
`tri_sound_qh` nor any landed checker was changed:

* 14 rows: `bl_ti.py`'s lattice finder in never-QH mode
  (`T.find(spec, 600, 'DN', 0)`, the default boots 3,000 / 12,000 /
  50,000), `blc/qh15_dn.jsonl`, batch `CBT_BLC_00`.
* The 15th row (`1RB1RA_1LC1RD_1LD1LB_0RA0RB`) certifies only from a
  late boot, at 200,000 steps (`blc/late_boot.py`: boots 200,000 /
  1,000,000, 3,000-step leaves), `blc/qh15_dn_late.jsonl`, batch
  `CBT_BLC_01`.

| batch | rows | route | compile (container, 4 cores) |
|---|---:|---|---:|
| `CBT_BLC_00` | 14 | `TriGlueTr`, `coversTr_nqh`, lattice finder | 38 s |
| `CBT_BLC_01` | 1 | `TriGlueTr`, `coversTr_nqh`, boot at 200,000 | 38 s |

Both are in `ci_costs.tsv` at 80 s, and `ci_shard.py --check 6`
passes.  `Print Assumptions` on `cv_BLC_00_0000` and `cv_BLC_01_0000`
shows `functional_extensionality_dep` only.

**The late boot on the other flat SPW rows: 0 of 49.**  The same late
boot (`blc/late_boot.py`, 300 s a row) was run on the 49 open SP rows
that `bl/classify.tsv` calls flat (`blc/spw_flat.txt`).  None
certified (`blc/late_spw_flat.jsonl`).  With the starting lattice
`G0 = 0` a leaf is always too long; with `G0 = 1` the result is "no
ranking" (mostly on the family pair `(2, 1)`) or "too many families".

**Part 1: piece (a).**

*The checker, `theories/Counters/ListGlueTr.v`* (1,390 lines, 3.5 s,
`lg_sound` / `lg_sound_mirror`, `functional_extensionality_dep` only).
It is TriGlue's families plus a TAIL on each side: a list of items
`(t, e)`, each rendered as `pre_t ++ rep u_t e`.  The items are read by
an automaton (`lc_kinds`, `lc_trans`, `lc_acc`).  Each transition
carries the item's relation to the item before it: either up,
`e + dn = a*p + dp`, or down, `p + dn = a*e + dp`, and with `a = 0`
also `e = 0`.  So one transition is `b_(i+1) = a b_i + d_i` for one
digit `d_i`, and a digit set is a set of parallel transitions.  The
three parts §7.4.BL asked for are these:

1. **The carry, by induction along the list.**  An unfold node (`UUnf`)
   takes the nearest item out of the tail into the window.  Its
   children are indexed by the transition read, and void children are
   proved empty by `tvoid`.  A `UVoid` node is closed by a certified
   per-state lower bound on the references (`lc_mins`, `mins_ok` /
   `mins_sound`, an induction over the accepted lists).  A fold pushes
   window blocks back into the tail and is checked coefficient-wise
   (`fchain`, `tail_end_ok`).
2. **The leftward sweep, item by item.**  That is the same machinery:
   a leaf's chain that crosses one item lands in the family whose tail
   is one item shorter.
3. **Liveness.**  A ranking `lrk` adds per-transition tail weights,
   with a default per side, to TriGlue's per-node value.  It is checked
   relationally (`lreach`, `lfires_rank`), and `llive_ok` makes every
   cycle of the family graph fire the rare instruction.

The whole check is `lg_check tm w = mins_ok && fams_ok ... && llive_ok
... && lboot_ok`.  A batch line is `apply coversTr_nqh, (lg_sound _
(mkLC ...)). vm_cast_no_check (eq_refl true).`

*The finder, `tools/closeouttr/lg_batch.py`* (untrusted, 2,100
lines).  First comes a concrete data pass that follows the real run.
Then, per shape, Karr affine-hull families, parametrised over a
nonnegative coordinate basis.  The automaton is learned from the run:
states `('S', unit, offset)` with shifted copies of transitions, and
the neighbour relation of each pair of adjacent window blocks in the
family key.  Region voids come from the certified minimum references.
It also contains an exact replica of `lg_check` (`c_check`), a MILP
liveness search, and the renderer.  **Validation:** TriGlue
certificates converted to the list format (`blc/ti2lg.py`, empty
tails) pass the replica and the kernel.  That is the renderer, the
replica and `lg_sound` agreeing end to end.  It is not a block-list
row.

*The finder does not converge on any block-list row, so nothing was
boarded by `ListGlueTr`.*  On a random 20 of the 248 open "grow" rows
(`blc/grow.txt`: DN 192, SP 56, the latter 42 regular and 14 of BL's
irregular grow rows), all 20 fail at boots 20,000 and 100,000 and
periods 1 and 2.  Nineteen fail on "too many families" (cap 200), and
one fails on "unfold depth" at boot 20,000.  Why, measured on
`0RB1RB_1LC1RA_1RA0LD_1LC1LD` at a 5,000-family cap and 400,000
rounds: the list is `0 (1)^(b_i)` with `b_(i+1) = 2 b_i + d_i`, and
the automaton learns digits `d_i` from -5 to +5, which is finite.  But
a carry leaves the items it has passed in a SHIFTED form, `b_i - k`
for the depth `k` of the carry so far.  So the learned states carry
offsets 0, -1, -2, -3, ... (`('S', (1,), -k)`).  The transitions
between offset states multiply until the automaton hits its
400-transition cap ("automaton too large", 1,442 of the failed
explorations).  The family key also splits by digit, window position
and tail offset (5,000 families, "too many families", 3,049 failures).
A larger cap does not help: from 200 to 5,000 families, the families
are still new at the cap.

**Residue: all 248 grow rows are open, and the next step is a finder
change, not compute.**

| rows | what | where it stops | next |
|---:|---|---|---|
| 234 | block-list counters (DN 192, SP regular 42) | `lg_batch.py` "too many families" / "automaton too large" | fold only CANONICAL items: keep the item a carry is modifying in the window (unfold both neighbours of the carry point), so that tail items never carry an offset and the automaton is `{unit} x {digit}`.  The checker already allows this (an unfold node per side, a fold that checks the relation), so the change is in `Explorer.fold` / `fam_of`, not in Coq |
| 42 of the 234 | the regular-fire SPW grow rows (`0RB1LB_1RC0LD_1LA0RD_1RA1LD`) | even with a converging finder, liveness | the list read as a binary number increases each round.  An item-additive ranking (`lrk`, a weight per transition) cannot express that: a carry turns many `1` digits into `0` digits and one `0` into a `1`.  They need a lexicographic or numeral-valued rank, which is a checker change |
| 14 | SPW irregular, grow | not tried | Collatz-like (BX's 2-adic problem); left alone as instructed |

**Commands** (resumable: `find` and `late_boot.py` skip rows already in
their output).  On the 14-core box, at `--jobs 12` and 300 s a row, the
`lg_batch.py` sweep of the 248 rows is at most 248 x 300 / 12 s, about
1.75 h.  Expect it to reproduce the failures above until the fold
change lands.  `late_boot.py` on the 49 flat rows takes about 20 min.

```
python3 tools/closeouttr/lg_batch.py find tools/closeouttr/blc/grow.txt lg_find.jsonl --jobs 12 --timeout 300
python3 tools/closeouttr/lg_batch.py batch lg_find.jsonl --tag BLC --chunk 10
python3 tools/closeouttr/blc/late_boot.py tools/closeouttr/blc/spw_flat.txt late.jsonl --jobs 12 --timeout 300
python3 tools/closeouttr/bl_ti.py batch late.jsonl --tag BLC --chunk 20
LG_VERBOSE=1 python3 -c "import sys; sys.path.insert(0,'tools/closeouttr'); import lg_batch as G; print(G.find('0RB1RB_1LC1RA_1RA0LD_1LC1LD', 600).get('err','OK'))"
```

#### 7.4.BLC2 The canonical fold lands, the offset states are gone, but the tail LANGUAGE is not free: 0 boarded (2026-09-30)

Workstream BLC2 (batch tag `BLC2`), over §7.4.BLC's 234 block-list rows
(`blc/grow.txt` less the 14 irregular ones).  Only the finder changed
(`tools/closeouttr/lg_batch.py`).  `ListGlueTr.v` and every landed batch
are untouched, no batch was written, and the open count is still 1,212.

**1. The canonical fold (done, as BLC diagnosed).**  `Explorer.fold` no
longer folds a SHIFTED item (`b_i - k`) into a state `('S', unit, -k)`.
When the block a tail's ref names was modified by the leaf, or is gone,
`fam_of` raises `NonCanon(side)`.  The explorer then turns that leaf into an
unfold node on that side (the same unfold node a leaf's end-of-window
request builds), so the modified block stays in the window and its
neighbour is folded against it.  A tail's ref is therefore always the
exponent of its pred in TAPE order: the side's outermost window block, or,
when that side has none (the head has just crossed the block), the other
side's nearest block.  On `0RB1RB_1LC1RA_1RA0LD_1LC1LD` no offset state is
ever created (`LG_CANON=0` restores BLC's shifted states).  The concrete
data pass cannot mirror this: its leaves walk constant blocks cell by cell
and end inside a block.  So under `CANON` it re-segments the whole
concrete tape (window plus the rest of the tail) at every leaf end, the way
the boot does, which folds canonically by construction.  Two bugs that a
non-trivial boot fold exposes are fixed on the way.  The data pass dropped
the tail that the boot family's own fold made (`folds0`), and `assemble`
built the anchor's concrete tails without it.

**2. Why canonical folding is not enough: the list's digits are a counter.**
With the offsets gone, BLC's automaton (one state per unit) accepts ANY
sequence of the learned digits.  On the worked example that is false.  The
list is a halving list `b_i = 2 b_(i+1) + d_i` whose rounds (a rightward
sweep crossing odd blocks unchanged, a turn at the first even one, a return
that shifts every separator one cell) increment `b_0` and one other block
(a ruler sequence).  Measured on every C0 fire to 3M steps (`blc2/sim.py`):

* counted from the head, even positions have `d_i` in {-4,-3,-2} and odd
  ones in {0,1,2};
* centred (`d+3` at even positions, `d-1` at odd ones), the digits are in
  {-1,0,1}, and **the nonzero ones alternate in sign, starting with -1**:
  all 511 observed digit strings match `0* (- 0* + 0*)* (- 0*)?`;
* so the partial sums of the centred digits stay in a window of width 1.
  That is a 4-state automaton (position class x last sign), but no k-gram
  language is closed: `blc2/closure2.py` builds tapes whose digit k-grams
  all occur in the run, runs one round, and about half leave the language
  for every k in 2..6 (95/200 closed at k=2, 103/200 at k=4, 100/200 at
  k=6).

The free automaton lets the exploration carry at positions the machine never
carries at, and the digits then drift without bound (-61 to +39 on the
example, "automaton too large" / "too many families").

**3. Learned tail automata (in the finder, not closing yet).**  The
automaton can be any DFA read from the tail's FAR end: a fold prepends one
item (next state `delta(state, item)`, deterministic), an unfold enumerates
predecessors, and each DFA edge becomes one `ltrans`.  `ListGlueTr`
accepts that unchanged.  `find` now tries, per boot and direction, the free
automaton and then `'bps'`.  That is a first data pass that collects every
concrete tail as a string of `(kind, relation)` symbols, a learned
automaton, and a second data pass that seeds the hulls under it.  Learners:

* `learn_dfa` (k-tails plus a determinising refinement): 70 states on the
  example for every k in 2..8, since a tail's futures are truncated where
  the sample string ends, so equivalent prefixes never merge;
* `alergia` (Carrasco-Oncina merging with Hoeffding tests): over 500 states,
  since 3,000 leaves are about 30 rounds and the far (high) digits barely
  vary;
* `fit_bps` / `build_bps` (**bounded partial sums**, used by `find`): the
  frequent digits (at least 3% of their type), 2-coloured into m = 1 or 2
  alternating classes by the least weight of same-class neighbours, a centre
  per class, and a bound on the SPREAD of the partial sums (`LG_BPS_ABS=1`:
  an absolute range instead).  States: the far end's non-digit prefixes,
  then (class, sum - min, spread).  On the example it recovers the right
  side's language exactly (classes {-4,-3,-2} / {0,1,2}, centres -3 / 1,
  spread 1).  The left tail is short (carries are usually shallow), so
  `transfer_bps` can fit both sides from the richer one (the same list read
  the other way: up and down swap), `LG_BPS_TRANSFER=0` turns that off.

With BPS the families become symbolic (lattice-coupled exponents `x`, `2x`,
`4x`), but the exploration still does not settle on the example: over 3,000
families in all four transfer / absolute settings.  Traced to the source,
the spurious families come from a region split.  A symbolic family's
small-value kids are concrete short lists (`65 32 18 8 6 3 0110 ...`) whose
far end is irregular, and the machine's round on them leaves the language
(spread 2).  The remaining gap is correlation: the left tail's state, the
window's digits and the right tail's state are parts of ONE counter, which
the family key checks only separately.  The far end, where new items are
born, is never seen changing in the data pass, since `b_0` only goes from
119 to about 150 over 3,000 leaves and no overflow happens.

**4. Yields.**

| run | rows | certify | failures |
|---|---:|---:|---|
| canonical fold, free automaton, the 20-row sample (`blc2/sample20.txt`) | 20 | 0 | "too many families" at every boot and direction, under 4 s a row |
| canonical + BPS, the 47 clean ratio-2 `1`-block lists (`blc2/clean47.txt`, from `blc2/survey.tsv`) | 47 | 0 | 347 of 354 attempts "too many families", 4 time-outs (300 s), 2 "leaf too long", 1 "unfold depth"; 14.4 min at 4 jobs |
| the same, all of `blc/grow.txt` (`blc2/find_all.jsonl`) | 248 | 0 | of 1,958 attempts (up to 8 a row), 1,840 "too many families", 45 "unfold depth", 45 BPS finds no automaton for a side (33 left, 12 right), 18 "exploration does not settle", 8 time-outs, 2 "leaf too long"; about 75 min at 4 jobs |

Liveness (step 3 of the brief) was not reached, since no row gets as far as
a ranking.  No new Coq file was needed or written.

**5. What the 234 rows are** (`blc2/survey.py`, the tape at 8e6 steps):
about 55 are clean halving lists of `1`-blocks with one-cell separators
(the example's cousins: `0RB1LB_1RC0LD_*_1RA1LD` and relatives, the 42
regular-fire SPW grow rows among them).  Most of the other 168 are also
lists, but with separators longer than 4 cells: halving lists of `0`-blocks
whose separator word carries a digit (`1^6` / `11011`, `10001` / `100101`),
ratio-4 lists of `(011)` / `(110)`, and a few bouncers with a list only at
the far end (`1RB1RD_0RC0RA_1LC0LD_1RA0LD`: `(0111)^n (0011)^m` plus a
slow `1^a 0^b 1^c` end).  On a separator-digit list the block recurrence
can be functional (`0^609 0^303 0^150 ...`: `d = 2 + (b mod 2)`, which the
free automaton states exactly), and those rows stop earlier.  The data
pass folds transient head-region blocks as list items with junk relations
(|d| up to `MAXD`), and `wrel` keys split on "relations" between constant
blocks.

**Residue: all 234 open, and the next step is again the finder.**

| rows | what | where it stops | next |
|---:|---|---|---|
| ~55 | clean `1`-block halving lists (the example) | BPS explores, "too many families" | a JOINT tail state: fit one BPS for the list and give the family the pair of positions (left sum from `b_0`, right sum from the far end) that one reading of the whole list allows, instead of two independent states; and a data pass long enough to see an overflow (a later boot, or a C data pass: the Python one does 3,000 leaves in about 13 s) |
| ~170 | separator-digit and ratio-4 lists | "too many families" in the free and the BPS automaton | stop the data pass folding transient blocks: fold only items whose relation is frequent in the run, and drop `wrel` for constant pairs |
| 42 of the 234 | the regular-fire SPW grow rows | as above | the numeral-valued rank, once any row explores |
| 14 | SPW irregular, grow | not tried | Collatz-like (TA's) |

**Commands** (resumable: `find` skips rows already in its output).  The
full sweep is ~75 min at 4 jobs and 300 s a row in the container, so about
25 min at `--jobs 12` on the box:

```
python3 tools/closeouttr/lg_batch.py find tools/closeouttr/blc/grow.txt lg_find.jsonl --jobs 12 --timeout 300
python3 tools/closeouttr/lg_batch.py batch lg_find.jsonl --tag BLC2 --chunk 10     # when anything certifies
LG_VERBOSE=1 python3 -c "import sys; sys.path.insert(0,'tools/closeouttr'); import lg_batch as G; print(G.find_dir('0RB1RB_1LC1RA_1RA0LD_1LC1LD', False, 20000, 'bps'))"
cc -O2 -o /tmp/bl_sim tools/closeouttr/bl/bl_sim.c && python3 tools/closeouttr/blc2/survey.py tools/closeouttr/blc/grow.txt > survey.tsv
(cd tools/closeouttr/blc2 && python3 closure2.py 0RB1RB_1LC1RA_1RA0LD_1LC1LD 4 200)
```

#### 7.4.BLC3 A joint tail language and per-state upper bounds: block lists get through ListGlue, 18 boarded (2026-10-01)

Workstream BLC3 (batch tag `BLC3`), over BLC2's 234 block-list rows
(`blc/grow.txt` less BL's 14 irregular ones, `blc3/rows234.txt`).  The
counters (LE2), the Collatz-like rows (TA) and the hybrids were not
touched.  **18 rows are boarded** (`CBT_BLC3_00..05`).  The first is BLC's
worked example `0RB1RB_1LC1RA_1RA0LD_1LC1LD`.  All of them are
kernel-checked, and `Print Assumptions` shows `functional_extensionality_dep`
only.

**1. The worked example through the kernel.**  BLC2's residue table named
the next step: a JOINT tail state.  Done exactly, it is not quite what that
table guessed.  Five things were needed, found in this order on the example:

1. *One forward automaton F over the whole list.*  The list
   `b_0, ..., b_k` reads as digits `d_i = b_i - 2 b_(i+1)`.  For the
   example, F is the bounded-partial-sum language of BLC2 §2: centred digits
   whose prefix sums from `b_0` stay in `{-1, 0}`.  It has 4 states
   (sum x position parity) plus an END table, the state before the last
   digit and the last block (`b_k` is 1 or 2).  Brute force over every list
   of up to 8 digits (681 lists) confirms that F is closed under one sweep.
   The RIGHT tail is read by the DETERMINISED REVERSE of F from the far end:
   its state is the set of F-states from which the rest of the list is
   accepted.  Both tail states are therefore measured from one reading of
   the list.  A family `Pre(q_L) x window x Suf(R)` is exact when the
   window's digits lead from `q_L` into `R`, so no per-side relative range
   is involved (BLC2's BPS learned one for each side independently).
2. *The left tails are a sub-language.*  Every element the sweep has
   already passed has "pass parity", so in a left tail all digits after
   `b_0`'s are centred 0, and `b_0` is shifted (+1, written by the anchor
   instruction).  With F itself on the left (any digit), the exploration
   builds lists whose prefix sums leave the window: 3,000+ families.  A
   left automaton that keeps only parity (forgetting the sum) also blows up
   (1,886+).  The left state must be F's absolute state restricted to the
   transitions left tails take.
3. *Lattice hulls.*  Karr's affine hull forgets congruences.  An element
   that is always even at a phase (A on its last cell, say) was generalised
   to every integer, and the odd instances turn at the wrong separator,
   which leaves the language.  The finder's hulls now keep a per-coordinate
   gcd (`LHull`: `lb + g x`), BL's lattice idea transplanted.
4. *Tape-order parsing and constant stops.*  The window is parsed in tape
   order (left side, head cell, right side) into elements and separators,
   so an element split by the head keeps its full exponent.  The neighbour
   relations of the window's blocks are keyed.  Leaves stop at constant
   blocks too (`leaf_run3`).  Otherwise a concrete region walks along a row
   of constant elements, and the canonical unfold chases it until "unfold
   depth".
5. *A checker extension, and it is the precise blocker.*  The far end of a
   block list is pinned: the END item's relation is `a = 0`, down, so the
   pred equals the constant `b_k`.  In the RIGHT automaton, the states just
   before the END bound their ref ABOVE (`b_k = 1`, so the ref is at most
   1).  An unfold from a state far from the end always has a kid "this
   item is the last block", with a SYMBOLIC exponent such as `2 + x`.  That
   region is empty, but `ListGlueTr` can only say so with `tvoid`, which
   for `a = 0` needs a constant ref, or with `lc_mins`, a lower bound.  No
   certificate exists without an upper bound.  **New file
   `theories/Counters/ListGlue2Tr.v`** (`ListGlueTr.v` untouched) adds
   `lc_maxs`, a certified upper bound per state.  `maxs_ok` requires that a
   listed state is not accepting and that each of its transitions bounds
   the ref by its target's bound (`rubound`) or pins it.  `maxs_sound` is
   an induction over the accepted lists.  A `UVoid` node closes a region
   by either bound; an upper bound needs no constant ref, since every
   coefficient is nonnegative (`aeval z r >= a_c r`).  The record and
   checker are renamed (`mkLC2`, `lg2_check`, `lg2_sound`,
   `lg2_sound_mirror`); everything else is `ListGlueTr` verbatim.  The
   file compiles in about 2 s and its axioms are
   `functional_extensionality_dep` only.

The example's certificate has 75 families and 105 leaves.  The search
takes 1.5 s and the batch compiles in 4.4 s (`CBT_BLC3_00`).  The liveness
search found item-additive rankings: on this row every instruction fires
once per sweep, so the numeral-valued rank is not needed (see 4. below).

**2. The language, learned per row** (`blc3/learn3.py`, on top of
`blc3/lg3.py`, which reuses `lg_batch.py`'s exploration, replica and
liveness search).  `blc3/lsnap.c` records the tape at every ANCHOR (the
head steps past the end of the list holding `b_0`) and at sampled steps
with the head deep in the list.  The learner then works out, in order:

* the orientation (mirror when `b_0` sits at the right);
* the separator words between long runs (`0`, `00`, `010`; `010` is
  parsed as one word, longest match);
* the ratio;
* F: a centre per (position class, separator word), with `b_0`'s digit a
  class of its own, because the anchor's `b_0` is off by one from mid-sweep;
  states are (class, absolute sum) in the range the anchors show, and the
  last M symbols plus `b_k` form the END table;
* the left tails: `b_0`'s shift (the one under which the left samples
  parse), and the F-transitions they take.

On the example, the learned F, shift and left automaton match the hand
derivation (`blc3/ex1.py`), and the row certifies in 2.7 s with nothing
hand-written.  The lists whose separator carries the digit (`1^7 00 1^15
00 1^31 0 1^62`: `d = 1` iff the separator is `00`) need no special case:
their F is the free language over the separator-digit symbols.

**3. Yields** (`blc3/learn3.py find`, 300 s a row, cap 800 families, 4
jobs).  The first pass, on BLC2's 47 clean halving lists at a 200-family
cap, certified 18; 16 of those pass the full replica.  The replica did not
check `maxs_ok` at first.  Two certificates had bounds computed by a
tighter formula than Coq's `rubound` and were redone; at the 800 cap both
pass.  The full sweep over the 234 rows:

| result | rows |
|---|---:|
| certify | 14 |
| time-out (300 s) | 5 (4 of them certified in the 47-row pass at the 200 cap, and are boarded) |
| learner: no ratio (multi-cell units such as `011^125 01 011^138`, `0`-block lists, a list only at the far end) | 95 |
| learner: no separators (`0`-block lists with `1^6` / `11011` separators, `(01)`, `(100)` / `(001)` alternating units, bouncers) | 87 |
| learner: ratio 0 or 1, no bounded-partial-sum automaton | 7 |
| exploration: too many families (800) | 26 |

18 rows are boarded (`CBT_BLC3_00..05`): the sweep's 14 and those 4.

All the boarded rows are 1-block halving lists with separators `0`, `00`
or `010`, at ratio 2, in either orientation.

| batch | rows | compile (container, 1 core) |
|---|---:|---:|
| `CBT_BLC3_00` | 1 | 4.4 s |
| `CBT_BLC3_01` | 6 | 8.8 s |
| `CBT_BLC3_02` | 6 | 10.7 s |
| `CBT_BLC3_03` | 1 | 2.4 s |
| `CBT_BLC3_04` | 2 | 5.2 s |
| `CBT_BLC3_05` | 2 | 6.8 s |

All six batches are in `ci_costs.tsv` at about twice the container time.
`ci_shard.py --check 6` passes, and the slowest shard is unchanged
(`CBT_BR_02`, 2,764 s).

**4. Residue: 216 rows, and where each group stops.**

| rows | what | where it stops | next |
|---:|---|---|---|
| 189 (with the next row) | lists whose unit is not a single `1` cell: `0`-block halving lists with `1^6` / `11011` separators (often with a second counter on `b_0`'s side, `1^1057 01 0^353 ...`), ratio-2/4 lists of `(011)` / `(110)` whose unit ALTERNATES along the list, `(01)` and `(100)` / `(001)` lists | `learn3.py` (one-cell `1` unit only) | generalise the parse to multi-cell and alternating units (`lg3.parse`, the item kinds); the checker needs nothing new |
| | not lists at the anchor: bouncers with a list only at the far end, long-period blocks, "spread" tapes | learner | not list counters; other routes |
| 26 | 1-block lists that learn but whose exploration does not close at 800 families | `lg3` | on the one traced (`0RB1LB_1RC0LD_0LD1RA_1RA1LD`), mid-sweep separator shapes the anchors never show (`010` with the digits shifted) pile up in the right window instead of folding.  The right tail language must also accept the transient separators (learn it from right tails mid-sweep, not only from anchors) |
| 1 | time-out | `lg3` | a longer budget on the box |
| 42 of the 234 | the regular-fire SPW grow rows | (in the groups above) | the numeral-valued rank BLC2 expected was never reached.  The boarded rows needed none: every instruction fires once per sweep, so the rare instruction is not the overflow.  Rows whose rare instruction fires only at the overflow still need it |

No row reached a liveness failure: every exploration that closed also
found item-additive rankings.  Step 3 of the brief (a new generic
numeral-rank file) was therefore not needed for any row reached so far.

**Commands** (resumable; the sweep is about 2 h at 4 jobs in the container,
about 40 min at `--jobs 12` on the box).  Multiprocessing workers can
deadlock on the `SIGALRM` timeout (two runs stalled), so `blc3/one_by_one.sh`
reruns the stragglers one process each, under a hard kill.

```
python3 tools/closeouttr/blc3/learn3.py find tools/closeouttr/blc3/rows234.txt blc3.jsonl --jobs 12 --timeout 300
tools/closeouttr/blc3/one_by_one.sh tools/closeouttr/blc3/rows234.txt blc3.jsonl     # rows the pool left out
python3 tools/closeouttr/blc3/learn3.py batch blc3.jsonl --tag BLC3 --chunk 6
LG3_MAXFAM=2000 python3 tools/closeouttr/blc3/learn3.py find ROWS.txt out.jsonl --jobs 12 --timeout 900   # the 26 + 5
(cd tools/closeouttr/blc3 && LANG_NAME=lang3 python3 run1.py 20000 0)                                     # the worked example, hand language
```

#### 7.4.BLC4 Block lists beyond the one-cell `1` unit: per-side units, end words, split elements; the `0`-block lists get through ListGlue2Tr (2026-10-01)

Workstream BLC4 (batch tag `BLC4`), over BLC3's residue: the 216 rows of
`blc3/rows234.txt` still open (`blc4/rows216.txt`).  The counters (LE/LE2),
the Collatz-like rows (TA) and the flat-block hybrids / cube sweep counters
were not touched.  **No new Coq**: `ListGlue2Tr`'s item kinds are
`(pre, u)` with `u` any word, chosen per transition, so multi-cell and
alternating units, end words and per-side forms are all plain items.
Everything below is finder work (`tools/closeouttr/blc4/`, untrusted).

**1. One row through the kernel first.**  The first row taken end to end
was a `0`-block halving list, `1RB0LA_1LC0RD_1LA1RB_1LC1RC`
(`1111 0^994 11011 0^497 111111 0^246 ...`).  Three things were missing
from BLC3's finder, found in this order:

1. *The unit is per side.*  The sweep rewrites the elements it passes:
   left of the head the list is `10 1^749 0110 1^375 0110 ...`, `1`-blocks
   with separator `0110`, while the right of the head (and the anchor) is
   the `0`-block list.  So each side has its own unit, separators and item
   kinds.  The left automaton is learned on F's own states: each left
   sample (the elements wholly left of the head, less the nearest) is
   aligned with the anchor list it was swept from.
2. *End words, as ordinary items.*  A constant word beyond `b_0` (`10`)
   ends a LEFT tail in a terminator item: kind `(word, unit)`, exponent 0,
   relation `up, a = 0, d = 0` (so `e = 0` and the pred `b_0` is free),
   into an accepting state.  A constant word after the last block is the
   RIGHT tail's END item, one kind per word, pinning `b_k` as BLC3's did.
   The list is read from `b_0` while the gaps are separators; the cells
   after the last such element are the end word.
3. *Split elements.*  While the head rewrites an element, its two halves
   sit in the window as two blocks: `1^x 0 [1] 0^y` (two units), or
   `1^x 0 [1] 1^z` (one unit, a marker).  The list relation is on their
   SUM, `x + y = a z + d`, and that set has no nonnegative affine
   parametrisation (Karr's hull gives `y = c - x`).  The finder marks a
   split (two window blocks within 3 cells of each other around the head,
   of different units or with no list relation), puts both halves'
   residues mod `a` in the family key (`NeedMod` refines the region when a
   leaf lands with a residue not fixed), and, when the data only has
   constant `z`, widens the hull along the two "element grows" directions
   `a e_x + e_z`, `a e_y + e_z`.  `z` then becomes a two-variable block,
   which is harmless while the split lasts: TriGlue only refuses to START
   a leaf on a multi-variable block, and the head reaches `z` only once a
   half is gone.

The row's certificate has 123 families; `CBT_BLC4_00` compiles in 6.6 s,
`Print Assumptions` shows `functional_extensionality_dep` only.

**2. Multi-cell units** (`(110)^611 000 (011)^153`, `(10)^434 (01)^217`,
`(100)^788 0000 (001)^197`).  One tape has several block spellings
(`11 (011)^e` is `(110)^e 11`) and the checker compares segments
syntactically.  So the finder fixes one: in each side's nearest-first
order a multi-cell block is pushed as far from the head as it goes (no
more `SRot 1` applies).  That depends only on cells beyond the block,
which a leaf that does not cross it never touches; a leaf that crosses a
block ends with the `SRotL 1` / `SRotR 1` steps that restore the form
(LapDecider steps, so no Coq change).  On a concrete tape the same form
is the periodic stretch aligned to its far end, which is how the learner
parses anchors (`lg4.parse4`).  A separator symbol is then
`(unit before, gap, unit after)`, so alternating rotations need no special
case.  The centre fit (F) gets a coordinate-descent fallback when the
brute force is too large (8 separator words x 3 position classes on the
`(100)` lists).

**3. What else the learner needed** (each found on a row):

* the boot at the first anchor from which ten in a row are F-lists (the
  `(110)` lists' far end carries a slowly growing `1^k` before ~100,000
  steps, outside the learned END table);
* right tails' other forms: the return sweep leaves the right part in a
  different spelling (`B10 1 B01` on a `(10)` list); right samples aligned
  from the far end add their symbols to F as alternative edges between the
  same F-states;
* a left end that is blank in some rounds and a word in others (both
  accepted);
* `learn3.snaps` keeps ~40,000 split snapshots of a `(10)` list (100M
  strings, OOM); the rows are kept as text and parsed on use.

**4. Yields.**

| batch | rows | compile (container) |
|---|---:|---:|
| `CBT_BLC4_00` | 1 | 6.6 s |
| `CBT_BLC4_01` | 6 | 102 s (with `make`'s dependency scan, under a 3-job sweep) |
| `CBT_BLC4_02` | 5 | 42 s (the same) |

**12 rows boarded**, all of them ratio-2 `0`-block halving lists with
`11011` / `111111` separators.  They come from the first sweep
(`blc4/sweep1.tsv`; 12 of the 27 `0`-block lists, 4 jobs, 300 s a row).
`ci_costs.tsv` lists the three batches at 15 s, 200 s and 90 s, and
`ci_shard.py --check 6` passes.  `Print Assumptions` on `cv_BLC4_00_0000`,
`cv_BLC4_01_0000` and `cv_BLC4_02_0004` shows
`functional_extensionality_dep` only.  CI (the PR's diff job) is green on
every push.

The last sweep (`blc4/sweep5.tsv`) ran the finished finder over the other
204 rows: 189 at 4 jobs and 400 s a row (about 2 h 40 min), plus the 15
`0`-block lists left over from the first sweep.  It certified no further row.

**5. Residue, and where each group stops.**

| rows | what (learned unit, ratio) | where it stops | next |
|---:|---|---|---|
| 13 | `0`-block halving lists (`0`, 2) | **the exploration closes**, but the liveness search finds no ranking for the rare instruction (`D0` on 11 rows, `A0` on 2).  It fires only at the list's OVERFLOW, at intervals growing x4 (`1RB0LA_1LC1RC_1LA1RD_1RB0RB`: 17,496, 67,800, 266,712, 1,057,752, 4,212,696 steps) | a numeral-valued ranking, which is a checker change (a new file beside `ListGlue2Tr`).  BLC2 and BLC3 predicted it; these are the first rows that need it.  `lrk`'s rank is window-affine plus a weight per tail item, and the distance to the overflow is about `a^k`.  The rank would have to read the tail as a numeral, `r(item :: T) = c_t + a * r(T)`, and the window's shift then rescales the unknown rest, so the edge inequality needs the folded and unfolded item counts matched.  That is research, not finder work |
| 27 | `1`-block lists (`1`, 2): BLC3's 26 and their cousins | too many families (cap 800; 3,000 tried on one row) | the head carries a `0` MARKER through an element (`1^x 0 [1] 1^z`, now a split element).  The right windows then keep a far-end pair whose digit is outside F (`-3` against F's `-1`/`-2`), so no right fold applies and the window grows.  `blc4/diag4.py` shows the first explored families differ from the real run's only in the right tail's class: unfolding from the boot enumerates every suffix class F allows, and the machine uses few of them |
| 45 | multi-cell lists, ratio 4: `(001)`/`(100)` 24, `(011)`/`(110)` 21 | too many families | `b_0` is rewritten in SEVERAL passes per round (`(110)^326 0 [1] (011)^202`, then `(110)^502 1 [1] (101)^26`, ...).  The left samples are rare (85 on the `(100)` row: the head reaches `b_2` once in 16 rounds), and the left folds miss the digits of elements the sweep has half rewritten.  Widening the left edges by one digit (`LG4_LWIDEN`) did not help |
| 16 | `(01)`/`(10)` lists (2, 9 rows), `(011)` ratio 2 (4), `(0011)` ratio 3 (3) | too many families | the head re-enters passed elements (carry-like), so the left windows hold elements mid-rewrite and no left tail forms |
| 94 | not learned (`blc4/sweep5.tsv`) | learner: no ratio 45, no long runs 19, ratio 0/1 14, no BPS 9, no separators 4, left samples disagree 1 | mostly NOT lists at the anchor: bouncers (`(10)^5 1 (10)^5 1 ...`), one long block (`1^1991`), spread tapes, a list only at the far end.  A few are lists of a kind the learner does not yet read: two unit CLASSES alternating (`1^9 0^15 1^17 0^31 ...`, ratio 0), separators of 7 to 8 cells on a `0`-list (`1000001` / `10101001`) |
| 9 | (no learn record) | time-out at 400 s | a longer budget on the box |

Kept from BLC3: no row reached a liveness failure EXCEPT the 13 above, and
the boarded rows' item-additive rankings needed nothing new.

**Commands** (resumable; `find` skips rows already in its output, and
re-executes itself under `PYTHONHASHSEED=0` so a run is reproducible):

On the 14-core box the whole sweep is about 216 x 400 / 12 s, so 2 h at
`--jobs 12`, at most.  Expect it to reproduce the table above.  The
numeral rank is the lever for the 13 closing rows, and the right-tail
class problem for the rest.

```
python3 tools/closeouttr/blc4/learn4.py find tools/closeouttr/blc4/rows216.txt blc4.jsonl --jobs 12 --timeout 400
python3 tools/closeouttr/blc4/learn4.py batch blc4.jsonl --tag BLC4 --chunk 6
python3 tools/closeouttr/blc4/diag4.py SPEC 3000 400      # explored families the real run never visits
LG4_MAXFAM=3000 python3 tools/closeouttr/blc4/learn4.py find ROWS.txt out.jsonl --jobs 12 --timeout 1800   # the time-outs
```

#### 7.4.BLC5 The overflow rows: a far-end lexicographic liveness, 13 boarded (2026-10-01)

Workstream BLC5 (batch tag `BLC5`), over BLC4's residue (`blc4/rows216.txt`,
204 open at the start).  The counters (LE/LE2), the Collatz-like rows (TA)
and the flat-block hybrids / cube sweep counters were not touched.  **13
rows are boarded** (`CBT_BLC5_00..02`): all of BLC4's `0`-block halving
lists whose exploration closes but whose rare instruction fires only at the
list's overflow.  Open rows: 824 -> **811**.

**1. Why an additive rank cannot work, and what replaces it.**  On the worked
example `1RB0LA_1LC1RC_1LA1RD_1RB0RB` the list is a bijective binary
numeral: `0^b_0 s_0 0^b_1 s_1 ...`, the separator `11011` meaning digit 1
and `111111` digit 2, `b_i = 2 b_(i+1) + d_i`, and the far end `1111` / `11`
pins `b_k` (2 / 1).  A round converts `b_0` (a zig-zag of ~`b_0` leaves),
then every following element while its digit is 2, and turns at the first
digit 1, which becomes 2; the return converts the passed elements back
(each with digit 1).  So a round adds one to the numeral, and `D0` fires only
when the list grows: at intervals `x4` (13, 109, 469, 1741, 6373, ...).  The
number of rounds to the next fire is about `2^k` minus the numeral, which no
sum of per-item weights expresses.

*The checker, `theories/Counters/ListGlueLexTr.v`* (new, ~640 lines,
2.5 s, `lgx_sound` / `lgx_sound_mirror`, `functional_extensionality_dep`
only).  It reuses ListGlue2Tr's families, leaves, tails, bounds and boot,
checked by ListGlue2Tr's own `fams_ok` / `mins_ok` / `maxs_ok` / `lboot_ok`;
`ListGlue2Tr.v` is untouched.  Only the liveness is new.  Per instruction
the certificate may give a lexicographic rank read from the list's FAR end
(the most significant one): per node a list of window forms `W` (affine in
the family's variables) and, per side and tail transition, a list of
weights `(alpha, beta)` (one sequence entry `alpha e + beta` each).  An
anchor's measure is

    rev(hi tail's entries) ++ W(vars) ++ (lo tail's entries) ++ [V]

with `V` ListGlue2Tr's additive rank.  On every step between nodes whose
leaves do not fire the instruction (`xedge`): the hi side's weights do not
grow (entrywise, same entry counts) and the lo side's entry counts do not
change, so the untouched tails line up; the MIDDLE (the hi items the leaf
unfolds, reversed, the window entries, the lo items it unfolds) and its
image at the target (folded items, the target's window entries) have the
same length; and the middle drops lexicographically, checked symbolically
(`lexchk`: the first entry that is not `<=` coefficient-wise fails, the
first that is `+1 <=` decides), or it may stay equal, and then the lo
side's weights do not grow and `V` drops as in ListGlue2Tr.  The length is
constant along a non-firing run and the lexicographic order on `N^n` is well
founded (`lex_wf`), so the instruction fires from every anchor (`xfires`).
An instruction with no lexicographic entry keeps ListGlue2Tr's check.

Two things were needed beyond the plain "numeral" picture BLC4 sketched:

* *The near side's weights are per NODE.*  A passed element is a pending
  carry before the turn (digit 2) and a resolved digit 1 after it.  The
  certificate revalues the whole near tail at the turn, which is exactly
  the step where the turning element's entry drops, so the less significant
  tail behind it is free.  (A per-transition weight fixed for all nodes
  fails: the return step `left form -> digit 1` is then an increase with
  nothing more significant decreasing.)
* *A transition may stand for no entry.*  On 8 of the 13 rows the far end
  has several spellings (an END item pinning `b_k = 1`, or `b_k` as a list
  item before an END pinning 2), and the item count changes on non-firing
  steps (no per-node window count makes the length constant: 30 conflicting
  steps on `1RB0LA_1LC1RC_1LA1RD_0RB0RB`).  Giving the `b_k = 1` END
  transition no entry restores a constant length.

The windows' entry counts and the reason the item-additive rank cannot
work are what BLC4 called "the window's shift rescales the unknown rest":
reading from the far end, the unknown rest is the most significant part and
is never rescaled, only compared entrywise.

*The finder, `tools/closeouttr/blc5/lx5.py`* (untrusted; scipy).  BLC4's
learner and exploration as they are (`learn4.learn`, `lg4.explore_row`).
Per instruction: ListGlue2Tr's additive MILP first; if it has no solution,
the lexicographic search: (1) per transition 0 or 1 entries and per node the
window entry count, a MILP over the steps' length equations (most
transitions 1); (2) constant entries only (window entries and weights in
`0..3`, the far side's weights global, the near side's per node), with one
0/1 "equal so far" variable per middle position and step, maximising the
strict steps; (3) the additive MILP on the steps left equal.  `c_xlive_ok`
replays `xlive_ok` exactly before a certificate is written.  On the 13 rows
the whole find takes 4-15 s a row (31 s for the 13 at 4 jobs); the
lexicographic search itself is under a second.  On the example: 127 nodes,
162 non-firing steps, 75 strict, one window entry at most per node; the far
side's weights are the complement digits (digit 1 above digit 2).

| batch | rows | compile (container, 1 core) |
|---|---:|---:|
| `CBT_BLC5_00` | 1 (the worked example) | 16.5 s |
| `CBT_BLC5_01` | 6 | 41.6 s |
| `CBT_BLC5_02` | 6 | 43.6 s |

`ci_costs.tsv` lists them at 35 / 90 / 90 s; `ci_shard.py --check 6` passes.
`Print Assumptions` on `cv_BLC5_00_0000` and `cv_BLC5_02_0005`:
`functional_extensionality_dep` only.

**2. The `1`-block lists with a marker (27 rows, 0 boarded).**  On
`0RB1LB_1RC0LD_1LA0RD_1RA1LD` (`1^1050 010 1^526 0 1^265 0 1^134 010 ...`)
the anchor lists are a binary counter in an OVERLAPPING-PAIR code: symbol
`i` (separator, digit) is the bit pair `(x_i, x_(i+1))`: `('0',-3)` = 00,
`('0',-4)` = 10, `('010',0)` = 01, `('010',-1)` = 11, and `b_0`'s symbol
(`('0',-5)` / `('010',-2)`) fixes the first bit.  The language is the
2-state DFA "the next symbol's first bit is this symbol's second bit".
BLC4's fit could not express it: a class's centre was searched only among
its observed digits, so `b_0`'s two symbols both started the partial sum at
0 and the sum range came out `{-1,0,1}` (width 2), which admits
`00`-after-`11`.  `learn4.py` now takes `LG4_B0WIDEN` (default 0, BLC4's
fit; `lx5.py` sweeps with 2 for these rows): `b_0`'s centre may sit two
outside its observed digits.  With it the learned F is exactly the pair-bit
DFA (range `{0,1}`, the observed-transition filter does the rest), but the
exploration still does not close (`too many families` at 800 and at 4,000):
the chain of new families runs through windows that hold the element the
head's `0` marker is crossing (`1^x 0 [1] 1^z`) with relations that are
`b_0`-like (`('010',-2)`, `('0',-5)` at interior positions) and never fold
into the right tail, so the right window keeps unfolding to the far end,
into concrete short lists.  The next step is the split-element rule of
BLC4 §1.3 for SAME-unit halves whose relation happens to be a (`b_0`-class)
list relation: key them as a split element, not as two list elements.

**3. Multi-cell / carry-like lists (61 rows) and the unlearned rows (94)
and time-outs (9).**  No finder change was made for these; the sweep below
records where each stops, now with the lexicographic liveness available.

**4. Yields and residue.**

The full finder (`lx5.py`, BLC4's exploration plus the lexicographic
liveness) over the 191 rows still open (`blc5/rows191.txt`, 400 s a row, 3
jobs, about 3 h 20 min here; `blc5/sweep191.jsonl`) certifies **none**.
Every one of them stops before the liveness, so no row is lost to a missing
ranking any more; the residue is all finder (learner and exploration):

| rows | learned unit, ratio | where it stops | next |
|---:|---|---|---|
| 27 | `1`, 2 (the marker lists) | too many families (25), unfold depth (2) | with `LG4_B0WIDEN=2` 25 of them learn the exact pair-bit language (`blc5/g2_b0widen.jsonl`) and still do not close (24 too many families, 2 unfold depth, 1 time-out).  The exploration's concrete small-value chains run through right windows holding mid-rewrite relations (`('010',-2)`, a `b_0`-class symbol, at the far side of the marker) that no right fold accepts; `LG4_SPLITF=1` (a same-unit pair around the head is split unless its relation is an INTERIOR F digit) does not change that.  The right tail's mid-sweep forms must enter the language (BLC4's `RALT` learns 4 of them here), or the fold must take the marker pair as one element |
| 24 | `001`, 4 | too many families (2 also leaf too long) | BLC4 §5: `b_0` rewritten in several passes; not attempted here |
| 21 | `011`, 4 | too many families (2 also no nonnegative parametrization) | the same |
| 9 | `01`, 2 | too many families (4 also exploration does not settle) | the head re-enters passed elements (carry-like) |
| 4 | `011`, 2 | too many families | the same |
| 3 | `0011`, 3 | too many families | the same |
| 94 | not learned | no ratio 45, no long runs 19, no BPS automaton 10, ratio 1: 9, no separators 5, ratio 0: 5, left samples disagree 1 | BLC4's survey: mostly not lists at the anchor (bouncers, one long block, spread tapes, a list only at the far end) |
| 9 | (time-out at 400 s) | | a longer budget on the box |

So the 13 overflow rows were the whole of BLC4's liveness residue, and the
lexicographic rank is now there for any later list row whose exploration
closes: `lx5.py` tries it automatically whenever the additive MILP fails.

**Commands** (resumable; `find` skips rows already in its output and
re-executes itself under `PYTHONHASHSEED=0`).

```
python3 tools/closeouttr/blc5/lx5.py find tools/closeouttr/blc5/rows13.txt find13.jsonl --jobs 4 --timeout 600   # the 13: ~31 s
python3 tools/closeouttr/blc5/lx5.py batch find13.jsonl --tag BLC5 --chunk 6
python3 tools/closeouttr/blc5/lx5.py find tools/closeouttr/blc5/rows191.txt sweep191.jsonl --jobs 12 --timeout 400   # the rest: ~2 h at 3 jobs here
LG4_B0WIDEN=2 python3 tools/closeouttr/blc5/lx5.py find tools/closeouttr/blc5/rows_g2.txt g2.jsonl --jobs 12 --timeout 300
```

#### 7.4.MP BLC5's residue: the multi-cell lists' far end, language and scale; the unlearned rows surveyed, 1 boarded (2026-10-01)

Workstream MP (batch tags `MP`, `MPU`), over BLC5's 191-row residue
(`blc5/rows191.txt`, all still open at the start): the 61 multi-cell /
carry-like lists, the 27 `1`-block marker lists and the 103 rows the
learner did not learn or timed out on (`tools/closeouttr/mp/rows_*.txt`).
The counter rows (LE2/LE3) and the Collatz-like rows (TA) were not touched.
**1 row boarded** (`CBT_MPU_00`).  Open rows: 745 -> **744**.  The 61
multi-cell lists still stop at "too many families".  Below is why, measured
on two rows, and what does not fix it.  No new Coq: everything here is
finder-side (`tools/closeouttr/mp/`).

**1. The far end is learned from too short a run** (`mp/asnap.c`,
`mp/farend.c`, `learn_mp.extend`).  learn4 reads F and the END table
(b_k pinned, then the end word) from the anchors of the first 4M steps.  The
far end changes only when a carry reaches it.  `mp/farend61.tsv` counts the
distinct 40-cell far ends of each of the 61 rows over 1e9 steps, with the
step of the last new one:

* 48 rows: the far end settles before 4M steps (12 to 69 forms);
* 13 rows: it settles later.  `0RB0LB_1LC1RD_0LD0LC_1RA1LC` and two
  others at 53-70M (142 forms), 8 rows at 4.4-5.6M (91 forms), and
  `1RB0RD_1LC1LB_1RA0LB_*` at 880-950M (82/84 forms).

On `0RB0LB_1LC1RD_0LD0LC_1RA1LC` the real run itself (lg_batch's data pass,
the exploration's cuts and folds on the concrete run) passes the learner's
horizon after ~9,000 leaves.  From then on its right windows hold the whole
list (no END fold applies), and the family count runs away: 214 families at
3,000 leaves, 800 (the cap) before 10,000.  `asnap` prints one anchor per
far-end change, to 300M steps by default (237 lines on that row).
`learn_mp.extend` adds their END entries, 96 on that row (26 -> 47 end
words), and the real run then has 313 families at 8,000 leaves.  But the
EXPLORATION still does not close (3,000 families at the cap).  With only
the END table extended, `lx5.py` on the 13 late rows certifies none of the 5
it finished (all too many families at 1,500; the sweep was stopped there).

**2. Why the exploration over-approximates.**  The second row,
`0RB0LD_1RC1LB_1LA1RA_1LA0LD` (`(001)` ratio 4, far end settled at 185k
steps), compares the real run (data pass, 6,000 leaves: 272 families, 103
window shapes) with the exploration (1,500 families, 404 window shapes, 371
of them never real).  Three sources, each found by following an unreal
family back to its first real ancestor (`mp/diag_mp.py`):

* *Short lists.*  An unfold far from the far end still has the kid "the
  next item is the END".  The exploration then runs two-element lists with
  tiny blocks, which the machine never builds after the boot.
  `lang_mp.Lang4D` counts the items to the far end in the right state,
  capped at `MP_DEPTH`, so `lc_mins` voids every constant ref below
  a^c b_k.  This is sound, a plain ListGlueTr automaton.  But
  lg4's `uge` request then splits a variable into that many singleton
  kids (~130 at depth 3, nested over several variables).  At depth 3 one
  family did not finish building in 15 minutes; at depth 2 the count still
  grows linearly (1,900 families, 594 queued).
* *Scale mixing.*  One window shape occurs at every list position.  The
  hull of a family met both at b_0 (hundreds of units) and next to the far
  end (2-10 units) has a base of a few units, and its leaves split into
  small constants.  Those form windows of several blocks whose exponents
  lost the list relation (`w=(None, ...)`), so no fold applies
  (`R=['B100','L000000','B100','L000000','B100', ...]`).  Keeping constant
  blocks up to 30 cells literal (`MP_SMALL=30`) made it worse (1,905
  families, 861 queued).
* *The tails are independent.*  The left tail's prefix state, the window's
  separators and the right tail's suffix set are keyed separately.
  Nothing makes an unfold kid agree with the window's last symbol or the
  left tail, and an unfold must cover every transition.  So the
  exploration builds lists whose consecutive symbols the machine never
  writes together.  On this row the anchor lists are a LOCAL language:
  each element cycles through ~6 phases (separator word plus spelling), and
  the 128 pairs of consecutive symbols are all present by 1M steps (none
  new to 16M; triples keep growing).  So `learn_mp.fit_local` (F = that
  local language, `MP_F=local`) is exact on the anchors, unlike BPS's
  partial-sum range `[0, 3]`.  With it the exploration is 3-4x slower per
  family (each unfold has ~10 kids) and still grows (585 families, 361
  queued).  The opposite, F free over the observed symbols (`MP_F=free`),
  blows up faster (1,557 families, 1,414 queued).  Tracking the element's
  spelling in the right state (`MP_ROT=1`) changes little.

The same local F on 2 of the 27 marker lists (`LG4_B0WIDEN=2`): too many
families (1,500 cap).  On the `(01)` ratio-2 row `0RB0RA_0LC1RA_0RD1LC_1RB1LB`
it is the LEFT window that grows (`L=['B01','L1','B01','L1', ...]`).  These
are passed elements whose left transitions the ~100 left samples never
showed.

**What would fix it** (not attempted): a finder whose families come from the
real run and whose unfolds are pruned by a JOINT state.  The checker cannot
prune an unfold kid that is consistent with the tail's own automaton.  So
the joint context has to be in the automaton: left and right as one
two-sided language read from the head, or a right state that remembers the
symbol across the head.  Alternatively, a ListGlue variant whose dispatch
tree can void a whole RANGE of a variable (`x < n`) in one node.  That is a
checker change (a new file beside ListGlue2Tr), and it would make the depth
bound of `Lang4D` cheap.  Of the three levers, it is the most mechanical.

**3. The 103 unlearned / timed-out rows** (survey: `mp/survey_unlearned.md`,
per row `mp/survey_unlearned.tsv`).  All are class DN.  Grouped by tape
shape:

| group | rows | shape | result |
|---|---:|---|---|
| SPREAD | 19 | irregular tape, no long periodic stretch | open: rank tier false / time-out at window 8, MB no closure |
| HYB2 | 14 | two blocks trading length plus a counter end (one row: low digit base 4 under base-2 digits, junction rotating every 2 laps) | open: hy2 at digit width <= 10, bases 2-6: "no counter family" (needs HY3's per-phase alphabets) |
| BLKSPR | 11 | long block(s) beside a growing irregular region | open |
| LIST2 | 11 | ratio-2 lists the learner rejects at its anchor (b_0 caught mid-transfer, phase-flipping `(10)/(01)` units) | open: BLC learner work |
| LONGPER | 11 | one 22-54-cell period over most of the tape | **1 boarded**: MB at `--pmax 64 --polish 900` (9,617 nodes; MB's earlier 15,758-node closure was left out for a 7.7 min kernel time); 10 no closure |
| LIST4 | 9 | `(011)/(110)` ratio-4 lists: BLC5's 9 time-outs | open (§2) |
| TRIO | 5 | `1^a 0^b` trading, then a binary counter with ~950 zero digits written at once | open |
| MULTI14 | 5 | three blocks, one of period 14 or 10 | open: MB no closure |
| LIST32 | 4 | x~1.45 lists, Collatz-like | left alone (TA's shape) |
| POW2 | 4 | power-of-two blocks, a counter whose digits are blocks | left alone |
| HYB1 | 3 | one block plus a counter end | open |
| UNARY 2, OVF2 2, MULTI4 2, LISTIRR 1 | 7 | | open (OVF2: needs HybridCtr2Tr's finder) |

The finder runs: `hy3_ti.py` on the 83 rows it had not seen (0: 72 "no
anchor key"), MB `--pmax 32` on the 50 rows MB had not tried (0: no
closure), `mp/hy2w.py` (hy2 with digit width up to 10, bases 2-6) on 23
hybrids (0), and the rank tier at window 8 on 37 rows (0: 19 false, 18
time-outs).

| batch | rows | compile (container) |
|---|---:|---:|
| `CBT_MPU_00` | 1 | 177 s (beside a 1-job finder) |

`ci_costs.tsv` lists it at 360 s, and `ci_shard.py --check 6` passes (the
slowest shard is still `CBT_BR_02`, 2,764 s).  `Print Assumptions
cv_MPU_00_0000`: `functional_extensionality_dep` only.

**Commands** (resumable; `mp_find.py find` skips rows already in its
output, caches learned languages in `$MP_CACHE`, and re-executes itself
under `PYTHONHASHSEED=0`).  Knobs: `MP_F=local|bps|free`, `MP_EXTEND`
(the long-run END table, default on), `MP_DEPTH` (default 3; 0 = Lang4's
right automaton), `MP_ROT`, `MP_TLONG`, `MP_SMALL`.

```
cc -O2 -o /tmp/farend tools/closeouttr/mp/farend.c
/tmp/farend SPEC 1000000000 40 L                         # far-end words at each anchor (L or R: b_0's side)
MP_F=bps MP_DEPTH=0 python3 tools/closeouttr/mp/mp_find.py find tools/closeouttr/mp/rows_multicell.txt mc.jsonl --jobs 12 --timeout 1200
MP_F=local MP_DEPTH=2 LG_VERBOSE=1 python3 tools/closeouttr/mp/mp_find.py one 0RB0LD_1RC1LB_1LA1RA_1LA0LD
python3 tools/closeouttr/mp/mp_find.py batch mc.jsonl --tag MP --chunk 4
```

The full 61-row sweep at the box's 12 jobs and 1,200 s a row is about
1 h 45 min per knob setting.  None of the single-row runs above suggests
it will certify a row.  The survey's box commands (LIST4 at 1,800 s, rank
tier window 8 on its 18 time-outs, hy2w on its 7 time-outs; about 2 h in
all) are in `mp/survey_unlearned.md`.

#### 7.4.BLC6 The multi-cell lists through range voids, local splits and a left language from the turn tapes: 38 boarded (2026-10-01)

Workstream BLC6 (batch tag `BLC6`), over MP's 61 multi-cell / carry-like
block lists and the survey's LIST4 / LIST2 groups (20 rows):
`tools/closeouttr/blc6/rows_scope.txt`, 81 rows, all open at the start.
The counter rows (LE2/LE3/LE4), the Collatz-like rows (TA) and the
hybrid / cube rows were not touched.  **38 rows boarded**: 37 in the first
sweep (`CBT_BLC6_00..09`, PR #207) and 1 in the second (`CBT_BLC6_10`).
Open rows in scope: 81 -> **43**.

**1. The checker: `theories/Counters/ListGlueRngTr.v`** (new; ListGlue2Tr
and ListGlueLexTr untouched).  ListGlue2Tr with two more nodes in the
unfold tree, both LOCAL to one unfold path:

* `URng lsd k n u`: on side `lsd` the tail is in state `s` with ref `r`.
  The node voids every point of the region with `z_k < n` (`rlow`: `r`
  depends on `z_k` alone and `r < mins s` there).  The rest of the region
  continues at `u` reparametrised by `z_k := n + z_k` (`shR` on the region,
  `shs` on the refs and the unfolded items).  This is MP's lever.
* `USpl k n p kids`: TriGlue's `TSplit` inside the unfold tree (`skid`,
  `sreg`, `sps`).

The soundness is ListGlue2Tr's `uwalk_ok` with the region and the
parameters carried along the path.  A concrete anchor with `z_k < n` would
have a valid tail below its state's bound (`mins_sound` against
`rlow_ok`); otherwise `z_k - n` is its new parameter (`shs_back`,
`rv_shR`); at a split, `snew` is (`sps_back`, `skid_ok`, `rv_sreg`, as in
`twalk_total`).  The statement of `lwalk_leaf` is unchanged, so
`theories/Counters/ListGlueRngLexTr.v` is ListGlueLexTr verbatim on these
families.  Both files compile in about 5 s; `Print Assumptions lgr_sound` /
`lgrx_sound_mirror`: `functional_extensionality_dep` only.

`USpl` was not in the brief; it was needed for the same reason as `URng`.
lg4 answers every case-split request a path raises (`ge`, `mod`, `umod`:
a chain needs `x >= n`, a relation needs `x mod a`) by splitting the
variable in the family's TriGlue tree.  Every OTHER unfold path is then
re-explored inside each kid, and on the depth-counted states those splits
nested five deep.

**2. Range voids alone are not enough** (the worked row
`0RB0LD_1RC1LB_1LA1RA_1LA0LD`, `(001)` ratio 4).  Measured in this order:

| change | families | |
|---|---:|---|
| MP's finder (`MP_F=local MP_DEPTH=2`) | 119 at round 50, still growing | baseline |
| + range voids, depth 2 | 116 at round 50, 646 at round 350 | the same growth |
| + range voids, depth 4 / 5 | 81 (10 queued) / 79 (2 queued) at round 100 | depth is now cheap, but per-family cost explodes |
| + local splits | depth 4 grows again (290+); depth 5 stalls in one family | |
| upper bounds without the eager split (`BLC6_MAXSPLIT=0`) | 800 (cap) in 2 s | the eager split was what kept it bounded |

On a depth-counted state the certified UPPER bound (`lc_maxs`, ~`a^c b_k`)
made lg4 split a symbolic exponent into one singleton per value below it:
hundreds of concrete kids, each a long concrete leaf run (one family took
56 s for 44 leaves).

The decisive measurement was on the REAL run (lg_batch's data pass, with
the exploration's folds on concrete tapes): **558 left-fold misses in 6,000
leaves, 2 right ones**, and the family count still growing (224 at 6,000
leaves).  The passed elements carry left digits `-2` / `-3` at `111111`.
The learned left automaton knew only `-1` (start) and `0`: learn4 learns it
from ~85 periodic snapshots deep enough to align, and they never show a
long carry's digits.  The exploration's off-by-one right misses were the
echo of this.

**3. The left language from every round's turn tape**
(`blc6/turns.c`, `blc6/learn6.py`).  `turns.c` runs the machine twice.
The first pass finds, per round (between two left-anchor entries), the
last step at which the head is at the round's rightmost cell.  The second
pass prints each round's anchor and that TURN tape in lsnap's format.  The
turn tape holds every element the round's carry passed, in its left form.
learn6 feeds those to learn4's `fit_left2` as the deep samples, with
`LDROP=0`: the element nearest the head is the one with the `-2` digit, and
learn4's default drop discarded it.

On the worked row (30M steps, 81 s): 1,038 aligned samples, `lstart`
`-1, -3`, interior `0, -2`.  The real run then misses **2** folds and has
155 families at 6,000 leaves.  The exploration with range voids and local
splits **closes**: 165 families at depth 3, 224 at depth 4, 278 at depth
5, each in about a second.  The certificate has 153 families and 162
`URng` nodes; the replica passes and `CBT_BLC6_00` kernel-checks in ~17 s.

One fix in `learn6`: a turn snapshot ends at the head, so learn3's
`strip_cells` dropped a 0 head cell and with it the head token (0 samples).
The tape is cut at the head and a `1` cell put right of it.

**4. Yields.**  `find6.py find` (learn6's language, `MP_DEPTH=3`,
`BLC6_MAXSPLIT=0`, 1,200 s a row, 3 jobs; about 3 h here across a
container restart; `blc6/runs/sweep1.jsonl`):

| shape (learned unit, ratio) | rows | certify | left |
|---|---:|---:|---|
| `(001)`, 4 (MP) | 23 | **16** | 7 too many families |
| `(011)`, 4 (MP 15 + LIST4 5) | 20 | **12** | 7 too many families, 1 no ranking (`(2,0)`) |
| `(01)`, 2 (MP) | 9 | **8** | 1 too many families |
| `1`, 2 (LIST2) | 1 | **1** | |
| `(01)`, 2 (LIST2) | 8 | 0 | 6 exploration does not settle, 2 too many families |
| `(0011)`, 3 (MP 2 + LIST4 1) | 3 | 0 | too many families |
| `(011)`, 2 (MP) | 2 | 0 | too many families |
| not learned | 15 | 0 | 10 time-out (1,200 s, no learn record), 5 left samples disagree on F states |

The 37 certificates have 119-626 families; the find takes 5-352 s a row
(learning included).  4 rows need the lexicographic liveness
(`lgrx_sound`); the rest are additive (`lgr_sound`).  17 are mirrored.

The second pass (`MP_DEPTH=4`, 1,800 s a row, 4 jobs, about 3 h here;
`blc6/runs/sweep2_d4.jsonl`) over the 44 rows the first left
(`blc6/rows_fail1.txt`) certifies **1** more, the `(01)` ratio-2 row
`1RB1LD_0LC0RB_1RA1LA_0LD0LA` (148 families).  Of the other 43: 22 too many
families, 11 time-outs, 5 left samples that disagree, 4 explorations that
do not settle, 1 no ranking.  Three of its rows never wrote a record (a
multiprocessing worker stuck in its `SIGALRM` time-out, as in §7.4.BLC3);
rerun one process each under a hard kill, all three time out.

| batch | rows | compile (container) |
|---|---:|---:|
| `CBT_BLC6_00` | 1 | 17 s |
| `CBT_BLC6_01` | 4 | 129 s |
| `CBT_BLC6_02` | 4 | 167 s |
| `CBT_BLC6_03` | 4 | 149 s |
| `CBT_BLC6_04` | 4 (2 lex) | 164 s |
| `CBT_BLC6_05` | 4 | 56 s |
| `CBT_BLC6_06` | 4 (1 lex) | 99 s |
| `CBT_BLC6_07` | 3 (1 lex) | 87 s |
| `CBT_BLC6_08` | 5 | 198 s |
| `CBT_BLC6_09` | 4 | 78 s |
| `CBT_BLC6_10` | 1 | 54 s |

01-04 and 06-08 were compiled beside a 3-job sweep.  `ci_costs.tsv` lists
every batch at about twice the container time; `ci_shard.py --check 6`
passes and the slowest shard is unchanged (`CBT_BR_02`, 2,764 s).
`Print Assumptions` on every batch's `cbt_*_covers`:
`functional_extensionality_dep` only.  CI (`core`, `closeout-changed`) was green on #207's merge commit, which
carried 00-07, and on #212's head with 10.

**5. Residue (43 rows), and where each group stops.**  The first error of
sweep 1; pass 2 moved none of them to another group except the row it
certified.

| rows | what | where it stops | next |
|---:|---|---|---|
| 21 | `(001)` / `(011)` ratio 4 (14), `(0011)` (3), `(011)` ratio 2 (2), `(01)` ratio 2 (2) | too many families (800) at depth 3 and at depth 4 | not traced row by row.  8 of MP's 13 late-far-end rows (`mp/farend61.tsv`, last new far end after 5.4M-70M steps) are here; the 3 that settle at 4.5M certify.  The far end itself is read to 300M by asnap, so it is not the obvious cause; the left language (learn6 reads 30M steps of turn tapes) and the right tails' mid-sweep forms are the next suspects.  `blc6/foldmiss_real.py` on one of them first |
| 6 | LIST2 `(01)` ratio 2 | exploration does not settle (MAXROUNDS) | the survey's "b_0 caught mid-transfer, phase-flipping units" rows: the anchor itself is mid-rewrite |
| 5 | (not learned) | learn4: left samples disagree on F states (33/1414 to 1097/1132; 2 of them are the 880-950M far-end rows) | with `LDROP=0` the nearest element's digit varies with how far the head has rewritten it; a per-phase left state, or LDROP=0 only on the turn samples whose head is past a separator |
| 10 | (no learn record) | time-out at 1,200 s, in the learner or the first exploration | learn4's 4M-step snapshot learner and asnap's 300M far-end run on wide tapes; a longer budget on the box |
| 1 | `1RB1RA_1LC0RA_1LA1LD_1LC0LB`, `(011)` ratio 4 | the exploration closes; no ranking for `(2, 0)` (additive or lexicographic) | the first liveness failure on these rows; not looked at |

**Commands** (resumable: `find` skips rows already in its output, caches
the learned languages in `$MP_CACHE`, and re-executes itself under
`PYTHONHASHSEED=0`).

```
cd tools/closeouttr
python3 blc6/find6.py find blc6/rows_scope.txt sweep1.jsonl --jobs 12 --timeout 1200        # ~1 h 20 min on the box
MP_DEPTH=4 python3 blc6/find6.py find blc6/rows_fail1.txt sweep2.jsonl --jobs 12 --timeout 1800
BLC6_T1=300000000 python3 blc6/find6.py find blc6/rows_fail1.txt sweep3.jsonl --jobs 12 --timeout 3600   # longer turn tapes (untried)
python3 blc6/find6.py one 0RB0LD_1RC1LB_1LA1RA_1LA0LD                                       # the worked row, ~80 s
python3 blc6/find6.py batch sweep1.jsonl --tag BLC6 --chunk 4
BLC6_LANG=l4 MP_DEPTH=0 python3 blc6/find6.py one 1RB0LA_1LC0RD_1LA1RB_1LC1RC              # regression: a BLC4 row through ListGlueRngTr
python3 blc6/foldmiss_real.py SPEC 100000 6000      # the real run's fold misses (MP_DEPTH, BLC6_LANG as for find6)
```

Knobs: `BLC6_LANG=l6|mp|l4` (the language), `BLC6_T1` (turn-tape run,
default 30M), `MP_DEPTH`, `BLC6_RNG`, `BLC6_LOCAL`, `BLC6_MAXSPLIT`
(each 0/1), `LG4_LDROP`.

#### 7.4.LE The counters the ladder emitter could not close: five closure gaps, a visit phase per instruction, 181 boarded (2026-09-30)

Workstream LE (batch tag `LE`), over the counters still open at the start:
the DN log counters (`dx/char_all.tsv` shape `log`, kind `counter`; 227),
the SP rows with a visited extent under 1,000 cells at 1e8 steps
(`spb/residue_char.json`; 482), and the open QH rows (144).  853 rows,
`tools/closeouttr/le/rows_{dn,sp,qh}.txt`.  The hybrids and block-list
tapes (BL) and the wide SP rows (SPW) were not touched.

**Where the rows stop, measured first.**  CE3's valfam run
(`le/vf_ce3.jsonl`) already covered 347 of the DN/QH rows, and 48 of them
close.  Emitting those 48 (`le/measure.py`, which runs
`emit_ladder.py --tr [--qh]` and optionally `coqc` and records the NOT BUILT
reason) gave: fill arm with no chain 33, interior arm 11, no visit phase 1,
a fill anchor that reaches no A1 1, and 2 QH boards that fail `coqc`
("true with false").  The first 27 SP rows valfam closed stopped as
follows: board 16, no visit phase 7, interior arm 3, `coqc` 1.  Every fix
below is in the emitter or in a new generic closer.  Each one runs only
where the old path had already failed, so every landed board is
byte-identical.

**The gaps, and what closes them.**

| gap | what it was | fix | boarded |
|---|---|---|---:|
| fill arm, no chain | the chain exists, but it ends one blank the machine WROTE beside a known-empty tail off the fill target.  The interior arm already accepted this through `ceqL` as a one-segment `LadderNest` program; the fill arm did not | the same acceptance for fill arms (`emit_ladder.fill_at`) | 26 DN (`CBT_LE_00`) + most later rows |
| no visit phase, one phase | an instruction that fires only in wider fills is missed at the smallest arm index, where the fill arm is symbolic | retry the fill grid at larger thresholds, so the small indices become concrete; walk a concrete anchor forward in one-sided windows (`_flat_walk`) until it fires | 4 DN + 4 QH |
| no visit phase, several phases | SP's multi-phase counters: the rare instruction fires only in ANOTHER phase's fill, so every phase's anchors miss a different instruction | **`Checkers/LadderCheckNestPvTr.v`** (new, generic): the nested board with the visit phase a function `pvf : Instr -> nat`.  The liveness premise (`glue_neverqhtrN`, `lap_qh_stage`) is per instruction already, and `tops_cof_pv` gives cofinal tops at any phase the cycle returns to.  It reuses `LadderCheckNestTr.lapN` and restates only the fires and both closers.  The emitter falls back to it after every single-phase attempt fails | 23 SP |
| interior arm, quadratic carry | `nest.py` fitted inner rules on the visits minus one at each end, but a carry followed by a sweep back passes the same state/symbol several more times; and after the rounds the count carries constant copies (`(11)^(j+2)`) that the chain engine can fold but never unfold | fit on windows trimmed by up to 3/5 visits; then a **respell**: ZERO rounds of the identity rule `(q,[],h,[]) -> itself` (empty chain, which `check_rule` accepts).  `LadderNest.nrun` compares a segment's start by normal form (`cexact`), so this re-spells the configuration with the copies materialised.  No new Coq | 4 DN (`CBT_LE_03`) |
| `coqc`: `mkFill -1` | a fill that NARROWS the counter (`widens_by = -1`, in a multi-phase cycle with a net gain) was emitted as `mkFill -1 ...`, which Coq reads as a subtraction.  This is SPB's "nat-typed term" | refused with its reason: `LadderFam.f_s` is a `nat` | 0 (23 SP rows, residue) |
| `coqc`: `true` with `false` (QH) | the certificate's mined ladder was derived on the unwrapped machine; one rule fires a pinned (quiet) instruction and fails `check_ladder` on the wrapped one | derive the mined ladder on the machine wrapped at the pins (the closure never uses those rules) | 2 QH |
| `coqc`: boot | the machine leaves a written blank on the OTHER side at the boot, which the exact boot lemma cannot see past | simulate the boot, and go through the lift boot when the sides differ only by trailing blanks | 1 SP |

The fill fix is the one most boards use: 160 of the 181 boards go through
the nested closure, since a fill arm stated through `ceqL` is a nested arm.

**The finder pass.**  valfam at `--cap 150` over the 506 LE rows CE3's run
did not cover (482 SP + 24 DN/QH), in 3 shards (`le/drive_vf.sh K`,
resumable).  It took about 1.9 min a row per job with the container's
other work, 3-4 h of compute, and about 6 h of wall time across two
container restarts.  `famclose.py` over the 64 DN rows CE3 filed as
"families found but none closed" closes 13 with the new emitter (CE3's
run, with the old emitter, closed none of them).

**Yields** (`le/tally.py le/measure_final.tsv` recomputes them):

| | DN | SP | QH | all |
|---|---:|---:|---:|---:|
| rows | 227 | 482 | 144 | 853 |
| **boarded** (`CBT_LE_00..09`) | **47** | **128** | **6** | **181** |
| valfam closes, emitter refuses: fill narrows | | 23 | | 23 |
| ... interior arm (a misread family: the carry reads a whole run past the digit, or the anchor drifts) | 7 | 14 | | 21 |
| ... fill arm / wide fill (3 digits, widens by 1) / other | 1 | 6 | | 7 |
| finder: families found, none closed | 51 | 230 | 77 | 358 |
| finder: no value family / no local rules | 94 | 20 | 29 | 143 |
| finder: time cap (150 s) | 27 | 61 | 32 | 120 |

By closer: nested (`LadderCheckNestTr`) 137, per-instruction visit phase
(`LadderCheckNestPvTr`) 23, lift-tolerant fill 13, plain `LadderCheckTr` or
`LadderCheckQHTr` 8.  Axioms: `functional_extensionality_dep` only (checked
on a board of each kind).  Times, measured at one core: `LadderCheckNestPvTr.v`
1.6 s once its dependencies are built; a board 1.5-2 s, including the
nested and respell boards; a 40-row batch 1.6 s beyond its boards.
`ci_costs.tsv` lists the five batches that take over a minute (60-90 s).
Closeout: 1,547 open when LE started, **1,274** now.  That count includes
BL and SPW, merged from `main`; LE's own share is the 181.

**The residue, by where it stops.**

1. **The emitter (51 rows).**  23 SP rows have a phase cycle with a
   NARROWING fill.  For example, `0RB1LA_1LC1RD_1RB0LA_1LC1RC` runs phases
   0 -> 2 -> 1 -> 0 with widths +1, -1, +1.  `LadderFam.Fill` states
   `f_s : nat`, and a per-phase width offset does not help, because the
   extra digit it would move into a terminator is the counter's top digit,
   which changes.  They want a family theory with an integer widening and a
   positive cycle sum; that is the largest emitter-side piece left.  21
   interior-arm rows are misread families, not cost problems.  On the ones
   traced, the carry either sweeps a whole run of `rest` past the digit it
   increments (no digit of lookahead states that), or the anchor drifts
   one digit per carry into the terminator.  Two rows are wide fills (a
   3-digit target at +1 width, which holds only from width 2).  They need
   `Inv` with a minimum width.
2. **The finder (621 rows).**  Most of them: 358 have families that
   valfam's arms do not close, 143 have no value family, and 120 hit the
   time cap.  famclose has NOT been run on the 230 SP or the 77 QH
   "families found" rows with the new emitter.  On DN it took 13 of 64.
   It costs 5-20 min a row, because every candidate family goes through
   the emitter's full grid.  That is a box job:

```
# on the 14-core box (resumable: famclose skips rows already in its --json)
python3 tools/closeouttr/le/tally.py > /dev/null     # sanity
python3 - <<'P' > le_fc_sp.txt
import json
rem = set(open('closeouttr_remaining.txt').read().split())
for l in open('tools/closeouttr/le/vf_le.jsonl'):
    r = json.loads(l)
    if r['spec'] in rem and not r['closed'] and 'families found' in str(r.get('reason')):
        print(r['spec'])
P
(cd tools/ladder && python3 famclose.py --list ../../le_fc_sp.txt --json ../../fc_sp.jsonl --jobs 12)          # ~230 rows, ~3-4 h
(cd tools/ladder && python3 famclose.py --list ../closeouttr/le/fc_todo_qh.txt --json ../../fc_qh.jsonl --jobs 12 --qh)  # 77 rows, ~1.5 h
python3 tools/closeouttr/sp_ladder_batch.py fc_sp.jsonl --tag LE --chunk 40
python3 tools/closeouttr/sp_ladder_batch.py fc_qh.jsonl --tag LE --chunk 40 --qh
tools/closeouttr/le/board_chunk.sh CBT_LE_NN ...     # gen, build, the four checks
```

At DN's rate (13 of 64), that would board roughly 40-60 SP rows and 10-15
QH rows.

```
# the container loop (what this section ran)
python3 tools/closeouttr/le/measure.py OUT.tsv VF.jsonl... --rows ROWS [--coqc] --jobs 3   # where each row stops
tools/closeouttr/le/drive_vf.sh K                                                          # valfam, shard K (resumable)
python3 tools/closeouttr/sp_ladder_batch.py VF.jsonl --tag LE --chunk 40 [--qh]
tools/closeouttr/le/board_chunk.sh CBT_LE_NN ...
python3 tools/closeouttr/le/tally.py tools/closeouttr/le/measure_final.tsv
```

#### 7.4.HY3 The flat-block hybrids and bouncers: the "unary counters" are two-block transfers, TriGlue seeded at the anchors takes 47 (2026-09-30)

Workstream HY3 (batch tag `HY3`), over the still-open hybrids and bouncers
with a flat block count: the DN/QH rows of §7.4.BL's `bl/classify.tsv`
whose block list does not grow (151), plus the open rows of HY2's "one long
block" residue (`hy2/residue.tsv`), 175 rows in
`tools/closeouttr/hy3/rows.txt`.  The Collatz-like SPW rows, the pure
counters (LE) and the block-list counters with a growing block count (BLC)
were not touched.

**The sample.**  About 30 rows were read by hand (`hy3/diag_sim.py`: the
last sweep turns at each tape end, run-length compressed), then all 175
were split by `hy3/shape.py` (the tape at the last sweep turns, cut into
long periodic blocks of >= 16 cells) into `hy3/shape.tsv`.  The biggest
group is not a counter at all:

| rows | tape at the sweep turns | what it is |
|---:|---|---|
| 66 | two long blocks | **two-block transfers with a reset**: `Lpre u^a Mid v^b Rpost`, `(a, b) -> (a + da, b - 1)` per lap; when `b` runs out the machine rewrites the tape into a new pair `(a0, alpha a + beta)`.  `1RB0LC_1LC0RA_1RA1LD_1LA1LA` is `1 (110)^a 11111 (011)^b 1111`, `a += 2`, `b -= 1`, and at `b = 0` the whole tape becomes `1^(3a + c)` and restarts with `b' ~ a`.  These are HY2's "unary counters" (`(011)^n ... (011)^k`, one block growing linearly and one slowly).  Ten rows are one machine family (`(1)^576 (01)^1579`, `(10)^1579 (1)^576`) |
| 34 | one long block | counter + block hybrids (HY2's shape) whose counter HY2 cannot read: a counter whose low end moves one cell a lap because the block grows one cell a lap on a two-cell unit (the digit words then depend on the position's parity, e.g. `1RB1LD_0RC1RA_1LD1RB_1LB0LD`), counters that step once per several laps, and the two-lap overflow |
| 47 | 1-4 long blocks, shape varies | transfers whose rounds pass through a counter-like phase, and counters beside a block |
| 28 | 4+ long blocks | block lists (`1^(2^k)` doubling, `(1)^k 0^k` ladders): BLC's shape although the count is flat over the sampled window |

**The route for the transfers: TriGlue, seeded at the anchors**
(`tools/closeouttr/hy3_ti.py`, no new Coq).  TriGlueTr's families
(symbolic tapes with affine exponents, one LapDecider chain per leaf,
affine rankings for the fires) state the transfers exactly.  What failed
was the search:

* `ti_batch.py` turns every literal run of two or more copies into a fresh
  variable.  The constant junctions (`11111`, `(1)^4`) become variables,
  and a variable explored at every length opens shapes the machine never
  produces (a 1-block that is always `3a + 4` long, explored mod 3):
  "too many families" at any cap;
* `bl_ti.py` gives each variable a lattice `c + g*x`, but seeds it with a
  generic concrete pass.  Starting constant (`G0 = 0`), the boot's blocks
  stay concrete and a leaf walks the whole lap cell by cell ("leaf too
  long"); starting generic (`G0 = 1`), it explodes as TI does.

`hy3_ti.py` reads the seed off the run.  The configurations at the sweep
turns are normalized as the explorer normalizes a leaf's end and grouped
by family key.  Over one key's turns, a block exponent that never changes
is a constant (lattice step 0), and one that does gets `c` = the least
value seen and `g` = the gcd of the differences.  The boot is the first
turn of the key the run keeps returning to late, and every family met
later starts constant and is widened only by the affine exponents leaves
land on it with (bl_ti's `LExplorer`, `G0 = 0`).  It tries the block
alphabets in order: ti_batch's primitive units of up to 4 cells; then
blanks and units of up to 6 cells (`(0)^a 1 (0)^b` and `(11011)^a` rows
need these); then both again with blocks of >= 16 units generic.
Rankings, replayed checks and rendering are ti_batch's.  A row is one
`tri_sound` line, as in `CBT_TI_*`.  Boots are at steps <= 376 and the
largest certificate has 67 families.

**Yield: 47 rows** in `CBT_HY3_00..03`, all kernel-checked (container, 4
cores):

| batch | rows | compile |
|---|---:|---:|
| `CBT_HY3_00` | 12 | 11 s |
| `CBT_HY3_01` | 12 | 16 s |
| `CBT_HY3_02` | 12 | 11 s |
| `CBT_HY3_03` | 11 | 67 s |

All four are in `ci_costs.tsv` at about twice the container time.  With
them, `ci_shard.py --plan 6` keeps the slowest shard at `CBT_BR_02` alone
(2,764 s).  All rows: 1,324 -> **1,277**.  The whole search is ~2 min
for the 175 rows at 4 jobs (300 s cap a row, most finish in seconds).

**The two-lap overflow: `HybridCtr2Tr` (built, no row boarded).**
`theories/Counters/HybridCtr2Tr.v` extends `HybridCtrTr` in a new file
(the landed file is untouched).  `Print Assumptions h2_sound_nqh_mirror`
shows `functional_extensionality_dep` only; the file compiles in 11 s.
A phase may carry a HOLD.  Its overflow is then a two-lap composite:

1. a KEEP chain `Dm^j ++ T (hi-1) -> Dm^j ++ Th`, a carry case whose
   digits come back as `Dm` instead of `D0`, onto its exit X1;
2. X1's sweep lands on a hold anchor `Ph`, an anchor shape of its own;
3. `Ph`'s overflow chain `Dm^j ++ Th -> D0^(j+1) ++ T lo` runs onto exit
   X2, and X2's sweep lands on the next phase.

The held word `Th` is the top table's entry `hcT hi`.  The numeration,
the ranks, the phase of a rank and the fire families are `HybridCtrTr`'s
unchanged: the composite is one step of the enumeration.  Fire kinds 4
and 5 witness the second lap (chain prefixes of the overflow chain and of
X2's sweep) from the members of the overflow's top family.  The certificate
is `mkH2C (hccert) [(phase, Ph)]`, and a row would be
`apply coversTr_nqh, (h2_sound_nqh(_mirror) _ ...)`.

No row is boarded with it yet, for two reasons found on the way:

* `hy3/hold_probe.py` runs one counter half from `Dm^j ++ X` at every top
  word HY2's finder learns, and reports a hold when the low digits come
  back as `Dm^j` (`hy3/hold_probe.txt`).  It finds a hold in 7 of the 58
  open one-long-block rows, plus HY2's own example.  So the two-lap
  overflow is real, but the group is about 8 rows, not 19.
* In most of those rows the block grows one cell a lap on a two-cell unit,
  so the anchor alternates between two phases.  A two-lap overflow shifts
  the lap parity against the rank parity: after it, the phase of rank `x`
  is `(i0 + x - v0 + #holds) mod L`, not `(i0 + x - v0) mod L`, and the
  number of holds is the counter's digit count.  `HybridCtr2Tr` lands the
  composite on the phase of the NEXT RANK, so on those rows the second
  sweep's check fails, by design.  The fix is to read the phase as
  `(i0 + x - v0 + |low| - |low0|) mod L`.  The top family's phase is then
  a function of `j` alone, but the interior families need a member of a
  given length as well as a given residue, so `hc_int_member` needs a
  length-aware `canon_exists`.

  HY2's example `0RB0LC_1LC1RD_1LA1LB_1RC0RB` does not reproduce from a
  constructed anchor either.  With a small block, its early overflows
  rewrite the block into counter digits (`1^13 0 1^6 -> (10)^9 111` at
  step 204), so the counter half there is not independent of the block.

Finder work left for it: a hold-aware `learn_cycle` (read `Th` and the
hold anchor's shape from the lap after X1), the keep chain (hy2's
`carry_case` with `Dm` as the output digit), and snapshots at the hold
anchor dropped from the family fit.

**Residue: 128 of the 175 rows are still open** (per row in
`hy3/residue.tsv`: shape, `hy3_ti.py` verdict, hold seen):

| rows | shape | where `hy3_ti.py` stops | why |
|---:|---|---|---|
| 12 | two blocks, one shape | no ranking (at every `P` up to 24) | the reset fires the rare instruction only on one parity of the round (`0RB0LC_1LA1RB_1RC1RD_1LA0RB`: only when `b` is odd at the reset, and the next round's `b` is `2 + 3a`).  This is BX's 2-adic liveness, which no mod-P node set sees |
| 10 | two blocks | too many families (6), leaf too long (2), no anchor key (2) | transfers whose reset passes through a transient that is not a block shape |
| 34 | one long block | no anchor key (24), too many families (8), leaf too long (2) | the counter hybrids above.  TriGlue cannot write a counter; HY2's reader cannot write a position-dependent digit alphabet or a hold |
| 44 | 1-4 blocks, shape varies | no anchor key (20), too many families (17), leaf too long (7) | transfers with a counter phase in each round, counters beside a block |
| 28 | 4+ blocks | no anchor key | block lists (BLC's shape) |

**Next.**

1. A phase-parity-aware `HybridCtr2Tr` (phase of rank read with the digit
   count), and the hold-aware finder above: ~8 rows.
2. The one-long-block counters whose low end moves with a two-cell unit
   (the largest part of the 34): a counter whose digit words alternate by
   position parity.  That is a base-`b^2` counter on digit pairs only when
   the block grows by a whole unit per lap, so it needs `HybridCtrTr`'s
   numeration with two alphabets, `D_even` and `D_odd`, and the anchor
   read in the junction's frame.
3. The 12 parity-reset transfers need the 2-adic liveness BX describes.

Commands (resumable: `find` skips rows already in its output):

```
python3 tools/closeouttr/hy3_ti.py find tools/closeouttr/hy3/rows.txt hy3_find.jsonl --jobs 4 --timeout 600 --maxfam 200
python3 tools/closeouttr/hy3_ti.py batch hy3_find.jsonl --tag HY3 --chunk 12
python3 tools/closeouttr/hy3/shape.py tools/closeouttr/hy3/rows.txt > shape.tsv
python3 tools/closeouttr/hy3/hold_probe.py ROWS.txt > hold_probe.txt
```

The whole `hy3_ti.py` sweep is ~2 min here, so it needs no box run.

#### 7.4.TA The Collatz-like rows: a 2-adic lexicographic liveness on TriGlue's families, 143 boarded (2026-09-30)

Workstream TA (batch tag `TA`), over the still-open rows where every route
stopped because the rare instruction fires on some residue classes of a
growing parameter only.  There are 203 rows (`tools/closeouttr/ta/rows.txt`,
sources in `ta/sources.tsv`):

* 160 rows of §7.4.BL's "SPW, irregular fires" class (`bl/classify.tsv`,
  `irr`), 152 SP and 8 DN;
* the 12 parity-reset transfers of §7.4.HY3 (`hy3/residue.tsv`, "no
  ranking"), 8 of them also in BL's `irr` class;
* BX's 29 cube sweep counters (`bx/cube.txt`);
* 10 more open SP rows that an earlier TriGlue run (`spw/ti_all.jsonl`,
  `bl/find1.jsonl`) had left at "no ranking".

The block-list counters with a neighbour recurrence (BLC) were not touched.

**What they are.**  `ta/dump.py` runs the three TriGlue finders in turn
(`ti_batch.py` at its defaults, the lattice finder `bl_ti.py`, the
anchor-seeded `hy3_ti.py`) and keeps the first family set that closes,
i.e. whose only failure is the ranking.  It closes on 170 of the 203 rows.
The family graph is then an exact piecewise-affine round map
(`ta/show.py` prints it).  Read by hand:

| row | lap | round end (the rare instruction's branch) | non-firing branch, shifted |
|---|---|---|---|
| `0RB0LB_1RC1LB_0LD0RD_1LD1LA` (C0) | `F1(a,b) -> F1(a+3, b-2)` | from `F1(0,b)`: odd `b -> (3b+7)/2` fires C0; even `b -> 3b/2 + 2` | `c = b+4`: `c -> 3c/2` |
| `0RB0LD_1RC1RB_1LA1LC_1LA1LA` (D0) | `F2(a,b) -> F2(a-1, b+3)` | from `F2(a,0)`: even `a -> 3a/2 + 2` fires D0; odd `a -> (3a+3)/2` | `c = a+3`: `c -> 3c/2` |
| `0RB0LD_1LC1RB_1RB0LA_1RD0RB` (A0) | two nested laps: `F1` shifts `b` into `a`, `F4(a,b) -> F4(a-2, b+3)` | even `a` fires A0; odd `a -> (3a+7)/2` | `E = 3a + 2b + 21` on `F4`: `x 3/2` per round, constant along both laps |
| `0RB0LC_1LC1LB_0RD1LA_1RB1RD` (A0) | `F14(a,b,c) -> F14(a-1, b, c+3)` | from `F12(0,b)`: even `b` fires A0; odd `b = 2y+1` is halved at one leaf, and the lap turns `y` into `3y` | `b -> (3b+11)/2`, `c = b+11`: `c -> 3c/2` |
| `0RB0LC_1LA1RB_1RC1RD_1LA0RB` (A0, HY3's example) | two-block transfer `(a, b) -> (a + da, b - 1)` | fires only when `b` is odd at the reset; the next round's `b` is `2 + 3a` | `x 3/2` (certificate at `P = 2`) |
| `1RB0RD_1LC0RA_1RB1LC_1LD0LC` (B0) | `F1(a,B) -> F1(a+3, B-2)` | `B` even fires B0; `B = 1 -> F0(a,0,0) -> F1(3, a)` | `E = 2a + 3B + 3`: `x 3/2`.  **Not certified**: see the residue |

Over all 143 rows certified below, `ta/summary.py` (`ta/summary.tsv`) reads
off the ratio `E'/E` on the non-firing edges.  It is ALWAYS the 3/2 map:
directly on one edge (95 rows, `P = 1` or `2`), or split as `x 1/2` at a
halving leaf and `x 3` at a lap (48 rows, `P = 3`).  So these rows are one
family: a two-block transfer whose round ends on a parity, the firing
parity is one branch, and the other branch is `c -> 3c/2` up to a shift.
None of them is Collatz-hard.  Because `3c/2` must stay an integer, `nu_2(c)`
drops by one on every non-firing round, so a run of non-firing rounds is
bounded by `nu_2(c)` at its start.  The orbit is never periodic mod any `P`,
which is why no mod-`P` node set with affine rankings sees this.  Two-
parameter maps occur (the nested-lap row), but the forms that scale are
still one-dimensional: `E` is an affine form in all the family's variables,
constant along every lap.

**The checker: `theories/Counters/TriNuTr.v`** (new, ~620 lines, only axiom
`functional_extensionality_dep`, compiles in ~2 s).  It keeps TriGlueTr's
families, dispatch trees, leaves, chains, node set `S` and boot, all checked
by TriGlueTr's own `fams_ok` / `boot_ok` and enumerated by its `tnxt`.  Only
the liveness is new.  Per instruction `t` the certificate carries a modulus
`l >= 2` and a count `K`.  Per node it carries a LEVEL, an affine form
`E >= 1` (constant at least 1, coefficients in N) and rankings `V_1..V_K`.
On every step between two nodes whose leaves do not fire `t`:

* the level drops; or
* the level stays, `B * E(src) = A * E'(tgt)` coefficient-wise (checked as
  two `ale`), `gcd(B, l) = 1`, `A = l^j * b` with `gcd(b, l) = 1` (`A` and
  `B` are computed from the contents of the two forms; soundness only uses
  the checked equation), so `nu_l(E') = nu_l(E) - j` (`nu_coprime`,
  `nu_pow`, by Gauss's lemma); and if `j = 0`, `(V_1..V_K)` drops
  lexicographically (each `V_i` non-increasing coefficient-wise up to a
  strict drop).

Then `(level, nu_l E, V_1, .., V_K)` decreases in the lexicographic order
on `N^(K+2)` (`lex_ind`), so `t` fires from every anchor (`nfires_lex`).
With `E = 1`, one level and `K = 1` this is TriGlueTr's liveness.  The
vector of rankings is not decoration: the nested-lap rows need `K = 2`,
because an inner lap of length `~a` inside an outer lap run `a/2` times
admits no single affine ranking.  A row is one line,
`apply coversTr_nqh, (tri_nu_sound(_mirror) _ (mkNC TC LIVE))`, where `TC`
is TriGlueTr's `tcert` with an empty rank list.  `tri_nu_sound_qh(_mirror)`
exist for QH rows; none is boarded.  Three corrupted certificates (an `E`
coefficient, a `V` constant, a `V` entry of the first row) fail to compile.
`Print Assumptions tri_nu_sound` shows `functional_extensionality_dep`
only.

**The finder: `tools/closeouttr/ta/nu_find.py`** (untrusted; numpy, scipy).
On TriGlue's closed node set, for `P = 1, 2, 3, 4, 6` and each instruction:

1. the levels are the SCCs of the non-firing graph, topologically;
2. in each SCC, a plain lexicographic ranking (`E = 1`) is tried first;
3. otherwise `E` is a common "eigen-form" of the SCC.  Every positive `E`
   can be rescaled per node so that the ratio is 1 on a spanning tree.  The
   tree constraints give a subspace, and each other edge's ratio `r` is
   taken where the edge's pencil `(M0 - r M1) w = 0` gains kernel
   (numeric generalized eigenvalues of a random square projection, plus
   `2^a 3^b`, each verified exactly).  A positive point comes from an LP;
4. the `l`-power of each ratio goes into node potentials (an MILP makes as
   many edges strict in `nu` as it can), then `V_1, V_2, ..` come from
   staged MILPs, each non-increasing on the edges left and strict on as
   many as possible;
5. the checker is replayed exactly in Python (`nu_check`) before a
   certificate is written.

`ta/nu_batch.py` writes the batches.  The finder takes seconds on the small
graphs and up to 20 minutes on the largest (26 families, P = 3).

**Yield: 143 rows** (134 SP, 9 DN) in `CBT_TA_00..11`, all kernel-checked.
Each batch of 12 compiles in 11-16 s here, so none needs a `ci_costs.tsv`
line.

| source | rows | closed families | certified | no certificate at `P <= 6` | families do not close |
|---|---:|---:|---:|---:|---:|
| BL `irr` only | 152 | 133 | 128 | 5 | 19 |
| HY3 parity resets (8 also `irr`) | 12 | 12 | 9 | 3 | 0 |
| BX cube counters | 29 | 15 | 0 | 15 | 14 |
| other TriGlue "no ranking" | 10 | 10 | 6 | 4 | 0 |
| all | 203 | 170 | **143** | 27 | 33 |

All rows: 1,212 -> **1,069**.

**Residue (60 rows: 33 whose families do not close, 27 with no certificate), and which look hard:**

* **33 rows whose families do not close** (14 cube, 19 `irr`): TriGlue
  "too many families" (31) or "leaf too long" (2).  These are the doubling
  tapes of §7.4.BX and §7.4.SPW, where the block count grows by one per
  burst.  They need a list-of-blocks family (BLC's piece), not a better
  liveness.  They are not 2-adic-hard as far as they were read.
* **The 15 closed cube counters: no certificate** (they timed out at 1,200 s;
  after the finder screened candidate ratios by kernel dimension and in floating
  point, all finish, and none certifies at `P <= 6`).  Read by hand,
  `1RB1LA_0RC0RD_1LC0LA_0LB0RC` is genuinely two-parameter.  The lap is
  `F4(a,b,c) -> F4(a-3, b+2, c+1)` and the round ends on `a mod 3`: residue
  0 fires D0, residue 1 maps `(a, b) -> ((a-1)/3 - 3, b + 2(a-1)/3 + 5)` (a
  3-adic contraction of `a + 5`), residue 2 resets to `(a + b + 2, 0)`.  No
  affine `E` is proportional across the reset (it forces `E` constant), so
  the reset and the chain cannot share a level, yet they lie on one cycle.
  The run continues only while the lowest nonzero ternary digit of `a + 5`
  is 1 at every reset.  On TriGlue's own map (`ta/runlen.py --anchor 9`) the
  longest non-firing run is 4, 5 and 6 resets for starts below 10, 100 and
  1,000: it grows, roughly like a logarithm of the start.  So a proof needs
  a valuation that also drops across the reset, a per-path invariant as BX
  suspected, or a cylinder automaton on residues mod `3^k`.  `P = 9, 27` was
  started on this row but lost to a container restart before it finished.
  The dynamics has no multiplication across the reset (it is an odometer on
  the ternary digits of `S + 7`, `S = a + b`), so it does not look
  Collatz-hard, but it is beyond TriNuTr as built.
* **The 5 other former timeouts** (3 HY3, 2 other): no certificate at
  `P <= 6` either; not read by hand.
* **7 more rows with no certificate at any `P <= 6`** (5 `irr`, 2 other).  In the one read by hand,
  `1RB0RD_1LC0RA_1RB1LC_1LD0LC`, the round map is the clean 3/2 map above,
  but the abstract graph at `P = 1` also has the non-firing cycle
  `F0(0,0,c) -> F0(0,0,c+1)`.  The machine never reaches it (the lap always
  ends with `a >= 3`), but a node (leaf, values mod `P`) cannot state
  `a >= 3`.  So this is TI's "relational invariant" gap (per-node lower
  bounds, or region refinement by small values), not a Collatz obstacle.
  The other six were not read.

No row in this workstream turned out to be genuinely Collatz-hard.  Every
certified family graph has a non-firing branch conjugate to `c -> 3c/2` on a
single forward orbit; the hardest rows found, the cube counters, are an
odometer across resets, not a multiplicative map.

**Next.**  (1) The cube counters: a valuation that also drops across the
reset.  One candidate is `nu_3` of a form defined per PATH (chain, then
reset) rather than per node.  Another is TriGlue's node set on residues
mod 9 and 27 with levels; the finder takes `--plist 9,27 --ells 3`, but that
run did not finish here.  (2) Lower-bound invariants on regions for rows
like `1RB0RD_1LC0RA_1RB1LC_1LD0LC`, TI's relational-invariant idea, which
TriNuTr would take unchanged once the node set can exclude the unreachable
cycle.  (3) The 33 rows whose families do not close go with BLC's list
segment.

Commands (resumable; the finder output is `ta/nu2.jsonl`, the per-row
summary `ta/summary.tsv`):

```
python3 tools/closeouttr/ta/dump.py tools/closeouttr/ta/rows.txt dump.jsonl --jobs 4 --timeout 180
python3 tools/closeouttr/ta/nu_find.py dump.jsonl nu.jsonl --jobs 4 --timeout 1200
python3 tools/closeouttr/ta/nu_batch.py nu.jsonl --tag TA --chunk 12
python3 tools/closeouttr/ta/summary.py dump.jsonl nu.jsonl > summary.tsv
python3 tools/closeouttr/ta/show.py dump.jsonl SPEC                 # a round map
python3 tools/closeouttr/ta/runlen.py dump.jsonl SPEC 3,0 --anchor 9  # non-firing runs
```

The dump takes ~40 min for the 203 rows at 4 jobs.  The finder takes
seconds per row on most rows and up to ~20 min on the largest; ~3 h in all
here.  In particular there is no
coupling between the parity of the round and a second, independent
parameter, which is where a real Collatz obstruction would sit.

#### 7.4.LE2 LE's residue: the respell (the top digit moves between the digit string and the terminator), 37 boarded; the finder residue is two-sided counters, not finder bugs (2026-10-01)

Workstream LE2 (batch tag `LE2`), over the counters still open after LE and
LEF: the LE rows (`le/rows_{dn,sp,qh}.txt`) still in
`closeouttr_remaining.txt`, **442 rows** (180 DN, 166 SP, 96 QH), bucketed
by where LE's `measure_final.tsv` left them in `le2/rows_<class>_<bucket>.txt`.
Block-list rows (BLC3), the Collatz-like rows (TA) and the hybrids were not
touched.

| bucket (LE's measure) | DN | SP | QH |
|---|---:|---:|---:|
| valfam closes, the emitter refuses (`closure`) | 8 | 6 + 23 narrowing | |
| families found, none closed (`fam`) | 51 | 79 | 43 |
| no value family / no local rules (`nofam`) | 94 | 20 | 21 |
| time cap (`cap`) | 27 | 61 | 32 |

**The narrowing fill needs no new Coq: it is a respelling.**  On all 23
narrowing rows the phase a narrowing fill lands in has a terminator that
STARTS with the top digit word.  For example `0RB1LA_1LC1RD_1RB0LA_1LC1RC`
fills phase 2 (empty terminator) into phase 1 (terminator `1101`), so the
width goes k -> k-1.  But `110^(k-1) . 1101` is `110^k . 1`, and that top
digit cannot change inside phase 1, because the phase runs until its own
top, which is all top digits.  So phase 1 is read with one more digit and
terminator `1`: the same tapes, the same tops, the widths go +1, 0, 0 instead
of +1, -1, +1, and the fill INTO the phase gets one top digit on its target
suffix (`mkFill 0 [] 0 [1] 1`).  On the three two-cell rows (digits `11`/`10`)
the move goes the other way.  `(10)^k` narrows onto `(11)^(k-1) 0111`, but the
phase it narrows FROM is entered at `... 10 11 10` (the fill target suffix
`[1,0,1]` ends in a top digit), so that phase is read with one digit fewer
and `10` on its terminator.  `emit_ladder.respell(cert, off)` takes one offset
per phase:

* `off[ph] > 0`: move up to `lead(tail[ph])` top-digit words off the front of
  the phase's terminator into the digit string;
* `off[ph] < 0`: move top digits onto the terminator, allowed only if every
  fill landing in the phase has that many top digits at the end of its
  target suffix.  A boot that is then too narrow moves to the next member
  the respelt family spells (`qh_boot`).

Every fill's widening becomes `s + off[to] - off[ph]`, which must be a `nat`.
`respell_narrow` takes the smallest such offsets and runs only when some
fill narrows.  The result is an ordinary `Fam` whose fill targets need not
have value zero.  `fam_next` already reads targets by value, so the kernel
(`LadderFam`, `LadderCheck*`) is untouched, and every arm is re-checked as
before.  **23 of 23 board** (`CBT_LE2_00`).

**The same move fixes 14 of the interior-arm rows.**  The 14 SP interior-arm
rows are counters whose fill is
`1^k -> 0^k 1`.  valfam reads the top digit as part of the counter, so the
value at width k runs from `2^(k-1)` up and the top digit never changes.
`LadderCheck`'s class split still needs the END arm `t^r d . terminator`
for `d < t` at the last digit, a tape the machine never builds.  Its carry
turns back on the next digit's first cell, which past the last digit is a
blank, so the end arm has no chain.  Respelt with `off = -1` (the top digit
on the terminator, fill target `0^k` at width k+1), the end arm is the
reachable one.  The emitter now retries a family whose closure is not built
with up to four respellings (`respell_offsets`, fewest moved digits first).
The first attempt is the old one, so every board that built before is
byte-identical; the 23 narrowing boards were re-emitted and compared.
**14 of 28 closure-stage rows board** (`CBT_LE2_01`: all 14 SP
interior-arm rows; none of the DN ones, below).

Times (one core): a board compiles in 1.0-1.1 s, and each batch builds in
51 s at `-j4` including its boards.  Axioms: `functional_extensionality_dep`
only (`Print Assumptions` on a board of each batch).

**Where the other 14 closure-stage rows stop:**

* **6 DN interior arms.  4 of them SWEEP the run past the digit**
  (`le2/sweep_detect.py`'s test on valfam's own family: the arm has a
  chain against `top^m 0` for every m = 1..4 and none against an opaque
  tail after `top`).  On
  `0RB0LA_0RC1RB_0LD1RC_1LA1LD` the increment of `1^n 0 . 1^m 0 rest`
  writes the `1` and then walks right across the `1^m` to the next `0` and
  back (the cost 6, 10, 14, ... tracks m).  No digit of lookahead states
  that, and `LRule` has one index, so the arm needs a second index for `m`:
  a class split `t^n d t^m e rest`.  That is new kernel, not an emitter fix.
  The other 2 have an r=0 arm and fail at longer carries (the "other"
  shape below).
* **2 SP rows: a fill target of 3 digits at +1 width**
  (`mkFill 1 [0;1;1] 0 [] 1`, LSB side), which holds only from width 2.
  `Inv` with a minimum width; the respell cannot move LSB-side digits.
* **4 multi-phase fill arms with no chain** (cycles 0, 0, 2, 0 over 4
  phases), **1 interior class arm** (DN `1RB0RC_1LC1LA_0LC1RD_1LB0RD`,
  one-cell digits, terminator `11`), and **1 fill anchor that reaches no
  A1** (DN).

**The finder residue (step 2), characterised on a sample.**
`ladder/nofam.py` on 30 "no value family" rows (18 DN, 6 QH, 6 SP;
`le2/nofam30.jsonl`):

| far side at the best anchor | rows | what it is |
|---|---:|---|
| a second counter | 18 | the side away from the counter has its own successor: a two-sided machine.  In `1RB1LD_1RC0RB_1RD0LD_1LA0LD` it is a mod-3 clock (`10111 -> 10001 -> 10011`) that advances on every anchor visit while a binary counter on the near side counts; in `0RB1RA_0LC0RA_0LD1LD_1RB1LC` it is a nested counter (a low counter in a fixed-width window whose overflow increments the high one).  The far sides count 2-20 distinct values on 6 of them and 200-1,500 on the rest |
| constant, fibonacci weights | 5 | `0RB1LD_1LA1RC_1LA1RB_0RC0LD`: two-cell `11` tokens at a MOVING cell offset (`0000 11`, `11 00 11`, `0 11 0 11`, `00 11 11`).  No fixed digit grid reads it, and `valfam --numeration --cap 400` still finds no family |
| unbounded | 4 | far sides that keep changing, with no successor function |
| bounded oscillation | 2 | |
| unary | 1 | |

And on the DN "families found" rows (`le2/sweep_detect.py`, famclose's
first four families, 17 rows; `le2/sweep_dn.jsonl`): **1 sweep, 16 "other"**.
In the "other" rows the r=0 interior arm has a chain, and the carry fails at
r >= 1.  The one read by hand, `0RB0LC_1LA1RB_0RB0LD_0RB1LD`, is read as base
3 (digits `10`, `01`, `11`) but is not positional: the low two digits run
`00, 10, 20, 11, 21, 02, 12, 22` (8 states), so the d=0 arm at r >= 1 is
stated on tapes the machine never builds.

So the largest piece of the finder residue is **two-sided machines** (a
second counter or clock on the far side), then **non-positional
numerations** (moving offsets, 8-state digit pairs).  Neither is a
`valfam.py`/`famclose.py` bug: each needs a family theory `LadderFam` does
not have.  For the clocks, that is a far side with a phase that advances on
every successor, not only on fills; for the rest, a two-sided family.  No
finder fix was made.

**famclose with the respell, measured here.**  On the DN "families" rows
(LE's emitter had closed none of these 51), 0 of 17 close.  Of 136 family attempts, 100
fail the interior arm (the "other" shape above), 16 the fill arm, and 20
are narrowing families the respell cannot state: no offsets within the
leading and trailing top digits make every widening a `nat`.  In the two
read (`0RB0RA_1RC1LD_1LC1RB_0LD0LA`, `0RB1LA_1RC0LA_0LD1RB_1LB0RC`) the
terminator the narrowing fill lands on (`101`, `0101`) does not start on a
digit-word boundary: the digit framing shifts by a cell between phases,
which is the moving-offset shape again.  On
SP, 0 of the first 9 close (`le2/fc_sp.jsonl`; a container restart stopped
the run).  Of their 64 family attempts, 42 are narrowing families the
respell cannot state and 22 fail the fill arm.  So the SP "families" rows
are narrowing cycles of the misaligned-terminator kind above, not the
aligned kind `CBT_LE2_00` boarded.  At 10-40 min a row here, the rest is
the box job below.  The 4 SP time-cap rows tried close 0 of 4
(famclose skips valfam's arm miner, so a time cap is not the reason).

**Yields:** 37 rows (`CBT_LE2_00..01`), all SP.  Closeout: 891 open
when LE2 started, **854** now.

**Box run** (resumable; famclose skips the rows already in its `--json`):

```
tools/closeouttr/le2/box.sh 12        # famclose over le2/rows_{sp,qh,dn}_fam.txt still open
# SP 79 rows ~3 h, QH 43 ~1.5 h, DN 51 ~2 h at 12 jobs (10-40 min a row a job)
python3 tools/closeouttr/sp_ladder_batch.py tools/closeouttr/le2/fc_sp.jsonl tools/closeouttr/le2/fc_dn.jsonl --tag LE2 --chunk 40
python3 tools/closeouttr/sp_ladder_batch.py tools/closeouttr/le2/fc_qh.jsonl --tag LE2 --chunk 40 --qh
tools/closeouttr/le/board_chunk.sh CBT_LE2_NN ...
```

```
# the container loop (what this section ran)
python3 tools/closeouttr/sp_ladder_batch.py VF.jsonl --tag LE2 --chunk 40   # the emitter retries respellings itself
tools/closeouttr/le/board_chunk.sh CBT_LE2_NN
(cd tools/ladder && python3 nofam.py ../closeouttr/le2/nofam30_rows.txt --json ../closeouttr/le2/nofam30.jsonl)
python3 tools/closeouttr/le2/sweep_detect.py tools/closeouttr/le2/rows_dn_fam.txt tools/closeouttr/le2/sweep_dn.jsonl
```

#### 7.4.LE3 LE2's counter residue: the "two-sided" rows are one counter read wrongly; three new generic checkers, 67 boarded (2026-10-01)

Workstream LE3 (batch tag `LE3`), over LE2's residue: the 442 rows of
`tools/closeouttr/le2/rows_{dn,sp,qh}_{cap,closure,fam,nofam}.txt`, all
open at the start (closeout 824).  The block-list rows (`blc4/rows216.txt`),
the Collatz-like rows (TA), the flat-block hybrids and the cube sweep
counters were not touched.

**The main finding: LE2's "two-sided machines" are not two counters.**
Both of LE2's worked examples, and most of what it filed as "a second
counter on the far side", are ONE counter that LE2's readings could not
state.  There are three shapes, and each now has a generic checker in a new
file (nothing landed is modified; `Print Assumptions` on every closer shows
`functional_extensionality_dep` only).

| shape | example | what it is | checker | boarded |
|---|---|---|---|---:|
| **step counter** | `1RB1LD_1RC0RB_1RD0LD_1LA0LD` (LE2's "mod-3 clock") | a base-4 counter that adds **3** per anchor visit, so its low digit cycles through the residues mod 3 while the high digits count.  valfam tries `STEPS = (1, 2)` only | `Checkers/LadderCheckStepTr.v`: a positional base-`b` `Fam` with step `s` dividing `b - 1`.  The value mod `s` is the digit sum mod `s`, an invariant per phase (`cres`); the successor splits three ways on the LOW digit (`u + s < b`: no carry; a carry through `t^n d`; the top `u t^n`), and the residue pins the top's low digit to one value per phase (`utop`), so the fill law applies as at step 1 | 12 (`CBT_LE3_00`, `_02`) |
| **terminator run** | `0RB1LA_1RC0LA_0LD1RB_1LB0RC` (LE2's "misaligned narrowing" and its nested-counter class) | `[B1] x (01)^m`: `x` binary over the words `11`/`10`, then a RUN of the terminator word.  Inside a width `x` counts; the top of `x` narrows it by a digit and lengthens the run (`(10)^j (01)^m -> (11)^(j-1) (01)^(m+1)`); an empty `x` refills (`(01)^m -> (11)^(m+1) 01`).  valfam reads it at small widths as a multi-phase family whose fills run `+2, -1` with terminators `01`, `0101`, which no respell states | `Checkers/LadderCheckRunTr.v`: a `Fam` for the digits plus the run word `T`, an end word and the refill law `(a, c)`; a total digit-wise successor; three arm classes (interior `t^n d X`, narrowing `t^j T X`, refill `T^m suf`); liveness by the length of `x` then its value, so refills recur and the fires are read from the refill arms | 41 (`CBT_LE3_01`; 23 never-QH, 18 QH) |
| **Zeckendorf** | `1RB1RA_0LC1LB_0RC1LD_0RA0LD` (LE2's "fibonacci weights") | a one-cell string with weights 1, 2, 3, 5, ... and no two adjacent ones, then the terminator `01`; valfam's `fibonacci(shifted)`, which `LadderCheck`'s `Fib`/`FibL` (weights 1, 1, 2, ...) do not state | `Checkers/LadderCheckZeckTr.v`: the digit-wise Zeckendorf increment `zinc`; every canonical string is `u (01)^k s` (`u` = `[]` or `[1]`, `s` = `00r`, `0` or empty), giving interior, end and top classes in two kinds; the width bound `fibvl 1 x < fibw (|x|+1)` makes tops recur | 14 (`CBT_LE3_03`, `_04`, `_05`; 4 QH) |

How each was found:

* **Steps.**  `le3/vf_step.py` runs valfam unchanged with `STEPS = 3..8`.
  Over the 255 nofam and cap rows (4 shards, cap 300 s; `le3/stp_*.jsonl`) it
  closes 26 rows: 12 base-4 step-3 families (all board; the first is the
  clock row), 1 base-2 step-4 family (step 4 does not divide `b - 1 = 1`: refused),
  and 13 step-1 Zeckendorf families that valfam reaches only because the
  restricted steps let its fallback passes run.
* **Runs.**  `le3/termrun_detect.py` reads the anchor visits (other side
  blank) as `pre x T^m suf`, with `x` over exactly two words and `m` taking at
  least 3 values; 42 of the 431 rows read this way (40 with words `11`/`10`
  and run `01`), and `le3/emit_run.py` reads the digit order and the refill
  law off consecutive visits.  41 of the 42 board; the 42nd
  (`1RB0RD_1LC1RA_0RB0LC_1LD0LA`, words `00`/`10`, run `11`) refills to
  something other than `D0^(m+a)`.  37 of the 41 are LE2 `fam` rows (the
  box's famclose run cannot state them, so it will not double-board them).
* **Zeckendorf.**  From the step sweeps: 14 rows, all board.

The three emitters (`le3/emit_step.py`, `emit_run.py`, `emit_zeck.py`) share
`emit_ladder`'s header and arm search (`emit_step.Arms`: a chain, a chain off
its target only by blanks beside a known-empty tail, or a `LadderNest`
program; nested programs only after every arm has failed without them, since
each costs seconds).  Every arm is stated as a `ReachL` segment program and
every fire as an `nfire`, so each checker has both closers
(`board*_neverqhtr` on the wrapped machine, `board*_qhtr` past the quiet
instructions' last fire).

**Times.**  Each checker compiles in 1-2 s.  A board compiles in 1-2.5 s at
one core (the 41 run boards about 1 s each), a batch in about 1 s beyond its
boards.  `ci_costs.tsv`: `CBT_LE3_00` 60, `_01` 120, `_03` 60 (the others
are small).  `ci_shard.py --plan 6` keeps the slowest shard at `CBT_BR_02`.

**A fourth checker that boards nothing: `LadderCheckNarrowTr.v`.**  Built
first for the "misaligned narrowing" families (a `Fam` plus a narrowing per
phase and a floor per phase, `minw`; liveness needs only that tops recur).
On the row it was built for, the narrowing family is a misreading: the
machine's `(10)^2 0101` never occurs, and the row is a terminator-run
counter (above).  It is kept (generic, compiled, `le3/emit_narrow.py`) but
no row is boarded with it.

**Yields** (67 rows; closeout 824 -> **757**):

| LE2 bucket | rows | step | run | Zeckendorf | open |
|---|---:|---:|---:|---:|---:|
| DN nofam | 94 | 12 | | | 82 |
| DN fam | 51 | | 6 | | 45 |
| DN cap / closure | 27 / 8 | | | 2 | 25 / 8 |
| SP nofam | 20 | | 4 | | 16 |
| SP fam | 79 | | 13 | | 66 |
| SP cap / closure | 61 / 6 | | | 8 | 53 / 6 |
| QH fam | 43 | | 18 | 1 | 24 |
| QH nofam / cap | 21 / 32 | | | 3 | 21 / 29 |

**Where the rest stop** (375 of the 442):

1. **Nested and two-sided counters that are really two counters.**  The
   cited nested example `0RB1RA_0LC0RA_0LD1LD_1RB1LC` is not a clean product:
   the anchor tapes shift structure every few laps
   (`111111011000001001111011011100000101010`), no reading fits.  Rows like
   `1RB1LA_1RC0RB_1LD1RA_1LA0LD` are bouncers with a counter at one end
   (`1^k 0^7 1001 (001)^m`), the hybrids' shape.  Neither is in this file.
2. **Zeckendorf over two-cell tokens at a moving offset**
   (`0RB1LD_1LA1RC_1LA1RB_0RC0LD`, LE2's five "constant, fibonacci weights"
   rows): the tape is `c_i = x_i OR x_(i-1)` of a Zeckendorf `x`, i.e. each
   one written as `11` across two cells.  That is a bijection but not a
   digit-word code: it wants a `Fam` whose cells are a two-state transducer
   of the digits, not `flat_map dig`.  The increment and the bound of
   `LadderCheckZeckTr` carry over unchanged.
3. **valfam closes, no checker**: 1 base-2 step-4 family
   (`1RB1LD_1LC0RB_1RD0LC_1LA1RB`; step and base are coprime, so the
   residue is not a digit sum and the top is not one string per phase), and
   CE3's one `fibonacci` (greedy) row whose interior arm has no chain.
4. **The rest of the `fam` / `closure` buckets** are LE2's shapes (DN
   carries that sweep the run past the digit, 8-state digit pairs,
   three-digit fill targets).  The step sweep over the 150 fam/closure rows
   still open (`le3/stpf.jsonl`, steps 3..8, cap 300 s) closes 2: one more
   Zeckendorf row (boarded, `CBT_LE3_05`) and CE3's greedy `fibonacci` row
   again (interior arm, no chain).  Of the other 148: no value family 84,
   families but none closed 54, time cap 10.

```
# the container loop (what this section ran)
tools/closeouttr/le3/drive_step.sh tools/closeouttr/le3/stp_todo_K.txt tools/closeouttr/le3/stp_K.jsonl   # K = 0..3, resumable
python3 tools/closeouttr/le3/step_batch.py STEP.jsonl --tag LE3            # step > 1 (LadderCheckStepTr)
python3 tools/closeouttr/le3/step_batch.py STEP.jsonl --tag LE3 --kind zeck   # Zeckendorf (LadderCheckZeckTr)
python3 tools/closeouttr/le3/termrun_detect.py ROWS termrun.jsonl
python3 tools/closeouttr/le3/run_batch.py tools/closeouttr/le3/termrun.jsonl --tag LE3   # LadderCheckRunTr
tools/closeouttr/le/board_chunk.sh CBT_LE3_NN
```

#### 7.4.LE4 LE3's counter residue: no bouncer hybrids; the Zeckendorf transducer, ladder-free positional readings, a marked terminator run and the sweep; 27 boarded (2026-10-01)

Workstream LE4 (batch tag `LE4`), over LE3's residue: LE2's row lists
`le2/rows_{dn,sp,qh}_*.txt` still in `closeouttr_remaining.txt`, less the 3
TA rows: **372 rows** (`le4/rows.txt`; by LE2 bucket 160 DN, 141 SP, 71 QH).  Branched from
`main` at 744 open with `claude/closeout-le3` (`CBT_LE3_05`) merged.  The
block-list rows (`blc4/rows216.txt`, no overlap) and the Collatz-like rows
were not touched.  The owner's `closeout-le2box` branch had not appeared
when this ran, so no row was skipped for it.

**1. There are no counter-plus-bouncer hybrids here.**  The tape extent of
every row at 1e5 · 4^i steps (`le4/ext.c`, `le4/extent.tsv`) grows by a
constant per factor of 4 in 364 rows and by at most 1.2x in the other 8:
all 372 are LOG-growth.  A hybrid in HY's sense has a block swept every lap,
so its extent grows like a square root, and `HybridGlueTr` / `HybridCtrTr` /
`HybridCtr2Tr` state exactly that (a lap per counter increment that crosses
the block).  None of them applies, with any counter part.  LE3's example
`1RB1LA_1RC0RB_1LD1RA_1LA0LD` (`1^k 0^7 1001 (001)^m`) grows 52, 60, 68, ...
cells: the `1^k` block gains one cell per OVERFLOW (it is a unary tally of
the widths), not per lap, and the right part is a counter whose low bits
drive the `(001)^j` region.  It is a nested counter, not a bouncer.  The
anchor-seeded TriGlue (`hy3_ti.py`, §7.4.HY3) on the first 32 rows: 0
certificates ("too many families" / "leaf too long" on every one;
`le4/hy3ti_32.jsonl`), as expected of counters.  At the overflows
(`le4/ovf.c`, `le4/ovf.tsv`) one tape end grows in 236 rows and both ends in
136 (the "two-sided" / nested shapes).

**2. Zeckendorf over two-cell tokens: `LadderCheckZeck2Tr`, 4 of 5.**  The
tape `c_i = x_i OR x_(i-1)` is the token string of `x` (read from the head,
every `1` of a Zeckendorf string is followed by a `0`) under `0 -> 0`,
`10 -> 11`: `zc`, a two-state transducer.  `theories/Checkers/LadderCheckZeck2Tr.v`
imports `LadderCheckZeckTr`'s `zinc`, bound and class split unchanged, and
changes only the cells: the configuration at `x` is
`fm_pre F ++ zc (x ++ [0]) ++ T` (`T`, the terminator, in cells).  Each
Zeckendorf class `u (01)^k s` becomes one side over the two-cell words `11`
/ `00` (`U 0 = 0`, `U 1 = 11`): interior `U i (11)^k 0 X -> U0 i (00)^k 11 X`,
end `... 0 T -> ... 11 T`, top `U i (11)^k T -> U0 i (00)^k 00 T`.  Finder
`le4/zeck2_detect.py` (anchor, prefix and `T` by generating
`zc (zinc^n x0 ++ [0]) ++ T` against 150 visits), emitter
`le4/emit_zeck2.py` (LE3's `emit_zeck.py`, cells changed).  4 of LE2's 5
rows board (`CBT_LE4_00`, all QH; `T = 11`, boot `x0 = [0]` at step 20-24).
The fifth, `0RB1LC_1LC0LC_0RD1LA_1RD1RB`, counts DOWN in the same code
(per width `0, 4, 3, 2, 1`, then wider): a decrementing `zinc` is a
different checker, for one row.

**3. Positional counters read straight off the anchors: `le4/pos_detect.py`,
9 boarded.**  valfam names its digit words from its mined ladder
(`digit_words`), so a row whose ladder names none is "no value family"
even when its anchor visits read as an ordinary odometer.  `pos_detect.py`
skips the ladder: for every end anchor with a constant far side it tries
prefixes up to 3 cells, terminators up to 8, digit widths 1-4 and every
assignment of the observed words to `0..b-1`; it drops visits that do not
decode or repeat (the fill passing the anchor again) and keeps a chain of
at least 80 `+1` / fill steps with at least 2 fills and one fill law.  It
writes a valfam-shaped certificate (one phase, binary code, step 1, no
arms) for `emit_ladder.py --tr`, which builds its own closure arms.  It
reads **143** of the 372 rows (1.4 s a row; ~7 min for all at 4 jobs).
`le4/try_emit.py` runs the emitter in parallel, first without the nested
search (`le4/emit_ladder_nonest.py`: `nest.derive_nested` stubbed, the
`ceqL` one-segment wrap kept, which many of these need: the carry leaves a
blank on the far side).  **9 board**: `CBT_LE4_01` (5), `_02` (2 QH),
`_03` (2), through `LadderCheckTr` / `LadderCheckQHTr` unchanged.  Where
the other 134 stop:

* **fill arm (116; 60 of 60 probed)**: the concrete fill
  `t^k T -> fill(k) T` reaches its target, but its cost roughly DOUBLES
  per width (`le4/fill_probe.py`: 52, 102, 200, 394, ...; 99, 199, 399,
  ...).  The fill counts: the visits the finder dropped as transients are a
  second phase.  Read by hand (`0RB0LC_1LC0RD_1LA1LD_0LA1RB`, digits
  `10`/`11`), that phase is a terminator run with a marker (item 4);
* **interior arm (16)**: of which 10 are SWEEPS (`le4/sweep_probe.py`: the
  `r = 0` arm has no chain against an opaque tail and one against
  `t^m z Y` for every m = 0..4), all 10 boarded by item 6; the rest are
  carries whose cost doubles;
* **a 3-digit fill target at +1 width (2)**: §7.4.LE2's two SP rows,
  refused by `emit_ladder` (`Inv` would need a minimum width).

**4. A terminator run with a marker: `LadderCheckRun2Tr`, 4 boarded.**  The
fill-that-counts rows are LE3's terminator-run shape with one difference: a
MARKER word `M` sits between `x` and the run, and the run may be empty:

    pre ++ x ++ M ++ T^m ++ suf      (0RB0LC_1LC0RD_1LA1LD_0LA1RB: A1 (10|11)^j 0 (11)^m)
    (x, m) -> (x+1, m);  (top^j, m) -> (0^(j-1), m+1);  ([], m) -> (0^(m+a), c)

LE3's `LadderCheckRunTr` is the case `M = T`, `m >= 1` (its narrowing
`t^j T X -> 0^(j-1) T T X` needs the word after `x` to BE the run word).
`theories/Checkers/LadderCheckRun2Tr.v` is that file with `M` added (every
name suffixed `M`) and three changes: the invariant drops `1 <= m` (refill
arms indexed from 0), the narrowing is `t^j M X -> 0^(j-1) M T X`, and the
interior class carries ONE WORD OF LOOKAHEAD (`t^n d w X`, `w` the next
digit or `M` when `x` ends; `ilookM`).  Finder `le4/termrun2_detect.py`
(LE3's reading with a marker; a reading is kept only if consecutive visits
follow the three laws: at least 40 steps, 2 narrowings and a refill, the
transient visits skipped), emitter `le4/emit_run2.py`, batches
`le4/run2_batch.py --jobs 4`.  It reads **44** rows (`le4/termrun2.jsonl`;
markers `0`, runs `1`, `01`, `10`, `11`, `111`; 10 s a row).  **4 board**
(`CBT_LE4_04`, SP).  The other 40 (`le4/run2_batch.log`):

* **refill (18)**: the concrete refill `M T^m suf -> 0^(m+a) M T^c suf`
  reaches its target at every m tried, every instruction fires from it, but
  its cost doubles with m (20, 32, 52, 88, 156, 288, ...; 43, 71, 123,
  223, ...): the run is itself counted down at the refill, a THIRD level;
* **interior, sweep (11)**: with a concrete tail the carry's cost does not
  depend on how long the tail is, but with next digit `1` it has no chain
  even at `r = 0`: the carry walks the following run of ones (in 8 of the 11
  `M = 0`, `T = 1`, so the whole tape is `x 0 1^m`).  Lookahead does not
  help (re-run with it: the same 4 board).  10 of the 11 board through
  their positional reading and the sweep checker (item 6);
* **interior, nested (9)**: the carry's own cost doubles with n (4, 16, 36,
  72, 140, ...): the digits are themselves counters;
* **refill law (2)**: an empty `x` refills to something other than
  `D0^(m+a)`.

**6. The sweep: `LadderCheckSweepTr`, 10 boarded.**  The rows whose carry
walks across the run of top digits after the digit it increments (LE2's
"DN carries that sweep the run past the digit"; `le4/sweep_probe.py` finds
10 among the positional readings, all with affine fills).  The class
`t^n d t^m e Y` has two run lengths, which no arm states, but its increment
is three ordinary one-index `ReachL` programs in a row:

* the carry `A d ra`: anchor -> the PIVOT, the head on the incremented
  digit's last cell, about to step into `X = t^m e Y` (opaque);
* the excursion `P d k ph rm`: pivot -> across `t^m` to `e` (kind `k = e`)
  or to the terminator (`k = b - 1`) and back to the pivot, the tape
  unchanged, both tails opaque (the counter-side one known empty at the end);
* the return `C d k ra`: pivot -> anchor, `X` opaque again.

Up to `lift` the configuration `A` lands on IS the one `P` starts from (the
counter side of `A`'s right-hand side and the far side of `P`'s are empty,
so the opaque tails carry the rest), so composing needs only `csteps_lift`
and `stepn_csteps_at`: no new chain engine.
`theories/Checkers/LadderCheckSweepTr.v` states that over `LadderCheck`'s
positional family (class split, `fill_top`, `iter_total`, `tops_cof_pv`
reused; fill arms and fires as in `LadderCheckTr`); `Print Assumptions`:
`functional_extensionality_dep` only.  The emitter `le4/emit_sweep.py`
reads the pivot and the return off a simulation of small increments and
requires them to be the same for every `n, m`.  What it found: in 6 rows
the machine sweeps FIRST and carries on the way back (the pivot's far side
is the uncarried `t^n`); in 4 (2-cell digits) the pivot is half-way through
writing the digit (`01` between `00` and `11`), and the machine writes a
cell beyond the anchor too.  **10 of 10 board** (`CBT_LE4_05`, `_06`, all
DN).  Tried on all 120 other open positional readings: 0 more (in every one
the excursion changes the tape: nested counters).

**5. The `fam` / `closure` remainder, measured.**  Of LE2's `fam` rows
still open (66 SP, 45 DN, 24 QH), every SP and QH row and 25 of the 45 DN
have an LE4 reading (item 3 or 4); 2 QH board, and every other one stops at
one of the shapes above.  Of the 14 `closure` rows (8 DN, 6 SP), 12 read
(8 as marker runs, 4 positional) and none boards: they stop at the sweep,
the nested carry and the doubling fill.  The cheap fixes found were the
ladder-free reading (item 3) and the marker (item 4); the two 3-digit fill
targets were left (two rows, a checker change).  LE2's "8-state digit
pairs" are the nested-carry rows of items 3 and 4 seen at a positional
anchor, and its "DN carries that sweep the run past the digit" are the 11
sweeps.

**Yields** (27 rows; closeout 744 -> **717**; per row `le4/residue.tsv`,
`le4/residue.py`):

| batch | rows | class | how | compile (container, `-j4`, incl. boards) |
|---|---:|---|---|---:|
| `CBT_LE4_00` | 4 | QH | `LadderCheckZeck2Tr` (two-cell Zeckendorf) | 52 s (the checker 40 s) |
| `CBT_LE4_01` | 5 | 2 DN, 3 SP | `pos_detect` + `LadderCheckTr` | 44 s |
| `CBT_LE4_02` | 2 | QH | `pos_detect` + `LadderCheckQHTr` | 11 s |
| `CBT_LE4_03` | 2 | SP | `pos_detect` + `LadderCheckTr` | 48 s |
| `CBT_LE4_04` | 4 | SP | `LadderCheckRun2Tr` (marker run) | 43 s (the checker 42 s) |
| `CBT_LE4_05` | 6 | DN | `LadderCheckSweepTr` (the sweep) | 57 s (the checker ~40 s) |
| `CBT_LE4_06` | 4 | DN | `LadderCheckSweepTr` | 42 s |

All in `ci_costs.tsv` at 90 s (the runner is about twice as slow); the
slowest shard is still `CBT_BR_02`'s.  `Print Assumptions` on both closers of
each of the four new checkers and on a row of `_00`, `_01`, `_04`, `_05`:
`functional_extensionality_dep` only.

**Where the rest stop** (345 of the 372):

| LE4 reading | rows | where it stops | what it is |
|---|---:|---|---|
| none | 224 | no finder reads them (177 grow at one end, 47 at both; 126 DN, 55 SP, 43 QH) | LE2's `nofam`/`cap` bulk.  Read by hand: nested counters (`1RB1LA_1RC0RB_1LD1RA_1LA0LD`, a unary width tally beside a counter that drives a `(001)^j` region), counters whose anchor visits are interleaved with a second phase no single terminator reads |
| positional | 90 | fill arm: the fill's cost doubles per width | a second counting phase at the overflow; for the rows read by hand it is a marked terminator run, but these do not parse as one at any anchor `termrun2_detect` tries (other marker/run lengths, or a deeper phase) |
| marker run | 18 | refill: cost doubles with the run | a third counting level: the run is counted down at the refill |
| marker run | 1 | interior arm: no chain past `n = 0`, and its excursion changes the tape | `0RB1RC_1LA1RB_0LD0RC_1LD0LA` |
| marker run | 9 | interior arm: the carry's cost doubles | nested digits |
| marker run | 2 | refill to something other than `D0^(m+a)` | |
| zeck2 | 1 | counts down | a decrementing `zinc` |

**Next.**  The doubling fills and refills (90 + 18) and the nested carries
(9) are counters nested two and three deep: a RECURSIVE family (a counter
whose fill or refill is itself one of these families, the inner family's top
being the outer arm's end) would state them, with `LadderCheckSweepTr`'s
composition (one-index programs chained through `lift`) as the way to glue
an inner run into an outer arm.  That is the next real checker.  The 224
rows no finder reads need reading by hand first; LE3's nested example is
one of them.

```
# the container loop (what this section ran; all resumable)
python3 tools/closeouttr/le4/zeck2_detect.py ROWS le4/zeck2.jsonl --jobs 4
python3 tools/closeouttr/le4/batch.py tools/closeouttr/le4/zeck2.jsonl --kind zeck2 --tag LE4
python3 tools/closeouttr/le4/pos_detect.py ROWS le4/pos.jsonl --jobs 4                    # ~7 min
python3 tools/closeouttr/le4/try_emit.py le4/pos.jsonl OUTDIR RES.tsv --jobs 4 --nonest   # ~6 min
python3 tools/closeouttr/sp_ladder_batch.py BUILT.jsonl --tag LE4 [--qh]
python3 tools/closeouttr/le4/termrun2_detect.py ROWS le4/termrun2.jsonl --jobs 4          # ~15 min
python3 tools/closeouttr/le4/run2_batch.py le4/termrun2.jsonl --tag LE4 --jobs 4          # ~25 min
python3 tools/closeouttr/le4/sweep_probe.py le4/pos.jsonl le4/sweep_probe.jsonl            # seconds
python3 tools/closeouttr/le4/batch.py le4/sweep_certs.jsonl --kind sweep --tag LE4         # ~20 s
tools/closeouttr/le/board_chunk.sh CBT_LE4_NN
python3 tools/closeouttr/le4/residue.py
```

No sweep here needed the owner's box: the slowest step, the marker-run
batch with nested programs on, is ~25 min at 4 jobs.  With the nested
search on for the 134 positional failures (`try_emit.py` without
`--nonest`, 900 s a row) it would be ~2-3 h at 12 jobs; the fill and refill
failures above are cost shapes no program changes, so it was not run.

#### 7.4.LE5 LE4's "nested" counters: mostly one counter read at the wrong place; a top digit with its own words, a phase-run family with an anchor per phase, 23 boarded (2026-10-01)

Workstream LE5 (batch tag `LE5`), over LE4's residue: the 345 rows of
`le4/residue.tsv` not boarded by LE4.  Branched from `main` at `3e69a628`
(710 open); `main` merged in once (BLC6, 13 rows).  The block-list rows
(`blc4/rows216.txt`), the Collatz-like / cube rows and the 22 leading-`0RB`
hybrids were not touched.  The target was LE4's 108 "nested counters" (90
positional readings whose fill costs about twice as much each width, 18
marker runs whose refill does).

**1. The main finding: most of the "nests" that read at all are ONE counter
read at the wrong place, not a counter inside a counter.**  LE4 proposed a
recursive family (the inner counter's full run as one segment of the outer
increment, through `LadderCheckSweepTr`'s composition).  Read by hand and
then by three new readers, the rows that read show no recursion.  Instead,
the word LE4 took as the terminator is itself part of the counter's state,
so LE4's single "fill" step contained a whole count.  Three ways:

| shape | example | what it is | rows read (of the 108) |
|---|---|---|---:|
| **top digit with its own words** | `0RB1LA_1LC1RD_0RB0LD_1RB0LA`: `[A1] x e (01)^m`, x over 11 (= 0) / 01 (= 1), e over 10 / 00 | LE3's terminator run with the counter's top digit spelled over its own two words: `(x, e)` counts, its top narrows `x` and lengthens the run, an empty `x` refills.  LE4's positional reading took `E0 T` as the terminator, so its "fill" was every narrowing and inner count between two refills | 26 (`termrun3_detect.py`) |
| **phases with a run** | `0RB1LA_0LC1RD_1LD0RB_1RB0LA`: `x 01 (01)^m`, then `x 10 1` whose top widens `x` | several words around the run in turn: a finite set of phases, each with a word before and after the run and a move at `x`'s top (carry with a widening, narrowing, refill) | 18 (`phrun2.py`; 30 over all 345) |
| **alternating anchor** | `0RB0RC_1RC1LB_1LD1RD_0LB1RA`: 011 (= 0) / 111 (= 1), terminator 1 | a plain binary counter counted from the counter's end at even widths and from one word in, with `01` left on the far side, at odd ones; LE4 saw only the even widths | 5 (`alt_detect.py`) |

**2. Two new generic checkers**, both in new files; nothing already landed is
modified.  `Print Assumptions` on both closers of each, and on a board of
each batch: `functional_extensionality_dep` only.

* `theories/Checkers/LadderCheckRun3Tr.v`: `pre ++ x ++ EW_e ++ T^m ++ suf`
  with the top digit `e` of base `be` over its own words.  It has four
  arm classes (interior with one word of lookahead, the top carry
  `t^j E_e X -> 0^j E_(e+1) X`, the narrowing, the refill).  Liveness is
  the mixed-radix value of `(x, e)` within a length, then the length.
  LE4's `LadderCheckRun2Tr` is the case `be = 1`.
* `theories/Checkers/LadderCheckPhRunTr.v`: phases `p < NP`, each with its
  own ANCHOR (state, head symbol, far side: `fam_at`) and words `W p` /
  `V p`, cells `pre ++ x ++ W p ++ T^m ++ V p`.  Each phase has one move for
  a nonempty `x` (`TCarry q dw dm`, `TNarrow q dm`, or `TNone`) and one for
  an empty `x` (`ECarry q dw dm` or `ERefill a q c`).  Each phase also has
  three flags the table keeps as invariants: runless (the run is empty, so
  its moves may rewrite `V` with both tails known empty), empty-only, and
  never-empty.  Liveness: the refills and the FIRE carries (carries whose
  arms fire every instruction) recur, because a linear rank
  `A |x| + B m + g p` falls at every other move and `x` counts up inside a
  phase.  It states LE3's Run, LE4's Run2 and Run3 as special cases, and
  the alternating-anchor counters as two phases whose fills are fire
  carries.  An arm from phase `p` to `q` starts at `p`'s anchor and ends at
  `q`'s, and every arm is a one-index `ReachL` program.  The doubling cost
  LE4 measured is the iteration of these arms, which `lapP` composes as it
  does any lap, so no recursive arm is needed for these rows.

The emitters (`le5/emit_run3.py`; `le5/emit_ph.py` over a phase MODEL from
either `phrun2.py` or `alt_detect.py`, Coq template `emit_ph_tmpl.txt`)
share `emit_ladder`'s header and `emit_step.Arms`.  `emit_ph.py` chooses the
flags, the fire carries (exactly the carries whose arms fire everything)
and the rank, and normalises the run on its far side (T's at the start of
`V`, never at the end of `W`: the arms read them).

**3. The readers.**  `termrun3_detect.py` (24 s a row): `x ++ e ++ T^m`, the
laws followed over 30,000 visits, at least 2 narrowings and a refill.
`phrun2.py` (~40 s a row): a BEAM over every parse of each visit (x over
the D words, a phase word of up to 10 cells, the run, a word of up to 3
cells after it).  An interior step must be `x + 1`, and each phase's move
must be the same every time.  The beam is what reads rows whose phase words
begin with a digit word.  `alt_detect.py` (~10 s a row): anchors keyed by
(state, symbol, side, far-side word up to 3 cells), a main anchor with a
blank far side and a second one; terminators per anchor; the fill table
along the merged visits.

**Yields** (23 rows; closeout open 710 -> 702 -> 690 -> 677 with BLC6 -> **674**):

| batch | rows | class | how | compile (container, incl. boards) |
|---|---:|---|---|---:|
| `CBT_LE5_00` | 8 | 2 DN, 6 SP | `LadderCheckRun3Tr` (top digit with its own words) | 55 s (the checker 53 s) |
| `CBT_LE5_01` | 12 | SP | `LadderCheckPhRunTr` from `phrun2.py` readings | 66-72 s (the checker 55 s) |
| `CBT_LE5_02` | 3 | SP | `LadderCheckPhRunTr`, alternating anchors (`alt_detect.py`) | 56 s |

The boards compile in 1-2 s each.  `ci_costs.tsv`: `_00` and `_01` at 120 s,
`_02` at 90 s.  `ci_shard.py --plan 6` keeps the slowest shard at
`CBT_BR_02`'s.  All 23 are LE4 "nested" rows: 18 from the 90 doubling
fills, 5 from the 18 doubling refills.

**4. Where the rest stop** (322 of the 345; per row `le5/residue.tsv`,
`le5/residue.py`):

| LE5 reading | rows | where it stops |
|---|---:|---|
| none | 296 | no LE5 reader reads them: 69 of the 108 "nests", 227 of the others (LE4's 224 unread, its nested carries, ...) |
| run3 / phrun | 9 | interior: no program (5 of them are positional counters whose terminator grows at larger widths, `1` -> `10001`: a real second level) |
| run3 | 5 | narrowing: no program |
| run3 / phrun / alt | 5 | refill: no program, or a refill that does not fire every instruction (the "refill" is a whole count at another anchor) |
| run3 | 5 | refill law not `D0^(m+a) E0` |
| phrun | 2 | an empty-carry arm with no chain; a phase move of another kind |

What the 69 unread nests are, by hand:

* **two phase-run shapes that share the run word with the zero digit**
  (`0RB1LA_1LC1RD_0RA1LD_1RB0LA`: a marker `0` moving left by a word per
  narrowing with the run `11`, then a second phase moving it right; the
  run word IS the digit `0`).  The beam's parse is ambiguous here, because
  `x`'s high zeros and the run are the same cells.  A reading that pins the
  marker would state it in `LadderCheckPhRunTr` as it is.
* **tails that grow** (`0RB0LA_1LC1RD_0RD0LC_1RB1LA`: a binary counter over
  `00` / `01` whose terminator is `1` at small widths and `10001` later;
  `0RB1LA_1LC1RD_1RB0LD_1RB0LA`: `x` with a 6-7 cell tail that steps
  through ~16 values per refill).  These are the real second levels.  The
  outer counter lives in the tail, at the far end, and grows, so its
  increments cross the inner counter.  That is `LadderCheckSweepTr`'s
  excursion (pivot, across the run, back) used as a phase move with a run
  that the move REWRITES.  `LadderCheckPhRunTr` refuses such moves today
  (a phase with a run must keep `V`).
* **anchors that wander** (`0RB0LB_1LC0RD_1LA0LA_1LB1RB`,
  `0RB1LA_1LC1RD_1LA1LD_1RB0LA`: the widths at the busiest anchor go up and
  down every few visits): no anchor key fits.

The 9 nested carries, the 2 refill-law rows, the excursion row and the
two-cell Zeckendorf countdown are outside the 108, so `termrun3_detect.py`
did not run on them.  They went through `phrun2.py` and `alt_detect.py`,
and neither reads any of them.

**Next.**  (a) A phase move that rewrites `V` across a run: an excursion
arm, composed through `lift` as in `LadderCheckSweepTr` (carry to the pivot,
across `T^m` to `V`, back).  This is the one missing piece for the
growing-tail rows and the "run but rewrites V" refusals.  (b) A reader
that pins a marker inside a run of zero digits (the 0RA1LD family).
(c) `alt_detect.py` also takes single-anchor readings (a counter whose
top widens `x`).  Its re-run over the 322 open rows (`le5/alt_res2.jsonl`,
~1.5 h at 3 jobs) reads 6.  Four are new single-anchor positional
counters (`0RB0RA_1RC1LD_1LC1RB_0LD0LA`, ...), and their interior arm has
no program.  The other two are the old alternating pairs whose carry has
none.  0 board (`le5/alt_batch2.log`).

```
# the container loop (what this section ran; all resumable)
python3 tools/closeouttr/le5/termrun3_detect.py le5/rows_nested108.txt le5/tr3_108.jsonl --jobs 3   # ~25 min
python3 tools/closeouttr/le5/run3_batch.py le5/tr3_108.jsonl --tag LE5 --jobs 4                     # ~4 min
python3 tools/closeouttr/le5/phrun2.py le5/rows_le4res.txt le5/phrun_res.jsonl --jobs 4             # ~1.5 h
python3 tools/closeouttr/le5/phrun_batch.py le5/phrun_res.jsonl --tag LE5 --jobs 2                  # ~11 min
python3 tools/closeouttr/le5/alt_detect.py le5/rows_le5open.txt le5/alt_res.jsonl --jobs 3          # ~20 min
python3 tools/closeouttr/le5/phrun_batch.py le5/alt_res.jsonl --alt --tag LE5 --jobs 4              # seconds
tools/closeouttr/le/board_chunk.sh CBT_LE5_NN
python3 tools/closeouttr/le5/residue.py
```

Nothing here needed the owner's box.  The slowest step is `phrun2.py` over
all 337 rows (~1.5 h at 4 jobs; ~30 min at 12).

#### 7.4.LE6 LE5's residue: a survey by growth rate; most of the Fibonacci rows count DOWN; conjugate transport; binary countdown runs; 134 boarded (2026-10-02)

Workstream LE6 (batch tag `LE6`), over LE5's residue: the rows of
`le5/residue.tsv` still in `closeouttr_remaining.txt`, **322 rows**
(`le6/rows.txt`: 296 with no LE reading, 26 read with an arm missing).
Branched from `main` with `claude/instruction-beeping-proof-scope-ww7zdk`
(`818a73a8`, LE5 and the AST checkers) merged.  None of the 322 is on the
AST list (`ta/rows.txt`), the block lists (`blc4/rows216.txt`) or BLC6's
scope.  The instruction-target Fuel finder (`fueltr_batch.py find --all`)
was left to the orchestrator.

**1. Conjugates first: 22 of the 322 are renamed / mirrored copies of
boarded rows, 15 transport.**  `le6/conj_check.py` puts every row in a
canonical form over the 24 state permutations and the mirror.  The 322
targets fall into ~155 classes (96 of them with 2-4 members), and 22 rows
are conjugates of rows already boarded.  A conjugate starts in another
state, so its run from blank differs at first; `le6/conj_find.py` runs both
machines and finds boots `m` (source) and `n0` (target) where the target's
configuration is the conjugate of the source's.  From there the runs are
in lockstep.  The new `theories/Counters/CConjCoverTr.v` (Astra's
`CConjugateTr` transports one value-lap family; this transports a whole
proof):

* `cconj_cover_run`: with `n0 <= m`, `coversTr src -> coversTr dst`,
  however the source was proved (never-QH or a bounded quasihalt).  A
  completion of `dst` is the conjugate of a completion of `src`, and a quiet
  instruction of it last fires either in its boot (`< n0 <= 2^20 <=
  B_close`) or `m - n0` steps before its preimage's last fire;
* `cconj_nqh_run`: any offset, `NeverQuasiHaltsTr src ->
  NeverQuasiHaltsTr dst`, given a finite check (`boot_ok`) that every
  instruction `dst` fires in its boot fires again after it.

10 rows by the first (`CBT_LE6_00`), 5 by the second from the source
machines' `nqhtr_` lemmas (`CBT_LE6_01`; the boots are 1-4 steps late), 1
later conjugate of an LE6 board (`CBT_LE6_08`).  The other 7 conjugates
(of CE2 rows) never come into lockstep in 20,000 steps: different orbits.

**2. The survey.**  For each row `le6/rec.c` (100M steps) logs every
extent record and the tape at the last ones; `le6/events.py` groups the
records into growth events (records within 1% of each other's time) and
takes the time ratio between consecutive events and the cells per event;
`le6/survey_table.py` groups the rows (`le6/survey2.jsonl`):

| group | rows | boarded, by route | open |
|---|---:|---|---:|
| F: Fibonacci growth (phi per cell / phi^2 per 2 cells) | 138 | Zeck2 (increment) 20, ZeckD (countdown) 70, ZeckDw (wider bottom) 24, conjugate 1 | 23 |
| B2: binary growth, both ends | 70 | - | 70 |
| I: irregular event ratios (a second level: the ratio cycles with an outer count) | 49 | - | 49 |
| B2: binary growth, one end | 25 | Run2z (countdown run) 4 | 21 |
| C: conjugate of a boarded row (boarded before the survey) | 15 | conjugate 15 | 0 |
| B3: base 3 / 4 growth (or 2 and 4 at the two ends) | 13 | - | 13 |
| R: other constant ratio (1.50) | 8 | - | 8 |
| R: other constant ratio (2.12) | 2 | - | 2 |
| R: other constant ratio (2.13) | 2 | - | 2 |

(Group C: the conjugates boarded before the survey ran.)  Every group is a
counter (no extent grows faster than ~t^0.1).  The Fibonacci group is most
of this section's yield; the binary groups are read in item 4.

**3. The Fibonacci group is Zeckendorf counters, three quarters of them
counting DOWN.**

* 20 are LE4's two-cell Zeckendorf increment (`zc`: `10 -> 11`): LE4 had
  run `zeck2_detect.py` on LE2's five rows only.  All 20 board
  (`CBT_LE6_02`, `LadderCheckZeck2Tr` unchanged).
* The rest, read by hand: after the anchor the tape is a string with NO
  TWO ADJACENT ZEROS, e.g. `0RB0LA_1RC0LC_1LD0RC_1LA1RC` at width 6 runs
  through the 13 strings `010101, 110101, 101101, ..., 111111` and widens.
  Its complement is a Zeckendorf string (LSB at the head) counting DOWN,
  12 to 0, then the largest string one digit wider.  LE4's lone
  "decrementing zinc" row is one of 75 such rows.  `le6/zeckw_detect.py`
  reads Zeckendorf strings over two token WORDS (`0 -> A`, `10 -> B`, A and
  B of 1-4 cells: LE3's code is `0`/`10`, LE4's `0`/`11`, these mostly
  `1`/`01`), up or down, following the predicted value and skipping up to 8
  other visits at the anchor key (the key also catches the head passing).

New generic checkers (new files; `Print Assumptions` on both closers of
each and on every batch: `functional_extensionality_dep` only):

* `theories/Checkers/LadderCheckZeckDTr.v`: the countdown over TOKEN LISTS
  (`false` = `0`, `true` = `10`; every token list is a Zeckendorf string),
  cells `pre ++ flat_map (A|B) tau ++ T`.  One step is
  `false^i true rho -> alt i ++ false rho` (`alt (2k) = false true^k`,
  `alt (2k+1) = true^(k+1)`) and at zero `false^m -> alt m`.  With
  `i = u + 2k` every class is one side over the words `AA` / `B`
  (interior `PL u (AA)^k B X -> PR u B^k A X` with `X` opaque, end, bottom
  `PL u (AA)^k T -> PR u B^k T`).  Liveness needs no Fibonacci arithmetic:
  the BINARY value of the digit string falls at every non-bottom step (the
  lowest one becomes a zero and the digits below it are worth less), so
  bottoms recur; the fires are read from the bottom arms.
* `theories/Checkers/LadderCheckZeckDwTr.v`: the same with a bottom that
  widens by `dw + 1` digits, `false^m -> alt (m + dw)` (the rows whose tape
  grows two cells per factor phi^2); it imports everything else.

Emitter `le6/emit_zeckd.py` (LE4's `emit_zeck2.py` with the classes
changed; emit_step's arm search), driver `le6/batch.py` (LE3's
`step_batch.py`, boards emitted and compiled in parallel).

| batch | rows | how |
|---|---:|---|
| `CBT_LE6_03`, `_04` | 40 + 25 | `LadderCheckZeckDTr`, countdown over `1`/`01` (most), `1`/`00` |
| `CBT_LE6_05`, `_06` | 21 + 3 | `LadderCheckZeckDwTr`, the bottom widens by two digits |
| `CBT_LE6_07` | 5 | `LadderCheckZeckDTr`: rows whose top digit is always 0, read with that digit in the terminator |

**4. The binary groups: LE4's marker run COUNTED DOWN.**  Read by hand,
`0RB1LA_1LC1RD_0RA1LD_1RB0LA` is `[A0] x 0 (11)^m`, `x` over `11` / `10`
counting DOWN: at `x = 0` it narrows by a word and the run grows, and an
empty `x` refills to `1^m 0`, whose top word's last cell and the marker are
blanks beyond the tape.  With the words swapped that is LE4's
`LadderCheckRun2Tr` increment, except for the refill.  Three things kept it
unread: LE4's `termrun2_detect.py` asks that half the visits at the anchor
key parse (here 10-20%: the key also catches the head passing mid-sweep)
and looks at 3,000 visits (no refill among them); the visit strings end at
the last nonzero cell, so the refilled `x` never parses and the reader
took refill + count + narrowing for one "refill"; and `(C, 1)` fires only at
the narrowing, never within reach of a refill anchor.

* `le6/run2_relax.py`: LE4's reader with a 10% parse floor, a 1.5M-step
  run (600k in the sweep) and every visit from the first quarter on, the
  visit string padded with up to `|M| + l` blanks.  Over the 194 open rows:
  **68 read** (`le6/run2r.jsonl`; ~25 s a row at 600k steps).
* `theories/Checkers/LadderCheckRun2zTr.v`: `LadderCheckRun2Tr` (every name
  suffixed `Z`) with the refill law `([], m) -> (0^(m+a) ++ z, c)` for a
  fixed digit string `z`, and the fires read from the refill OR the
  narrowing anchors, per instruction (`nar_cofinalZ`: with `z <> []` every
  refill leaves `x` nonempty, so narrowings recur too).
* `le6/emit_run2z.py` (LE4's `emit_run2.py`: `z` read off the visits, a
  refill target taken from the first of the next 4 visits that is
  `D0^k ++ z`, `k >= m`, so rows that refill to all-top narrow inside the
  refill arm; fire witnesses with the narrowing arms' tail flags), driver
  `le6/run2z_batch.py`.

**4 board** (`CBT_LE6_09..11`).  The other 64 readings: refill, no program
or no fire witness (49; read by hand, `0RB1LA_1LC1RD_1LA1LD_1RB0LA`: the
reader sees one refill, at the boot, and then the run grows to 11 with no
refill -- from an empty `x` the machine runs a whole second count, which
the relaxed reader skips as transients), interior (10) or narrowing (4)
with no program, and one emitter error.

**Yields** (134 rows; closeout 599 -> **465** before merging `main`).  After
merging `main` (BLC6, FTA) 10 of the 134 are also boarded by the orchestrator's
instruction-target Fuel batches (`CBT_FTA_*`, which sort first in
`closeouttr_boarded.tsv`): duplicates, harmless; 124 rows are LE6's alone.

| batch | rows | route | compile (container, `-j4`, incl. boards) |
|---|---:|---|---:|
| `CBT_LE6_00` | 10 | conjugates, `cconj_cover_run` | 10 s (the checker 47 s) |
| `CBT_LE6_01` | 5 | conjugates, `cconj_nqh_run` | 47 s |
| `CBT_LE6_02` | 20 | `LadderCheckZeck2Tr` (`zeck2_detect.py` over the survey) | 67 s |
| `CBT_LE6_03` | 40 | `LadderCheckZeckDTr` | 61 s (the checker 44 s) |
| `CBT_LE6_04` | 25 | `LadderCheckZeckDTr` | 22 s |
| `CBT_LE6_05` | 21 | `LadderCheckZeckDwTr` | 45 s (the checker 39 s) |
| `CBT_LE6_06` | 3 | `LadderCheckZeckDwTr` | 41 s |
| `CBT_LE6_07` | 5 | `LadderCheckZeckDTr` | 46 s |
| `CBT_LE6_08` | 1 | conjugate of a `CBT_LE6_06` row | 38 s |
| `CBT_LE6_09` | 2 | `LadderCheckRun2zTr` (binary countdown runs) | 43 s (the checker 41 s) |
| `CBT_LE6_10` | 1 | `LadderCheckRun2zTr` | 46 s |
| `CBT_LE6_11` | 1 | `LadderCheckRun2zTr` | 47 s |

A board compiles in 1-2 s.  `ci_costs.tsv` carries every batch (30-300 s,
the runner being about twice as slow); `ci_shard.py --plan 6` keeps the
slowest shard at `CBT_BR_02`'s.

**5. Where the rest stop** (188 of the 322; by survey group and LE4/LE5's
last reading, `le5/residue.tsv`):

| group | open | LE4 / LE5 reading | what it is (read by hand) |
|---|---:|---|---|
| B2: binary, both ends / one end | 70 / 21 | 46 LE4 positional ("the fill counts"), 39 none, 6 marker runs | binary countdowns: item 4 reads 68 rows as marker runs counted down and boards 4; from an empty `x` most run a whole second count (a run counted by an outer counter: three levels), and LE5's "tails that grow" (`0RB0LA_1LC1RD_0RD0LC_1RB1LA`) are here too |
| I: irregular event ratios | 49 | 20 none, 20 positional, 9 marker runs | the per-event time ratio cycles (`1.01, 1.08, 1.01, 1.08`): a second level whose period is an outer count; not read |
| F: Fibonacci, still open | 23 | none | two-level Zeckendorf: `0RB0LC_1LC1RD_0RD1LC_1RB1LA` is a Zeckendorf INCREMENT over `1` / `01` beside a run of `1`s that shortens at each top (LE3's terminator run, in Zeckendorf); three rows grow phi at one end and 2 (three cells) at the other |
| B3: base 3 | 13 | 9 none, 4 marker runs | ratio 3 per two cells, records `0 1^k C0`: base-3 counters not read |
| R: ratio 3/2, 2.12 | 12 | 8 none, 4 marker runs | 3/2 per two cells (`0RB0LA_1LC0RD_1LA1LB_1RC1RD`); 2.12 is LE5's growing-tail row |

The common thread of what is left: COUNTDOWNS (every LE2-LE5 reader follows
`x + 1` only; a countdown is an increment in the swapped words only if the
narrowing and refill laws also come out right, which is what item 4 had to
fix) and SECOND LEVELS: the step from an empty `x` is itself a count (the
B2 refills), or a run / tail counts the widths (the F residue, LE5's growing
tails).  The next steps: (a) a refill that is a whole inner count, stated as
one phase move composed through `lift` (LE5's proposed excursion arm; the
49 B2 refill failures are the test set, `le6/run2r.jsonl`); (b)
`LadderCheckZeckDTr` / Zeck2's classes beside LE3's terminator run (the F
residue, `le6/rows_F_open.txt`); (c) the conjugate pass after every new
board (`conj_find.py` is seconds).

```
# what is still running / left to run (resumable; the owner's 14-core box)
python3 tools/closeouttr/le6/run2_relax.py le6/rows_open.txt le6/run2r.jsonl --jobs 12 --steps 600000   # ~25 s a row (done: 194 rows)
python3 tools/closeouttr/le6/run2z_batch.py le6/run2r.jsonl --tag LE6 --jobs 12                         # ~15 min at 4 jobs
python3 tools/closeouttr/le6/conj_find.py le6/rows_open.txt le6/conj.jsonl && python3 tools/closeouttr/le6/conj_batch.py le6/conj.jsonl --tag LE6
```

```
# the container loop (what this section ran; all resumable)
python3 tools/closeouttr/le6/conj_find.py ROWS le6/conj.jsonl --steps 20000          # seconds
python3 tools/closeouttr/le6/conj_batch.py le6/conj.jsonl --tag LE6
python3 tools/closeouttr/le6/survey.py ROWS le6/survey.jsonl --jobs 4                # ~1 min
python3 tools/closeouttr/le6/events.py le6/survey.jsonl le6/survey2.jsonl            # ~1 min
python3 tools/closeouttr/le6/survey_table.py --md
python3 tools/closeouttr/le4/zeck2_detect.py ROWS le6/zeck2.jsonl --jobs 4           # ~1 min
python3 tools/closeouttr/le4/batch.py le6/zeck2_ok.jsonl --kind zeck2 --tag LE6
python3 tools/closeouttr/le6/zeckw_detect.py ROWS le6/zeckw2.jsonl --jobs 4          # ~3 min / 200 rows
python3 tools/closeouttr/le6/batch.py CERTS.jsonl --kind zeckd --tag LE6 --jobs 4    # ~10 min / 70 rows
tools/closeouttr/le/board_chunk.sh CBT_LE6_NN
```

## 8. What we deliberately do NOT redo

* The state-level theorem and its census `.vo` stay frozen and untouched;
  the new development builds beside, not on top.
* No strengthening of in-walk tiers to rescue deferrals (PLAYBOOK Rule 4
  survives verbatim: prove machines, keep the walk light).
* No hand-porting of generated layers (`Machines/` ~2.6M lines,
  `Closeout/CB_*`, census lists): they regenerate from tools once the
  checker layer lands.

#### 7.4.TA follow-up: cube counters at moduli 9 and 27 (2026-10-01)

The suggested larger-residue search was run on the 15 cube rows for which
`ta/dump.jsonl` contains a closed TriGlue family graph.  With node moduli 9
and 27 and three lexicographic levels, `TriNuTr` certifies **1 of 15** rows:
`1RB1LA_0RC0RD_1LC0LA_1RC0RC`, at modulus 9.  The certificate is boarded
in `CBT_AST_00`.  The resumable results are recorded in
`tools/closeouttr/ta/cube_nu27.jsonl`.  Of the other 14 graphs, eight exceed the node cap at both moduli and six
have no nu-ranking at modulus 9 before exceeding the node cap at 27.  Thus
the larger residue split supplies one missing valuation across the cube
reset, but does not by itself close the family.

Command:

```
# First select the 15 cube records containing a saved `cert` into cube_dump.jsonl.
python3 tools/closeouttr/ta/nu_find.py cube_dump.jsonl \
  tools/closeouttr/ta/cube_nu27.jsonl --plist 9,27 --ells 3 \
  --jobs 4 --timeout 900
```

#### 7.4.TA follow-up: AST requested rows at moduli 5, 9 and 27 (2026-10-01)

The larger-residue search was extended to the requested rows for which
`ta/dump.jsonl` retained a closed TriGlue family graph.  It certifies three
more rows with the existing `TriNuTr` checker:

* `1RB1LA_1LA0RC_0RC0RD_1LD0LA` at modulus 9;
* `1RB1LA_1LA0RC_0RA0RD_1LD0LA` at modulus 5;
* `1RB1LA_1LA0RC_1RB0RD_1LD0LA` at modulus 5.

They are boarded in `CBT_AST_01..02`.  The complete modulus-9/27 probe is
recorded in `tools/closeouttr/ta/astra_nu9.jsonl`; the two targeted
modulus-5 certificates are in `astra_nu5.jsonl`.  The other saved family
graphs either lack a nu-ranking at these moduli or exceed the 3,000-node
cap.  Requested rows without a saved family graph still stop in the
TriGlue family finder and were not presented to the liveness search.

#### 7.4.TA follow-up: modulus-5 sweep of the remaining saved graphs (2026-10-01)

A modulus-5 sweep over all 23 still-open rows with a saved closed TriGlue
family graph certifies two further requested rows with `TriNuTr`:
`0RB0RD_1RC1LB_1LB0RA_1LD0LB` and
`1RB0RD_1LC0RA_1RB1LC_1LD0LC`.  They are boarded in `CBT_AST_03` and the
complete probe is retained as `tools/closeouttr/ta/astra_nu5_remaining.jsonl`.
The other 21 saved graphs have no modulus-5 nu-ranking.  The newer requested
set is dominated by rows that stop before this stage (hybrid/list family
closure), so changing the liveness modulus alone does not reach them.

#### 7.4.AST follow-up: deeper search over the later requested list (2026-10-01)

Three independent follow-ups found no further board in the later requested
list.  This narrows the missing checker work rather than exposing another
parameter-only win:

* A deeper anchor-seeded TriGlue run on its 22 leading-`0RB` hybrids
  (`hy3_ti.py`, 300 seconds, 1,000-family cap) still ends at no stable
  anchor, no positional-counter reading, leaf-length overflow, or genuine
  family explosion.  The two apparent HY2 timeouts
  `0RB0RA_1LC1RA_0LD0LC_1LA1LB` and
  `0RB0RA_1RC1RD_0LD0LC_1RA1LC` had already reached `no counter family`
  at the 1,800-second budget; they are not timeout-only misses.
* For `1RB1LB_0RC0LA_1LC0LD_1RA1RC`, the saved TriGlue graph admits no
  `TriNuTr` ranking at moduli 1--7, 11, 13, 17, or 19 with l-adic bases
  2, 3, 5, and 7; modulus 23 exceeds 3,000 nodes.  Thus the valuation
  search used by `CBT_AST_00..03` is exhausted for this row.
* A transition-target NGramHist probe was tried on the Fuel rows, including
  `1RB---_0RC0RB_1LC0LD_1RA0LD` and
  `1RB0LA_0LC1RD_1LC1LA_0RB0RD`.  The plain history abstraction does not
  close.  Their landed `FuelWide` certificates establish state recurrence,
  not instruction recurrence; a sound reuse needs a generic
  instruction-target `FuelSCCTr`/`FuelWideTr` port and regenerated
  certificates.  `NeverQuasiHaltsSt` cannot be lifted directly to
  `NeverQuasiHaltsTr`.

#### 7.4.AST2 Token transducers and instruction-target fuel, 51 boarded (2026-10-01)

This continues the AST session on the requested 164 rows. Six were already
boarded in `CBT_AST_00..03`; this follow-up adds **51**: four word
transducers, eight state-renamed/mirrored token variants, and 39
instruction-target Fuel certificates. All new batches
kernel-check under Coq 8.18.0. Their `Print Assumptions` reports contain only
`functional_extensionality_dep`; the transducer and sweep lemmas themselves
are closed under the global context. No census, existing checker, closeout
kit, workflow or Makefile was changed.

**The primary target, `0RB0RA_1LC1RA_0LD0LC_1LA1LB`, is boarded in
`CBT_AST_04`.** Its C1 anchor is reached at step 13 and has the supplied
shape `encode(w) [C1] (110)^(2*n+1) 1`. The new generic
`Counters/MutualTokenTr.v` proves its counter phase by induction on the
token word. On arbitrary words the two carry ports admit one uniform
transducer `T`: `[] -> [1]`, `0::w -> 2::w`, `1::w -> 0::w`, and
`2::w -> 1::T(w)`. The successor is `[] -> [1]`, `1::w -> 2::w`,
`2::w -> 0::T(w)`, `0::w -> 1::T(w)`. This agrees with the supplied
F/G description on the observed orbit while also closing on every token
word, so no reachable-language invariant is needed. An explicit final
blank in the nonempty terminator makes the finite-list step equations
exact; bootstrap equality uses `ceqb_lift`.

`Counters/TokenSweepTr.v` proves both periodic sweeps, preserving an
arbitrary counter tail, and witnesses all seven instructions other than
C1. C1 fires at offset zero of every anchor. The exact positive lap is
`36*n + 62 + 6*mt_depth(w)` steps. The new `Counters/ValueLapTr.v`
closes positive laps indexed by a natural sweep parameter and an
arbitrary value with a total successor; it also supplies a wrapped version
for pinned instructions. No numerical interpretation of the word is needed.

**Two adjacent rows share a moving binary-word transducer**
(`Counters/MovingTokenTr.v`, `MovingSweepTr.v`, `CBT_AST_30`):

* `0RB0RA_1LC1RA_0LD0RD_1RA1LB`;
* `0RB0RA_1LC1RA_0LD1LC_1RA1LB`.

Both boot at step 11. A mutual structural induction proves the two carry
ports on every finite binary word. A C1 macro parameter accounts for the
one-step versus three-step implementations, and the bouncer sweep takes
`12*k+12` steps. All eight instructions are live from every anchor.

**The B0-right sibling**, `0RB0RA_1RC1RA_0LD1LC_1RA1LB`, is boarded in
`CBT_AST_31`. Its frontier recurrence is
`C1(1::0::w,1,[0]) -> C1(1::0::mv_g(w),1,[0])`, booting at step 17.
`Counters/FrontierTokenTr.v` proves this lap and its instruction witnesses.
D0 need not fire in every lap: a lap without it strictly decreases the
lexicographic pair (number of ones, number of adjacent pairs of ones).
Well-founded induction gives a future D0 fire from every word. The other
seven instructions have direct witnesses. The three manual batches each
compile in under 0.4 seconds locally.

**The missing instruction-target Fuel port boards 39 more rows**
(`CBT_AST_05..17`). `Checkers/FuelSCCTr.v` reuses FuelSCC's existing
lexicographic components, runner descent and fuel bounds. It checks the
graph avoiding one `(state,symbol)` instruction, including any instruction
which fired in the boot. `Checkers/FuelWideTr.v` instantiates it with
FuelWide's unchanged refined contexts, fuel classes, successor soundness
and measures. It does not infer transition recurrence from state recurrence.

The new `tools/closeouttr/fueltr_batch.py` reuses the landed abstraction,
rank search and certificate serialization, but constructs and replays
per-instruction certificates. Six of the twelve requested rows in the
state-level Fuel manifest certify. A broader pass finds eight at window 3;
two window-4 passes find twelve and ten more, with one overlapping the
manual frontier proof and removed from the Fuel batches. Window-6 passes
add four checked rows. All 39 retained certificates use the mirror and
boot at zero. Window-5 passes over actual window-4 failures add none. Bounded timeouts remain, and every search result is saved in
`fueltr_ast*.jsonl`. The newly proved rows include
`1RB1LB_0RC0LA_1LC0LD_1RA1RC`, which exhausted the earlier valuation search.
A corruption check empties a fired A0 certificate in AST05 and confirms
that the checker returns false.

**Eight conjugate token machines** are boarded in `CBT_AST_50`.
`Counters/CConjugateTr.v` transports finite-tape steps and instruction
witnesses through a state permutation and optional tape reflection, with a
separate checked bootstrap for the destination machine. `TokenLapTr.v`
generalizes the original token and moving-word laps to arbitrary initial
block counts. This allows the proofs to apply even when the renamed
machine's blank run enters a different anchor. AST50 compiles in 0.48 seconds.

The thirteen Fuel batches compile in 1.8--13.9 seconds locally; all new
batches have explicit conservative `ci_costs.tsv` entries. This checkpoint
was updated by fast-forwarding to merged main (653 open rows), then restoring
the new proofs. None of these 51 rows overlaps the intervening main changes.
The full closeout has **602** rows remaining, and **107 of the requested
164** remain open. Saved search failures and timeouts are not proofs of the
remaining rows. The unfinished cube-family integration is excluded from
this checkpoint.

#### 7.4.AST3 Cube resets, certificate transport, and longer Fuel measures (2026-10-01)

The next checkpoint adds **24 requested rows**, bringing the AST follow-up
to 75 new rows beyond `CBT_AST_00..03`. There are **578** rows left in the
full closeout and **83 of the requested 164** still open. Each new batch
proves `coversTr (row_to_tm r)` and kernel-checks under Coq 8.18; its
assumption report contains only `functional_extensionality_dep`.

**Six cube-family variants** are boarded in `CBT_AST_60..65`. They have
prefix `1RB1LA_0RC0RD_1LC0LA_` and final pairs `0LB0RC`, `1LC0RC`,
`0LA0RC`, `1LB0RC`, `1LD0RC`, and `1LA0RC`. These reuse the saved TriGlue
family graphs for all machine steps. The new `Counters/TriReachTr.v`
transfers eventual instruction fires backward through checked leaves and
closes the resulting family invariant using `ValueLapTr`.

The missing D0 argument is proved in `Counters/CubeRoundTr.v`. In the
13-family graph for AST60, shift the F10 parameters to `x = a + 2`.
A nonfiring division sends `(x,b)` to `(x/3,b+2*x/3+1)`. After
`r = nu_3(x)` divisions, a reset sends `x` to `x+b+r+2` and clears `b`.
With `b=0` and `r>=2`, group a second reset when `r mod 3 = 2`.
The total increment is then `r+2` or `r+4`, positive and below `3^r`;
hence the ternary valuation strictly decreases. The residue-zero case
fires D0, and valuation one fires after the next division. The generic
`cube_round_total` theorem proves all natural parameter pairs from six
abstract predecessor rules. Its proof is closed under the global context.
The batches combine it with direct witnesses for the other seven
instructions and backward reachability from every checked family.

**Seven rows reuse landed certificates at new starting configurations.**
`CBT_AST_51` retains four HY3 graphs and ranking certificates, renames their
states, and checks new boots at steps 26, 294, 20, and 25. `CBT_AST_70`
retains three `MetaBlkPfxTr` block-rule certificates with renamed states
and reflected tapes. Their new boots are steps 794, 788, and 139, with
counter parameters 19, 19, and 5. No source coverage theorem is assumed to
apply to a new blank run: the destination machine and its bootstrap are
rechecked by the original checker. The latter search and emission are
reproducible with `tools/closeouttr/ast_sp_retarget.py` and the adjacent
saved mappings and results. The two batches compile in roughly 4.1 and
0.9 seconds respectively.

**Eleven further Fuel rows** are boarded in `CBT_AST_18..25`. The original
finder capped pattern-count measures at length four even when the n-gram
window justified longer patterns. `fueltr_batch.py --max-pattern` now
exposes that cap. Window five with length-six measures and window six with
length-seven measures produce new certificates accepted by the unchanged
`FuelWideTr` checker. Cached local deltas, rejection of a cycle whose
measure deltas are all nonnegative, and a topological computation of SCC
ranks reduce search cost. The optimized default finder reproduces AST17's
certificate exactly. Saved `fueltr_ast*.jsonl` records distinguish actual
failures from bounded timeouts; neither is a proof of an open row.

Other bounded probes gave no new certificates: allowing both left and
right fueled runner SCCs at windows three and four; exact capped fuel
classes at caps two and four; reuse of the two RepWL-conjugate rows; and a
120-second HY2 probe with top cycles up to length 16 for
`1RB0RA_0RC0LD_1LD1RA_1LB0LD`. The latter timed out. No generic checker was
added for these unsuccessful probes. The remaining HY3-conjugate pair
needs correlated block parameters: pooling them into independent lattices
produces unreachable branches. That exploration remains separate from the
checked batches in this checkpoint.

#### 7.4.AST4 Parity words, correlated families, and invariant cube graphs (2026-10-01)

This checkpoint adds **32 requested rows**: twelve Fuel rows, ten parity
transducers, two correlated-family certificates, and eight further cube
rows. The AST follow-up now totals **107 new rows**; together with the six
previous AST rows, **113 of the requested 164** are proved. The full
closeout has **546** rows left, including **51 from the requested list**.
All new batch coverage theorems are kernel-checked and use only
`functional_extensionality_dep`.

**Parity transducers (`CBT_AST_53..55`, ten rows).** The generic
`ParityTokenTr` and `ParityCTokenTr` anchors have empty left tape, state B0,
and right word `(10)^k 00w`. Two phases return to that family with `k+1`
and a total mutual-transducer successor of `w`, in
`12*k+8+uCost(0w)` steps. `ParityGateTokenTr` handles the related three-phase
word `(100)^k 00w`: the prefixes evolve through `00w`, `110w`, and `1010w`
before returning, in `24*k+15+uCost(0w)` steps. Structural recursion proves
each transducer on arbitrary finite words. For `k>=1`, finite witnesses
cover all eight instructions in these macro phases. `ValueLapTr` supplies
recurrence and `CConjugateTr` transports the state-renamed/reflected
variants. All bootstrap steps are checked exactly; the three generic
files are axiom-free and compile in under a second each, as do the batches.

**Correlated block families (`CBT_AST_52`, two rows).** The stubborn
`0RB1LD_1RC1RB_1LA1RA_1LC0LA` and
`1RB1RA_1LC1RC_0RA1LD_1LB0LC` share 148 families and 159 checked leaves.
The finder retains the relation between the middle block and both outer
blocks during a transfer; treating the three lengths as independent
creates unreachable branches and prevented the earlier closure. The
result is an ordinary `TriGlueTr` certificate, with period-one affine
liveness ranks. The two boots are steps 446 and 445. No new trusted checker
is needed. `tools/closeouttr/ast_cone.py` and `ast_cone.jsonl` preserve the
finder and certificate data. AST52 compiles in about three seconds.

**Eight further cube rows (`CBT_AST_66..69`, `71..74`).** AST66/67 add the
`1RA0RC` and `1RD0RC` variants; AST69/71 identify the same cube recurrence
in two other state graphs. AST68 (`0RC0RC`) needs a reachable-state
invariant: the unrestricted family graph contains a zero-parameter path
that avoids D1, although the actual boot never reaches it. The new generic
`TriReachInvTr` checks preservation of the stated family predicate and
uses it in the recurrence argument. Each leaf's preservation obligation
is proved by linear arithmetic.

AST72/73 transfer `(a,b,c)` to `(a-2,b+1,c+1)`. For D0, even exits fire;
odd exits reset `b=0` and reduce `a+2*b`. For B0, odd exits fire; even exits
reset `c=0`, after which `a` decreases by `a -> a/2-2` until a firing exit.
AST74 has a transient `(0111)^d` prefix before the already-proved cube
component. At fixed `d`, the core parameter contracts to `(a-4)/3` until
a scan consumes a prefix block; nested induction on `d` and the core
parameter closes it. These batches compile in roughly 1.8--5.2 seconds.
All fifteen previously saved closed cube graphs are now covered: the
fourteen rows in AST60..69 and AST71..74, plus the older AST00 row. The
remaining `0RA0RC` and `1RB0RC` siblings need a block-list invariant and
are not included in this count.

**Longer Fuel measures (`CBT_AST_26..29`, `32..35`, twelve rows).** Full
window-seven/length-eight pattern pools continue to certify rows which
the original length-four cap missed. The finder now computes the sparse
set of global pattern-count changes around the head once per context and
pattern length, then answers each measure query by lookup. It was compared
against the original delta function on 27,200 legal context/pattern pairs;
independent replay reproduces existing certificates. The generic Coq
checker is unchanged. Compile costs, including the slower AST32 and AST33
batches, are recorded conservatively in `ci_costs.tsv`.

#### 7.4.AST5 Block stacks, separated carries, and weighted pattern counts (2026-10-01)

This checkpoint adds **eight requested rows**, bringing the follow-up to
**115 new rows** and the requested list to **121 of 164 proved**. The full
closeout has **538** rows left, including **43 requested rows**. All seven
new batches compile and their assumption audits contain only
`functional_extensionality_dep`.

**Stack cube variants (`CBT_AST_75..78`, five rows).** `StackCubeTr` extends
the cube argument to a finite list of right blocks. The framed transfer
`(a+3,b,r) -> (a,b+2,r+1)` has cost `4*a+13`. Non-firing exits consume a
block; induction on stack length reduces the empty-stack case to the
landed `CubeRoundTr`. D0 either pushes a block or merges the first blocks,
and each return preserves the language and supplies all eight instruction
witnesses. AST75/76 use one-step and three-step implementations of D0,
both with bootstrap 19. All twelve requested
`1RB1LA_0RC0RD_1LC0LA_??0RC` siblings are now proved.

`PairStackTr` closes `1RB1LA_1LB0RC_1LD1RC_0LD0LA` in AST77. Its transfer
moves two cells from the active left block into one cell on each side.
The invariant requires at least two ones in the farthest left block;
this excludes an actual non-firing fixed point outside the reachable
language. Induction on the block list and the odd reset
`a -> (a+3)/2` proves a return to D0. The bootstrap is step 17.

AST78 contains two state-renamed stack variants, with separately checked
boots at steps 20 and 19. The new `CConjugateReachTr` transports arbitrary
families with existential positive returns and eventual instruction
witnesses. It compares endpoints after `lift` and needs neither a chosen
successor function nor a choice axiom. The stack helpers compile in about
0.6--1.0 seconds and each batch in under a second.

**Separated carries (`CBT_AST_56` and `79`, two rows).**
`SeparatorTokenTr` proves `1RB0RA_0RC0LD_1LD1RA_1LB0LD` with an outer
base-four digit, a fixed one-cell separator, and an arbitrary finite inner
digit word. The digits are `010/000/011/001`; an empty inner carry creates
`011`. The carry crosses the separator only when the outer digit wraps.
Structural induction proves the carry, and a checked LapDecider chain
proves the `18*n+38` sweep. The exact bootstrap is step 81.

`BinaryGateTokenTr` proves `0RB1LC_1LC1RD_1LA0LC_0RD1RB`. Its anchor is
`D1` with left word `01 ++ encode(w)` and right block `(101)^n`. The
digits `00/01` have terminator `010`. One carry pass creates a prefix of
ones and a second pass converts it to the successor word, with three
uniform sweeps between and around them. Each carry is proved for every
finite digit word; the exact lap cost is `18*n+26+c1(w)+c2(w)`. The
bootstrap is step 21, and finite sweep prefixes witness every instruction.
Both helpers and both batches compile in under a second.

**Weighted pattern counts (`CBT_AST_36`, one row).** `FuelMixTr` permits
nonnegative sums of legal pattern counts as natural-valued measures.
Their exact integer deltas follow by induction from the landed pattern
delta lemma; the existing `FuelSCCTr` engine checks lexicographic descent
and fueled runners. A sum of three pattern counts certifies
`1RB1LD_0RC0RB_1LC0LA_0RB1RD` at window six. The untrusted LP finder rounds
and rechecks every inequality with integers, then independently replays
the whole certificate before emission. The checker compiles in about
0.4 seconds and AST36 in 2.0 seconds. Replacing its A0 certificate with
an empty certificate computes false. The finder and saved certificate are
`tools/closeouttr/fuelmixtr_batch.py` and `fuelmixtr_ast.jsonl`.

#### 7.4.AST6 Dyadic ranks, seven-phase hybrids, and moving counter boundaries (2026-10-01)

This checkpoint adds **twelve requested rows** in six batches. The
follow-up now totals **127 new rows**; including the six earlier AST rows,
**133 of the requested 164** are proved. The full closeout has **526**
rows left, of which **31** are on the requested list. Every new coverage
theorem is kernel-checked with only `functional_extensionality_dep`.

**Dyadic pair (`CBT_AST_57`, two rows).** The machines
`1RB0LA_0RC0RB_0LD1LA_1LD0LA` and
`1RB1RC_0RC0RB_0LD1LA_1LD0LA` have a complicated scaled-word increment,
but only A1 recurrence needs a manual argument: window-two Fuel
certificates cover the other seven instructions. `DyadicRankTr` ranks a
finite window by its binary complement value and then head index.
`DyadicWindowTr` proves that an A0 macro either increases the first
changed bit or moves left in an unchanged word, so the rank decreases
until A1 fires. This holds for any finite A0 tape. `DyadicRecurTr`
combines it with a positive return from A1 and the checked step-15 boot.
The new `FuelMixPartialTr` checker requires an explicit recurrence proof
for every skipped target and checks all remaining targets with the landed
Fuel engine; skipping a target alone proves nothing. The arithmetic rank
and core window lemma are axiom-free. AST57 compiles in about 1.5 seconds;
`dyadic_batch.py` and `fuelmixtr_dyadic.jsonl` reproduce its certificates.

**Seven-phase hybrids (`CBT_AST_58`, four rows).** The four related
`(011)^n` bouncers have a binary end and a seven-phase sweep cycle, with
net block growth two. The earlier finder tried at most four phases, or
only one when anchored at a fixed instruction. `HybridGlueTr` already
supports arbitrary finite phase counts. The new `hy_longphase.py` supplies
seven and immediately obtains full certificates, including all
instruction witnesses, with boots at 70, 8, 8 and 27. The saved data are
in `hy_longphase.jsonl`. All four compile together in about 0.4 seconds;
no new trusted checker is used.

**The final requested cube (`CBT_AST_80`).** `TernaryStackTr` proves
`1RB1LA_0RC0RD_1LD1RC_0LC0LA` from a step-three D0 anchor. Its transfer
subtracts three from the active block, adds one to the next block and two
to the right block. Residues zero and one reach D0; residue two consumes a
stack entry before a division-by-three contraction. All stack entries
remain positive. Explicit short cases handle the right block lengths
one, two and three, and the longer case reaches a phase firing the other
seven instructions. The helper and batch compile in about 0.9 and 0.3
seconds respectively.

**A moving binary boundary (`CBT_AST_81..82`, four rows).**
`BinaryResetTr` proves `1RB0RC_1LC0LD_1RA1RD_1RC1LB` over arbitrary digit
words `10/11`, with an optional one-cell top marker and right block
`(10)^n 1`. An ordinary carry is followed by a checked sweep of cost
`4*n+14`. At overflow, `k` carried digits expose an empty left tape and
right word `(01)^k (10)^n 1`. Two uniform sweeps, of combined cost
`6*k+2*n+19`, turn this into left word `(10)^(k+n) 111` and right word
`101`. Thus overflow can move the word boundary without requiring a
fixed top-word cycle. Every anchor reaches an ordinary sweep whose finite
prefixes fire all eight instructions. Positive returns give recurrence.
The source bootstrap is step 17; three state-renamed/reflected variants
use independently checked boots 12, 23 and 27 through `CConjugateReachTr`.
The carry and overflow lemmas are axiom-free, and all three files compile
in under a second each.

**Parity-indexed tail grammars (`CBT_AST_37`).** `FuelPhaseTr` adds a
Boolean head parity to FuelWide nodes and separates the possible distant
windows by parity. Both move directions toggle the parity. Checked
successors preserve these tail grammars and the original FuelWide cover
over their union, so existing pattern and fuel soundness applies.
`1RB0LA_1LC0RD_0LB1LA_0RB1LA` closes at window three with 144 contexts.
The finder `fuelphasetr_batch.py` independently replays the supplied
integer certificate; `fuelphasetr_ast.jsonl` preserves it. The checker
compiles in about 0.4 seconds and AST37 in 1.0 second. Its successor lemma
is axiom-free; replacing the A0 certificate with an empty certificate
computes false.


#### 7.4.AST7 Finite returns, sweep resets, and wider counter readings (2026-10-01)

This checkpoint adds **sixteen requested rows** in ten batches. The
follow-up now totals **143 new rows**; including the six earlier AST rows,
**149 of the requested 164** are proved. The full closeout has **510**
rows left, including **15** requested rows. All ten batch coverage
lemmas are kernel-checked with only `functional_extensionality_dep`.

**Universal B0 returns (`CBT_AST_38`, `83`).** `FuelB0ReturnTr` proves a
positive B0 return from every finite B0 tape. Its C routine consumes
left prefixes `11` or `101` while preserving a right-hand zero. A marker
bound on A1 carries then gives A0-to-B0 reachability by induction on the
right tape length. AST38 uses this for
`1RB1RC_0LC0RA_1RA1LD_1LA0LC`; AST83 transports the return through
`CConjugateReachTr` to the C0 target of
`1RB0RD_1LC1LD_0RD0LB_1LB1RA`, with a checked step-four boot.
Window-three partial Fuel certificates prove the other seven targets.
The helper compiles in 0.2 seconds and each batch in about 0.9 seconds.
`b0_return_batch.py` and `fuelmixtr_b0_return.jsonl` reproduce AST38.

**Two-top and five-phase hybrids (`CBT_AST_39`, `90`, three rows).**
AST39 reads a reflected A0 anchor at cell zero as binary digits `110/100`,
top words `1/101`, and a unary far block. It uses `HybridCtrTr` unchanged,
with boot 18; `hy2_two_top.py` preserves the focused seed and certificate.
AST90 uses `HybridGlueTr` unchanged for two five-phase binary hybrids,
with boots 34 and 52. `hy_longphase.py --phases 5` and
`hy_fivephase.jsonl` reproduce them. Both batches compile in under a
second. These successes concern family discovery, not stronger axioms
or new trusted checker rules.

**Two expanding sweeps (`CBT_AST_40`, four rows).** `DoubleSweepReturnTr`
returns an A0 anchor with left word `00 L` and right word `(10)^(2k+1) 1`
to left word `001 L` and right word `(10)^(4k+5) 1`. An inner sweep
consumes two left `10` blocks and adds four right blocks; two uniform
sweeps and a finite drain finish the lap. Every instruction fires in a
lap, so `ValueLapTr` gives the full result without Fuel. Three state
renamings have independently checked boots. The helper compiles in
about 0.7 seconds and the four-row batch in 0.4 seconds;
`double_sweep_batch.py` reproduces the batch.

**Paired carries (`CBT_AST_59`, two rows).** `PairedCarryTr` works over
arbitrary finite digit words encoded by `10/11` with terminator `11`,
and a right word `1^m (01)^n`. Short returns consume two ones or one
`01`; boundary sweeps lead to a finite carry that stops at zero or blank.
Positive returns establish the manual target's recurrence. Checked
window-three Fuel certificates cover the other seven instructions.
`paired_carry_batch.py` and `fuelmixtr_paired_carry.jsonl` reproduce both
rows. The helper and batch compile in about 0.5 and 3.2 seconds.

**A preserved five-one suffix (`CBT_AST_91`).** `FiveOnesTr` proves that
any A configuration with right word `X 111110` reaches D1 while preserving
that suffix. Strong induction on the prefix length handles the scan;
explicit boundary cases take 23, 49, or 50 steps. A finite C scan and a
positive D1 return complete recurrence, with the other seven targets
certified by window-three Fuel. The helper compiles in 0.7 seconds and
the batch in 3.4 seconds. Reproduction uses `five_ones_batch.py` and
`fuelmixtr_five_ones.jsonl`.

**Geometric resets (`CBT_AST_92`, two rows).** `GeometricCounterTr` has
binary digits `110/100` and phase-dependent terminators `1010/10`.
An interior carry resets passed digits and adds two ones. The natural
binary-complement rank decreases until overflow, which flips the phase
and grows the counter width. An outer sweep fires all eight instructions.
This supplies a full recurrence proof without an exponential lap-length
formula or Fuel certificate. Boots are 18 and 14 for the two orientations.
The helper compiles in 0.7 seconds and the batch in 0.4 seconds;
`geometric_counter_batch.py` preserves the instantiations.

**Reflected symbolic laps (`CBT_AST_85`).** `ReflectedLapTr` composes
individual landed `LapDecider` steps in either orientation. Reflecting
`SCycL` supplies the needed contextual right cycle, with an axiom-free
soundness theorem. `SweepResetTr` uses seven symbolic branches and four
small cases over six finite-word families to prove recurrent D0 for
`1RB1RC_1LC1RA_1LD0RA_1RA0LB`, starting at step eight. Window-four Fuel
covers the other targets. Helpers compile in 0.4 and 0.5 seconds, and
the batch in 2.5 seconds.

**An unrestricted A1 return (`CBT_AST_93`).** `RightScanReturnTr` proves
`1RB0LA_0LC1RD_1LC1LA_0RB0RD` by normalizing only trailing blank padding.
A D scan either returns to the saved A head or reaches A0 with a strictly
shorter normalized right word. Strong induction proves A0-to-A1
reachability for every finite tape. Erasing the finite left run then
gives a positive A1 return, and window-three Fuel handles the other
seven targets. The helper and batch compile in 0.4 and 2.9 seconds.
`right_scan_batch.py` and `fuelmixtr_right_scan.jsonl` reproduce the
checked certificate.


#### 7.4.AST8 Wider digits, finite transfers, and reflected seed alignment (2026-10-01)

This checkpoint adds **twelve requested rows** in five batches. The
follow-up now totals **155 new rows**; including the six earlier AST rows,
**161 of the requested 164** are proved. The full closeout has **498**
rows left, including **three** requested rows. All five batch coverage
lemmas are kernel-checked with only `functional_extensionality_dep`.

**Seven-cell ternary digits (`CBT_AST_41`, four rows).** The landed
`HybridCtrTr` closes the family of
`1RB0LA_1LC0RD_1LA0LB_1RB0RD` once the finder considers digit widths above
its previous cap of six. The final reading has digits
`0100101/0100010/0100110`, prefix `10`, and three top words
`01001/010001001/010011001`. Every second A1 visit at cell -3 exposes the
counter; each full lap grows the right `(10)` block by three units.
The four state-renamed/reflected rows have independently checked boots
169, 142, 169 and 198. The batch compiles in about 0.4 seconds.
`hy2_wide_seed.py` and `hy2_wide_seed.jsonl` reproduce the certificates;
no new trusted checker is needed.

**A unary frontier (`CBT_AST_42`).** `UnaryFrontierTr` proves
`1RB0LB_0RC0RD_1LC1LA_1RA1RD`. At the D0 right frontier, the left word is
`0^a 1^b 0 L`. The short turn sends `(0,3k+2)` to `(4,3k+1)`;
each transfer sends `(a,b)` to `(a+6,b-3)`. After exactly k transfers,
b=1 and a reset produces `1^(a+4) 0 1 L`. Thus the outer parameters
change by `k -> 2k+2`, `n -> n+1`. Every instruction fires in the reset.
The local sweep and drain lemmas are axiom-free; `ValueLapTr` closes the
proof. The helper and batch compile in about 0.5 and 0.3 seconds.
`unary_frontier_batch.py` reproduces the batch.

**A pair-block transfer (`CBT_AST_43`, two rows).** `PairTransferTr`
proves a positive return from A0 with empty left tape and right word
`(10)^m 11`, changing m to `2m+10`. Three sweeps, a finite drain, and a
reset establish the return, with explicit witnesses for all eight
instructions. The two graph-conjugate machines use boots 5150 (m=46)
and 79717 (m=163), each checked independently. The helper compiles in
about 0.7 seconds and the batch in 0.6 seconds. Its inner transfer and
lap lemmas are axiom-free. `pair_transfer_batch.py` preserves both
instantiations.

**Reflected RepWL seeds (`CBT_AST_94`, two rows).** The machines
`1RB0RD_1LC0LC_1LD1LC_1RA0RB` and
`1RB1RA_1LC0LD_1LD0LB_1RA0RA` close under the existing `RepWLTr` tier
with L=6, T=2, and warmup zero after reflection. The previous search used
the original orientation; seed-buffer alignment changes which closure
it explores. The reflected closures have 28,206 and 25,008 nodes, with
checked fueled rankings for every instruction. `neverqhtr_mirror`
transports the result, so no alternate-seed checker is added. The
combined batch compiles in about 384 seconds in isolation and 699 seconds
under concurrent load; its CI cost entry is a conservative 700 seconds.
A reflected L6 survey over the remaining requested rows found no further
closure.

**A budget of ones (`CBT_AST_97`, three rows).** `OnesBudgetTr` closes
`0RB0RC_1LC1RC_1LD1RA_1RA0LD` and two state-renamed/reflected machines.
A0 with a finite left word L and right word `0 R` reaches A at the head
of R, with exactly two additional ones on the left and a prefix `10` or
`110`. This is proved by strong induction on the number of ones in L.
A D scan erases m ones; each nested crossing restores two, but every
recursive call starts strictly below the original number. The word
length can grow, so length induction would not justify these calls.
The returned prefix supplies all eight liveness witnesses after short
additional paths. Positive frontier returns give the full theorem,
transported by `CConjugateReachTr` for the variants with boots 1 and 5.
The core scan lemma is axiom-free; only the final lifted recurrence uses
functional extensionality. The helper and batch each compile in about
2.6 seconds under concurrent load. An n11 partial-potential probe did not
close this family; the finite-word argument avoids a large certificate.


#### 7.4.AST9 Completing the 164 requested rows (2026-10-01)

The final **three requested rows** are boarded in `CBT_AST_44`, `95`,
and `96`. This completes **all 164 machines on the requested list**:
six were already proved by the earlier AST work and **158 new proofs**
were added in this follow-up. The full transition closeout now has
**495** rows remaining; none belongs to this requested list. All final
coverage theorems are kernel-checked with no assumptions beyond
`functional_extensionality_dep` and no `Admitted`.

**Dyadic expanded digits (`CBT_AST_44`).** `DyadicFrontierTr` proves
`1RB0LA_1LC1RD_0LC1LA_0RD0RB`. Bit i occupies `2^i` cells, so a carry
through e low one bits erases `2^e-1` cells and fills the next `2^e`.
Strong induction on e proves this fill; an auxiliary fixed-width Boolean
counter decreases its complement rank at each increment and invokes
only smaller carries. At the B0 right frontier the left word is
`0^(r-1) 1^r`, with r a power of two. An overflow and a finite counter
drain double r. The checked step-six boot has r=2, and explicit witnesses
in the overflow scan/fill cover all eight instructions. Blank padding is
justified after `lift`. The prefix theorem is axiom-free; the final
lifted recurrence uses functional extensionality. The helper and batch
compiled privately in 3.3 and 1.7 seconds. `dyadic_frontier_batch.py`
reproduces the batch.

**Independent instruction certificates (`CBT_AST_95`).**
`1RB0LA_0RC1RB_0RD1RC_1LD1LA` uses window six for seven targets and
window ten only for C1. The C1-avoiding graph has 19,182 contexts. Its
96-component natural-valued lexicographic certificate consists of 48
finite graph ranks, 46 single-pattern measures, and two weighted pattern
sums with node potentials. Every avoiding edge strictly descends; its
runner gate is empty. The untrusted LP search allows nonincrease on all
edges with strict decrease on some edges, then replays the rounded
integer certificate exactly before peeling another component.
`FuelMixTargetTr` extracts each target's recurrence from the landed
partial checker, allowing different windows. `FuelMixTargetFastTr`
short-circuits strict lexicographic edges and avoids pattern arithmetic
outside the component's gate; its Boolean evaluator is proved equal to
the landed one. These changes add no stronger proof rule. Rank maps use
binary literals and shared finite patches to reduce source elaboration.
The final batch compiles in about 361 seconds (800-second CI allowance),
including about 41 seconds for the large Boolean check. The finder
`fuelpotentialtr_batch.py`, per-target emitter `fuelpotentialtr_targets.py`,
and `fuelpotentialtr_c1.jsonl` reproduce both records exactly; a fresh
reproduction was checked before installation. The evaluator equality
lemmas are axiom-free, and final recurrence has only the permitted axiom.

**A long translated cycle (`CBT_AST_96`).**
`1RB0LA_0RC1LA_1RD0RD_1LB1RB` reaches its checked anchor at step
24,378,294. Thereafter a 2,575,984-step lap translates the active tape
right by 1,440 cells and fires all eight instructions. Its guarded left
window is zero: the lap never needs to read left of the anchor boundary.
The old translated-cycle probes capped the period at 20,000 and the
prefix at 200,000, missing this eventual cycle. `TCyclerAllNTr` uses the
landed binary-fuel `cstepsN` bootstrap once, then checks the guarded lap
and all eight firing witnesses. Soundness reduces to the existing
`TCyclerTr` theorem; the early-exit firing scan is proved equal to the
landed scan. The final batch compiles in about nine seconds on an idle
host, or 27 seconds under concurrent load (35-second CI allowance).


#### 7.4.AST10 The fourteen irregular block-list rows (2026-10-01)

A new request covers the fourteen irregular block-list rows excluded from
BLC3's 234-row input. The first **four** are boarded in `CBT_AST_100`
(one row), `CBT_AST_105` (two rows), and `CBT_AST_106` (one row), reducing
the global remainder from 495 to **491**. All four reuse `ListGlueLexTr` unchanged: the BLC5 finder
learns affine neighbour relations between zero blocks, checks the finite
family graph, and supplies far-end lexicographic liveness for the rare
instruction. The certificates have 90, 167, 168, and 178 families. Their
saved JSON records and replay/emission scripts are in
`tools/closeouttr/blc5/`. Kernel compilation and `Print Assumptions`
confirm only `functional_extensionality_dep`; there are no admissions.
AST100 compiled in about 10 seconds, AST105 in about 26 seconds, and
AST106 in about 22 seconds under concurrent load (CI allowances 20, 30,
and 30 seconds).

AST106 fixes an untrusted search objective: `entry_counts` previously
traded one retained tail entry against 100 window slots, so a graph with
230 nodes could lose essential entries. The priority now exceeds the
maximum total window cost (`30 * len(S) + 1`). The resulting constant-slot
lexicographic D0 ranking passes the unchanged `lgx_check`; no new trusted
proof rule is needed.

The ten other requested rows remain open at this checkpoint. The
six period-three rows need a tighter list language than the stock BLC5
learner, whose exploration exceeds 800 families. Four zero-block rows
first reach an untrusted finder limitation on upper bounds of
multivariable tail references; splitting or deferring that bound removes
the immediate error but still exceeds the family cap. These search results are not coverage proofs.

The batch emitter already formats indices with a minimum of two digits.
The collector and shard matcher now accept indices of two or more digits
as well, allowing the AST sequence to continue past 99. The six-shard
partition check includes the new three-digit batches.


#### 7.4.AST11 Three-phase zero-block lists: four more of the new fourteen (2026-10-01)

`CBT_AST_102` boards four more rows from the new request. Together with
AST100, AST105, and AST106, **eight of the fourteen are proved**, leaving
**six requested rows** and **487 rows globally**. The four AST102 proofs
reuse `ListGlueLexTr` with 192, 185, 187, and 185 families. The installed
batch compiled in 16.18 seconds; a private run under concurrent load took
56.83 seconds. All row and aggregate assumption audits show only
`functional_extensionality_dep`. The conservative CI allowance is 100s.

The successful invariant tracks position modulo **three**. Across left
one-block separators `0110`, neighbour offsets repeat `2, 2, -3`, with
multiplier two. Right zero-block separators `11011` have offsets
`3, 3, -2`; separators `111111` have `4, 4, -1`. After subtracting the
centre for each position class, the partial sum is identically zero.
The old learner considered only periods one and two, producing a wider
language whose exploration retained arbitrarily many explicit blocks.
`LG4_PERIODS` now allows the period list to be selected; its default
remains `1,2`. `LG4_PERIODS=3` with the ordinary BLC5 finder reproduces
AST102 without changing exploration or any Coq checker. The saved
certificates, row list, and `ast102_batch.py --check` reproduce and replay
the installed source.

The six unproved rows are:

```
1RB0LC_1LA1RD_1LA1LC_1RB0RA
1RB0LC_1LC1RD_1LA1LC_1RB0RA
1RB0RC_1LC1RA_1RB0LD_1LC1LD
1RB0RD_1LC1RA_1LD1LC_1RB0LC
1RB1LD_1RC1RB_1LA0RB_1LA0LC
1RB1RA_1LC0RA_1RA1LD_1LC0LB
```

These have three-cell periodic units and neighbour multiplier four.
For the first core, periods 3, 4, and 6 retain a residual-sum range of
width two and do not close. BLC6's local language, depth-counted right
tails, and local range splits also do not close. Actual-run diagnostics
identify missing left offsets `1,8,9` for the first core and a missing
start offset `7` for the second; adding their aligned-snapshot edges
moves the failure to growing symbolic right windows. Right-DFA
minimisation, periodic return samples, and a refit using far-end data
through 300 million steps do not yet give an invariant.

For the second core, the bounded-sum fit has a misleading tie: one
optimal centre assignment makes the learned left graph acyclic, while
an equally narrow assignment preserves its carry cycle. Forcing the
cyclic centres and taking a product with the last block spelling still
admits right-return suffixes that prevent closure. Enlarging these
refined graphs to 6,000 families did not stabilise them. Wider samples
also include unfinished near-head blocks, so their large offsets must
not simply be added to the finished-block language.

Two exact finite-prefix reductions are available: the third row joins
the first row's state-renamed orbit after step one; the fourth similarly
joins the second. The first two cores differ only at B0. A universal
finite-tape B0-hitting lemma would therefore cover both, but remains
unproved. Short-tape experiments and a decreasing real-valued tape
potential are insufficient: an all-ones input can grow far to the left,
so neither a fixed left boundary nor a natural-valued rank follows from
that potential. No conjectural lemma or incomplete batch is installed.

#### 7.4.AST12 Finite-word termination closes the last six of the fourteen (2026-10-02)

The six remaining AST10/AST11 rows are now boarded in `CBT_AST_98`,
`99`, `101`, `107`, `108`, and `109`. Together with AST100/102/105/106,
this completes all fourteen requested rows. The six reduce by exact state
permutations and reflection to two cores differing only at B0:

```
1RB0LC_1LA1RD_1LA1LC_1RB0RA
1RB0LC_1LC1RD_1LA1LC_1RB0RA
```

The failed unbounded block-list closures were replaced with a finite-word
termination proof. At A0 with a blank left half-tape, define
`P(n)=(10)^n110`, `Q(n)=(10)^n111`, and `U(n)=1^(2n+2)0`.
A complete sweep transforms `P(ms) Q(n) R` into `U(ms) U(n) 10 R`;
a scan ending at `P(ms) (10)^n 0 R` reaches B0. Both statements are
kernel-checked for arbitrary lists, counts, and suffixes.

The decisive normalization uses inert P0/P3 prefixes. A unary U-block
with index congruent to 0 modulo 3 preserves eventual B0 reachability;
index 1 leaves a two-zig carry; index 2 forces B0. A nonfinal two-zig
carry either forces B0 immediately or creates a P2 prefix, which is also
mortal. Strong induction on the untouched suffix proves every finite
frontier word reaches B0, including the formerly difficult mixed and
three-phase lists. A separate reset argument proves D0 reachability for
both B0 choices. Finite-left sweeps extend both results to *every finite
configuration*, so the conjugate variants need no orbit-joining or
special unary-seed invariant.

The generic proof chain is in `theories/Counters/`:

- `Period3MacroTr.v`: exact token scans and returns, without a B0 hypothesis.
- `ValueFrontierTransducer.v`: P/Q/U sweeps and the terminal B0 branch.
- `ValueWordNormalization.v`: inductive word rewriting and unary normalization.
- `Period3WordTermination.v`: termination for every finite frontier word.
- `ValueFrontierD0.v`: frontier D0 reachability for both B0 variants.
- `Period3FiniteTr.v`: arbitrary finite-tape B0/D0 reachability.
- `FiniteInstrTr.v`: recurrence from universal finite-tape reachability and
  its transport through state permutations/reflection.

Each batch combines the two manual recurrence results with the landed
`FuelMixPartialTr` checker for the other six instructions (window 3,
167--187 contexts). `tools/closeouttr/period3_ast.json` retains the six
certificates and conjugacies; `period3_batch.py --check` verifies the
mapping tables, skipped instructions, and byte-exact batch reproduction.
All six `coversTr` proofs compile. Their assumption audits contain only
`functional_extensionality_dep`; the pure word-termination theorem is
axiom-free. Each batch has a conservative five-second CI cost entry.

After merging main and regenerating: **513 batches, 10,663 boarded,
261 remaining**. No frozen census, RunTr, CloseoutKit, workflow, or Makefile
source was changed by this proof work.
