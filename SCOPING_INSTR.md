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

## 8. What we deliberately do NOT redo

* The state-level theorem and its census `.vo` stay frozen and untouched;
  the new development builds beside, not on top.
* No strengthening of in-walk tiers to rescue deferrals (PLAYBOOK Rule 4
  survives verbatim: prove machines, keep the walk light).
* No hand-porting of generated layers (`Machines/` ~2.6M lines,
  `Closeout/CB_*`, census lists): they regenerate from tools once the
  checker layer lands.
