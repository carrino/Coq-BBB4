# Coq-BBB4: scoping the Coq formalization of the BBB(4) results

_**Historical document** (2026-07-13, the pre-build plan).  Its inventory and
coverage numbers are frozen at that date; the current state of the
development is [README.md](README.md) and [docs/CLAIMS.md](docs/CLAIMS.md)._

Status: scoping document, 2026-07-13.  Nothing here is built yet; this
maps the work of porting everything the BBB harness repo
(`carrino/BBB`) proves into a machine-checked Coq development, using
`carrino/Coq-BB5` (mxdys' BB(5) = 47,176,870 proof) and
`carrino/busycoq` (meithecatte's individual-machine framework) as the
foundation.  The BBB harness currently stands at **3685 / 3713
holdouts decided (3514 never-quasihalting + 171 quasihalting with
exact scores), 28 machines open**.  The formalizer can be built now;
the 28 gaps (plus any new certificate types they force) slot in as
they are whittled down.

---

## 1. What "everything in BBB" means, precisely

The BBB repo's trust surface is `src/verify.c` (9,082 lines of C): an
independent checker that re-simulates from the blank tape and
re-derives every claim of every certificate.  The search/prover side
(`bouncer.c`, `irules.c`, `quiet*.c`, `prototype/*.py`) is heuristic
and *not* part of what needs formalizing — it only arms
verifications.  So the port is:

> Replace `bin/verify` with Coq: for each committed certificate,
> a Coq theorem `never_quasihalts tm` or `quasihalts_with_score tm s`,
> checked by a verified reflective checker running inside Coq
> (`vm_compute`/`native_compute`), consuming the same certificate
> data.

That decomposes into (a) a **semantic core** — the machine model and
quasihalting definitions, which exist in *neither* reference repo —
and (b) one **verified checker per certificate type**, of which there
are 20 committed, in five natural groups (§3).

### Two scopes, one architecture

- **Scope A (the port — this document's main subject):** every
  decided holdout in `BBB4_holdouts_3713.txt` gets a Coq-checked
  decision.  Deliverable: a per-machine theorem table covering
  3685 machines today, 3713 when the residue closes.
- **Scope B (the stretch — full `BBB(4) = N`):** the holdout list is
  itself the *output* of external, unformalized deciders (the
  bbchallenge wiki's list; the producer/decider set is not even
  documented — BBB README open question 2).  A genuine BBB(4)
  theorem must therefore re-decide the *entire* (4,2) TNF space in
  Coq, not just the 3713 holdouts, and additionally certify the
  champion's score as the maximum.  Coq-BB5's BB4 project proves
  this is tractable in principle (its full halting census of the
  (4,2) space compiles in ~30 s), but the quasihalting census of the
  non-holdout complement is new measurement + new bulk-decider work.
  Scope A is a prerequisite and should be built so Scope B is a
  matter of adding enumeration + bulk sweeps, not of re-architecting.

Recommendation: **build Scope A now, structured for Scope B.**  The
final theorem stays conditional ("every machine in list L
quasihalts/does not, with these scores") until both the residue-28 is
closed and the Scope B census lands.

---

## 2. Foundation: what lifts from the reference repos

### From Coq-BB5 (start from `CoqBB5/BB4/`, not BB5)

Coq 8.20.1, plain `_CoqProject` + `coq_makefile`, one stdlib axiom
(`functional_extensionality_dep`).  The BB4 subproject is the right
skeleton: same file layout as BB5 but all-generic (no hardcoded
tables, no sporadic machines), compiles in seconds.

Lifts nearly verbatim:

- **Machine model** (`BB4_Statement.v`): `St` (4 constructors), `Σ`,
  `Dir`, `Trans`, `TM := St -> Σ -> option Trans`,
  `ExecState := St * (Z -> Σ)`, `step`, `Steps`.  This matches the
  BBB harness model (deterministic, two-way-infinite blank tape,
  `None` = halt) exactly.
- **Encodings + machine construction** (`BB4_Encodings.v`,
  `BB4_Make_TM.v`): machine → `positive` encoding, `FMapPositive`
  lookup — the mechanism for embedding per-machine certificate
  tables.
- **TNF enumeration** (`TNF.v`, `BB4_TNF_Enumeration.v`,
  `SearchQueue`) — needed for Scope B; note §7 caveat about
  quasihalting vs. TNF normalization.
- **Decider plumbing** (`Deciders_Common.v`): the
  `HaltDecider`/`HaltDecider_WF`/`decider_cons`/`decider_list`
  composition pattern.  The *plumbing* transfers; the result type
  and every `*_WF` contract must be re-founded on quasihalting
  (§4).
- **Reflective closure deciders as code**: `Decider_NGramCPS.v` and
  `Decider_RepWL.v` implement, verified, the same abstractions the
  BBB `neverqh_*` certs use — but their soundness theorems prove
  only *non-halting*.  The closure-construction code and its
  covering lemmas are reusable; the liveness layer on top (§5
  Group C) is new.
- **Proof-engineering patterns**: `vm_compute`/`native_compute`
  reflective checking, generated `.v` certificate tables, per-file
  parallelism.  Coq-BB5 verified 47M-step simulations this way, so
  the BBB certs' `t ≈ 5·10^5` re-simulations and exact fire-count
  claims are comfortably in budget.

### From busycoq (`verify/` is the Coq; `beaver/` is Rust)

- The generic `Ctx` functor core (`TM.v`): coinductive stream tapes,
  `step`/`multistep`/`evstep`/`progress`, and the non-halting kit
  (`progress_nonhalt`, `progress_nonhalt_simple`, `_cond`) — the
  natural language for **individual machine proofs**.
- The `Individual.v` Ltac layer (`prove_step`, `execute`, `follow`,
  `simpl_tape`) — the biggest labor-saver for hand-proving the hard
  residue machines; simple machines are ~26 lines, Skelet-class
  100–1500.
- The specialized arithmetic (`FixedBin.v`, `ShiftOverflow*.v`) —
  directly relevant: the BBB residue is *dominated by binary-counter
  machines*, which is exactly what these were built for.
- `Compute.v` (computable tape + `eqb` bridge) and the
  Cyclers/TCyclers/Bouncers in-Coq certificate-checking pattern.
- Coq-BB5's `BusyCoq_Translation.v` bridges stream-world nonhalting
  proofs into `Z -> Σ`-world (`to_NonHalt`).  We need the analogous
  bridge for quasihalting statements (finite extra work: the
  translation preserves the step-for-step trace, so fire counts
  transfer).

**Neither repo contains any quasihalting/beeping content** (verified
by grep: zero hits in both).  The semantic core is genuinely new.

---

## 3. Inventory: the 20 certificate types to formalize

Counts are committed-cert tallies (some `results/certs_*` dirs are
re-sweeps of the same machines by later prover generations; the
deduplicated scoreboard is 3685 machines).  C-verifier line counts
approximate the checking logic each type needs.

### Group A — exact cycle certificates (trusted core; ~160 lines C)

| type | claim | count |
|---|---|---|
| `halt` | halts exactly at `anchor_step` | (census use) |
| `inplace` | configs at `anchor_step` and `+period_steps` identical ⇒ verbatim loop forever | few |
| `tcycler` | translated cycle: after `period_records` records on `side`, state + `reach+1`-cell frontier window recur; head confined | ~80 |

The `tcycler` induction (BBB README "Soundness (induction)") is the
single most-reused lemma in the whole development: blank-beyond-the-
all-time-extent + determinism ⇒ the relative motion repeats forever.
It also underpins the counter certs' uniformity arguments (Group B)
and the record argument (Group C).  A cycle cert fixes every
transition's class (I inside the loop, F before it, N unfired), so
one certificate resolves both transition- and state-level QH plus
the exact score.

### Group B — parametric counter certificates (bbbcert v8; 12 machines; ~2,500 lines C)

`bounce_counter` (#8,#33), `mono_counter` (#10,#26,#31),
`spacer_counter` (#16,#22,#23), `gray_counter` (#19),
`double_counter` (#30), `interleave_counter` (#18,#35).  Shared
skeleton: a decode function tape ⇄ counter value (six distinct
encodings: 2-cell binary digits, odd-cell binary, Gray code,
interleaved binary, doubling comb, counter+spacer), a **faithfulness**
lemma (`C(n) → C(n+1)` re-derived by raw simulation over a parameter
range, all 8 transitions firing), **all-parameter uniformity** via
translated-cycle sub-proofs + a read-window locality bound, and a
blank→`C(n₀)` **bootstrap**.  Liveness = parameter → ∞ (only
`bounce_counter` needs a well-founded measure).

### Group C — n-gram / RepWL closure + liveness (the bulk; ~1,750 lines C)

| type | abstraction / extra rule | count |
|---|---|---|
| `neverqh_ngram` | n-gram window closure; per-state acyclicity | 21 |
| `neverqh_rank` | + ranking measures, rules (a)/(b) (Bellman–Ford) | **2611** |
| `neverqh_fuel` | + capped sided nonblank counts, rule (c2) | 62 |
| `neverqh_drift` | + rule (c3), the record argument | 17 |
| `neverqh_wall` | + frozen-boundary distance, rule (c4) | 0 (road exhausted) |
| `neverqh_rwl` | RepWL whole-tape block closure | 15 |
| `neverqh_rwlrank` | + five exact-delta measures incl. interior blanks `0/l`,`0/r` | 106 |
| `neverqh_rwlsilent` | + silent (fully-undefined) states | 5 |

Certificates are tiny — `(t, n)` or `(t, L, T)` plus per-state
measure lists — because the verifier *recomputes the entire closure
and liveness procedure*.  The Coq checkers do the same (this is
exactly Coq-BB5's NGramCPS/RepWL pattern), so no bulky tables.

The shared mathematics: a **covering invariant** (every concrete
config reachable from `config(t)` is covered by an abstract context;
halt-free closure ⇒ non-halting), the **SCC liveness lemma** (an
infinite q-avoiding run's infinitely-often set is a cyclic SCC of the
context graph; no reachable q-free cycle ⇒ q recurs), and the
**measure rules**: (a) nonincreasing measure ⇒ strictly-decreasing
edges fire finitely; (b) every-cycle-strictly-decreasing ⇒ SCC cannot
confine a run; (c2) fueled uniformly-directional runner SCCs die;
(c3) every-cycle-nets-toward-a-fueled-side dies by the **record
argument** (a diverging head keeps entering never-visited, hence
blank, territory); (c4) wall distance as a measure with exact
per-node deltas.  Each measure needs finiteness, nonnegativity, and
an exact per-step delta derivable from the abstract context alone
(window-coverage bounds).

### Group D — inductive-rules geometric sweepers (`irules` v1–v4; ~1,200 lines C, the largest single subsystem)

610 never-QH + 163 QH certs.  Symbolic RLE tapes with affine
run-counts, engine ops (concrete step, chain hop, bulk rule
application with induction on the application count R), rule replay
from fresh-variable generalizations, and the meta-cycle induction
`C(k) →* C(a·k+b)` with `f : [kmin, ∞) → [kmin, ∞)`; v2 adds block
runs + peel/absorb, v3 multi-decrement rules + rule-in-rule (one
level) + block hops, v4 the multi-variable linear meta map
`x → M·x + cc` (geometric and polynomial regimes in one form).  The
same cert type proves QH sweepers with exact scores (a late-epoch
state going quiet).

### Group E — wrapped quiet-state QH certificates (~500 lines C)

`wrapctl` (12, RepWL block-1), `wrapfar` (18, DFA-abstracted
half-tapes), `wrapngram` (103, n-gram; also single-transition wrap).
Construction: `M'_q` = M with state q redirected to halt; a halt-free
closure of `M'_q` from `config(t)` proves q never fires after t.
Score exactness comes from the simulated prefix.  Plus `bouncer` (6,
affine formula tapes).

### Not yet existing (the gaps to fill later)

The 28 open machines: #12 (EXP marker counter), families B/C/D/E
(period-2/3/4 comb variants — plausibly more Group-B-style cert
types or individual proofs), and **family F** (~13
cascade/nested-fractal machines) whose macro-step has k-dependent
phase structure — these need a *nested/scaling* translated-cycle
abstraction that doesn't exist yet even in C (research, not port).
The architecture must let these land as either (i) new cert types
with new Coq checkers, or (ii) busycoq-style individual proofs — see
§6 recommendation.

---

## 4. The new semantic core (exists nowhere yet)

Definitions, per BBB README, to be fixed in `BBB4_Statement.v`:

- **Traces and fire counts.**  With `Steps tm n c0 c` deterministic,
  define `fires tm tr n` (transition `tr = (q, s)` fires at step n;
  steps numbered from 1, and **reaching a halt/undefined transition
  counts as a step** — the bbchallenge convention, load-bearing for
  scores and a classic off-by-one trap).
- **Transition classes.**  In an infinite run each transition fires
  never / finitely / infinitely (N/F/I).  `quasihalts_tr tm :=
  ∃ tr, fires ≥ 1 ∧ finitely`; transition-level score = max last-fire
  among such.
- **State level (BBB proper).**  A state's last visit = max last-fire
  over its transitions; `quasihalts_st tm := ∃ q, visited finitely
  but ≥ 1`; score = last visit.  Prove the derivation lemmas
  (state quiet ⇔ all its transitions F/N) once; every checker then
  works at transition level and state results are derived, exactly
  as the C does.  The two levels genuinely differ
  (`1RB1LA_0LA1RA`: transition-level QH score 7, state-level not QH)
  — both must be modeled.
- **Halting interaction.**  A halting machine quasihalts trivially
  (score = halting step); the interesting census is non-halting
  quasihalters.
- **Silent states.**  A never-visited state (score 0): the
  convention question is open upstream and cannot affect any BBB
  value.  Parametrize the top-level statement over the convention;
  `neverqh_rwlsilent` certs prove exactly the convention-independent
  facts (non-halting + liveness of every defined state + silence of
  the undefined one).
- **Result contract.**  Replace `HaltDecider_WF` with a
  `BBBDecider` returning
  `Result_NeverQH | Result_QH (score) | Result_Unknown`, with WF =
  soundness against the predicates above; keep Coq-BB5's
  `decider_cons`/`decider_list`/identifier plumbing verbatim.
- **Record events and extents.**  Running min/max head position,
  "cells strictly beyond the all-time extent are blank" — the shared
  substrate of tcycler, (c3) and (c4).  Prove once, early.

Also needed: the **nonhalt-side strengthening of busycoq's
`progress_nonhalt`** — a variant certifying "the invariant family of
configs never enters state q" (⇒ q quiet) and "each lap fires every
transition" (⇒ never-QH) — the closer for individual proofs, plus
the quasihalting-preserving version of `BusyCoq_Translation.v` if we
keep two tape worlds (§6).

---

## 5. Phased plan with effort estimates

Estimates are hand-written-Coq lines (generated tables excluded) and
are calibrated against Coq-BB5 (~26k lines for all of BB5) and
busycoq.  Order chosen so that the highest machine-coverage-per-
effort lands first, and each phase ends with certs being checked
end-to-end in CI.

| Phase | Content | Machines covered (cum.) | Est. Coq LOC | Risk |
|---|---|---|---|---|
| **0. Core** | repo scaffold (BB4 skeleton), model, quasihalting semantics (§4), fire-count/trace lemmas, record/extent lemmas, cert-table toolchain (.cert → .v generator, out of trust surface) | — | 2–3k | low; design-heavy |
| **1. Cycle certs** | `halt`, `inplace`, `tcycler` checkers + the tcycler induction + full N/F/I classification from a cycle | ~80+ | 1.5–2.5k | low |
| **2. Closure + liveness framework** | generic covering-abstraction interface; n-gram and RepWL instances (port/extend Coq-BB5's `Decider_NGramCPS.v`/`Decider_RepWL.v` closure code); SCC liveness lemma; rules (a)/(b); then (c2)/(c3)/(c4) and the fuel/wall refinements; `rwlrank` measures; silent states | **~2,840** (all Group C) | 5–8k | **the mathematical heart**; (c3)/wall covering invariants are subtle (see §8) |
| **3. Wrap QH certs** | `M'_q` construction + reuse of Phase-2 closures; exact-score derivation from the simulated prefix; `wrapctl`/`wrapfar`/`wrapngram`; `bouncer` | +~139 QH | 1.5–2.5k | low-medium |
| **4. irules engine** | affine-expression algebra, RLE symbolic tape, engine-op soundness, rule replay, meta-cycle induction, v2–v4 extensions | +~700 | 6–10k | largest engineering block; v3/v4 features are intricate but well-specified |
| **5. Counter certs** | shared counter toolkit (decode + faithfulness + uniformity-via-tcycle + bootstrap), then the 6 types — or individual proofs instead, see §6 | +12 | 3–5k (checker route) | medium |
| **6. Assembly** | per-machine theorem table over the 3713 list, coverage checker, top-level conditional statements, CI | 3,685 → 3,713 | 1.5–2.5k + generated | low |
| **(B) Census** | TNF enumeration + bulk quasihalting sweeps of the non-holdout complement; final `BBB(4)` value statement | whole (4,2) space | unknown until measured | needs a measurement run first |

Total Scope A: roughly **20–35k hand-written lines**, i.e. a
development on the order of Coq-BB5 itself.  That is consistent with
what the C side suggests: `verify.c` is 9k lines of *dense* checking
code, and Coq formalizations of such code with their soundness
proofs typically come out 2–4×.

Compile-time: dominated by Phase-2 closure recomputation × 2,800
certs and Phase-6 re-simulation to each cert's `t`.  Both are the
same workload shape Coq-BB5 handled with `native_compute` (45 min
for BB5, 30 s for BB4); at (4,2) sizes with t ≈ 5·10^5 this should
sit comfortably under an hour with per-file parallelism.

---

## 6. Design decisions (recommendations)

1. **Toolchain**: Coq 8.20.1 + coq-native, `_CoqProject` +
   `coq_makefile`, mirroring Coq-BB5/BB4 so its files import with
   minimal churn.  (Migrating to Rocq naming can happen later; don't
   pay it now.)
2. **Tape representation**: `Z -> Σ` (Coq-BB5) as the *statement*
   world — the top-level theorems and all reflective checkers live
   here.  Keep busycoq's stream world as an optional *proof* world
   for hand proofs, connected by a quasihalting-aware port of
   `BusyCoq_Translation.v`.  This is exactly the BB5 architecture
   and lets us steal `FixedBin.v`/`ShiftOverflow*.v` for the counter
   machines.
3. **Checkers recompute; certificates stay small.**  Follow the C
   verifier's philosophy (and Coq-BB5's): the Coq checker re-derives
   closures, SCCs, replays and simulations from `(machine, small
   parameters)`; certificate tables embed only what `verify.c`'s
   cert files carry.  A ~200-line untrusted script converts the
   committed `.cert` files to generated `.v` tables.
4. **Prove the semantic predicate, not the C bookkeeping.**
   `check_claims` demands bit-exact fire-count/last-fire tables;
   the Coq theorems should target `never_quasihalts tm` /
   `quasihalts_with_score tm s` directly.  The classification
   lemmas exist internally (they're how scores are derived), but we
   don't owe the C cert format its full claim surface — this cuts
   real work.
5. **Counter machines: prefer individual proofs first.**  Six
   bespoke checker types for 12 machines is the C-side economics
   (one checker covers a family, re-runnable).  In Coq the
   economics flip: with the busycoq `Individual` + `FixedBin` kit,
   12 binary-counter machines are plausibly cheaper as 12 direct
   proofs (a few hundred lines each) sharing a counter-lemma
   library, than as 6 verified parametric engines.  Decide after
   prototyping one machine both ways (#10/mono is the simplest).
   The same choice recurs for whatever decides the residue-28 —
   and for ≤ 30 machines, individual proofs are almost certainly
   the right landing zone, which means **the residue does not block
   the formalizer**: it lands through a door we need anyway.
6. **Freeze cert semantics by type**, as the C does (committed
   types never change meaning; new powers = new types).  The Coq
   side should mirror this: one checker function per type, no
   flags that alter soundness.
7. **Statement hygiene**: top-level theorems parametrized over the
   silent-state convention; the holdout-list hash
   (`3666f0fa…`) recorded; per-machine theorems named by
   bbchallenge machine text.

---

## 7. Scope B notes (full BBB(4) theorem)

- **TNF vs quasihalting**: the standard TNF census stops at halting
  leaves; the BBB enumerator (`enumerate.c`) deliberately includes
  machines with no halt transition, and machines differing only in
  never-fired (`---`) transitions are enumerated once — harmless for
  the BBB *value* (an unfired transition is N and a never-visited
  state can't set a positive score) but it must be *proved*
  harmless: a "don't-care completion" lemma that the QH status and
  score of any completion of an enumerated representative are
  determined.  Coq-BB5's `TNF.v` needs this quasihalting analogue of
  `CountHaltTrans_0_NonHalt`.
- **The complement census** (everything not in the 3713 list) was
  decided by external tools with no certificates.  Plan: run the
  existing C harness's cheap deciders over the full enumeration to
  measure what fraction falls to cyclers/tcyclers/closures, then
  size the Coq bulk sweep.  Until that measurement, Scope B effort
  is honestly unknown.
- **The value**: `BBB(4) = N` additionally needs the champion's
  score verified exactly (a Group E-style cert) and every other QH
  machine's score bounded below it — the assembly is mechanical
  once per-machine theorems exist.

## 8. Risks and mitigations

1. **A soundness argument fails formalization.**  The drift rule
   (c3) was once (wrongly) marked unsound upstream, and the wall
   covering invariant is the subtlest piece in the repo.  Coq is
   exactly the tool for settling these; if a rule genuinely resists
   proof, the fallback is cheap: 17 (`drift`) and 0 (`wall`)
   machines ride on them, and the C prover can re-emit those
   machines under stronger types (or they become individual
   proofs).  The falsification sweeps upstream (0 false claims in
   5,977 adversarial runs) make an actual unsoundness discovery
   unlikely but not impossible — finding one would itself be a
   headline result.
2. **irules v3/v4 complexity** (multi-decrement binding-run
   selection, rule-in-rule dependency order, block-phase stream
   equality, the anti-circularity scale restriction from
   `docs/groups.md`).  Mitigation: formalize v1 first (it already
   covers most irules certs via the v1-compatible subset), gate
   v2–v4 features behind separate lemmas, and lean on the C repo's
   corruption tests as a spec: every mutation the C verifier
   rejects, the Coq checker must reject too (port the corruption
   suite as negative CI tests — `Fail`-style checks).
3. **Certificate drift** while BBB is still moving (new types for
   the residue).  Mitigation: the frozen-types discipline (§6.6) +
   the cert→table generator make new types purely additive.
4. **Compile-time blowup** on the 2,611 rank certs.  Mitigation:
   Coq-BB5's playbook — `native_compute`, per-file splitting,
   `positive` encodings; and the closures at (4,2), t = 5·10^5,
   n ≤ 12 are small by BB5 standards.
5. **Convention mismatches** (halt-step counting, score off-by-one,
   silent states) surfacing late.  Mitigation: Phase 0 includes
   differential tests — Coq `vm_compute` simulation vs. the C
   harness's CSV output on the (2,2)/(3,2) censuses before any
   checker is built.

## 9. Proposed repo layout

```
Coq-BBB4/
  _CoqProject  Makefile
  theories/
    Prelims.v  Tactics.v                  (lifted from Coq-BB5)
    BBB4_Statement.v                      (model + quasihalting core, §4)
    BBB4_Encodings.v  BBB4_Make_TM.v      (lifted)
    Traces.v  Records.v                   (fire counts, extents, record lemmas)
    Deciders_Common.v                     (BBBDecider result type + WF + plumbing)
    Checkers/
      Cycle.v                             (halt / inplace / tcycler)
      Closure/  (NGram.v RepWL.v Cover.v SCC.v Rank.v Fuel.v Drift.v Wall.v Silent.v)
      Wrap.v  Bouncer.v
      IRules/  (Expr.v RLE.v Engine.v Rules.v Meta.v V2.v V4.v)
      Counter/ (shared toolkit, if the checker route wins §6.5)
    Individual/                           (busycoq Ctx instance BB42 + tactics + bridge)
    Machines/                             (per-machine proofs for residue/counters)
  tables/                                 (generated .v cert tables — untrusted generator in tools/)
  tools/cert_to_v.py
  Enumeration/                            (Scope B, later)
```

## 10. First milestone (vertical slice)

Prove the pipeline end-to-end before going wide: scaffold + Phase 0
core + the `tcycler` checker + one generated table entry, closing
with a Coq theorem for the sample machine
`1RB1LD_1LC0LD_1RC1RA_0LB0RA` (period 118 records / 17,620 steps, all
8 transitions I ⇒ does **not** quasihalt) — the same machine BBB's
README uses as its worked example.  That slice touches every
architectural joint (model, semantics, reflective checking, table
generation, CI) at minimal size, and everything after it is
parallelizable by certificate group.
