# Plan: mxdys' `Inductive` / `RRBA` deciders against our residue

_Written 2026-07-26 after mxdys pointed John at
`https://github.com/ccz181078/busycoq/tree/BB6/`.  Everything in §1 was
checked against a clone of that branch today; §3 onward is the plan._

**This retires a do-not-retry entry.**  `WAVE13_FINDINGS.md` §8 and every
prompt since say *"mxdys' implementation: John reports it is NOT available.
Stop asking."*  It is available.  `WAVE9_FINDINGS.md` §7 asked for exactly
this three waves before the lap decider was built.

## 1. What is actually there (verified)

`verify/Inductive.v` (8,945 lines) and `verify/RRBA.v` (5,063 lines), plus
`RWLAcc.v`, `UBRRBA.v`, `CTL.v`.  **No `Axiom`, no `Admitted`** in either.
Coq 8.18 — the same toolchain we build with.

### 1a. The top-level theorem is halting-only

    Lemma decide_hlin_nonhalt_spec_1 T : decide_hlin_nonhalt T = true -> ~halts tm c0.
    Lemma decide_loop2_spec ... : ~halts tm c0.

and grepping the whole tree for `QuasiHalt` / `beeping` / `infinitely often`
returns **nothing**.  So neither decider answers our question directly: the
BBB residue needs `NeverQuasiHaltsSt` or `QHBound B`, and non-halting alone
moves `D_remaining` by zero.

### 1b. But the proof is an exact forward model, and that is the part we need

John's point, and it is the right one: to prove `~halts` these deciders have
to *model the behaviour*.  That model is first-class and exposed:

    Inductive prop0_expr :=
      | multistep_expr (a b : config_expr) (n : nat_expr)
      | multistep_lb_expr (a b : config_expr) (n : nat_expr)
      | ...

`config_expr = side_expr * side_expr * Q * dir` — a symbolic configuration
**carrying its state**.  A non-halting proof is a chain of such rules
returning to a shifted copy of its start.  That is the same shape our
`LapDecider` certificate has, and `LapGlue.glue_neverqh` consumes exactly
it: per lap an existential `csteps` witness, plus a per-state visit witness.

**The visit witnesses come from the rule ENDPOINTS, not from inside a rule** —
each `config_expr` carries a `Q`, so if the four states appear among the
configurations of the chain, liveness follows.  That is precisely the
mechanism `LapCertGlue.vis_via_ovf` already implements for our own chains.

### 1c. Their count language expresses what ours cannot

This is the decisive fact.  `WAVE14_FINDINGS.md` §3 measured our wall: the
overflow lap costs `Θ(2^j)`, and `sside` carries `a*j+b` while `srun`
returns `ca*j+cb`, both affine, so it is **unrepresentable** for us.  Theirs:

    Inductive nat_expr :=
      | from_nat (n:N) | nat_add | nat_mul
      | nat_powsum (k:N) (n:nat_expr) | nat_powsum2 (k:N) (n:nat_expr)
      | nat_var | nat_ivar

    Definition powsum  k x := (((k+2)^x - 1) / (k+1))%N.
    Definition powsum2 k x := (((powsum k x) - x) / (k+1))%N.

`powsum 0 x = 2^x - 1`.  A geometric sum — **exponential**.  `nat_mul` gives
the quadratic family; `powsum k` gives the base-`(k+2)` families; `powsum2`
gives the level above that.  Mapped onto our measured buckets:

| our class (`ovfshape.py`, all 1,176) | count | their constructor |
|---|---:|---|
| `AFFINE/EXP2` (the overflow wall) | 496 | `nat_powsum 0` |
| `QUAD/QUAD` | 25 | `nat_mul` |
| `EXP4` | 19 | `nat_powsum 2` |
| `HIGHER` (~`3^j`) | 17 | `nat_powsum 1` |
| `AFFINE/AFFINE` (we can already do these) | 304 | affine |

And the tape language has counters built in:
`side_binary`, `side_binary_Pos`, `side_3ary_Pos`, `side_binary_dec`,
`side_BL` — binary-counter side representations, which is what six waves of
`Ip`/`Jp`/`Kp`/`Dp`/`Mp`/`Bp`/`Gp` alphabet work has been reconstructing.

### 1d. It is instantiable at (4,2), cheaply

The framework is a functor:

    Module Type Ctx.  Parameter Q : Type.  Parameter Sym : Type.  ...
    Module Individual (Ctx : Ctx).

with instantiations for (2,5), (3,3), (5,2), (6,2).  **`Individual52.v` is 26
lines.**  A `BB42` context (states `A..D`, symbols `S0/S1`, decidable
equality) plus `Individual42.v` is a morning's work, not a project.

### 1e. The tape models are isomorphic

    theirs:  Notation side := (Stream Sym).   tape := side * Sym * side
    ours:    Record Tape := { t_left : nat -> Sym; t_head : Sym; t_right : nat -> Sym }

`Stream Sym` and `nat -> Sym` are isomorphic, and both projects already pay
`functional_extensionality` for it.  Their `TM : Q -> Sym -> option (...)`
matches our `TM : St -> Sym -> option Trans`.  The bridge is a pair of
conversions plus one simulation lemma — small, and it is the main integration
cost.

### 1f. There is an extracted native decider

`verify/Extraction.v`, `verify/decider.ml`, `verify/main.ml`, and a Rust
`beaver/`.  So the SEARCH can be run natively over our 1,176 without
compiling any Coq.

## 2. What this does and does not buy

* It **does not** hand us boards.  `~halts` is not `QHBound`.
* It **does** supply the two things we are actually blocked on:
  a count language that expresses `Θ(2^j)` (our 532-machine wall, plus the
  quadratic and base-3/4 families), and a rule-discovery engine that finds
  those rules — the "nested lap" design pass `WAVE14_FINDINGS.md` §6 ranked
  first, already done and already verified by someone else.
* The liveness half stays ours, and it is small: `glue_neverqh` is generic in
  the anchor family, and the visit witnesses fall out of the rule endpoints.

## 3. The plan

Staged so the cheapest step is also the decisive one.  **Do not skip Stage 0**
— every wave that templated before measuring is in the do-not-retry list.

### Stage 0 — measure, no Coq (target: hours)

1. `BB42` + `Individual42.v` (~30 lines, patterned on `Individual52.v`).
2. Build the extracted OCaml decider from that branch.
3. Run `Inductive` and `RRBA` over all **1,176** residue machines.
4. Report three numbers:
   * how many are decided `~halts` at all;
   * of those, how many have a rule chain whose configurations cover **all
     four states** (⇒ liveness is free, they are boards);
   * how many need a `nat_powsum`/`nat_mul` rule (⇒ confirms §1c against our
     own `ovfshape.py` buckets rather than assuming it).

**Decision gate.** If (ii) is large, Stage 1-3 is the wave. If (ii) is near
zero but (i) is large, the rule chains exist but do not visit every state at
their endpoints, and the work moves inside a rule — a different, larger job.
If (i) is small, their search is tuned for BB(6) shapes and this is a dead
end; say so and go back to the nested lap.

### Stage 1 — the bridge (target: 1-2 days)

`theories/Bridge/BusyCoqTM.v`: `Stream Sym ↔ nat -> Sym`, their config ↔ our
`cconf`, and

    Lemma multistep_csteps : forall tm n a b,
      BC.multistep (tr_tm tm) n (tr a) (tr b) -> csteps tm n a = Some b.

Keep it axiom-free apart from the standing `functional_extensionality_dep`.
This is the only genuinely new mathematics and it is one theorem.

### Stage 2 — the liveness layer (target: 2-3 days)

`theories/Bridge/RulesToLap.v`:

    Theorem rules_to_never_qh : forall tm (chain : list rule),
      chain_valid tm chain ->
      chain_returns_shifted chain ->
      states_covered chain = true ->
      NeverQuasiHaltsSt tm

built from Stage 1 plus the existing `glue_neverqh`, and a `glue_qh` variant
for the 164 quasi-halters.  **One theorem, not one per machine** — the same
architecture as `srun_sound`.

### Stage 3 — run it and board (target: the rest of the wave)

Emit one small `.v` per machine: the TM table, the rule chain as data, a
`vm_compute`, and the closing theorem.  Then `inventory.py` +
`gen_stages.py` + `audit.py` as usual.

## 4. Risks, honestly

| risk | mitigation |
|---|---|
| Their search is tuned for BB(6) halting; our (4,2) machines may fall outside its heuristics | Stage 0 measures this before any Coq is written |
| Compile cost — the README says ~1 month for the full repo | We need only `Individual` + `Inductive`/`RRBA` + deps; measure in Stage 0 |
| Rule chains may not cover all four states at their endpoints | Stage 0 gate (ii); if so, extract states from inside a rule — bigger, still bounded |
| Vendoring another repo into ours (provenance, licence, maintenance) | John's call.  Alternative: keep it out-of-tree as a *search oracle* and re-prove each rule with our own checker extended by `powsum` counts |
| `-native-compiler yes` in their `_CoqProject` | We build with `no`; should be fine, verify early |

## 5. The cheaper fallback, if Stage 0 disappoints

Even if integration fails, §1c is worth the trip on its own: it tells us the
count language a nested `LapDecider` needs is **`a*j + b` extended by
`powsum k` and one multiplication**, and that `side_binary*` are the right
tape constructors.  That is the design pass `WAVE14_FINDINGS.md` §6 asked
for, answered by an existing verified implementation — we would be
re-deriving a known-good design rather than inventing one.
