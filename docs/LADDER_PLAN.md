# The generic solver: build rung two once, stop paying a session per shape

_Written 2026-07-30 (branch `claude/residue-class-analysis-6wrb8t`), after a
cross-repo survey of Coq-BBB4, BBB, and the busycoq clone.  This is the
operational plan for `docs/RULE_LADDER.md` §5 ("what would mxdys do with OUR
residue? … Build the second rung, once"), which has been a design note without
an owner since 2026-07-26 while waves 29–32 continued shape-by-shape.
Companion reading, in order: `RULE_LADDER.md` (the design),
`MXDYS_INDUCTIVE_STAGE0.md` (the measured gate), `BBB/docs/irules.md` +
`irules2.md` (the engine this extends), `WAVE32_PROMPT.md` (the wave route
this runs beside)._

## 0. The diagnosis: why the burn-down slowed to one machine at a time

The wave route pays **one session per lap shape**.  Each wave lands one new
piece of certificate grammar (an alphabet, a peel, a frame family, a nesting
lemma) plus its emitter plumbing, and the rows whose exact lap structure fits
fall together.  That worked while whole buckets shared a shape (wave-22:
102 rows in one build; wave-29: 34 of 36 "short" rows were one reader
constant).  It stopped working when the residue's remaining 150 core rows
split across **10 gate buckets** (`WAVE32_PROMPT.md` gate table), each needing
its own grammar piece, with rows queued behind SEVERAL gates in series —
wave-31 opened the interior gate for 30 rows and boarded **zero**, because
every one of them then hit its next gate.

The root cause is stated in `RULE_LADDER.md`: our checkers have a **fixed,
one-rung rule grammar** (affine lap chains, plus hand-built specials for one
level of nesting, two-form frames, and the register composition).  Every shape
outside the grammar costs a wave.  mxdys's `Inductive.v` does not have this
problem because its checker **discovers and proves its own rules at run time**
(`find_IH` / `try_ind` / `follow_rule`): a level-`k+1` rule is proved by an
induction whose step case invokes only levels ≤ `k`.  New shapes cost a
constructor, once, instead of an emitter per shape.

## 1. What exists today (verified this session, with locations)

* **The design**: `RULE_LADDER.md` — rules as data, one `rule_sound` theorem
  by ladder induction, count language `add`/`mul` (+ `powsum`/`powsum2` only
  at rung 3), liveness as an SCC property of the rule-application graph.
* **The nearest running ancestor**: the irules stack, on BOTH sides.
  - Prover: `BBB/bin/irules` (v2+: block-run configurations, multi-variable
    affine meta maps, prefix handling).  Its own docs name the frontier
    exactly: mid-cycle geometric cascades "still need … rule-in-rule
    application" (`BBB/docs/irules2.md`, deferred "class 3").
  - Checker: `theories/Checkers/IRules/` up to the v5c block engines,
    **including QH-sound variants** (`MetaBlkPfxQH.v`
    `irulesblkpfx_check_qh_sound`; 22 machine files already board through the
    QH checkers).  The liveness bookkeeping is already right at both levels:
    transitions fired inside a rule body applied `R ≥ 1` times are Infinite;
    fired only at the anchor, Finite; unfired, Never.
* **The reference implementation**: mxdys's `Inductive.v` (8,945 lines,
  axiom-free, Coq 8.18) is IN the session's busycoq clone
  (`busycoq/verify/Inductive.v`), with the `ExtraRules` typed counter-rule
  interface and the hand-hint files `IndSBCv1.v` / `IndBECv1.v`.
  `MXDYS_INDUCTIVE_STAGE0.md` measured why a straight port cannot work for us:
  the top-level theorem is halting-only, rule-endpoint liveness is
  **structurally zero** (endpoints carry 1–2 states), and his counter families
  are human-hinted, not searched.  The ladder must be rebuilt on OUR liveness
  bookkeeping — which is irules'.
* **The eval set with known answers**: the 150 core rows
  (`tools/closeout/core_rows.txt`), every one hand- or tool-diagnosed:
  late-confirmed counter encodings for 65 of them
  (`tools/counter_encodings.tsv`; the sweep that built it measured 96% of the
  then-open population decoding as counters), gate labels per row
  (`tools/counters/buckets31/*.txt`), lap shapes per row
  (`tools/closeout/residue_map.tsv`).  Closing the 150 closes all 226 — the
  76 `0RB` shadows fall with their cores (`Closeout/ShadowKit.v`).

## 2. Baseline (measured 2026-07-30, this branch)

Current `bin/irules` (BBB commit `5f1856e`) over the 150 core rows:
**0 / 150 at 2·10⁵ steps AND at 1·10⁶ steps, zero certs, every derived
column zero** — no anchor, no meta map, no rules discovered on any row
(`tools/ladder/baseline_irules_150.txt`).  The 5× budget escalation changing
nothing confirms the blocker is SHAPE, not budget; and the number matching
the wave-8 sweep (`tools/nghist/wave8_irules_sweep.csv`, 0/150 on a far
older engine) despite block runs, multi-variable meta maps and prefixes
landing since confirms none of those touched the missing rung.  The counters
defeat the current grammar because a binary odometer's carry ripple
restructures the mid-cycle tape, so no fixed-run replay closes (`irules2.md`
"Scope and limits"; `COUNTER_CLOSEOUT.md` §0's RepWL measurement — 706/708
NOCLOSE — is the same fact for lossy closures).

## 3. The build, staged with kill criteria

**Stage A — rule-in-rule in the UNTRUSTED prover first.**  Extend the irules
replay engine so a proven rule can be applied a SYMBOLIC number of times
inside another rule's replay (the count becomes `mul`/`add` of existing
exprs), with rule discovery by history-matching exactly as today, plus the
interpolation step (`find_IH`'s job): observe the same candidate at two
indices, conjecture the general rule, verify by symbolic replay.  Prototype in
Python against 5 hand-picked rows with KNOWN structure before touching C:

| row | known structure |
|---|---|
| `1RB---_1RC1LB_0LB1RD_1RA0RC` | bounded inner carrier (innerfam33 line 1) |
| `1RB---_0LB1RC_0RD0RC_1LB1LD` | interior `j = S j'` wall (largest bucket) |
| `0RB0RD_1LC1RB_1RA0LC_1LB0LC` | two-form frame family |
| `1RB0LA_1LC0RD_1LA1LB_0LB1RD` | boot-blocked |
| `1RB1RD_1LC1RA_0RB0LC_1LA0RD` | register step, phase ratio ~4 (rung 3; expect FAIL at rung 2 — a correct failure) |
**Gate: catch count on the 150 at rung 2.**  The shape data says the
bounded-carrier 39 and most of the interior-wall 40 are rung-2 shapes; the
register 17 are rung 3 (`WAVE30_FINDINGS.md` §6g: phase ratio ~4, a nested
branch inside a nested branch).  **Kill criterion: fewer than ~40 of 150 catch
at rung 2 → stop, write the failure taxonomy, fall back to the wave route.**

**Stage B — the ONE Coq build: the ladder checker.**  Rules as data
(`lhs sconf, rhs sconf, count expr, fired-transition set`); one soundness
theorem by induction on ladder position, step case invoking earlier rules —
`srun_sound` one level up.  Reuse unchanged: the v5c block engine, the
QH/neverQH property derivations, `Closeout` assembly.  New trust surface: the
single `rule_sound` and the ladder-validation `vm_compute`.  Funext-only, like
everything else.  This is a big build, but it is ONE build — the alternative
it replaces is a lemma-plus-emitter session per bucket, ~10 more times.

**Stage C — mass-board.**  The emitter renders one ladder cert per Stage-A
catch; boards compile; `make closeout` regenerates; shadows fall.  From here
new catches cost prover CPU, not sessions.

**Stage D — the tail.**  Rung 3 (add `powsum` to the count language) for the
register 17 and whatever else measures exponential-inside-exponential; then
hand-reads for the genuine stragglers.  `RULE_LADDER.md` §6's honest limit
stands: a few rows may be outside every finite ladder — those are wave work,
with John's reads (38-for-38 so far) as the scarce resource they've proven
to be.

## 4. Run BESIDE the wave route, not instead of it

Wave-32's two items stay live and are deliberately disjoint from this build:

* Item (1), the bounded inner carrier (39 rows), is specced to the lemma
  statement and touches `NestedLapLift.v` + `nestcert.families` — none of the
  ladder's files.  It is ALSO the ladder's Stage-A validation set: if rung 2
  works, these 39 are its first catches, and the two routes cross-check.
* Item (2)'s cheapest move is measurement + a class-level hand-read
  (absolute-coordinate dumps, "why does the increment out of `j = 0` chain
  and out of `j = 1` not?").  That read feeds BOTH routes.

If the ladder hits its Stage-A gate, the wave route stops being the plan of
record and becomes the tail-cleanup tool.  If it misses, we have lost one
stage-A prototype and still hold both wave items.

## 5. What this is NOT

* NOT a port of `Inductive.v` — measured dead for QH
  (`MXDYS_INDUCTIVE_STAGE0.md` gate (ii) = 0, structurally).
* NOT a new cert zoo — the BBB counter families (`xd_counter`,
  `tower_counter`, …) are generic FORMATS with per-machine hand-fitted
  parameters (their `--emit` registries are hardcoded machine lists); that
  route took 19 sessions for 40 machines and is exactly what we are declining
  to repeat.
* NOT a bigger RepWL/n-gram sweep — `COUNTER_CLOSEOUT.md` §0: finitization
  itself is the bottleneck, 706/708 NOCLOSE, and a richer measure vocabulary
  cannot help.
