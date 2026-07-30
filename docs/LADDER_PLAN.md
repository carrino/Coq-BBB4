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

## 4b. Addendum (2026-07-30, later the same day): wave-32's first commit
confirms the diagnosis from the other side

`origin/claude/wave32-prompt-residue-cotlom` @ `5ffdebb` (concurrent session,
6 boards, core 150 → 146, shadows 76 → 74):

* **Two of item (1)'s three sub-buckets were emitter blindness, not missing
  mathematics.**  The entire 6-row "fill lands off the endpoint" bucket was a
  replay bug (the octave shift ignored in the inner start), and 13 of the 33
  `no inner family` rows were invisible only because `_nested_ovf` searched
  `ENCS` while the two-form reader uses `TRY` — three alphabets registered
  privately in one module that another module's search could not see.  That
  is the strongest evidence yet for §0's root cause: hand-plumbed,
  per-module search vocabularies (25 alphabets, private `ENCDATA` rows) fail
  by omission, silently, and each omission reads as a new "shape".  A ladder
  that DERIVES its rules has no curated alphabet list to be blind to.
* **The moved-not-boarded pattern, third instance.**  The 13 opened rows
  board none of themselves — they advance to `no boot chain` (9) and
  `no exit chain` (4).  Gates in series, again; per-gate grammar work keeps
  paying per-gate.
* **Stage-A instrumentation now exists.**  The commit lands exactly the
  probes a ladder searcher wants as its observation layer: `intnest.py`
  (does the interior lap carry an inner counter), `intfit.py` (per-octave-
  class affine fit), `jspeel.py`, `innerrun.py`, `innerenc.py`.  Stage A
  should consume these rather than re-derive them.

All five Stage-A rows in §3's table are still open at `5ffdebb`.  Item (1)'s
remaining lemma-shaped target shrinks from 39 rows to ~20; the bounded-carrier
lemma is still worth landing but its bucket was smaller than its label.
File-coordination note: the live wave session owns `tailcert.py` and the
`REG_*`/closeout tables; this plan's files (`docs/LADDER_PLAN.md`,
`tools/ladder/`) are disjoint by construction, and Stage A must keep it so.

## 4c. Stage-A gate zero, measured (2026-07-30, `tools/ladder/`)

The prototype exists and the discovery layer works on the real rows.  On
the dev fixture (`0RB---_0LC1RB_1LA1LD_1LC0RB`, the one counter the wave
route derives today) the miner finds and the engine PROVES exactly the
machine's three fundamental local rules — the B increment chain and both
carry drains — as context-free rules behind a wall marker, all passing
raw-simulator differential validation.  On the five pinned Stage-A rows
(20k-step traces, per-machine time cap):

| row | rules | states | invalid |
|---|---:|---|---|
| `1RB---_1RC1LB_0LB1RD_1RA0RC` (bounded carrier) | 9 | BCD | 0 |
| `1RB---_0LB1RC_0RD0RC_1LB1LD` (interior wall) | 3 | BC | 0 |
| `0RB0RD_1LC1RB_1RA0LC_1LB0LC` (two-form) | 5 | ABC | 0 |
| `1RB0LA_1LC0RD_1LA1LB_0LB1RD` (boot-blocked) | 3 | BCD | 0 |
| `1RB1RD_1LC1RA_0RB0LC_1LA0RD` (register, ~4^k) | 3 | ABC | 0 |

Compact, validated rule sets on every row — on machines where the
production irules engine discovers NOTHING (§2: zero anchors, zero rules,
zero certs at two budgets).  The rule-in-rule machinery (bulk application
of proven rules inside another rule's replay) and the single-application
subsumption check are what separate the two — both were engine bugs or
absences at some point in the build, and both are now differentially
validated.

The closure layer does NOT yet close any row, fixture included, and the
failure is exactly `RULE_LADDER.md` §3's prediction: an octave meta-cycle
is 2^k rests whose mid-octave shapes follow the bit pattern, so no
fixed-shape anchor family with an affine self-map exists.  The next
increment is the VALUE-INDEXED rule family — a counter-segment tape item
with a cview-style case split, discovered from the ladder's own carry
rules (they identify the digit alphabet mechanically: the drained block
words ARE the digits).  That is rung two proper; the local-rule layer
underneath it is built and measured.

## 4d. Rung two, measured: the value-indexed family on all 143 core rows

_All numbers below measured at commit `cf7eeab` (branch
`claude/ladder-value-family-3j1776`), 20k-step traces, 300 s hard wall cap per
machine, 3 jobs.  Raw: `tools/ladder/core150_valfam.jsonl` (one JSON
certificate candidate or failure report per row); readable table:
`tools/ladder/core150_valfam_rows.txt`; the fixture's certificate:
`tools/ladder/ladder_fixture_cert.json`.  Total 12,153 s of per-row wall
(~3.4 CPU-hours), median 26 s/row, max 309 s, **0 timeouts, 0 crashes**._

The increment is real and it is the one §4c called for: a counter-segment tape
item `CTR(alph, v)` whose increment is a RULE FAMILY over the carry index `j`,
with the alphabet read off the ladder (the words its own rules move one of per
application) and the digit VALUES pinned by requiring consecutive anchor
visits to differ by exactly +1.  On the dev fixture it closes end-to-end:

    digits 11 = 0, 10 = 1 (10 named by ladder rule r1), LSB next to the head
    boot      5 steps from blank to E(1)
    interior  1^{2+z} #          -> 1 0 1^z #             4 steps      j = 0
              10^1 1^{2+z} #     -> 1^3 0 1^z #           8 steps      j = 1
              10^2 1^{2+z} #     -> 1^5 0 1^z #          12 steps      j = 2
              10^{1+y} 1^{2+z} # -> 1^{3+2y} 0 1^z #   8+4y steps      j >= 3
                                          (ONE bulk application of r1, y free)
    overflow  10^1 / 10^2 / 10^3 -> 1^3 / 1^5 / 1^7     (k = 1,2,3, fire once)
              10^{1+y}           -> 1^{3+2y}          8+4y steps, k >= 4

254/254 digit strings covered to k=7, stable to k=9, 8 arms, liveness ABCD read
only off the five arms taken infinitely often, and the raw simulator agrees on
shapes AND exact step counts at every probe including every octave boundary.
Base = concrete replay at small `j`, step = the ladder's own rules bulk-applied:
`find_IH`/`try_ind` at the value level, as §4c predicted.

### The gate: 21 of 143.  It fires.

| outcome | rows | what it means |
|---|---:|---|
| **closed** | **21** | full certificate candidate: family, arms, boot, liveness |
| overflow leaves the family | 88 | every INTERIOR value covered; only the fill fails |
| no counter reading at any anchor | 24 | (14 no signal, 6 far side varies, 3 partial, 1 broken) |
| arm lands off the family | 7 | family + interior, arms stop at the wrong anchor |
| interior not covered | 3 | carry classes the repair never reached |

The five pinned Stage-A rows (`tools/ladder/stageA_valfam5.jsonl`) land where
§3's table says they should: the interior-wall row `1RB---_0LB1RC_0RD0RC_1LB1LD`
**closes** (base-3, two-cell digits `00`/`01`/`11`, 10 arms, 40 laps); the
bounded-carrier, boot-blocked and register rows all reach `overflow leaves the
family`; the two-form row has no counter reading at any anchor.  The register
row failing at rung two is the correct outcome §3 predicted.

**21 < ~40, so §3's kill criterion fires and this is the failure taxonomy, not
a build-out.**  What the 21 are is as informative as the number:

* 20 of the 21 come from ONE gate bucket, `no_interior_jS_j_chain_at_octave_
  parity_0` — wave-31's largest, 40 rows.  Rung two takes **half of that bucket
  in a single sweep**, on rows where `bin/irules` finds zero anchors (§2).
* 8 of the 21 are never-QH (every visited state infinitely often).  The other
  13 close with i.o. `BCD` and visited `ABCD`: the family PROVES those machines
  quasi-halt and names the witness state.  That is a real verdict, not a
  failure — `BBB4_Statement.QuasiHaltsSt` has a `Visited` conjunct, so a state
  visited once and never again is exactly a quasi-halt witness.
* 17 base-2 with one-cell digits, 4 base-3 with two-cell digits.  17 of 21 have
  their alphabet named outright by a ladder rule; 4 rest on the weaker
  provenance (digit WIDTH from a ladder word, values from a chain twice as
  long).  No terminator was needed on any of the 21; boots are all <= 17 steps.
* Every one of the 21 passes raw-simulator differential validation; 18 of 21
  also match the arms' PREDICTED STEP COUNTS exactly; all 21 confirm >= 40
  consecutive laps replayed from the blank tape.  Median 24 arms, max 31.

### Ranking the 122 misses

**(b) needs a second parameter or rung three — 88 rows, the dominant mode.**
`overflow leaves the family` is not a near miss; it is a precise diagnosis.
These rows cover a **median 98.8 %** of their digit strings — every value whose
digit string has a clear digit somewhere — and fail on exactly the all-max
strings, `v = b^k - 1`.  The interior arms are proved, the differential agrees,
and then the FILL steps out of the one-parameter family.  Two sub-cases, and
the gate labels separate them cleanly:

* **17 rows are `register_step_does_not_close`** — the Θ(4^k) double nesting.
  On `1RB1RD_1LC1RA_0RB0LC_1LA0RD` the fill turns the counter's TERMINATOR from
  `01` into `11`, i.e. the terminator is itself a digit of an outer register.
  These are rung THREE and **failing here is the correct outcome** §3 predicted.
* **71 rows are not rung three** — 32 `no_inner_family_at_pow2_j`, 18
  `no_boot_chain`, 14 `no_gap-free_two-form_family`.  Their fill leaves the
  family because the far side carries an outer parameter the family cannot
  name: on `1RB0LA_1LC0RD_1LA1LB_0LB1RD` the overflow goes to state A with a
  growing unary block.  The next increment is a **two-parameter family
  `E(p, v)`** — one CTR plus one affine outer count, with the interior arms
  unchanged (they already work) and only the fill arm crossing `p -> p+1`.
  That is rung two-and-a-half, and it is where the next 70 rows live.

**(c) engine gaps — 10 rows, plus ~10 more hiding in (a).**  7 `arm lands off
the family` and 3 `interior not covered`: a family is found and the interior
nearly covers, but an arm stops at the wrong anchor visit or a carry class was
never mined.  Separately, 10 of the 14 `no signal` rows sit in the SAME gate
bucket where 20 sisters closed — a searcher gap, not a shape gap.  Realistic
recovery from fixing these: ~15-20 rows, which would put rung two near 40 but
only reaches the gate by clearing bugs, not by new mathematics.

**(a) genuinely not a counter at this anchor — ~14 rows.**  The remainder of
the no-reading bucket: no anchor whose counter side decodes over a
ladder-named alphabet with +1 steps.  6 of them are `far side varies` — the
largest constant-far-side group at any anchor is 4 visits of 200
(`0RB0RD_1LC1RB_1RA0LC_1LB0LC`), i.e. both sides move together, which is again
a two-parameter shape rather than a non-counter.  3 more show a +1 delta on
50-90 % of visits with the rest at 3^k, a counter whose visit sequence is not a
pure odometer.

### What this says about the plan

The diagnosis in §0 survives and sharpens.  Rule discovery is NOT the
bottleneck: the ladder finds and proves local rules on every row, the value
family reads its own alphabet with no curated list (and the two rows that
needed a 3-symbol, 2-cell alphabet were found without one being written down),
and the interior of the odometer is covered on **109 of 143 rows** — 21 fully
plus 88 that cover every interior value.  The bottleneck is a **single missing
constructor**: the fill needs to move an outer parameter.  A one-parameter
`CTR(alph, v)` cannot express `E(p, v)`, and 71 rows queue behind exactly that,
with 17 more behind the rung-3 version of the same thing.

So the honest read is not "rung two failed" but "**rung two is one constructor
short, and the sweep names the constructor**".  Whether to spend the next
session on `E(p, v)` or fall back to the wave route is a scope call §3 reserves
for the gate — and the gate says stop and report, which this section does.
What Stage B should NOT do yet is design a kernel checker: the surviving cert
shape (family + arms + boot + liveness, all four present on 21 rows) would be
re-cut the moment a second parameter lands.

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
