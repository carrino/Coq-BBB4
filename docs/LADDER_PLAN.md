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

## 4e. Rung two-and-a-half, measured: 21 of 143 becomes 69 of 143

_Sweep 1 measured at commit `0153dd1` (branch
`claude/ladder-two-parameter-anchor-c0vkav`), engine at `3341a3c`; 20k-step
mining traces, 300 s hard wall cap per machine, 3 jobs, 9,127 s of per-row
wall.  Raw: `tools/ladder/core143_fill.jsonl`; readable table
`core143_fill_rows.txt`.  Every count below is printed by
`tools/ladder/rowcounts.py` from those files rather than restated here, and the
working sets are files, not prose: `work71_twoparam.txt` (the 71 non-register
overflow rows), `work24_enginegap.txt`, `work17_register.txt`,
`work21_closed.txt` (the regression set)._

§4d named a blocker: 88 rows covered a median 98.8 % of their digit strings and
failed on exactly `v = b^k − 1`, so "the fill steps out of the one-parameter
family" and the missing constructor was a second parameter.  The measurement
reproduces exactly.  The diagnosis of WHY was wrong, and how it was wrong is
the content of this section.

### The fill did not leave the family.  The model had the wrong successor.

`next_ds` hard-coded the odometer carry — the top string of width `p` goes to
`[0]*p ++ [1]`, the value `b^p`.  Nothing measured that.  It is what a binary
odometer does, and it was written down as though it were a property of the rows.

Read instead off the trace — take the anchor visits, decode each, and look at
where the successor of every top string actually is — the law is `pre ++ mid^n
++ suf` at width `p + s`, and **the hard-coded carry is 21 of the 69 rows that
close: precisely the 21 that already closed.**  Every one of the 48 new rows
closes on a law that had to be read off the machine.  Fourteen distinct laws
appear; the commonest new one widens by TWO and resets to zero.

So the constructor §4d asked for was already half-present.  The counter's own
WIDTH is the second parameter: a digit string of length `p` **is** `E(p, v)`,
the interior arms never touch `p`, and the fill is the only arm that crosses
it.  What was missing was not the ability to express `E(p, v)` but the
willingness to READ `E(p, b^p−1) → E(p', c)` instead of assuming it.  `Fill`
interpolates it from the top string's successor observed at two widths —
`find_IH` at the width level — and rejects any law that fails to reproduce
every observed fill.

### Three engine gaps, all one bug

Each was something that wanted a family MEMBER and settled for an anchor VISIT.
The head crosses the anchor cell several times per increment, so a config
matching `(state, head)` plus the far side is routinely a mid-flight tape that
decodes to nothing.

* the differential probe (fixed earlier, `cf7eeab`);
* `_replay_arm`, which stopped at the first anchor-shaped config — that IS what
  "arm lands off the family" is;
* `observe_fill`, which read the successor off the immediately following visit.
  Measured on three rows, the successor sits 2–8 visits along and every visit
  between is undecodable; of the 41 rows sweep 1 left failing only at the
  overflow, a law was fitted on 6.

Plus one guard that inverted its own meaning: the repair loop ran only `while
not fails_only_at_overflow`.  Correct while the law was hard-coded — no
specializing reaches a successor the model has wrong — and precisely wrong once
the law is read off the machine, which left rows one digit string short.

### The far side as a run template

`Fam.other` was a constant cell tuple and `anchor_shaped` demanded equality with
it; that is where the one-parameter assumption was baked in.  It is now a run
template `word^(a·p + b)`, inferred like everything else: group anchor visits by
the far side's run WORDS instead of its cells, take the coordinate that moves as
the carrier, fit the rest affinely, and reject the template if it fails to
reproduce any observed far side.  `find_families` gained a matching pass for the
case where every constant-far-side group falls under the chain threshold — which
is what the `far side varies` rows are — letting the `+1` chain cross `p` at the
top string and nowhere else.  Coverage, boot, liveness, the differential and
`chain_check` all run over `(p, v)`; the interior arms are proved once with `p`
symbolic and are unchanged in what they do to the counter.

**This layer contributed nothing measurable in sweep 1** — it landed after it
(`95af653`, `143a9d1`) and is measured by sweep 2 (`core143_two.jsonl`).  Stated
plainly because it is the layer this session was commissioned to build, and the
yield came from the fill law instead.

### The result

| working set | rows | before | after |
|---|---:|---:|---:|
| engine-gap (c) | 24 | 0 | **0** |
| two-parameter target | 71 | 0 | **32** |
| register (rung 3) | 17 | 0 | **16** |
| regression (already closed) | 21 | 21 | 21 |
| **total** | **143** | **21** | **69** |

All 69 pass raw-simulator differential validation and confirm 40 laps replayed
from the blank tape; 68 of 69 also match the arms' predicted step counts
exactly.  55 are never-QH, 14 name a quasi-halt witness state.  Median 24 arms,
median 36 s.  No row that closed before stopped closing.  3 rows spend the full
300 s cap.  §3's kill criterion (≥ ~40 of 150 at rung two) is cleared.

### Two of §4d's calls were wrong

* **The register 17 are not rung three.**  16 of 17 close.  §4d read their fill
  as "the terminator becomes a digit of an outer register" — which is exactly a
  fill target with low digits set, `E(p, b^p−1) → E(p+2, 11⟨0⟩)`, stated
  directly by the inferred law.  §3 predicted these would fail at rung two and
  called that "a correct failure"; the prediction was wrong, and the Θ(4^k)
  growth comes out of a fill that widens by two.
* **The (c) engine-gap pass recovers ZERO of its 24 rows**, against §4d's
  estimate of 15–20.  The engine bugs were real and are fixed, but they are not
  what was holding those rows.  Counting the distinct counter-side strings of
  each length at the busiest constant-far-side anchor (`tools/ladder/numsys.py`,
  no ladder and no decoding needed) gives, on twelve of them,

      length     1  2  3  4  5  6   7   8   9
      strings    1  1  2  3  5  8  13  21  34

  exactly the Fibonacci numbers to length 9 — six of the seven `arm lands off
  the family` rows and six of the fourteen `no signal` rows, including the ten
  §4d called "a searcher gap, not a shape gap" because twenty sisters in the
  same gate bucket closed.  They are not a searcher gap.  Those counters are in
  a **Fibonacci rank system**, their successor is not positional, and no base-`b`
  `CTR` decodes them however far the search is widened.  The signature appears in
  none of the other 121 rows.

Both errors have the same shape as the main one, and it is worth naming the
pattern: **a reader that assumes an arithmetic reports the machine as the thing
that failed.**  Three times now the "missing constructor" was a hard-coded
assumption about the counter's own arithmetic — the carry, the anchor, the base.

### Ranking the 74 misses

* **(a) not a base-`b` counter — 12 rows, named exactly.**  The Fibonacci-rank
  rows above.  The next constructor is a `CTR` over a rank system with `Fill`'s
  successor generalized from "carry the odometer" to "the successor in this
  system" — the same shape of fix as this section's, and the sweep names it as
  precisely as §4d named the last one.
* **(b) fill law not yet inferable — 41 rows** (`overflow leaves the family`),
  the dominant mode.  Interior fully covered, failing on a median 4.7 % of
  strings, all at the overflow.  Sweep 1 fitted a law on only 6 of them because
  `observe_fill` was looking at the wrong visit; `143a9d1` fixes that and sweep 2
  measures it.  On the two rows checked by hand the law is now inferred and the
  rows are 2 and 3 digit strings short — the residue is the fill ARM, not the
  law.
* **(c) still engine gaps — a handful.**  7 `arm lands off the family` (6 of
  them Fibonacci, so not really), 2 `interior not covered`, and 3 rows that
  spend the full 300 s cap and are cut off mid-repair rather than mid-argument.
* **(d) no counter reading at any anchor — 24 rows**, of which 6 are `far side
  varies` (the far-side template's target) and 3 show `+1` on 50–90 % of visits.

### What this says about the plan

The §0 diagnosis holds and sharpens again.  Rule discovery was never the
bottleneck and still is not.  What each round has cost is one hard-coded
assumption about the counter's arithmetic, and each has been worth 30–50 rows.

Stage B is now worth considering — but §4d's reason for deferring it has not
expired so much as changed owner.  The cert shape (family + fill law + arms +
boot + liveness) has been re-cut once this session already, and the Fibonacci
rows will re-cut `Fill` again.  The honest reading is that the cert shape is
stable in its FOUR PARTS and unstable in the arithmetic of one of them, so a
kernel checker should be designed against the parts and parameterized in the
successor — not designed now against `pre ++ mid^n ++ suf` specifically.

### Sweep 2: the far-side template is worth exactly zero, and that isolates the blocker

_Sweep 2 measured at `143a9d1` over the same 143 rows, same budget:
`tools/ladder/core143_two.jsonl`, 10,758 s of per-row wall._

It carries everything this branch built after sweep 1 — the far-side run
template, `find_families`' template pass, the repair reaching the overflow, the
forward-scanning fill observer, `drop_wrong`.  The result:

| | sweep 1 | sweep 2 |
|---|---:|---:|
| closed | 69 | **69** |
| rows gained | — | **0** |
| rows lost | — | **0** |
| far-side template fired on | — | **0 rows** |
| per-row wall | 9,127 s | 10,758 s |

**Zero delta on all 143 rows, for 18 % more wall clock**, and three rows crossed
from `arm lands off the family` to a hard timeout — they now return no diagnosis
where they used to return a wrong-anchor report.  The far-side template never
fired once: `find_families` prefers anchors with a long constant-far-side chain,
which are by construction the anchors where the far side does not move, and its
template pass only runs when every constant group falls under the chain
threshold.  The layer is built, it is inert, and nothing here credits it.

**But one component did exactly its job, and that is the useful finding.**  The
forward-scanning observer took the number of still-open overflow rows with an
inferred fill law from **6 of 41 to 27 of 41** — and not one of those 21 rows
closed.  Sweep 1 could not separate "the law is unknown" from "the law is known
and no arm realizes it"; sweep 2 separates them.  For at least 27 of the 41,
**the law is right and the fill ARM is the whole blocker**, which is why §4f's
task is arm selection and not more inference.  A null result that moves 21 rows
from one side of a diagnosis to the other is worth more than the 18 % it cost.

### Addendum: what 69 is worth against the LIVE residue

_Added after merging `origin/main` at `e955ed8`, which is 9 commits and three
boarding waves ahead of where this branch was cut._

The 69 above are 69 of the **143 core rows as they stood when the sweep ran**.
While it ran, the wave route boarded heavily — wave-33's parity-0 offset peel,
the HALFWAY nested arm, the ReachSt PAIR counters — and `tools/closeout/core_rows.txt`
is now **65 rows**.  Against that list:

| | rows |
|---|---:|
| closed by the ladder AND still in the live core | **36** |
| closed by the ladder, already boarded by the wave route | 39 |
| still in the live core, ladder does not close | 29 |

So the ladder's marginal contribution **today** is 36 of 65, not 75 of 143, and
it is 30 rows of *untrusted certificate candidates* — Stage B does not exist, so
the number of machines this branch boards is **zero** and the core count does not
move.  Both framings are true and the second is the one that matters for
scheduling: the two routes are working the same population concurrently and 39
rows of this sweep's yield were overtaken mid-measurement.

That is an argument for Stage B's priority, not against it — 30 rows the wave
route has NOT reached, found by a searcher that costs CPU rather than a session,
is exactly what §3 Stage C was for.  But it also means the honest headline for
this work is "a prover that finds 36 live candidates and a taxonomy", not
"75 of 143".

## 4f. Rung two-and-three-quarters: arm selection settled, and the counter's PHASES

_Working set: the 41 rows sweep 1 left at `overflow leaves the family`
(`tools/ladder/work41_fill.txt`, extracted from `core143_fill.jsonl`).
Baseline for them re-measured at `66ad4c2` before any change this session:
**41 of 41 still open**, so `143a9d1`'s member-stop fix moved none of them —
what it moved was the LAW, from 6 of 41 fitted in sweep 1 to 20 of 41.  All
counts below print from `tools/ladder/rowcounts.py`, `fillcost.py` and
`phases.py` over the artefacts they cite._

### The blocker was named correctly and diagnosed wrongly

§4e's reading was that the fill law is right and no arm realizes it, and that
two things were in the way: the fill arm is not built, and arm selection
shadows its own repair.  The first half is right.  The second is not what the
measurement says, and the reason the arm is not built is not a search gap.

**An arm's step count is a sum of affine `fired` expressions.**  So before
looking for the arm, measure what the machine actually charges for one fill.
`tools/ladder/fillcost.py` walks the raw machine and times the top string of
each width to the next family member:

| population | fill cost | interior |
|---|---|---|
| the 41 open rows | **39 exponential** (per-digit ratio 1.95–2.01), 2 affine | affine, all 41 |
| 8 rows sampled from the 69 CLOSED | **8 affine** (ratio 1.08–1.11, one 0.75) | affine |

The separation is exact, and it is not a near miss: a fill costing `Θ(2^p)`
against an affine interior is not an arm that a wider search finds.  No amount
of arm mining closes those rows, and sweep 1 spending 300 s on some of them was
spent against a wall.

### Except that it is a misreading, and the fourth one of the same kind

`Fam` pinned ONE terminator — the common suffix of the anchor visits sharing
the commonest far side.  `tools/ladder/phases.py` varies that and nothing else
(anchor, digits, base, far side exactly as the family read them) and asks what
the visits the one-tail family calls undecodable would read as:

* **26 of the 41 read on THREE terminators**, 5 on two, 4 on four, 6 on one;
* 23 of the 41 then read **100 % of their anchor visits**;
* and the machine laps once per terminator before widening.

On `1RB1LA_1LC0RD_1LA1LB_0LB1RD` — §3's boot-blocked Stage-A row, open since
sweep 1 — the three terminators are `101`, `001`, `01`, all 10001 anchor visits
read, and the cycle is `0 → 1 at p`, `1 → 2 at p+1`, `2 → 0 at p+1`: the width
moves twice per lap of the cycle, which is where the `p+2` of the one-terminator
reading came from.  The `Θ(2^p)` fill was two whole laps the reader could not
see.  It closes with 14 arms, exact step counts and 40 laps.

So the phase is part of the counter's state, exactly like the width, and it is
inferred rather than assumed (`fit_phases`), with three guards: a phase must
read ≥ 8 distinct visits, every phase must have a fill law that interpolates to
a single target phase, and the whole reading must be a CHAIN the model's own
successor explains (≥ 0.95 of consecutive read visits).  A family that already
reads all its own visits is left exactly as it was; a family with visits it
cannot read is re-read wherever the guards pass, whether or not it was failing,
and on the full sweep that includes eight rows which already closed (see the
gate below — they still close, with fewer arms).

**This is the fourth time the missing constructor has been a hard-coded
assumption about the counter's own arithmetic** — the carry (§4e), the anchor
(§4e), the base (§4e's Fibonacci rows), and now the terminator.  §4e's rule
holds: a reader that assumes an arithmetic reports the machine as the thing
that failed.

### Arm selection, settled

The choice §4e left open is closed in favour of **first applicable in the
listed order, with the order a linearization of pattern subsumption, most
specific first** (`order_arms`).  Three reasons, in order of weight:

1. **It is checkable from the arms as data.**  Applicability is `match_rule`
   plus `apply_rule`'s lower-bound test, both syntactic, so `covers` decides
   subsumption by interval containment per run coordinate and `order_ok`
   re-derives the ordering property from the arm list.  The Stage-B kernel
   never trusts the order it is handed and never has to decide membership.
2. **The alternative does not settle the case it was proposed for.**  `First
   applicable whose result is in the family` was the other candidate; but the
   failure it was meant to fix — an interior arm firing at an overflow — lands
   ON a family member, just the wrong one.  Membership does not separate it.
3. **It makes the repair reachable by construction.**  The old `spec_key` put
   the most general arm of a shape first, so a specialization built for a
   string the general arm gets wrong was never asked.

`cover`, `repair`, `differential` and the emitted certificate all use the one
order; `arm_selection` in the certificate JSON states it and
`arm_order_is_subsumption_linearization` carries the check.  `cover` also now
MEASURES shadowing (`shadowed_by_selection`) rather than asserting it — and the
measurement is that on the working set it is **0**: where an arm was wrong, no
later arm was right.  `drop_wrong` stays, but it is no longer the only way to
unshadow a repair.

### The cheap pass, reported separately

None of this is mathematics; all of it is where a 300 s cooperative cap stopped
being one.  `covers` is memoized per arm pair (`order_arms` is quadratic and
ran inside `cover` and once per item in `repair` — 17.7 s of a 56 s row);
`repair` recomputes the order only when the arm set grows; the raw anchor walk
is cached per (state, head) instead of re-walked 150k steps per candidate
family; `repair` checks its deadline per window and per pin rather than once
per item (measured 98.8 s against a 90 s deadline on
`1RB---_0LC1RD_1LB1RC_1LB0RD`, the row §4e reports as hard-timing-out);
`_replay_arm` and `prune` take deadlines at all; and fallback candidates do not
START past 70 % of the cap, with the certificate recording how many were
skipped.

| row | before | after |
|---|---:|---:|
| `1RB0LD_1RC1RA_1LA1RA_0RB1LD` | 56.1 s | 26.2 s |
| `1RB0LC_1LC0RD_0RA1LB_0LC1RD` | 308.7 s | 73.7 s |
| `1RB0LD_0LC1RA_0LA1LA_0RB1LD` | 302.9 s | 79.7 s |
| the dev row `1RB1LA_1LC0RD_1LA1LB_0LB1RD` | 58.0 s | 29.2 s |

### The result on the working set

| the 41 | before | after |
|---|---:|---:|
| closed | 0 | **18** |
| `overflow leaves the family` | 41 | 23 |

All 18 pass raw-simulator differential validation, **all 18 match the arms'
predicted step counts exactly**, all 18 confirm 40 laps replayed from blank,
all 18 are never-QH, and all 18 cover EVERY digit string rather than only the
reachable ones.  Median 19 arms, median 33 s, max 275 s — no row hit the cap.
Every one of the 18 was closed by the phase pass (2 phases on 4 rows, 3 on 11,
4 on 3); none of them closes without it.  `arm_order_is_subsumption_linearization`
holds on all 18 and `shadowed_by_selection` is 0 on all 18.

The cycles read like counters, which is the point — e.g.
`1RB0LD_1RC1RA_1LA1LC_0RA1LD`: `0→3 p+0`, `3→2 p+0`, `2→1 p+2`, `1→0 p+0`,
four terminators and the width moving once per cycle.

### Ranking the 23 that are still open

Every one of them fails at the OVERFLOW and nowhere else — the interior is
covered on all 23 — and the split is by what the terminators do
(`tools/ladder/work41_after.jsonl`, the `terminators_by_phase` of the best
candidate):

* **(a) the terminator is `word^m` — 8 rows, and 6 of them are ONE digit
  string short.**  Their phases come out as `[]`, `01`, `0101`: not a cycle of
  distinct terminators but one terminator GROWING, `tail = (01)^m`.  The
  reading is right as far as it goes and then the last phase's fill wants
  `(01)^(m+1)`, a phase a finite set does not have.  Measured directly on
  `1RB0LC_1LC0RD_0RA1LB_0LC1RD`: the anchor-visit gap at the last phase's fill
  is 4 at width 2 and 16 at width 4 — still exponential, because that fill is
  the register's own increment.  **This is the register, and it is the same
  move `fit_far` already makes for the far side**: a terminator as a run
  TEMPLATE `word^(a·m + b)` with its own law, `m` a third parameter beside the
  width and the phase, the arms generalizing over a sample of `m` exactly as
  they now do over `p`.  §4d called these Θ(4^k) and put them at rung three;
  the measurement says the constructor is one more template, not one more rung.
* **(b) the phase pass found nothing — 6 rows, 1 to 5 strings short.**  One
  terminator, and no second terminator reads ≥ 8 of the visits it cannot read.
  `1RB---_1LC1RD_0LB1RD_1LB0RD` is the clean case: 100 % of anchor visits read
  on one phase and the fill still costs `Θ(2^p)` (ratio 1.98).  Nothing here is
  a misreading; these look like genuine nested fills.
* **(c) a phase cycle that does not close — 9 rows, 4 to 5 strings short.**
  Three or four terminators are found, the chain holds, and several of the
  phases' fills still want a phase outside the set — the same shape as (a) with
  a less obvious word.

### The gate

**87 of 143, against the ~100 the session's gate set.  The gate fires, so this
section is the taxonomy and the constructor stops here.**  Measured on the full
143 at `d4bbdd9` (`tools/ladder/core143_ph.jsonl`, table `sweep143_ph.log`,
8,763 s of per-row wall, median 33 s, max 301 s, **0 hard timeouts and 0
crashes**), printed by `rowcounts.py`:

| working set | rows | sweep 1 | now |
|---|---:|---:|---:|
| engine-gap (c) | 24 | 0 | 0 |
| two-parameter target | 71 | 32 | **50** |
| register (rung 3) | 17 | 16 | 16 |
| regression (already closed) | 21 | 21 | 21 |
| **total** | **143** | **69** | **87** |

All 87 pass the differential, 86 of 87 match predicted step counts exactly, all
87 confirm 40 laps from blank, all 87 cover every digit string, and **no row
that closed before stopped closing** — the only transitions are 18 rows from
`overflow leaves the family` to `closed`.  73 are never-QH, 14 name a
quasi-halt witness.  `arm_order_is_subsumption_linearization` holds on 87 of 87
and `shadowed_by_selection` is 0 on 87 of 87.

26 of the 87 read on more than one terminator (12 on two, 11 on three, 3 on
four).  Eight of those 26 already closed at sweep 1 on ONE terminator and now
read as multi-phase: the guards let the pass fire wherever it improves the
reading, not only where the old reading failed, and those eight still pass the
differential and the lap check — with FEWER arms (median 15 against 32 for the
single-phase rows), because a phase absorbs case splits the arms were carrying.

The one cost, and it is the cheap pass's not the constructor's: three rows that
sweep 1 reported as `arm lands off the family` now spend the whole cap and
report `time cap` instead of a per-candidate diagnosis
(`1RB---_0LC1RD_1LB1RC_1LB0RD`, `1RB---_1LC0RB_0LD1RB_1LC1RD`,
`1RB---_1LC1RB_0LB1RD_1LC0RD`).  The first of them is the row §4e records as
HARD-timing-out; it now returns inside the subprocess timeout, which is the
half of that complaint the budget work was aimed at.  The other half — the
phase pass costs one raw walk and one fit per candidate family, and these rows
have many candidates — is unfinished, and it is a budget item, not a
mathematical one.  What it bought is
not only the 18: it is that the residue is now 23 rows all failing at one
place, with 8 of them naming their own next constructor, and a per-row
measurement (`fillcost.py`, `phases.py`) that says in advance whether a row's
fill can be an arm at all.  That measurement did not exist before this session,
and it is what stops the next round spending 300 s per row against a wall.

### What this says about Stage B

§4e's position was that the certificate shape is stable in its four parts and
unstable in the arithmetic of one, so the kernel should be designed against the
parts and parameterized in the successor.  This session is evidence for that
and against waiting any longer:

* the successor moved AGAIN — one terminator became a cycle of them, and the
  residue says it next becomes `word^m` — so freezing `pre ++ mid^n ++ suf`
  would have been wrong for the third time running;
* but the four parts did not move at all.  Family, fill law, arms, boot,
  liveness: the phase went in as another coordinate of the family's state and
  every part kept its shape;
* and **the one part §4e listed as open is now closed**.  Arm selection is
  decided, and decided in the form Stage B needs: a case split the checker
  re-derives from the arms as data (`order_ok`), with no membership decision
  inside the kernel and no reliance on the order the search happened to emit.

So the Stage-B kernel can now be specified: rules as data, one soundness
theorem by induction on ladder position, a case split that is
first-applicable-in-a-subsumption-order, and the successor as a PARAMETER of
the family rather than a fixed law.  The next constructor (the terminator
template) is a change to that parameter, not to the kernel — which is the test
§4e asked for and the first time the answer has been yes.

## 4g. The counter's CODE and its step, read not assumed

_Merged from `claude/ladder-two-parameter-anchor-c0vkav`, which ran beside §4f
on the same files.  The two are complementary and were measured separately
before the merge: §4f's phase pass closes 87 of 143 at `0246b0c`, this layer
closes 75 of 143 at `66db337`, the union of the two closed sets is 93, and the
six rows this layer adds are exactly the six §4f does not reach.  The merged
number is measured below._

John read `1RB0RB_0LC0LD_1LC1LD_1RA0RA` off the tape: *"a wall and msb on the
left; when the wall moves over the high bit is set, then it counts up to full,
then back down to 0, then the wall moves over again."*  That is the **reflected
binary (Gray) code**, and "up to full then back down" is the reflection itself.
Decoding the left side as Gray gives 300 consecutive `+2` steps out of 300
anchor visits; read positionally the same tape gives 24, 27, 30, 29, 20, 23,
18, 17, which is why the search reported "+1 on 26 % of visits" and filed the
machine under *no counter reading at any anchor*.

Two more assumptions, the same shape as the fill law's in §4e and the phase's
in §4f, both now inferred rather than hard-coded:

* **the CODE.**  `Fam.value` read the digit string positionally, full stop.  It
  now reads `binary` or `gray`, positional first.  The codec is the general
  base-`b` reflected code — running sum down to decode, difference to the next
  digit up to encode — which collapses to the XOR chain at `b = 2`.  `next_ds`
  is stated on the VALUE rather than as a digit-wise carry ripple so it is
  right for either code, and the top of an octave is tested by value rather
  than by "all digits max", which for a reflected code is not the top at all.
* **the STEP.**  `_try_parse` required consecutive anchor visits to differ by
  exactly `+1`.  A machine whose lowest cell is a phase bit crosses the anchor
  once per TWO counter steps.  A step other than 1 means only part of each
  width is a member, so those families are checked against the states reachable
  from the boot rather than against every digit string.

One bug fell out of the first: `repair` rebuilt the failing digit string from
`(k, v)` by positional decomposition, which is the wrong string for any family
whose code is not positional.  It goes through `of_value` now, and that single
fix is what took the Gray rows from "family found, interior 65 % covered" to
closed.

The rows this adds, all `gray` with step 2, all previously *no counter reading
at any anchor*, all with the differential agreeing on shapes AND exact step
counts and 40 laps confirmed from the blank tape:

    1RB0RB_0LC0LD_1LC1LD_1RA0RA   C1/L   1RB0RD_1LC0LB_1LD0LB_1RD0RA
    1RB0RB_0RC1RC_0LD1LA_1LD0LA   C0/L   1RB0RD_1LC0LC_1LD0LB_1RD0RA
    1RB1LC_0LA0RB_0LD1LD_1RA0RA   A0/L   1RB1LD_1RC0RC_1LA0LA_0RA0LD

Four of the six are in the `no interior j=S j' chain at octave parity 0`
bucket, which that layer alone takes 21 → 25 of 40; two are outside it.  That
bucket names how forty machines failed ONE test — positional base-`b`, `+1` per
anchor visit — and it is at least four things: now-closed rows, Fibonacci-rank
counters (exactly F(n) distinct counter words per length, `numsys.py`),
wall-clock timeouts, and engine gaps.  **A label that records how a search
failed keeps being mistaken for a property of the machines.**  §4d made that
error twice, §4e once more, and it is the same error each time: an assumption
about the counter's own arithmetic, reported as the machine's failure.

Credit where it is due: the Gray reading came from John's read of the tape, not
from the searcher.

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
