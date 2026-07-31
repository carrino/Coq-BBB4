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

## 4h. Stage B, built: the kernel, and what it does and does not yet close

_Three boards at `2dfb26c`, kernel at `fca3334`, emitter and first board at
`48e53b9`.  Coq 8.18.0.  Every number below is a file that compiles or a
count printed by `tools/ladder/emit_ladder.py`._

### First, two corrections to the numbers this session was handed

* **`tools/ladder/core143_merged.jsonl` is 4 rows, 0 closed.**  That sweep is
  still in flight (`7f5b0fd`, "merged-code 143 sweep in flight"); its log
  stops at row 4.  The ~93 figure is the UNION of two separately measured
  files -- `core143_ph.jsonl` closes 87 of 143, the Gray layer closes 75, and
  4g records the union as 93 -- not a merged number anyone has measured.  The
  merged sweep is still worth finishing; it is just not evidence yet.
* **`tools/ladder/ladder_fixture_cert.json` is stale.**  It predates 4f and
  4g: 8 arms, and no `code`, `phases` or `value_step_per_anchor_visit`
  fields at all.  Re-certifying the dev row at this commit gives **13 arms**.
  The boards below are all built from freshly emitted certificates.

### What was built

Two kernel files, and nothing in `theories/Census/`:

* **`theories/Checkers/LadderFam.v`** -- the four things 4f and 4g say the
  certificate carries, as a record: the fill law per phase with the phase it
  lands in, the terminator of each phase, the CODE (positional or reflected,
  with the general base-`b` codec and its round-trip proved), and the value
  STEP per anchor visit.  `fam_succ` is computed from them.
* **`theories/Checkers/LadderKernel.v`** -- rules as data over
  `LapDecider.sconf`, and `rule_sound`: ONE theorem, by induction on ladder
  POSITION, whose step case invokes the rules earlier in the list.  The base
  steps are the reused engine's `sstep`/`sstep_sound`; the single new step
  constructor is `RU i`, "apply ladder rule `i`".

Reused unchanged, as 3 said: the block engine, `LapDecider`, `WTape`,
`CTape`.  New trust surface: `rule_sound` plus the `vm_compute` that runs
`check_ladder`/`check_arm`.

### The gate: the dev fixture boards, and so do the other two

| row | code | step | phases | fills | arms | ladder | compiles |
|---|---|---:|---:|---:|---|---|---|
| `0RB---_0LC1RB_1LA1LD_1LC0RB` | binary | 1 | 1 | 1 | **13/13** | 4/4 | yes |
| `1RB0RB_0LC0LD_1LC1LD_1RA0RA` | **gray** | **2** | 1 | 1 | **49/49** | 2/2 | yes |
| `1RB0RC_1LC1RA_1RD1LB_0LC0RD` | binary | 1 | **2** | **2** | **12/12** | 2/2 | yes |

**No kernel file changed between the three.**  The whole difference is inside
the `Fam` record, and it is worth printing because it is the claim itself:

    Binary 1 [mkFill 1 [] 0 [1] 0]                    the dev fixture
    Gray   2 [mkFill 1 [] 0 [1;1] 0]                  the Gray row
    Binary 1 [mkFill 1 [] 0 [] 1; mkFill 0 [] 0 [] 0] the phase cycle

The last line is 4f's phase cycle as data: phase 0 widens by one and lands in
phase 1, phase 1 widens by NOTHING and lands back in phase 0.  **That is the
test 4e asked for, and it passes.**

`Print Assumptions` on the arm-soundness lemmas is *Closed under the global
context* -- **zero axioms**, not even funext, because the arm statements are
on `csteps`/`cden` and never go through `lift`.

### Two normalisations the emitter needed, both recorded in the code

* the certificate prints its right-hand side with trailing blanks stripped,
  so the search matches up to `lift` and the kernel is handed the EXACT
  configuration the chain reaches.  Composition needs that: a rule whose
  target is only right up to blanks cannot be the source of the next one.
* the guaranteed copies of a repeated block are materialised into `pre`
  (`rep u (a*j+b) = rep u b ++ rep u (a*j)`).  Without it the two arms that
  must see the END of the counter -- the fill, and the string just after it
  -- have **no chain at all**, because a symbolic block count cannot have one
  copy peeled off its front.  With it the fill arm is
  `(10)^(j+1) -> (11)^(j+1) ++ 10` in exactly `4j+8` steps.

A third was needed only for Gray: an arm may print a run count as `-2 + y0`
under `y0 >= 2`, and `sside` counts are `nat`, so the arm's variable is
re-indexed to its own lower bound.  That is a representation fix in the
emitter, not a kernel change, and it took Gray from 48/49 to 49/49.

### What does NOT yet close, stated exactly

The boards prove every RULE the certificates carry.  They do not yet prove a
MACHINE-level theorem: the closure from the arms to `NonHalt` and
`NeverQuasiHaltsSt` is not built.  Three things are missing, and only the
first is real mathematics.

* **(a) The coverage reduction, and it is the one place where "the successor
  is a parameter" is not free.**  The prover checks coverage by ENUMERATING
  every digit string up to `kmax = 9`; a kernel cannot enumerate.  The
  reduction to a finite case split is a list decomposition -- every digit
  string is `t^n ++ d :: rest` with `d <> t`, or `t^k` -- which is generic and
  cheap.  What is not generic is the SUCCESSOR of each class.  `fam_next` is
  stated on the VALUE, which is exactly what makes it right for Gray and for
  step 2 (4g), and the arms are patterns on CELLS with one symbolic run
  length; bridging the two needs, per family, a lemma of the form "the class
  `t^n ++ d :: rest` has successor `0^n ++ (d+1) :: rest`".  For positional
  base-`b` step-1 that is elementary arithmetic on `val_pos`.  For a
  reflected code, and for step 2, it is a DIFFERENT lemma.  So the successor
  being a parameter buys a kernel that does not change; it does not buy the
  class law for free.  **This is one lemma per (code, step) pair -- per
  parameter VALUE, not per machine, and not per row** -- which is still the
  right side of the trade 3 was making, but it should be written down rather
  than discovered later.
* **(b) Liveness has a cheap route on these rows and it should be taken.**
  `arms_infinitely_often` is a MEASUREMENT in the certificate ("an arm still
  claiming digit strings at the widest width covered"), not a theorem.  For
  the FILL arm it is provable outright: the value strictly increases by
  `fm_step` within a width and is bounded by `b^k - 1`, so the top of every
  width is reached and the fill fires there, and the width grows without
  bound.  On the dev fixture the fill arm alone fires `A0 B0 B1 C0 C1 D0` --
  **all four states** -- so the fixture's liveness needs no interior arm at
  all.  `LapGlue.glue_neverqh` then consumes it unchanged.
* **(c) `RU` is so far unexercised by any arm.**  All three rows' arms derive
  with base steps only (`SWin`/`SWinL`/`SCycL`/`SCycR`/`SRot`/`SFold`), so the
  ladder is one level deep in practice.  The position induction is real and
  is exercised -- 4 window rules validate on the dev row, 2 on each of the
  others -- but no arm yet invokes one.  `SCycL`/`SCycR` are still
  primitives, which is RULE_LADDER 5.4 undone; that is a simplification, not
  a gap, and it costs nothing until a row needs a rung-1 rule the engine has
  no primitive for.

### What this says about the next session

The order 4f implies still holds, with (a) sharpened: build the closure --
(b) first, because it is short and it is what turns a pile of rule theorems
into a boarded machine; then (a) for positional step-1, which covers the dev
fixture and the bulk of the sweep; then (a) for `(gray, 2)`, which covers the
six rows 4g adds.  **Only after a row is boarded end to end should the
Fibonacci-rank constructor land** -- the reason 4d gave for deferring Stage B
is now the reason to finish it, and the evidence above is that a new
constructor is a new `Fam` field and 49 arms that still compile.

## 4i. The gate, answered: the class law's shape, and the first boarded machine

_Kernel at `b8797cf`, the row at `fa6f759`.  Coq 8.18.0.  Every number below
is a file that compiles or a count a script printed._

### The one thing that moved a number

`1RB1LC_0LC0RB_1LA1LD_1RC0LD` is boarded end to end:
`nqh_1RB1LC_0LC0RB_1LA1LD_1RC0LD : NeverQuasiHaltsSt tm`, axiom footprint
`functional_extensionality_dep` only.  `tools/closeout/audit.py` reports

    settled by a board   5073 -> 5074
    core undecided         62 -> 61

`inventory.py` needed no change: it already scans `theories/Machines/**/*.v`
for `Theorem _ : NeverQuasiHaltsSt _`, and a ladder board is one more file
with one more such theorem.  The gate's second clause did not fire.

**Re-certifying at HEAD was not optional.**  The row has **12 arms**, not the
7 the session was handed and not the 8 the stored fixture claims.  4h said the
stored cert was stale by two sections; it is stale by three now.

### Verified to the end

The full tree builds clean and `make closeout` runs in full: 51 `CB_*.vo`,
`Closeout.vo`, and

    closeout_partial : forall tm, Deferred D_census tm ->
                       boarded tm \/ skipped D_remaining tm

with `D_remaining` at **59** rows, axiom footprint funext, and
`census_cache.py --check` MATCH.  The 62 -> 59 is the kernel's number, not
only the audit's.

### The gate: yes, with exactly one widening -- and it is not the one expected

The question was whether the class-successor lemma can be stated so that
`(gray, 2)` is a second INSTANCE rather than a rewrite.  It can, and the
interface is

    Record Class := mkCls { cs_u; cs_t; cs_w;  cs_u'; cs_t'; cs_w' }
    ClassSucc F P c :=
      forall n rest ph, <digits in range> -> P (cls_lhs c n rest) ->
        fam_next F (cs_u  ++ cs_t ^n  ++ cs_w  ++ rest) ph
        = Some     (cs_u' ++ cs_t'^n  ++ cs_w' ++ rest)

**The record's shape did not have to widen at all**, and that is the result
worth having: the class shape IS the engine's `sside` shape --
`s_pre ++ rep u (a*j+b) ++ s_post ++ X` -- which is why an arm proved for an
arbitrary tail covers a whole class at once, and why the bridge between
"patterns on cells" and "a successor on the value" is one rewrite
(`flat_map_repeat`) rather than a translation layer.

Measured on `1RB0RB_0LC0LD_1LC1LD_1RA0RA`'s family (`Gray`, step 2, base 2),
by transcribing `LadderFam.v`'s `fam_next` into Python and enumerating:

| | classes needed | interior strings covered, widths 3..12 |
|---|---:|---:|
| parities mixed | -- | the classes CONTRADICT each other |
| parity fixed | **4** | **4082 / 4082** |

and the four are, verbatim, instances of the record above:

    [0;0] ++ 0^n ++ []      ->  [1;1] ++ 0^n ++ []
    [0;1] ++ 1^n ++ []      ->  [1;0] ++ 1^n ++ []
    [1]   ++ 0^n ++ [1;0]   ->  [0]   ++ 0^n ++ [1;1]
    [1]   ++ 0^n ++ [1;1]   ->  [0]   ++ 0^n ++ [1;0]

against `(binary, 1)`'s, which are the same record with `cs_u` empty:

    []    ++ (b-1)^n ++ [d] ->  []    ++ 0^n ++ [d+1]     for each d < b-1

**What did have to widen is the PREMISE, and the reason is 4g's.**  A step
other than 1 means only part of each width is a member, and for `(gray, 2)`
the discriminator is the parity of the whole digit string -- which is the
value's low bit, and `+2` preserves it.  That is GLOBAL: it is not a pattern
on any bounded window, so it cannot be pushed into `cs_u`/`cs_w`.  Hence the
predicate `P` in `ClassSucc`.  `(binary, 1)` instantiates it at
`fun _ => True` and never mentions it again.

So the honest statement of the trade 3 was making: **one lemma per (code,
step) pair, plus one membership invariant per pair, and the invariant is the
part that was not anticipated.**  It is still per parameter VALUE and not per
machine -- the six rows 4g adds share one parity invariant between them.

### What the closure is, in three pieces

* **Liveness.**  `glue_neverqhN` is `LapGlue.glue_neverqh` with the same
  proof and a weaker `Hvis`: not "every state from every anchor" but "for
  every `N`, some anchor past `N` reaches `q`".  Indexed by `nat` rather than
  `positive`, because the premise has to compare an anchor index with `N`.
  `tops_cofinal` discharges it from the FILL arm exactly as 4h(b) predicted:
  within a width the value rises by `fm_step` and is bounded by `b^k - 1`
  (`fam_next_wf`), so the measure `b^k - value` strictly decreases, every
  width tops out, and the fill widens.  The certificate's
  `arms_infinitely_often` MEASUREMENT is now a theorem.

  One correction to 4h(b)'s reading, and it is about the fixture, not the
  claim: on THIS row the fill arm's chain has no PREFIX landing in state D --
  `D` is inside a `SWinL 13` macro step.  It costs nothing, because
  `vis_of_run` wants a chain from the anchor and not a prefix of the arm's:
  `[SWin 2; SCycL 2 0; SWin 1; SWinL 1]` reaches `D` from the same
  configuration.  No interior arm was needed, which is what 4h(b) actually
  claimed.

* **Coverage.**  Generic half: `digs_decomp` (every string is `t^n ++ d :: rest`
  with `d <> t`, or `t^k`) and `fam_cells_class`.  Non-generic half:
  `ClassSucc` and `pos1_class_succ`.

* **Selection.**  4f settled it so the kernel "never trusts the order it is
  handed and never has to decide membership".  Under a PROVED case split
  there is no order left to trust: the two classes are disjoint because
  `digs_decomp` says so, not because an ordering check said so.  `sel` is
  therefore a lookup in the arm list as data, and `covers`/`order_ok` are not
  built.  **That is a real reduction in the trust surface, not a shortcut
  taken** -- but it means the subsumption linearization is load-bearing only
  for the SEARCH, and 4f's argument for it as a kernel obligation does not
  survive contact with a proved split.

### The certificate's arms are not the closure's arms

This is the finding that cost the most and generalises the furthest.  The
prover's 12 arms are multi-variable patterns; `sside` carries ONE symbolic
run, so the emitter boards each with every run length but one pinned to its
lower bound.  Each boarded arm keeps one free run length, so each still
covers infinitely many strings -- but **with the others pinned there is no
argument that the twelve TOGETHER reach every string of every width**, and
the only coverage claim behind them is the prover's enumeration to
`kmax = 9`.  A kernel handed those arms has nothing to do but enumerate
alongside it.

So the emitter now BUILDS the class arms from the `Fam` record instead:

| | arms | coverage argument |
|---|---:|---|
| the certificate's, as boarded | 12 | none: an enumeration to `kmax = 9` |
| the closure's, built from `Fam` | **2** | `digs_decomp`: every string, every width |

one interior arm per digit below the top and one fill arm.  For base 2 that
is `1 + 1`.  Both derive with the existing chain search and both land on the
exact configuration, so `check_arm` validates them unchanged.

4h's second normalisation still earns its keep and is now checked rather than
recalled: the fill arm's guaranteed block copy MUST be materialised into
`s_pre`.  The canonical `rep u (1*j+1)` form finds **no chain at all**; the
`u ++ rep u j` form finds one in six steps.

`RU` is still unexercised -- both class arms derive with base steps only, so
the ladder remains one level deep in practice.  4h(c) is unchanged.

### The live core, swept, and where the other rows actually stop

All 61 remaining core rows re-certified at HEAD (`valfam --kmax 9 --cap 150`).
The breakdown is not the one this session was handed, and the difference is
worth recording:

| | rows | |
|---|---:|---|
| no value family PROBED AT ALL | **15** | worth a human read; see below |
| families found, none closed | 12 | mechanical: coverage or differential |
| closed, quasihalts (`live = BCD`) | 11 | needs the QH-witness closer |
| closed, `live = ABCD`, binary/step-1/one-phase | **10** | this session's target |
| closed, `live = ABCD`, gray | 6 | needs the `(gray, 2)` `ClassSucc` |
| time cap | 4 | |
| closed, `live = ABCD`, two phases | 3 | needs the phase cycle in `Inv` |

The first two lines are DIFFERENT failures and an earlier draft of this
table collapsed them into one number, which is the same mistake 4g names.
"Families found, none closed" means the searcher probed 19 to 74 candidate
families and they failed on coverage or on the differential -- mechanical,
and diagnosable without a human.  "No value family probed at all" means it
probed **zero**: no anchor's counter side decoded over ladder-named digits
with +1 steps.  That is not a statement about the machine, it is a statement
about the number system the searcher tried, and it is the bucket the six
Gray rows sat in until someone read one off the tape.  The fifteen are
listed with their tapes in `tools/ladder/core15_unread.txt`
(`tools/ladder/tapes.py`, which reproduces 4g's reading -- at C1
`1RB0RB_0LC0LD_1LC1LD_1RA0RA` reads 0, 2, 4, 6, 8, 10 as Gray).

and of the ten, **two board** and eight stop at ONE place, which was not on
anyone's list:

**The carry ripple's step count is not affine in the run length.**  `LRule`
carries `ca*j + cb`.  Measured, walking the run from `t^n ++ d` to
`0^n ++ (d+1)` for n = 1..10:

    boarded rows (digit word 2 cells)   4n+4, 4n+8, 6n+6        affine
    4 rows       (digit word 1 cell)    8,6,16,10,24,14,...     TWO affine laws,
                                        4,12,8,20,12,28,...     one per parity of n
    2 rows       (digit word 1 cell)    6,12,20,30,42,56,...    (n+1)(n+2), quadratic
    2 rows                              no chain at any n       not yet diagnosed

The three rows that board all have TWO-cell digit words; every row that stops
here has a one-cell word.  That is not a coincidence: with a one-cell digit
the head's parity across the run is part of the state, so the cost either
alternates or accumulates.

`cls_side` now carries a STRIDE for exactly this reason -- the class is
`t^(r + s*m) ++ w ++ rest`, one arm per residue, each affine in `m` -- and
the emitter tries `s = 1, 2, 3, 4`.  It is not enough for the four
parity rows: at `s = 2` the odd residue derives (`4m+4`, as predicted) and
the even one does not, because its arm needs a guaranteed block copy
materialised into `s_pre` the way the fill arm's does, and then `m = 0` is
no longer covered by it.  **So the next widening is known and small: the
interior arm needs the same [m1] offset the fill arm already has, plus a
separate arm for the residue's own `m = 0`.**  Four rows.

The two quadratic rows are a different matter and they are `RULE_LADDER` 5's
table row, not a gap in the emitter: no stride and no offset makes
`(n+1)(n+2)` affine.  They want either `RU` (derive the class arm by
induction on the run, which is what the ladder is FOR and what 4h(c) records
as still unexercised) or a count language with a product in it.

### What this says about the next session

The order 4h implies still holds, and the two next items are now cheaper than
4h estimated because the interface exists and is measured:

* `(gray, 2)`: four `ClassSucc` instances and one parity invariant, the four
  classes already known (above).  The kernel does not change.
* the remaining binary/step-1 never-QH rows: the emitter builds their class
  arms already; what is not yet known is how many of the live core's 16
  candidates have a fill law that is a pure widening, which is the one
  condition `emit_ladder.py` refuses on.

The quasi-halt-witness closer is still untouched, and it is the bigger prize
on the live core: 11 of the 62 are binary/step-1 rows whose liveness reads
`BCD` rather than `ABCD`, and `board_neverqh` proves the wrong theorem for
them by construction.

## 4j. John reads a bouncer, and the outer parameter turns out to be carried everywhere and used nowhere

_John, on `0RB0RD_1LC1RB_1RA0LC_1LB0LC` from the fifteen: "that's a bouncer
counter."  Measured below; the reading holds._

### The reading, quantified

The head bounces, drifting left.  At each lap where it reaches a NEW leftmost
cell, take the tape to its right.  On every SECOND such lap:

    lap k:   0^(2k+5)  followed by a binary counter reading  4k+3

    k=0   0^5   1^2                 =  3
    k=1   0^7   1^3                 =  7
    k=2   0^9   1^2 0 1             = 11
    k=3   0^11  1^4                 = 15
    k=4   0^13  1^2 0^2 1           = 19
    k=5   0^15  1^3 0 1             = 23        ... exactly, to k = 11

Binary, LSB nearest the counter's own low end -- the SAME convention the
certificates already use.  `0RB0RD_1LC1RB_1RA0LC_1LD0LC` is identical.  So
the reading is worth at least two rows, and it is a counter by any standard
the ladder already applies.

### Why the searcher probed ZERO families, exactly

Two places, and they are the same assumption on both sides of the trust
boundary:

* **The prover.**  `valfam.py` `Fam.read()`:
  `if tuple(base[:len(self.pre)]) != self.pre: return None`.  The near-head
  prefix is a FIXED tuple, matched exactly.  Here it is `0^(2k+5)` -- it
  grows with the lap -- so `read()` returns `None` for every candidate at
  every anchor, so `n_families = 0`, so the row is filed under *no anchor
  whose counter side decodes*.
* **The kernel.**  `LadderFam.fam_cfg` is
  `let '(ds, _, ph) := s in ...`.  That `_` is the OUTER PARAMETER.  It is
  carried through `fam_succ`, it is a field of `CtrSt`, the certificate
  reports an `outer_p_law` and a `fill_moves_outer_p` for it, and there is a
  merged branch named for it (`claude/ladder-two-parameter-anchor`, 4d) --
  **and it does not appear in the denotation at all.**

So the outer parameter is carried everywhere and used nowhere, and a machine
whose near-head prefix grows with it cannot be seen by either half.

### The fix is a shape both halves already have

The near-head prefix wants to be `s_pre ++ rep u (a*p + b)` instead of a
fixed word -- which is exactly `sside`, the engine's own side shape, the one
4i notes the class decomposition already coincides with.  `fm_pre : list Sym`
becomes a prefix plus a repeated block whose count is affine in `p`.

**This is 4g's lesson for the fifth time.**  The carry, the anchor, the base,
the terminator, the code: each was a hard-coded assumption about the
counter's own arithmetic, each was reported as the machine's failure, and
each became a parameter.  The near-head prefix is the sixth, and unlike the
others it is not even new work on the kernel side -- the field is already
there.

### The probe, widened from the two reads, and what it does and does not say

John confirmed the second row independently; it measures identical to the
first.  `tools/ladder/bounce.py` generalises both, and drops exactly the
assumption `valfam` bakes in -- nothing else.  It searches every

    frontier (west / east)  x  side of the head (left / right)
    x  spacer symbol  x  digit WORD WIDTH 1..3  x  stride 1..4 and offset
    x  alphabet ordering  x  binary / gray  x  LSB-first / MSB-first

for: spacer length affine in the lap index AND value affine in it with a
positive step.  It carries `--selftest`, which re-finds both of John's rows,
and it earned that: **two earlier versions of this probe missed them both.**
The first interleaved the two frontiers into one lap stream, which scrambles
the stride.  The second built the digit alphabet per lap, and a value of
`1^2` has only one distinct word, so the lap was skipped.  Neither bug is
visible without a known-positive case to test against, and both would have
been reported as "the other thirteen are not bouncers".

Run on all fifteen it matches **two: John's**.  The other thirteen do not
have a counter of this shape at a frontier.

**That is still a statement about the probe**, and the record says so
plainly: `valfam` had a wider search than this one along every axis except
the fixed prefix, and it was wrong about six Gray rows.  What can be said is
narrower and worth saying: the thirteen are not blocked by the near-head
spacer alone.  Whatever they are, fixing the outer parameter will not reach
them, and one more human read is worth more than another axis on the probe.

### Cross-check: PR #90 read the same fifteen, on a different axis

`docs/LADDER_NOFAM.md` (merged from `claude/fifteen-nofam-measurement-iuw18b`,
which ran beside this session on the same fifteen rows) reports **13 of 15**
with a monotone reading.  `bounce.py` here found **2**.  The two are not in
conflict and the difference is the axis each held fixed:

* this section varied the ANCHOR and the SPACER -- frontier, side, growing
  near-head prefix -- and kept the numeration at base-`b`/gray;
* #90 varied the NUMERATION -- Fibonacci weights, redundant base over cell
  pairs, binomial, unary -- and kept the anchor at a (state, head) pair.

Each found what its own axis could see.  Together: `no value family` is one
label over at least two unrelated failures, and neither probe alone
establishes anything about the rows the other one found.

**On John's two bouncer rows the two readings differ, and #90's is cheaper.**
This section reads them at the west frontier with a spacer `0^(2k+5)`, which
needs the outer parameter.  #90 reads them at `D0/R` and `A1/R` with a
terminator SET (`tl=*`, which is 4f's phases) and base 2 -- 16 of 20 and 15
of 20 width classes exact, gap 1.  If #90's reading holds, those two rows
want the phase cycle, which three other live-core rows already want, and not
the outer parameter at all.  **That should be checked before 4j's fix is
built**: 4j's cost estimate assumed the spacer was the only way in.

And the largest single group in #90's table is **six rows on Fibonacci
weights** -- the constructor 4d deferred and every brief since has ruled out
of scope.  It is now measured, and it is the biggest numeration bucket in the
live core.

## 4k. The glue was never the bottleneck.  The ARMS are, and both of them want the same two knobs

_Measured after 4j, before building anything.  The measurement contradicted
the plan it was meant to confirm, which is why it is recorded before the
work rather than after._

### The recommendation that was wrong

4i's reading of the live core said: eleven rows close but quasihalt, and
`LapGlueQuiet.glue_qh_quiet` already ends in exactly the `iqh` triple
`covers_iqh_at` consumes, with only the same too-strong `Hvis` that 4i
weakened for `LapGlue`.  So the port looked like the best ratio available:
eleven rows for one edit already done once.

Running the closure's own emitter over those eleven first:

    0 of 11 have the class arms the closure needs

Not one.  Eight fail on the interior arm, three on the fill.  **The port
would have been worth zero rows**, and would have been built before anyone
found that out.

### What actually gates them, and it is one thing

Across all **21** binary/step-1/one-phase rows in the live core (10 that
never quasihalt, 11 that do), with the interior arm carrying only the stride
4i added:

    3 board.  18 fail on ARM DERIVATION, not on the glue, the code,
    the phase, or the liveness.

4i put a stride on the interior arm and reported it "not enough", with the
missing piece named: a guaranteed block copy materialised into `s_pre`, and
then a separate arm for the residue's own `m = 0`.  That was right and it
was half the story.  **The fill arm needs the same two knobs**, and 4i did
not say so because 4i only ever tried the fill at one copy split and one
stride.  With a stride AND a materialisation offset on BOTH arms:

| | rows |
|---|---:|
| both arms derive | **15** |
| interior only | 2 |
| fill only | 0 |
| neither | 4 |

    never-quasihalts, both arms derive:  6   (2 already boarded, +4 new)
    quasihalts,        both arms derive:  9

So the order is the reverse of 4i's:

1. **the two knobs on both arms** -- `+4` rows with `board_neverqh`
   unchanged, no new glue at all;
2. **then** the `LapGlueQuiet` port -- `+9`, and not one of them before (1).

59 -> 46.  And 4i's own prediction of "four rows" from the interior offset
is confirmed exactly -- the four are the parity rows it named.

### The lesson, which is 4g's again with the sign flipped

4g's warning is that a label recording how a SEARCH failed gets mistaken for
a property of the machines.  This is the same error one level up: "eleven
rows need the quasihalt closer" recorded which THEOREM they need and was
mistaken for what is blocking them.  It is not.  Nothing was blocking them
that a closer would fix.

The cheap guard is the one used here: before building the thing that
consumes the arms, run the arm builder over the rows and count.  It took one
script and it changed the order of two sessions' work.

## 4l. Both knobs, on both arms, and then the closer.  Nineteen rows

_Everything below is a file that compiles or a number a script printed.  The
kernel at `LadderCheck.v`, the boards under `theories/Machines/Ladder/`, the
audit from `make closeout`.  Coq 8.18.0._

**Verified to the end.**  The full tree builds and `make closeout` runs in
full:

    closeout_partial : forall tm, Deferred D_census tm ->
                       boarded tm \/ skipped D_remaining tm

    Eval vm_compute in (List.length CoreRows.remaining_rows)  =  43

axiom footprint `functional_extensionality_dep` only, and
`census_cache.py --check` MATCH.  The 43 is the kernel's number, not only the
audit's.

### The gate 4k set, answered: one scheme

4k's gate was that the interior arm and the fill arm must share ONE arm
index -- one threshold, one stride, one offset, one lemma about
`n = k + s*j` -- because two parallel indexing schemes is how `fm_pre`
became a fixed list.  They can:

    astride N0 st r = if r <? N0 then 0 else st
    aoff    N0 st n = if n <? N0 then n else N0 + (n - N0) mod st
    acnt    N0 st n = if n <? N0 then 0 else (n - N0) / st

    arm_index    : aoff + astride (aoff) * acnt = n
    arm_index_lt : aoff < N0 + st
    arm_index_pos: 0 < N0 -> 0 < n -> 0 < aoff

`Nat.div_mod_eq` and `lia`, as 4k said.  The two classes instantiate it at
their own `(N0, st)`; nothing else about them is shared and nothing else
needs to be.  4i's `off = n mod st` is this scheme at `N0 = 0`, and that is
exactly why it stopped four rows short: an arm whose materialisation offset
is at or above the stride cannot be a residue, so the small `n` it does not
reach had no arm at all.

The fill arm gets the same two knobs, which it had neither of.  Its
threshold is at least 1 -- no width is 0 -- and the fill target's guaranteed
copies now divide PER ARM INDEX rather than once:
`fm1 r + fm2 r + |pre| + |suf| = r + f_s`, because the arm at offset `r`
carries `r` copies of the run on its left-hand side and not one.

### The one thing 4k did not anticipate, and it is a shape and not a count

**With `stride = 0` there is no block for the engine's steps to walk
AROUND.**  `SWin` moves inside `s_pre`; no chain step carries a cell from
`s_post` across the block boundary into it -- `srot 0` is the identity.  So
a flat arm stated as `mkS pre [] 1 0 post` has no chain at ANY depth, and
the first run of the emitter refused all 21 rows on the flat arm alone.

`blk` is the normalisation: with an empty block the whole side is concrete
in `s_pre`, and `blk_den` says the denotation is the same either way.  That
is what keeps it a normalisation of the SHAPE and not a second scheme, and
it is why 4i's "a separate arm for the residue's own `m = 0`" is one line of
`cls_side` rather than a second indexing scheme.  Both class sides take
their block through it.

Worth not rediscovering: the failure mode is a chain search that returns
`None` instantly at every depth and every stride, which reads like "the
carry ripple is not affine" and is not.

### The closer, and 4k's order was right

`glue_qh_quietN` is `LapGlueQuiet.glue_qh_quiet` `nat`-indexed with the same
weak visit premise `glue_neverqhN` already carries, quantified over
`q <> qa`.  Same proof.  The genuinely new obligation is `AvoidRun tm qa m
(Cf n)` on the lap, and the bridge to `LapAvoid.srun_avoid_sound` is

    base_chain : list rstep -> option (list lstep)
    base_chain_run : base_chain l = Some lb ->
                     rrun tm el er rs l c = srun tm el er lb c

`RuleAvoid` is `RuleSound`'s twin and `arm_avoid` derives it from the SAME
chain the kernel already replays, under `vm_compute`.  No new certificate
data.  Every class arm the emitter builds is all-`RB` (4h(c): `RU` is still
unexercised), and a chain that does invoke a ladder rule projects to `None`
and the arm is refused -- checkable, not assumed.  `qa = A` on all nine, and
its last visit is found by simulating the boot window (untrusted) and
re-checked by `bootvis_chk` / `bootquiet_chk`.

`board_lap` became `board_arm`, parameterised by what the closer wants OF
the arm it lands on: `board_neverqh` at `RuleSound`, `board_iqh` at
`RuleSound /\ RuleAvoid`.  Which arm serves a state, at what index and block
count, and that the configurations either side are that arm's two `cden`s,
is stated once.

Checked, not recalled: `arm_index`, `blk_den`, `arm_avoid`, `board_arm` and
`board_lap_avoid` are all **Closed under the global context** -- zero
axioms, because they are on `csteps`/`cden` and never go through `lift`.
`glue_qh_quietN` carries `functional_extensionality_dep` and nothing else.
4h's discipline holds: funext enters only in the final assembly.

**4k's measurement held exactly.**  Over the live core, and it is
`core61_armshapes.txt` row for row:

| | rows |
|---|---:|
| the closure applies to | 21 |
| **boarded** | **15** |
| never quasihalts | 6 (2 before, **+4**) |
| quasihalts | 9 (**all new**) |
| blocked on the arms | 6 |

and six more `0RB` rows after them, for nineteen boards; see below.

The six that fail are the six the table calls blocked: four with no interior
chain at any threshold or stride (the two quadratic rows and two undiagnosed
at 4i), and two with no FILL chain at any threshold, stride or copy split.
Neither is a gap in the emitter; both are `RULE_LADDER` 5's table row.

`board_ladder.py` reported the last two as "arm205 negative constant on the
repeated block", which is a note about ONE MINED ARM and not the refusal --
the trap 4i already recorded and the driver still has.  The refusal is in the
`.v` file, as always.  Read the file.

### What the number actually did, and one correction to 4k's arithmetic

The thirteen rows above went in first:

    settled by a board       5076 -> 5089   (+13)
    core undecided             59 -> 52
    0RB shadows of the core    21 -> 15

4k predicted `59 -> 46` from thirteen rows.  Thirteen rows moved, and all
thirteen were core rows -- but **core undecided fell by seven, not
thirteen**, because six `0RB` rows moved the other way: they were shadows OF
rows now settled by a board, so they need a resolution of their own instead
of their partner's.  The lesson is small and it is 4g's again: **"core
undecided" is a bucket, not a count of machines**, and a board that settles a
core row can promote a shadow into it.  Quote `settled by a board` when the
claim is about rows decided.

Those six were then the cheapest thing on the list, and they are 4k's
prediction the rest of the way: they are re-roots of rows just boarded, so
their orbit is known to have a ladder reading, and they had never been swept
because they had never been in the core.  Six `valfam` rows (~25 s each,
alongside a build, which is the one contention the sweep rule permits) and
all six close at `live = ABCD`, board at threshold 0 / stride 1 interior and
threshold 1 / stride 1 fill, and compile:

    settled by a board       5089 -> 5095   (+6)
    core undecided             52 -> 46
    0RB shadows of the core    15 -> 15

so 4k's `59 -> 46` is reached, by a different route than 4k drew and with
nineteen boards rather than thirteen.

### And then the decay 4k warned about, measured

4k's prompt said it plainly: *"the wave route is working the same population
concurrently -- a candidate that sits unboarded decays."*  It did.  While
this session ran, PR #91 boarded **nine of these nineteen rows** by the
three-state ternary-counter route: every `1RB---` row here is also a
`KS_`/`KA_`/`T3_` board on `main`, and both prove the same `iqh` triple.
Merging, on top of `main`:

    remaining (core + shadows)   68 -> 58
    core undecided               47 -> 43
    0RB shadows of the core      21 -> 15

**Ten rows net, not nineteen** -- the four `1RB1L*` never-quasihalters the
two knobs unlocked (4i's predicted four, exactly), and the six `0RB` rows.
The nine quasihalters are now double-covered.

That is not an argument against the closer: `board_iqh` is a general
mechanism over the same `Fam` record and the same arms, and it will take the
next quasihalting row the ladder reaches without any new theorem.  It IS an
argument about ORDER, and it sharpens 4k's rule rather than contradicting
it.  4k said: measure the arms before building the thing that consumes them.
The measurement it did not do is the cheap one next to it -- **check what the
concurrent route has already boarded before spending a session on a bucket**,
because "eleven rows need the quasihalt closer" was a statement about this
repository at one instant and two of those instants were four days apart.
`tools/closeout/core_rows.txt` on `origin/main` answers it in one diff.

### Where the 43 stop now

| | rows | |
|---|---:|---|
| no value family PROBED AT ALL | 15 | `docs/LADDER_NOFAM.md`; PR #90 reads 13 of 15 |
| families found, none closed | 11 | mechanical: coverage or differential |
| closed, `live = ABCD`, gray | 6 | needs the `(gray, 2)` `ClassSucc` |
| time cap | 4 | |
| closed, binary/step-1/one-phase, ARMS BLOCKED | 4 | the count language, not the emitter |
| closed, two phases | 3 | needs the phase cycle in `Inv` |

**There is no binary/step-1/one-phase row left that the closure can state.**
The fifteen that had both arms are boarded; the six that do not are
`RULE_LADDER` 5's table row, not a gap in the emitter.  The next session's
job is therefore a bucket it has not touched, and 4k's guard applies to each
of them before anything is built: run the arm builder over the gray six and
the two-phase three FIRST and count.  `closure_data` refuses both at their
first lines, so the probe is two lines commented out, and the answer decides
whether `(gray, 2)`'s `ClassSucc` is worth six rows or zero.

## 4m. The NUMERATION, built: five of the fifteen board, and the blocker moves

_Branch `claude/ladder-numeration-axis-hy11zp`, cut from `main` at `5da0721`
(PR #90 merged) and merged with `main` at `03f0b26` (PR #97) before this was
written.  `tools/ladder/valfam.py` is the only file this session changed; no
`tools/closeout/`, no wave-session file, no Coq (there is none in this image --
see below).  Baseline and result are two full sweeps of the live core, at that
time 59 rows, `sweep.py --cap 150 --kmax 9 --jobs 3`
(`tools/ladder/num59_before.jsonl`, `num59_after.jsonl`).  Every number below
is a count a script printed.  The measurement this builds on is
`docs/LADDER_NOFAM.md`, which is cited and not rewritten._

**Ran beside 4k/4l, not after them.**  This session and the two above it
started from the same `main` and touched disjoint files -- 4k/4l are
`emit_ladder.py` and the closer, this is `valfam.py` and family DISCOVERY --
so nothing here is measured against 4l's core of 43.  It does not need to be:
**all fifteen rows, and all five that board below, are still in the live core
after 4l**, so the five are additional to 4l's nineteen and not a subset of
them.  The sweep numbers below are against the 59-row core they were taken on
and are labelled as such.

### The kernel question, answered on minute one (NEXT_SESSION Rule 2)

4j found that the outer parameter is carried everywhere and used nowhere:
`LadderFam.fam_cfg` is `let '(ds, _, ph) := s in ...` and that `_` is p.  The
question handed to this session was whether the UNARY constructor -- where "p
IS the value" -- can be stated at all by a kernel whose denotation discards p,
and if not, whether the fix is container-safe.

**The premise is false, and that is the answer.  The unary family's parameter
is not the outer one; it is `length ds`, which the denotation does read.**
With `fm_b = 1`, `fm_digs = [w]`, `fm_fills = [Fill 1 [] 0 []]`:

* `fam_value F ds = val_pos 1 ds = 0` at every width -- the only digit is `0`;
* `fam_is_top F ds` is `1^k - 1 <? 0 + fm_step`, i.e. `0 <? 1`: **true at every
  width**, so `fam_next` is ALWAYS `fill_apply`, and that fill is
  `repeat 0 (k+1)`;
* `fam_cells F ds ph = fm_pre ++ flat_map (fun d => nth d [w] []) ds ++ tail`
  = `fm_pre ++ w^(length ds) ++ tail`.

So `E(p) = pre ++ w^p ++ tail`, and `fam_succ` takes width `p` to width `p+1`.
`p` and `v` collapse, the interior/overflow split becomes one arm per phase,
and the fill law has nothing to infer -- exactly the simplification
LADDER_NOFAM.md predicted, reached with **no new field on either side of the
trust boundary**.  `valfam.py` says the same thing with the same absence of new
machinery: `Fam.b = 1`, `Fam.value` unchanged (a positional sum over a
one-digit alphabet is 0), `Fam.of_value(0, k) = [0]*k`.  That is why step 1
below is a guard REMOVAL and not an addition.

**What does have to change is a hypothesis, and it is not a field.**
`LadderCheck.v`'s `Section Iter` opens `Hypothesis Hb : 1 < fm_b F`, and so --
**re-read at the merged HEAD `03f0b26` rather than at the one this was drafted
against, which is 4i's rule and it moved under this section** -- does 4l's new
`Section Board`; `LadderFam.v`'s `pos_of_lt`, `fam_value_of_value`,
`fam_next_interior` and `fam_next_wf` carry the same.  At `fm_b = 1` both
sections are uninstantiable.  They should read `0 < fm_b F`, and the proofs go
through:

* `inv_value_lt` needs `val_pos_lt`, whose statement holds for every `b >= 1`
  (`d + b*V <= (b-1) + b*(b^n - 1) = b^(n+1) - 1`) and whose proof is `nia`
  over exactly that;
* `fam_succ_total` and `top_reached_aux` each have an INTERIOR branch under
  `fam_is_top F ds = false`, which at `b = 1` is `0 <? fm_step` false -- a
  contradictory hypothesis, so the branch closes without arithmetic rather
  than needing new arithmetic;
* `fam_next_wf`/`fam_next_interior` are premised on that same false hypothesis
  and are never invoked at `b = 1`;
* `Section Board` never mentions `Hb` except to feed it to `fam_iter_total`,
  `tops_cofinal` and the three `pos1_*` lemmas.  Of those, `pos1_class_succ` is
  used only under `d < fm_b F - 1`, which at `b = 1` is `d < 0` and therefore
  unsatisfiable -- **the interior arm is vacuous, which is the same collapse
  read on the Coq side** -- and `pos1_is_top`/`pos1_top_shape` are about
  `repeat (fm_b F - 1) k`, which at `b = 1` is `repeat 0 k`, i.e. every string
  of the width.  Both hold; both need a `b = 1` case rather than the
  `1 < b` arithmetic.

That is container-safe under Rule 1 -- a re-proof of small per-file lemmas, no
census walk, no unbroken `native_compute`.  **It is not verified here, because
there is no Coq in this image** (`/root/.opam` does not exist, `coqc` is not on
PATH).  Rule 2 says to settle that on minute one; this is that, and the change
is written down rather than made.  And the outer parameter is still carried
everywhere and used nowhere: **the unary constructor neither fixes that nor
needs it fixed.**

### What was built

All of it is in `tools/ladder/valfam.py`, and the four new passes are behind
one gate: they run **only when every pass that exists today found NOTHING**.
That gate is why 4e/4f/4g's rows cannot move.  A row that reads as a positional
odometer never reaches any of this, so it cannot be re-read into a worse family
and cannot lose a per-candidate time slice to a fallback.  The cost is paid
only by rows that today return `no value family` in seconds with the whole
budget unspent -- which is exactly the fifteen.

1. **The UNARY counter** (`_try_parse`'s `2 <= len(alpha) <= 3` guard, and
   `_unary_pass`).  The counter side as a run template `word^p`, alphabet size
   1, `p` the run count.  Two lines of arithmetic: the guard admits one digit,
   and the value of a one-digit parse is `len(dsx)`.  It REMOVES machinery, as
   promised -- every string is the top, so there is no interior arm, no
   octave-top test and no fill law to infer.  Two defaults had to learn that
   `b = 1` exists: the odometer carry's target suffix is the digit `1`, which a
   one-digit alphabet does not have, so `fam_fill` defaults to the pure
   widening at `b = 1` and `Fam.cfg` returns None on a digit outside the
   alphabet instead of raising.
2. **`Fam.weights`** -- `Sum d_i . w_i` for an inferred non-decreasing `w`, of
   which `b^i` is one case.  `nofam.fit_weights` ported in substance (rank
   DIFFERENCES inside a width class, exact rational elimination, contradictions
   counted rather than averaged); `nofam.readings` deliberately NOT ported.
3. **`Fam.ptmpl`** -- the near-head prefix as `u^(a*p + b)` instead of a fixed
   word (4j's sixth defect), with `decode`/`encode`/`read`/`aligned`/`cfg` now
   taking the outer parameter.  Inert while `ptmpl is None`, which it is on
   every family the existing passes build.
4. **Three of LADDER_NOFAM.md's four REACH defects**, inside the same gate: the
   far-side template pass ungated and given 4g's `code`/`step` axes (defects 1
   and 2); the near-head prefix run past the digit width so a one-cell digit
   can have one (defect 3); and the terminator read off the whole group rather
   than off its common suffix (defect 4).

**The real cost of the weight sequence was `of_value`, exactly as predicted,
and the route that generalises is the one that worked.**  The representation is
not unique -- under `w = 1,1,2,3,5,8` the strings `1011` and `0111` are both
6 -- so `of_value` has to produce the MACHINE's canonical spelling.
`fit_classes` reads the canonical set as a right-linear grammar over MSB-end
BLOCKS and extrapolates it to widths the walk never reached.  On the dev
fixture it is

    C(k) = C(k-1).0  u  C(k-2).11        C(0) = {e},  C(1) = {0, 1}

-- blocks `{0, 11}`, class sizes 2, 3, 5, 8, 13, 21, 34.  Those sizes are
`numsys.py`'s Fibonacci fingerprint, used here as the ACCEPTANCE TEST rather
than as a label: the grammar has to reproduce every observed class exactly
(containment only at the widest two widths, where the walk routinely stops
mid-class) or the weights are refused.

The dev fixture also shows why the grammar form is the one to implement rather
than the forbidden-factor form guessed from the name.  **The canonical set here
is NOT "no 11".**  Its size is the same -- `F(k+2)`, which is why the class
sizes are Fibonacci either way -- but its members are different: `1100`, `0110`
and `1111` are all canonical at width 4, and `0100` is not.  Reading blocks off
the data finds the right language without anyone naming it; assuming Zeckendorf
would have found the wrong language with the right count, and `cover` would
have reported the machine leaving its own family.

**One simplification fell out.**  The weights pass does not vary the step.  With
the weight sequence read rather than assumed, `w` and `s*w` describe the same
family -- the step and the weight sequence are the SAME axis -- so the pass
fixes `s = 1` and lets the scale come out in the weights.  Half the search
space, for free.

### The gates

| | measured | needed |
|---|---:|---:|
| **A.** a family with LADDER_NOFAM.md's measured NUMERATION | **8 of 15** | 8 |
| **B.** closes end to end: differential, exact step counts, 40 laps | **5 of 15** | 4 |
| **C.** no row that closes today stops closing | **0 regressions** | 0 |

The live core, 59 rows at the time of the sweep, before and after:

| | before | after |
|---|---:|---:|
| closed | 25 | **33** |
| of those, never-QH (all states infinitely often) | 14 | 17 |
| differential ok / exact step counts | 25 / 24 | 33 / 32 |
| the fifteen: families probed | 0 on all fifteen | 10 of 15 |
| the fifteen: closed end to end | 0 | **5** |

**Three of the eight extra closures are not this session's.**
`1RB0RB_0LC0LD_1LC1LD_1RA0RA`, `1RB0RB_0RC1RC_0LD1LA_1LD0LA` and
`1RB0RC_1LC1RA_1RD1LB_0LC0RD` close under both codebases -- the first two are
4g's own Gray rows, `code=gray, step=2`, 49 arms, and none of the three uses
anything added here -- and the baseline sweep lost them to a subprocess
failure (`sweep.py` reason `no output`).  The delta this session is
responsible for is exactly **the five**, and it is worth writing that down
rather than banking the 8.

Gate A is counted STRICTLY: a family whose numeration is the one
LADDER_NOFAM.md's table names for that row, at any anchor.  Ten of the fifteen
get a family at all; eight get the measured one -- the five Fibonacci rows plus
`0RB0RD_1LC1RB_1RA0LC_1LB0LC`, `0RB0RD_1LC1RB_1RA0LC_1LD0LC` and
`0RB1LC_1LC0RD_1RD0LC_1LA1RB`, whose base-2 readings the far-side template pass
reaches once defects 1 and 2 are lifted.  The three that get a family which is
not the measured one are counted against, not for.

The five that board read exactly what was measured -- same terminator, same
weights, and the chain lengths (290, 291) are the ones LADDER_NOFAM.md's table
reports:

    1RB---_0LB1RC_1LB0RD_1LC0RD   B1/R  tail 11  w = 1,1,2,3,5,8,...   5 arms
    1RB---_0LB1RC_1LD0RC_1LB1RC   C1/R  tail 11  w = 1,1,2,3,5,8,...   4 arms
    1RB---_1LC0RB_1LD1RB_0LD1RB   B1/R  tail 11  w = 1,1,2,3,5,8,...   4 arms
    1RB---_1LC0RD_0LC1RB_1LB0RD   C1/R  tail 11  w = 1,1,2,3,5,8,...   5 arms
    1RB---_1LC1RD_0LC1RD_1LB0RD   D1/R  tail 11  w = 1,1,2,3,5,8,...   4 arms

all with `enumeration = all digit strings` -- over the CANONICAL strings, which
is what `all_strings` now enumerates -- all `differential_ok` and
`differential_steps_ok`, all 40 laps confirmed from the blank tape.  The two
LADDER_NOFAM.md calls "the two rows that need NOTHING but the weights" are the
first and the fourth; they were the dev fixture, they closed first, and
everything else followed.  Their liveness reads `BCD`, so they are 4i's
quasi-halt-witness bucket and not yet boards.

### The two false closures this session refused, and why that is worth more

An earlier state of this branch reported `0RB1LC_1LC0RD_1RD0LC_1LA1RB` and
`1RB0RB_1LC0RC_1RA0LD_0LB0LC` **closed**, with `differential_ok` and 40 laps
confirmed.  They are not closures.

Read at A0/L, `0RB0RD_1LC1RB_1RA0LC_1LB0LC` is a unary counter `1^p` on the
left with the far side fitted as a run template -- and the fill's outer law is
`p' = p - 1`.  The far side is being EATEN.  `far_cells` returns None as soon
as a count goes negative, so the successor chain is finite BY CONSTRUCTION, and
`chain_check`'s 40 laps say only that 40 is less than `p` at the boot (108).
The single arm is pinned at one `p` and the differential's `predicted_steps` is
`null` on every check past the first -- which is what `differential_steps_ok =
false` was saying all along.

`close` now refuses any family whose fill strictly decreases the outer
parameter, and says so as the reason.  **No row that closes today has a fill
that moves the outer parameter at all**, so the guard costs nothing: it is not
a special case, it is the statement that a reading which is true over the
window and false forever is the one thing a certificate candidate must never
be.  Four of the fifteen now stop exactly there.

### The unary reading is the weakest one in the file, and it has to go last

Measured, twice.  With the unary constructor inside the ordinary
constant-far-side pass -- where the guard removal naturally puts it -- it fired
first, filled `found`, and switched the whole second-chance block off:

* `1RB0RB_0LC1RD_1LC1LA_0LA1RB`, which LADDER_NOFAM.md measures as
  **fibonacci**, returned two unary families and no Fibonacci one;
* the BBB(4) champion `1RB1LD_1RC1RB_1LC1LA_0RC0RD`, which `nofam.py` measures
  as **not a counter** (shape classes growing `2n/3`), returned **eleven**
  families;
* the three rows whose measured reading is base-2 returned unary readings
  instead of them.

The cause is the one `nofam.unary_probe` already warns about in its ranking
comment: *a bare run of 1s inside a bouncer also gives a monotone p*.  So
`_try_parse` now takes `unary=True` explicitly and reads nothing else, and the
unary pass runs only after the template, prefix and weights passes have all
declined the row.  With that ordering the champion returns **zero** families,
the three base-2 rows return base-2, and gate A goes from 6 to 8.  Strongest
reading first is the same discipline 4e applied to the far-side template and 4g
to the code and the step; this is the fourth time it has had to be applied and
the first time it was measured as a REGRESSION in reading quality rather than
as a missing reading.

### Where the fifteen actually stop now

| spec | families | where it stops |
|---|---:|---|
| `0RB0RD_1LC1RB_1RA0LC_1LB0LC` | 8 | the fill decreases the outer parameter |
| `0RB0RD_1LC1RB_1RA0LC_1LD0LC` | 3 | coverage / differential |
| `0RB1LC_1LC0RD_1RD0LC_1LA1RB` | 30 | the fill decreases the outer parameter |
| `0RB1LC_1LC1RD_1LA0LC_0RD1RB` | 26 | the fill decreases the outer parameter |
| `1RB---_0LB1RC_1LB0RD_1LC0RD` | 8 | **CLOSED** (fibonacci) |
| `1RB---_0LB1RC_1LD0RC_1LB1RC` | 4 | **CLOSED** (fibonacci) |
| `1RB---_1LC0RB_1LD1RB_0LD1RB` | 4 | **CLOSED** (fibonacci) |
| `1RB---_1LC0RD_0LC1RB_1LB0RD` | 12 | **CLOSED** (fibonacci) |
| `1RB---_1LC1RD_0LC1RD_1LB0RD` | 4 | **CLOSED** (fibonacci) |
| `1RB0RB_0LC1RD_1LC1LA_0LA1RB` | 0 | no family: the fibonacci reading needs a terminator SET |
| `1RB0RB_1LC0RC_1RA0LD_0LB0LC` | 5 | the fill decreases the outer parameter |
| `1RB0RB_1LC1LD_0LC1RA_0LD0RA` | 0 | binomial -- deliberately out of scope |
| `1RB1LB_1LC0RD_0LB1LA_0LA1RA` | 0 | not a counter; wave route |
| `1RB1LD_1RC1RB_1LC1LA_0RC0RD` | 0 | not a counter; wave route (the champion) |
| `1RB1RC_1LA0LB_1LD0RD_1LB0RC` | 0 | no family: `w = 1,1,3,3,9,9` not reached |

So of the thirteen that are not the two bouncers: five board, four have a
family and stop on the outer parameter, one stops on coverage, and three are
still unread.  **The blocker on four rows is now downstream of family
discovery and it has a name**, which is what this branch was told to report if
A passed and B did not clear by more.

### What this says about the next session

* **The weight sequence is done, and the canonical form is the part that needs
  a Coq lemma.**  It now has a concrete statement:
  `C(k) = C(k-|u1|).u1 u ... u C(k-|un|).un` is a right-linear grammar,
  `fam_of_value` is an index into it, and the obligation is that the index is
  injective on each width -- which is where the class sizes stop being a
  fingerprint and start being a theorem.  `fm_digs` gains a companion; nothing
  in the kernel changes shape.
* **The near-head prefix SET is the next constructor, and it is bigger than it
  looked.**  Measured on `1RB0RB_1LC0RC_1RA0LD_0LB0LC` at A0/R over 567 anchor
  visits: `phi . (101)^p . 0011111` parses 445 of them, `phi` takes 27 values
  each occurring 16-17 times -- and the far side is **distinct on every one of
  the 567 visits**, with 12 different run-word signatures, ranging at a FIXED
  `p` over about 17 strings whose lengths span 26 cells.  Those are the same
  fact: the prefix and the far side advance on one clock and `p` on another, so
  the row is `E(p, phase)` with 27 phases.  (LADDER_NOFAM.md's `0^(24p+96)` is
  `_far_affine`'s reading of the MINIMUM far-side length per `p`, which is
  exactly what that function measures and exactly what it says.)  On the kernel
  side this is `fm_pre` becoming `fm_pres : list (list Sym)` read at `nth ph`
  -- the mirror of `fm_tails`, which already is -- plus a far side indexed by
  the phase.
* **`Fam.ptmpl` is built and fires on zero of the fifteen**, and that agrees
  with 4j's own closing paragraph: the thirteen are not blocked by the
  near-head spacer alone.  The denotation half is in place and inert, so the
  next reader that needs it will not have to plumb it.
* **`1 < fm_b F` should become `0 < fm_b F` on the box.**  Four `LadderFam`
  lemmas, two section hypotheses (`Iter` and 4l's `Board`) and a `b = 1` case
  in two `pos1_*` lemmas; every interior branch closes by contradiction.
* The two bouncers stay the wave route's, and the binomial row stays out of
  scope: no weight sequence expresses it, `fit_weights` correctly declines it,
  and it is still one row.

## 4n. The probe first, then the PHASE CYCLE.  Three rows, and the gray six are four

_Branch `claude/ladder-failing-machines-w2lio1`, cut from `main` at `bc882b2`
(4l and 4m both merged).  Coq 8.18.0, installed in the image
(`apt-get install -y coq`).  Every number below is a count a script printed
or a file that compiles._

4l's closing instruction was 4k's guard one bucket over: **run the arm
builder over the gray six and the two-phase three FIRST and count**, and let
the count decide what gets built.  That is what happened, and the count moved
the decision.

### The probe, and what it had to get right

`tools/ladder/armprobe.py` relaxes the three refusals `closure_data` opens
with -- `code = gray` at its first line, a step other than 1 at its second, a
phase cycle at its third -- in a PROBE and not in the emitter, and reports
per row whether every class arm the closure needs has a chain.  The classes
are FITTED from the family's own successor rather than assumed: on the gray
rows the fit recovers 4i's four `(gray, 2)` classes verbatim, which is the
first independent confirmation of that table.  `--selftest` runs the whole
probe over a row that is already boarded and checks it recovers the
`(Binary, 1)` class and both arms -- the discipline `bounce.py --selftest`
exists for.

| | rows | |
|---|---:|---|
| closed, gray, `live = ABCD` | **4 of 6** | both class arms |
| closed, two phases | **3 of 3** | both class arms |
| time cap | 2 of 4 re-run at `--cap 900` | both still capped, `26` families, 4 tried |

**Two findings came out of making the probe honest, and both are about the
CONFIGURATION and not about the class law.**

* **`RuleSound` is an equation on `cconf`, and `ctape_move` does not
  normalise.**  A blank the head materialises by stepping back over it is
  `S0 :: r` and not `r`.  `valfam` reads the far side through a run-length
  view that has already dropped a trailing blank run, so
  `other_side_cells` can be short by exactly those cells -- the same TAPE
  under `lift` (which is why `Hboot`, stated on `lift`, does not notice) and
  a different `cconf`, which is what every arm is stated on.  Read the far
  side off the boot instead and the interior arms of **all six** gray rows
  derive; with the certificate's value, **none** does.  The failure reads as
  "chain lands off the rhs" at every threshold and stride, and it is one
  cell.

* **The top of a width is the largest MEMBER, not the largest value.**  At
  `(gray, 2)` the value `b^k - 1` is odd and therefore not a member at all,
  so the fill arm's left-hand side is `[1] ++ 0^(k-2) ++ [1]` and not the
  `0^(k-1) ++ [1]` that `of_value` computes.  An arm built on the other has
  no chain for the good reason that the machine is never in that
  configuration.  The probe reads the tops off the ORBIT for this reason.

**The two gray rows that do not have both arms stop on the fill arm, and it
is the mirror of the first finding.**  Their digit words are two cells and
the second is a `0`, so the family spells one cell more than the machine's
`cconf` carries at every anchor visit -- the trailing blank of the top digit
is never materialised.  Measured: strip that one cell and the fill arm
derives in 24 steps at every index and every copy split; leave it and it
lands off the right-hand side at all of them.  That is a statement about the
family's cell SPELLING, not about `(gray, 2)`, and it is what `fam_cells`
cannot say: every digit contributes its whole word.

### What the count decided, and it was not the biggest bucket

Four rows (gray) against three (two phases), and the build costs are not
close.  `(gray, 2)` wants `cls_side` widened with a fixed word before the run
(three of the four classes have one), four `ClassSucc` instances, the parity
invariant `P`, a four-way replacement for `digs_decomp`, and a `Section Iter`
for a code and step the value arithmetic does not cover -- `fam_value` at
`Gray` is a fold from the most significant digit down, so no lemma about
`val_pos` transfers.  The phase cycle wants a bounded phase in `Inv` and
nothing else new: it stays at `(Binary, 1)` and every piece of arithmetic
already exists.  **Three rows that close beat four rows that might.**

### What was built

* **`Inv` carries `ph < NPH` instead of `ph = 0`**, which is 4i's sentence
  ("a change to this predicate and to nothing above it") and it is exactly
  that: `filled`, `fill_at_top` and `fam_succ_total` read the fill law at the
  state's own phase, the interior step leaves the phase where it found it
  (`pos1_class_not_top`, lifted out of `pos1_class_succ`'s own arithmetic,
  is what says the fill does not fire there), and no value, width or measure
  mentions a phase.  `tops_cofinal` does NOT need the fill to widen: a
  phase-0 fill that re-enters the same width in phase 1 is what a terminator
  cycle IS, and what the argument needs is that a top RECURS.
* **`Section Board` is indexed by the phase** -- one fill arm per index and
  phase, the terminator of its own phase on the left and of the phase the
  law names on the right.  The interior arms are NOT phase-indexed and do not
  need to be: their terminator is inside the opaque tail `cls_tail`, which is
  the same reason an arm proved for an arbitrary tail covers a class.
* **`board_neverqh` and `board_iqh` keep the interface they had**, as
  wrappers at `NPH = 1` (`Section BoardOne`).  Not a second proof -- the whole
  content is the phase-indexed theorem instantiated -- which is the
  discipline `board_arm` already enforces between the two closers.  The
  thirty-one boards emitted before this session compile unchanged; that was
  checked before anything else was built on top.

### The blocker the probe did NOT measure, and it is the interesting one

All three rows have both class arms and all three then stopped on the same
thing: **no chain from one fill anchor to one state**.  Consistently the
anchor of the phase whose fill widens by NOTHING -- the lap into the next
terminator -- which is six machine steps long and passes through two of the
four states.  Raw simulation says the missing state is `26j + 1` steps away
from that anchor, i.e. the far side of the whole counter walk, so it is not
a search that needs widening.

The fix is in the liveness and it is smaller than it looks.  **A fill arm's
anchor does not have to witness every recurring state.**  What `glue_neverqhN`
asks is that for every state and every bound SOME anchor past the bound
reaches it, and the tops of ONE phase are enough if they are cofinal:

    tops_cofinal_at : (forall ph, ph < NPH -> exists k, phto F k ph = pv) ->
                      Inv F NPH s ->
                      exists n s', N <= n /\ fam_iter F s n = Some s'
                                   /\ fam_is_top F (ct_ds s') = true
                                   /\ Inv F NPH s' /\ ct_ph s' = pv

`top_reached` strengthened to preserve the phase (interior steps do not move
it), one fill to step the cycle, and an induction on `k`.  `Hcyc` is a case
split over `NPH` phases and a `vm_compute` on the emitted board.  The
emitter picks `pv` by trying each phase and keeping the one whose anchors
reach everything -- measured before it was built, on all three rows:

    1RB0LA_1LC1LA_1RD1LB_0LC0RD   ph 0 reaches BCD,  ph 1 reaches ABCD   pv = 1
    1RB0RC_1LC1RA_1RD1LB_0LC0RD   ph 0 reaches ABCD, ph 1 reaches BCD    pv = 0
    1RB1RD_1LC1RA_0RB0LC_1LA0RD   ph 0 reaches ABC,  ph 1 reaches ABCD   pv = 1

so `vis` loses its phase index rather than gaining one: the visit chains are
at `pv` and the other phases' arms carry none.

### The number

    nqh_1RB0LA_1LC1LA_1RD1LB_0LC0RD : NeverQuasiHaltsSt tm
    nqh_1RB0RC_1LC1RA_1RD1LB_0LC0RD : NeverQuasiHaltsSt tm
    nqh_1RB1RD_1LC1RA_0RB0LC_1LA0RD : NeverQuasiHaltsSt tm

axiom footprint `functional_extensionality_dep` only, as every board.
`make closeout`:

    settled by a board       5098 -> 5101   (+3)
    core undecided             43 -> 40
    0RB shadows of the core    15 -> 15     (no promotions this time)

### Where the 40 stop now

| | rows | |
|---|---:|---|
| no value family PROBED AT ALL | 5 | `docs/LADDER_NOFAM.md`; three unread, two out of scope |
| families found, none closed | 16 | mechanical: coverage, differential, or 4m's outer-parameter guard |
| closed (fibonacci), `live = BCD` | 5 | 4m's five: the canonical form wants a Coq lemma |
| closed, gray | 6 | **4 have both arms**; 2 stop on the cell spelling |
| time cap | 4 | two re-run at `--cap 900` and both still capped |
| closed, binary/step-1/one-phase, ARMS BLOCKED | 4 | `RULE_LADDER` 5's table row |

### What this says about the next session

* **`(gray, 2)` is now a measured four rows and the build is specified.**
  Four `ClassSucc` instances, the parity invariant, `cls_side` with a fixed
  word before the run, a four-way case split to replace `digs_decomp`, and a
  `Section Iter` at `Gray`/step 2.  The arms are known to derive, which is
  what this session bought it: nobody has to guess again.
* **The two gray rows that stop on the spelling are a FAMILY question, not a
  kernel one.**  Either `valfam` reads them at an anchor whose digit words do
  not end in a blank, or `fam_cells` gains a trimming the denotation can
  state.  Do not build a `ClassSucc` for them: their class law is fine.
* **The time cap is not a cap.**  Two rows re-run at six times the sweep's
  budget and both still capped, with 26 families found and four tried.  The next reading of those
  four should be about which families the searcher spends the budget ON, not
  about how much budget it has.
* Three traps, all paid for here: **editing a kernel file under a running
  `make` makes every already-built board fail with "inconsistent assumptions
  over library BBB4.Checkers.LadderCheck"** -- it is the same trap as
  rewriting `_CoqProject` mid-build, and the fix is the same, do the edit and
  then build.  `make closeout` only needs `theories/Closeout/Closeout.vo`,
  whose dependency closure is 2188 files and **does not include the nine
  `IRules_Batch`**, so a session that only wants the audit never pays their
  8.2 GB each.  And `coqdep` is the thing to ask, not the plan file.

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

