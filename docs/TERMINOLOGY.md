# TERMINOLOGY — shared vocabulary for the (4,2) quasihalting project

_The glossary for the finished result: what "census / D_census / holdouts /
residue / hammer" mean, where the sets came from, and what work each one
implied.  The definitions are stable and the counts are final — the burndown
closed at 5,156 of 5,156 on 2026-08-01._

---

## The result's own vocabulary

The headline theorem and its terms (see `docs/CLAIMS.md` for the precise
claim, `theories/BBB4_Spec.v` for the definitions):

- **`BBB4_statement`** — the claim, `BBB4_is champion_score`: 32,779,478 is
  attained and no machine attains more.  **`BBB4_value`**
  (`theories/Closeout/BBB4_Value.v`) is its proof.
- **`Attains tm B`** — machine `tm` has a state whose last visit is at
  configuration index `B − 1`, i.e. whose last transition fires at step `B`.
- **the champion** — `1RB1LD_1RC1RB_1LC1LA_0RC0RD` (`tm_champion`), whose
  state `D` attains exactly 32,779,478.
- **`skipped` / `not_skipped_nil`** — the closeout chain's escape disjunct
  for still-unboarded rows.  It ranges over `D_remaining`, which ended
  EMPTY, so `not_skipped_nil` proves it uninhabited — that discharge is
  what turns the chain into the unconditional upper bound.

## The one census theorem everything hangs off

`Census_Theorem.census_decided`:

```
forall tm, QHBound B_census tm  \/  Deferred D_census tm      (B_census = 2000)
```

Every TNF (4,2) machine is EITHER decided by the census's `QHBound 2000`
proof, OR it is deferred into the list `D_census`. This is Qed'd through the
kernel (`Print Assumptions` = `functional_extensionality_dep` only) and the
built `.vo` are committed + hash-guarded (`CENSUS_VO_HASH`,
`census_cache.py --check` must stay MATCH). **`D_census` is a frozen,
certified set** — see `docs/NGHIST_WAVE5.md` §5.

- `QHBound B tm := forall q s, QuietAfter tm q s -> S s <= B` — every state
  that eventually goes quiet made its last visit by step `B`. (A never-QH
  machine satisfies this vacuously: it has no quiet states.)
- The `QHBound 2000` census tier is deliberately **LIGHT** (in-walk
  qhb-lex / RepWL at small params; PLAYBOOK Rule 4 kept it weak on purpose,
  because strengthening the in-walk tier makes the native_compute walk
  ~100× slower per machine). So `D_census` is "resisted the *light* B=2000
  proof", NOT "intrinsically hard".

## `D_census` = 5,156 — and how it partitioned

`D_census` is the deferred set: the machines that **resisted the B=2000
census proof**. It split by mxdys' holdout list (below):

| term | definition | count |
|---|---|---|
| **`D_census`** | machines that resisted the census `QHBound 2000` proof | **5,156** |
| **holdouts** | `D_census ∩ mxdys' 3,713 holdout list` | **27** (`tools/census_holdouts_kept.txt`) |
| **residue** | `D_census ∖ mxdys' 3,713 holdout list` | **5,129** (`tools/census_residue.txt`) |

Verified: `27 + 5,129 = 5,156`; `holdouts ⊆ 3,713`; `residue ∩ 3,713 = ∅`.

The split was by **whose proof failed** — that is what made it useful:
- **residue** = "our light census tier failed, but the machine is NOT on
  mxdys' can't-do list" ⇒ *presumably* mxdys decided it ⇒ a **strength gap
  between us and mxdys**, nothing more.
- **holdouts** = "our census tier failed AND it's on mxdys' can't-do list"
  ⇒ both procedures failed, the second being state of the art ⇒ the genuine
  frontier.

**CAVEAT (recorded during wave-8): list-absence is an inference, not a
record.**  The 3,713 list is the ONLY artifact of mxdys' BBB run — the
machines that didn't make it were never *enumerated as decided* anywhere.
"Not on the list" = "his deciders ate it" only if his BBB enumeration
actually visited the machine, and his tree provably differs from ours at the
edges (5 of his 3,713 are not leaves of our tree; ours has 3,995,005 nodes,
no cnt-pruning).  Positive per-machine evidence existed only for the
≤7-transition targetable subset; for full-8 residue machines "easy" was a
strong prior, not a guarantee.  Checked at the time: 0 of the 5,129 residue
canonicalize onto a 3,713 entry under TNF relabel + mirror (`tnf_canon`), so
the split was not hiding relabeled holdouts.  **The inference is no longer
load-bearing**: every residue machine now carries its own kernel-checked
board, so nothing rests on guessing what mxdys decided.

## mxdys' holdout list (the 3,713) — provenance and meaning

`BBB4_holdouts_3713.txt` (in the **BBB repo** `carrino/bbb`, copied into
`Coq-BBB4/tools/`) is **mxdys' output**: he ran his best beeping-busy-beaver
(quasihalting) inductive deciders over the (4,2) space, and the 3,713 are
what those deciders **could not decide**. It is the starting point this
whole project grew from — not an arbitrary external list.

mxdys' two claims about how the list was made (the load-bearing principle):
1. *"these holdouts are filtered by my inductive deciders"* — holdouts =
   what's left after the deciders run.
2. *"my inductive decider can only decide a TM when it can model the forward
   behavior EXACTLY."*

Contrapositive: **a machine is a holdout ⟺ no finite EXACT forward model
exists** at the tried parameters — i.e. it is **not perfectly predictable**.
An over-approximate closure is enough to prove NonHalt (halting), but
quasihalting needs the *faithful* model to read each state's recurrence, so
"can't model exactly" = "quasihalting genuinely undecided by his method".

The **27** were the residual of that 3,713 inside `D_census` (prior waves
proved & dropped ~3,686), and all 27 are now boarded — the last, tower #20,
on 2026-07-28.  NOTE: the BBB repo's own `results/open_holdouts_3221.txt`
is a STALE snapshot from 2026-07-06 (pre-harvest) — the residual lived in
the Coq census (`census_holdouts_kept.txt`), not that file.

## Two oracles (both UNTRUSTED targeting aids; the kernel re-checked everything)

- **`BB4_verified_enumeration.csv`** (CoqBB5 v1.0.0 release; kept out of git
  for size, see `tools/nghist/BB4_verified_enumeration.README`) — mxdys'
  **HALTING** BB4 pipeline: per-machine `(status, decider, params)` for all
  858,909 machines. A *proxy* for "an exact model exists" (halting is easier
  than quasihalting); it was used for closure targeting, never as the last
  word.
- **BBB repo `results/certs_*`** — OUR OWN (carrino/bbb) per-machine
  quasihalting certs from the **holdout** grind (rank/irules/rwlrank/fuel/
  drift/... — this project's engines, not mxdys'). These covered holdouts
  only — measured **zero** overlap with the unboarded residue — so they were
  never a residue oracle; their value for the residue was the *engines*
  behind them (irules, RepWL), not the cert files.

## The two fronts, as they were worked

The burndown ran on a two-front discipline: point the porting machinery at
the residue; keep it *away* from the holdouts.

- **Residue → PORT WORK.**  mxdys had (presumably) already solved these, so
  boarding them was catching up in Coq with a weaker in-walk tier: bounded,
  mechanical, high-confidence.  Wave-6 `NGramHist` (his history-augmented
  NGramCPS ported to Coq + extended to quasihalting) was the opening tool
  and delivered the first ~964 boards; the prediction that it would drive
  the residue to ~0 was **wrong** — the finish came from the ReachSt and
  Ladder routes (below), which is its own lesson about the safety≠liveness
  gap.
- **Holdouts (27) → RESEARCH WORK.**  Beyond mxdys' method by his own
  verdict, so porting his method was never expected to crack them.  They
  fell to different ideas: individual busycoq-style proofs for the
  counter/tower/double families, ending with tower #20 on 2026-07-28 —
  including `1RB0RB_1LC1RC_0RA1LD_1RC0LD`, for a long time the last
  genuinely open machine, boarded in `Closeout/CB_37.v`.

The discipline held: no oracle-driven sweep was ever aimed at a holdout,
and the two fronts closed by different methods, as the split predicted.

## Scoreboard — final

**5,156 of the frozen 5,156 settled (100.0%); 0 undecided core machines,
0 0RB shadows — the residue list is empty (since 2026-08-01, tracked to
zero in [issue #61](https://github.com/carrino/Coq-BBB4/issues/61)).**
Reproduce the figure with `python3 tools/closeout/audit.py` (untrusted
bookkeeping; the kernel-checked form of "done" is `remaining_rows = []`
and `not_skipped_nil` — see `docs/CLAIMS.md`).

Two vocabulary corrections, because the situation changed under older
notes in this tree:

* **The HOLDOUT list is closed.**  Earlier documents call the 27 holdouts
  "the open problem, may never hit 0" and the residue "a tooling debt".
  Tower #20, the last holdout, was boarded on 2026-07-28.
* **The residue's character inverted along the way.**  It began as machines
  whose lap our emitter could not FRAME; what remained at the end was
  mostly machines whose lap is not affine at all (`docs/RESIDUE_MAP.md`,
  "The families").

## `boarded`, and how the residue closed out without a re-walk

`boarded tm := NeverQuasiHaltsSt tm \/ iqh tm`. The closeout is a single
theorem `Forall boarded D_census` built by `app`-chaining the staged per-file
`Forall`s (route A, `docs/NGHIST_WAVE5.md` §5) — **no native_compute census
walk, `D_census` never changed.** The 5,156 number inside `census_decided`
was never shrunk; the project proved *properties over the frozen 5,156 set*
until the `Forall` closed.

## How the residue was eliminated (the plan, as executed)

"Eliminate the residue" had a precise meaning: **every one of the 5,129
residue machines carries a kernel-checked `NeverQuasiHaltsSt` or `iqh`
proof**.  It did **NOT** mean shrinking the 5,156 inside `census_decided`
(that stayed frozen — see §`boarded` above), and it did **NOT** touch the
holdout front (worked separately, above).  When the plan was written the
score stood at 964 / 5,129; the steps below took it to 5,129 / 5,129,
cheapest leverage first — steps 1–3 and 6 as planned, step 6 landing as
`theories/Closeout/` (`CB_*.v` stages plus `Closeout.v`) rather than the
originally sketched `Census/Assembly.v`:

1. **Full sweep, not a pilot.**  `tools/nghist/harvest_sweep.py sweep` and
   `sweepqh` over the *entire* residue.  At `(k=2,n=2)` / `(k=4,n=2)` this
   boarded the bulk of the counter tail with no human input.
2. **Param escalation on the fail set.**  For machines that didn't close at
   small params: climb history `k` (2→4→6→8), gram `n` (2→3), `MAXCTX`,
   fuel.  Each rung cost more per machine and boarded a further slice.
3. **Both shapes, always.**  never-QH (`NGHStage/`) *and* R_QH
   (`NGHWStage/`).  A machine the never-QH gate rejected because it
   genuinely goes quiet was a wrap/R_QH board, not a failure.
4. **Pattern measures for the liveness-lag tail** — machines that close
   (safety) but whose liveness the lex gate couldn't rank.  The wave-8
   diagnostic put ~85% of the then-remaining gap here (NOMEAS).
5. **Oracle-target the stubborn remainder** — use the halting CSV and the
   BBB certs to set params and pick measures instead of searching blindly.
6. **Wire the closeout (Route A)** — `app`-chain the per-file `Forall`s
   into `Forall boarded D_census`.  Done; it is `theories/Closeout/`.

In the event, steps 4–5 were not where the endgame happened: the last ~120
rows came from the ReachSt and Ladder routes (next section), which stepped
around the measure-vocabulary gap instead of filling it.

## REFUTED — "the hammer" (measured in wave-8; do not rebuild)

**The decisive experiment was run and the hypothesis is FALSE.**
`tools/nghist/hammer_probe.py` swept history k ∈ {2,4,6,8,12} × gram
n ∈ {2,3,4} × seed t ∈ {150,600} over a stratified 300-machine sample of the
unboarded residue (100 oracle-targetable + 200 full-8), measuring both
whole-closure out-degree and the load-bearing weaker condition (a
deterministic ρ-trajectory from the seed node under LEAN gram sets — seed
windows + trajectory donations only). Result: **0/300 machines determinize at
ANY grid point**; every failure is BRANCH (far-cell ambiguity), and the
branch position creeps by +2 per +2 of k — the ambiguity sits a fixed
distance beyond the history horizon. Even the wave-6-boarded pilot counter
(`0RB---_0LC0RA_0LD---_1RA1LC`, 26/33 nodes out-degree 1) never reaches a ρ.

The structural reason: cells of a uniform tape block written by the same
sweep carry IDENTICAL truncated histories, so position within a block is
indistinguishable at any bounded k — the block boundary's far cell stays
ambiguous forever. The pilot's "out-degree ≈1" was the misleading average;
the ~7 branching nodes per machine are block boundaries, incurable by
history. mxdys' "models the forward behavior exactly" therefore operates at
his deciders' RULE level (macro-step / repeated-word structure), not at the
per-cell level of this abstraction. The follow-up diagnostic
(`tools/nghist/fail_diag.py`, 400 unboarded machines) showed where the
remaining effort would go: 85 % closed fine but failed the liveness measure
search (NOMEAS — the vocabulary/lex-synthesis gap), 11 % were prefix-quiet
quasihalters (wrap route), 3 % exceeded the search caps, <1 % genuinely
failed to close.

_The original hypothesis, superseded by the measurement above and kept
verbatim for the record:_

Because the residue is mxdys-exact, don't *search* for a lex certificate —
make the augmented closure **deterministic** (out-degree exactly 1: history
determines the incoming far cell) and *read* the answer. A deterministic
closed augmented set is a **ρ-shape** (a tail running into one cycle), and
then quasihalting is immediate: **states on the cycle recur (never-QH iff
every visited state is on the cycle); states only on the tail are quiet
(QH, bound = tail length).** This is sound for exactly mxdys' reason —
determinism *is* "models the forward behavior exactly" — so it dissolves the
safety≠liveness trap rather than searching around it.

## The two routes that produced the last ~120 boards

* **REACHST tier** (`Checkers/ReachSt.v`, `ReachStI.v`;
  `docs/REACHST_TIER.md`).  The liveness obligation is "state `q` recurs
  forever".  Instead of modelling the machine's lap, DELETE `q` from the
  table and ask whether the remaining sub-machine TERMINATES from every
  configuration — if it must always come back to `q`, `q` recurs.  The
  avoid sub-machine is routinely several rungs simpler than the machine
  (plain binary counters running down, closed by an exact power-of-two
  measure).  `ReachStI` relativises that to a proven state invariant, so
  termination need only hold from configurations the machine actually
  reaches.  This is why `docs/WHY_NO_HAMMER.md` is SHARPENED rather than
  refuted: liveness is hard *for a finite abstraction*, and this route
  removes the abstraction for one state.
* **The LADDER** (`Checkers/Ladder*.v`, `Machines/Ladder/`;
  `docs/LADDER_PLAN.md`).  Carries a counter segment as a value-indexed
  rule family `CTR(alph, v)`, with the increment stated as a family over
  the carry index — and, the load-bearing discipline, reads its parameters
  (fill law, terminator, code, step) OFF the machine instead of assuming
  them.  Every assumption it replaced with a measurement moved rows.  It
  boarded its first machines in Stage B, and wave 4l made it the main
  producer: ONE arm-indexing scheme shared by the interior and fill arms,
  plus `LapGlueQuiet`'s closer ported to the `nat` index, so a ladder board
  can certify QUASIHALTING and not only never-quasihalting.  Boards that
  stopped at a single refused arm are listed in
  `tools/coqproject_exempt.txt` rather than left to rot.

## Pointers
- `docs/CLAIMS.md` — what is proved, exactly, including what is not.  If
  this file and that one disagree, that one is right.
- `docs/RESIDUE_MAP.md` — the residue map: how each family of core
  machines fell, and what the map got wrong.
- `docs/REACHST_TIER.md`, `docs/LADDER_PLAN.md` — the two routes that
  closed the last rows.
- `NEXT_SESSION.md` — the PLAYBOOK (compute discipline) and the
  accumulated lab notebook.
- `docs/NGHIST_WAVE5.md`, `docs/IRULESQH_WAVE3.md`,
  `docs/REROOT_LISTC_STAGE.md`, `docs/V5GAP_STAGE.md` — the early
  residue-harvest waves, kept for their design record.
