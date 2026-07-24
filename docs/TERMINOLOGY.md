# TERMINOLOGY — shared vocabulary for the (4,2) quasihalting project

_Living glossary. Written 2026-07-24 to get everyone on the same page about
what "census / D_census / holdouts / residue / hammer" mean, where the sets
came from, and what work each one implies. Numbers are a snapshot; the
definitions are stable._

---

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
  qhb-lex / RepWL at small params; PLAYBOOK Rule 4 keeps it weak on purpose,
  because strengthening the in-walk tier makes the native_compute walk
  ~100× slower per machine). So `D_census` is "resisted the *light* B=2000
  proof", NOT "intrinsically hard".

## `D_census` = 5,156 — and how it partitions

`D_census` is the deferred set: the machines that **resisted the B=2000
census proof**. It splits by mxdys' holdout list (below):

| term | definition | count |
|---|---|---|
| **`D_census`** | machines that resisted the census `QHBound 2000` proof | **5,156** |
| **holdouts** | `D_census ∩ mxdys' 3,713 holdout list` | **27** (`tools/census_holdouts_kept.txt`) |
| **residue** | `D_census ∖ mxdys' 3,713 holdout list` | **5,129** (`tools/census_residue.txt`) |

Verified: `27 + 5,129 = 5,156`; `holdouts ⊆ 3,713`; `residue ∩ 3,713 = ∅`.

The split is by **whose proof failed** — that is what makes it useful:
- **residue** = "our light census tier failed, but the machine is NOT on
  mxdys' can't-do list" ⇒ mxdys decided it ⇒ a **strength gap between us and
  mxdys**, nothing more.
- **holdouts** = "our census tier failed AND it's on mxdys' can't-do list"
  ⇒ both procedures failed, the second being state of the art ⇒ the genuine
  frontier.

## mxdys' holdout list (the 3,713) — provenance and meaning

`BBB4_holdouts_3713.txt` (in the **BBB repo** `carrino/bbb`, copied into
`Coq-BBB4/tools/`) is **mxdys' output**: ~a year ago he ran his best
beeping-busy-beaver (quasihalting) inductive deciders over the (4,2) space,
and the 3,713 are what those deciders **could not decide**. It is the
starting point this whole project grew from — not an arbitrary external list.

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

The **27** are the live residual of that 3,713 (prior waves proved & dropped
~3,686). NOTE: the BBB repo's own `results/open_holdouts_3221.txt` is a STALE
snapshot from 2026-07-06 (pre-harvest) — read the residual off the Coq census
(`census_holdouts_kept.txt`), not that file.

## Two oracles (both UNTRUSTED targeting aids; the kernel re-checks everything)

- **`BB4_verified_enumeration.csv`** (CoqBB5 v1.0.0 release; kept out of git
  for size, see `tools/nghist/BB4_verified_enumeration.README`) — mxdys'
  **HALTING** BB4 pipeline: per-machine `(status, decider, params)` for all
  858,909 machines. A *proxy* for "an exact model exists" (halting is easier
  than quasihalting); use it for closure targeting, not as the last word.
- **BBB repo `results/certs_*`** — mxdys/BBB's actual **quasihalting**
  decisions (decider + witness) for the machines he decided. The more direct
  oracle for the residue: it names the quiet state / the measure he used, and
  is a second independent check on every board.

## The two fronts (and the discipline)

- **Residue → PORT WORK.** mxdys already solved these; we're catching up in
  Coq because our in-walk tier is weaker. Bounded, mechanical, high-
  confidence. Wave-6 `NGramHist` (his history-augmented NGramCPS ported to
  Coq + extended to quasihalting) is the tool; it should drive residue → ~0.
- **Holdouts (27) → RESEARCH WORK.** Beyond mxdys' method by his own year-old
  verdict. Porting his method (NGramHist, oracle params, patterns) should NOT
  be expected to crack them — that is re-running his failed experiment. They
  need different ideas: individual busycoq-style proofs (counter/tower/double
  families) and the one truly-open machine `1RB0RB_1LC1RC_0RA1LD_1RC0LD`.

**Discipline:** point the porting machinery at the residue; keep it *away*
from the 27. If an oracle-driven sweep ever "targets" a holdout, that's a
signal it is aimed wrong.

## Scoreboard snapshot (2026-07-24, wave-6)

- `D_census` = **5,156** = 27 holdouts + 5,129 residue (certified, frozen).
- Wave-6 boarded **964 of the 5,129 residue** (staged, kernel-checked;
  NOT yet subtracted from `D_census`): **434 never-QH** (`NGHStage/`,
  `Forall NeverQuasiHaltsSt`) + **530 R_QH** (`NGHWStage/`, `Forall iqh`,
  `iqh := NonHalt /\ QHBound 2000 /\ QuasiHaltsSt`). Disjoint (overlap 0).
- The scoreboard's two numbers mean: **residue count = a tooling debt vs
  mxdys** (target 0), **holdout count = the open problem** (shrinks slowly by
  hand, may never hit 0).

## `boarded`, and how the residue closes out without a re-walk

`boarded tm := NeverQuasiHaltsSt tm \/ iqh tm`. The closeout is a single
theorem `Forall boarded D_census` built by `app`-chaining the staged per-file
`Forall`s (route A, `docs/NGHIST_WAVE5.md` §5) — **no native_compute census
walk, `D_census` never changes.** We do NOT shrink the 5,156 number inside
`census_decided`; we prove *properties over the frozen 5,156 set* until the
`Forall` closes.

## Eliminating the residue — what "done" requires (the completion plan)

"Eliminate the residue" has a precise meaning: **every one of the 5,129
residue machines carries a kernel-checked `NeverQuasiHaltsSt` or `iqh`
proof**, so that `Forall boarded D_census` closes with only the 27 holdouts
left undischarged. It does **NOT** mean shrinking the 5,156 inside
`census_decided` (that stays frozen — see §`boarded` above), and it does
**NOT** touch the 27 (research front, out of scope here).

Where we are: **964 / 5,129 boarded** (wave-6), ~**4,165 residue machines
still unboarded**. Getting that gap to 0 is bounded, mechanical port work —
mxdys already decided every one of these, so a witness is guaranteed to
exist. The steps, cheapest-leverage first:

1. **Full sweep, not a pilot.** Run `tools/nghist/harvest_sweep.py sweep`
   and `sweepqh` over the *entire* residue (the sweep already dedups against
   the staged manifests). At `(k=2,n=2)` / `(k=4,n=2)` this boards the bulk
   of the counter tail with no human input.
2. **Param escalation on the fail set.** For machines that don't close at
   small params, climb history `k` (2→4→6→8), gram `n` (2→3), `MAXCTX`
   (1200→higher), and fuel. Each rung costs more per machine but boards a
   further slice. Re-emit staged files, `coqc`-validate each, commit per
   compiling artifact.
3. **Always try both shapes.** never-QH (`NGHStage/`, `Forall
   NeverQuasiHaltsSt`) *and* R_QH (`NGHWStage/`, `Forall iqh`). A machine the
   never-QH gate rejects because it genuinely goes quiet is a **wrap/R_QH
   board, not a failure** — route it to `sweepqh`.
4. **Pattern measures for the liveness-lag tail.** Some machines *close*
   (safety: finite augmented set ⇒ NonHalt) but the lex gate can't rank them
   (liveness lags closure — the safety≠liveness gap). These need `NgPattE`
   pattern measures; this is the residual the blind sweep leaves.
5. **Oracle-target the stubborn remainder.** Use
   `BB4_verified_enumeration.csv` (halting proxy ⇒ an exact model exists) +
   BBB `results/certs_*` (the actual quiet state + measure mxdys used) to
   *set* params / *pick* the measure instead of searching blindly. Because
   the residue is mxdys-decided, the oracle names a witness for every one.
6. **Wire the closeout (Route A).** When every residue machine is staged,
   `app`-chain the per-file `Forall`s into `Forall boarded D_census` in a
   `Census/Assembly.v` — **no native_compute census walk, `D_census`
   unchanged.** That closes the residue front.

**Try the shortcut first.** If the hammer (next section) works, steps 4–5 —
the expensive per-machine measure search and oracle targeting — mostly
evaporate: one uniform determinism lemma boards the bulk, and only genuinely
non-determinizing machines fall through to the measure/oracle path. So the
rational order is: cheap full sweep (1–3) to knock down the count, **the
out-degree-vs-history probe** to decide whether to build the hammer, then
either the hammer or the measure/oracle grind for whatever remains.

## HYPOTHESIS — "the hammer" (a uniform residue-killer, not yet built)

We would like one uniform procedure that clears the whole residue without
per-machine measure search. The current best candidate, marked clearly as a
**hypothesis to test, not a result**:

Because the residue is mxdys-exact, don't *search* for a lex certificate —
make the augmented closure **deterministic** (out-degree exactly 1: history
determines the incoming far cell) and *read* the answer. A deterministic
closed augmented set is a **ρ-shape** (a tail running into one cycle), and
then quasihalting is immediate: **states on the cycle recur (never-QH iff
every visited state is on the cycle); states only on the tail are quiet
(QH, bound = tail length).** This is sound for exactly mxdys' reason —
determinism *is* "models the forward behavior exactly" — so it dissolves the
safety≠liveness trap rather than searching around it.

Status / risks: (a) it is a NEW `Closure.v` soundness lemma keyed on
"closure is deterministic", not "find a certificate" — not yet written
(but simpler than the lex machinery); (b) determinism is STRONGER than
mxdys' reachable-set exactness and may need higher history than he used —
the pilot showed out-degree ≈1 (26/33 nodes) at history=2, so it is *close*
but unconfirmed at scale. **The decisive cheap experiment: sweep history on
a residue sample and plot out-degree vs history.** If a bounded history
drives ~every machine to out-degree 1, the hammer is real (and most of the
oracle-param / pattern-measure work becomes unnecessary). If some machines
never determinize, those are the tell — residual far-cell uncertainty,
i.e. not as exact as the halting result implied.

## Pointers
- `docs/NGHIST_WAVE5.md` — wave-6 design, safety≠liveness, oracle, yields,
  the two wire routes.
- `NEXT_SESSION.md` — PLAYBOOK (compute discipline) + the wave-6 section +
  the wave-7 oracle-drive plan.
- `docs/IRULESQH_WAVE3.md`, `docs/REROOT_LISTC_STAGE.md`,
  `docs/V5GAP_STAGE.md` — earlier residue-harvest waves.
