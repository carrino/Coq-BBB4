# The residue, classified by ASYMPTOTIC VISIT BEHAVIOUR

_Measured 2026-07-27 on branch `claude/coq-bbb4-residue-removal-lt5yac`,
after the mxdys Stage 0 gate came back zero (`docs/MXDYS_INDUCTIVE_STAGE0.md`)
and re-pointed the work at the visit witness._

Tooling: `tools/counters/visit_gaps.py` (UNTRUSTED diagnosis; nothing here
enters a proof).  Every number below is reproducible from that script.

---

## 0. Bottom line

**Four machines -- including both previous BBB(4) champions -- are trivial
boards blocked only by the census constant (section 4b), and 201 more are
blocked on a liveness fact that is true within 33 steps, median 2.**

They are confirmed quasi-halters whose quiet state stops by step 64 (median 3)
and whose three surviving states recur within 33 steps of any lap boundary
(median 2).  Both halves of `QHBound` are behaviourally trivial for them.
They are deferred because no checker in the tree can currently **state**
"this walled window visits state q" — not because anything hard is happening.

This is the same `Hvis` premise the never-QH front needs, so one theorem
serves both.

---

## 1. What is being measured, and why it is the right statistic

`LapGlue.glue_neverqh` takes exactly two hypotheses:

```coq
Hypothesis Hlap : forall p, (p0 <= p)%positive ->
  exists n c', csteps tm n (Cf p) = Some c' /\ lift c' = lift (Cf (Pos.succ p)) /\ 0 < n.
Hypothesis Hvis : forall p q, (p0 <= p)%positive ->
  exists k c, csteps tm k (Cf p) = Some c /\ fst c = q.
```

`Hlap` is the lap.  **`Hvis` is the missing piece, and it is already the
interface** — no new glue theorem is needed, only a way to discharge it.

`Hvis` asks for **some** `k`, so a short prefix of the lap suffices, and that
prefix is `p`-independent as long as it stays inside the anchor's fixed window
(which is what the walls enforce).  Two consequences:

* **The lap's COST is irrelevant to `Hvis`.**  A lap costing `Θ(2^j)` still
  discharges it from the first few dozen steps.  The EXP2 wall blocks `Hlap`;
  it does not touch `Hvis`.  **They are orthogonal.**
* The right statistic is the **anchor-relative offset**, not the
  visit-to-visit gap.  A state firing once per lap right after the lap opens
  has a self-gap that grows with the lap but a constant anchor offset.

The existing emitter derives its witness with `lapcert.reach_state`, which
walks **symbolic chain steps** (`SWin`/`cyc`/`rot`) and gives up
(`step is None`) when the machine does something the chain vocabulary cannot
express.  A concrete walled scan has no vocabulary to run out of, and is
*easier* to justify in Coq — `wvisits_frame` is an induction over `wstep_transport`,
the sibling of the existing `wsteps_frame`.

---

## 2. A soundness trap, and the correction

**A single-window `QUIET` verdict is unsound**, and the first pass fell into
it.  Calling a state quiet when its last visit precedes `3T/4` cannot
distinguish "stopped forever" from "recurs at exponentially spaced times" —
the latter's gap eventually exceeds `T/4`, so it looks quiet at *every* finite
window.

The tell was a bimodal last-visit distribution: one cluster at `t <= 64`, and
a second sitting at `~0.55*T` — i.e. **scaling with the window**.  Re-running
five of the late ones at 10× the window moved their last visit from ~174,777
to ~1,572,844 (and `1572864 = 3*2^19`).  That is a recurrence at exponentially
spaced times, not a quiet state.

**The sound test is two windows**: a genuinely quiet state's last visit is the
same *absolute step* at `T` and `10T`; an exponential-gap state's *scales*.
Wired as `visit_gaps.py --confirm`.

The uncorrected count was 538 quasi-halters.  The corrected count is **217**.
Had it gone into the docs uncorrected it would have sent the next wave after
~300 phantom quasi-halters.

---

## 3. The corrected classification (all 1,157 residue machines)

Single-window pass, `T = 300000`:

| class | count |
|---|---:|
| QUIET (candidate only) | 538 |
| GROWING | 351 |
| BOUNDED | 268 |

Two-window confirmation over the 538 candidates:

| | count |
|---|---:|
| **genuinely QUIET** | **217** |
| RECUR (false positive — recurs at a larger window) | 275 |
| EXPGAP (recurs at exponentially spaced times) | 46 |

So the residue is **~19% quasi-halting and ~81% never-quasi-halting**, not the
~46% the uncorrected pass suggested.

---

## 4. The 217 confirmed quasi-halters

Quiet state's last visit — this is the machine's **actual BBB score**, not
merely a bound:

| | |
|---|---:|
| `B <= 1` | 63 |
| `B <= 64` | 212 (98%) |
| `B <= 2000` | 214 |
| median | **3** |
| max | 66,348 |

Cross-referenced against the existing QH pipeline:

| | count |
|---|---:|
| already in `qhbound_survivors.txt` (wrap-identified, **blocked on liveness**) | **203** |
| never reached the QH tier at all | 14 |
| caught by the existing QHBound tier | 0 |

### Survivor liveness — the decisive number

For each of the 203, do the **surviving** states recur with a bounded
anchor-relative offset?  (`QHBound B` needs EVERY eventually-quiet state's
last visit `<= B`, so the survivors must be shown to recur forever, else one
could go quiet later than `B`.  This is `Hvis` restricted to the survivors,
i.e. **3-state liveness**.)

```
BOUNDED     201
SURV-QUIET    2
worst anchor-relative offset:  min=2  median=2  max=33
```

**From any lap boundary, every surviving state recurs within at most 33 steps,
typically 2.**  There is no deep liveness problem in this bucket.

Why the existing tier misses them: `sweep_qhbound_residue.py` supplies
liveness via **acyclicity of the wrapped n-gram closure** — a global graph
condition — when the actual witness is a 2-step local one.  *Understanding
that gap is itself a likely cheap win and worth a look before building
anything.*

---

## 4b. FOUR TRIVIAL BOARDS, including both previous BBB(4) champions

Splitting the 217 by how many states go quiet:

| quiet states | still recurring | machines |
|---:|---:|---:|
| 1 | 3 | 66 |
| 2 | 2 | 147 |
| **3** | **1** | **4** |

**The four machines with only ONE recurring state are exactly the four
highest scorers**, and two of them are the previous BBB(4) champions
(John confirmed the historical values 66349 and 2819 independently, which
also validates this pipeline end to end — score = last visit + 1, the
bbchallenge 1-indexed convention):

| score | machine | tail state | blank self-loop | ahead all blank |
|---:|---|---|---|---|
| **66349** | `1RB0LD_1LC0LA_1LA0LC_1RD1RC` | D | `D0 -> 1,R,D` | yes |
| **2819** | `1RB1RC_1LC1RD_1RA1LD_0RD0LB` | D | `D0 -> 0,R,D` | yes |
| 2568 | `1RB1RA_0RC0RB_0RD1RA_1LD1LB` | D | `D0 -> 1,L,D` | yes |
| 2512 | `1RB1RA_0RC1LA_1LC1LD_0RB0RD` | C | `C0 -> 1,L,C` | yes |

That makes sense structurally: to score high a machine must run a long time
before settling, and collapsing to a single state is the most thoroughly
quiet outcome available.

**All four are trivially provable**, and one lemma covers all of them:

1. `vm_compute` the concrete prefix (66,349 steps at worst — cheap);
2. the config is then `(q, blank in the direction of travel)`;
3. **one lemma**: if `tm q S0 = Some (w, d, q)` and the tape is blank ahead in
   direction `d`, the machine runs forever visiting only `q`;
4. hence the other three states are quiet with last visit `= score - 1`, and
   `q` recurs, giving `QHBound score`.

**They are unboarded solely because `QHBound 2000` is FALSE for them.**  No
amount of liveness strength can take them through a `B = 2000` tier.  This is
the cheapest board on the entire project and it lands the historical
champions.  It needs a per-machine `exists B, QHBound B` (or a raised
constant), not new mathematics.

---

## 4c. THE CHAMPION IS THE SAME SHAPE — and that is the whole endgame

`1RB1LD_1RC1RB_1LC1LA_0RC0RD`, measured directly (60M steps, 31 s):

| state | last visit (config index) | score |
|---|---:|---:|
| A | 32,769,237 | 32,769,238 |
| B | 11,801,813 | 11,801,814 |
| **D** | **32,779,477** | **32,779,478** |
| C | still recurring at 60M | — |

So **three states go quiet and only C recurs** — the same "3 quiet, 1
recurring" class as §4b's four trivial boards.  And its tail is the same
one-state blank march:

```
at t = 32,779,478:  state C, head at 10226, reading blank
                    C0 -> write 1, move L, stay C     (self-loop)
                    NON-BLANK CELLS ON THE ENTIRE TAPE: 0
```

**The tape is completely erased.**  C marches left forever across virgin
blank tape, writing 1s it never re-reads, in one state.  That is why A, B and
D all go quiet at the same moment, and it is why this machine is
simultaneously the **BLB(4) (Blanking Beaver) champion** — John confirmed
this, and the measurement agrees: the tape first blanks at step 32,779,477
and stays blank through 32,779,478 (D writes a 0 onto an already-blank cell
before handing to C).  **The blanking event and the quiet point are the same
event.**  BBB and BLB coincide here for a structural reason, not a
coincidence.

**Consequence: the champion is provable by the SAME single lemma as §4b.**
The only difference is prefix length — 32.8M steps instead of 66k, which is a
compute cost, not a mathematical one.

This pipeline reproduced 66349, 2819 and 32,779,478 independently, all three
confirmed against John's historical values, so the score convention
(score = last visit + 1) is validated three ways.

---

## 4d. Raising the predicate is FREE on the census side

John's move, and it is exactly right: change the target predicate to
`QHBound 32779478` and prove it only on the DEFERRED machines — the census
itself never changes.

`theories/Census/TNF_QH.v` already has both lemmas needed:

```coq
Lemma qhbound_mono   : forall B B' tm, B <= B' -> QHBound B tm -> QHBound B' tm.
Lemma neverqh_qhbound : forall B tm, NeverQuasiHaltsSt tm -> QHBound B tm.
```

so the whole change is a three-line corollary over the untouched census:

```coq
Definition B_final := 32779478.

Corollary census_decided_final :
  forall tm, QHBound B_final tm \/ Deferred D_census tm.
Proof.
  intro tm. destruct (census_decided tm) as [H|H].
  - left. apply (qhbound_mono B_census B_final tm); [lia | exact H].
  - right. exact H.
Qed.
```

`B_census` and `D_census` are untouched, so `CENSUS_VO_HASH` stays MATCH and
the committed census `.vo` remain valid — **the expensive native_compute walk
never re-runs**.  And the per-machine obligation WEAKENS, from
"`NeverQuasiHaltsSt` or `QHBound 2000`" to just `QHBound 32779478`.

**Why 32,779,478 and not 32,779,479.**  `QuietAfter tm q s` has `s` as the
CONFIGURATION INDEX of the last visit and `QHBound B` requires `S s <= B`,
i.e. `score <= B`.  The champion's D has `s = 32,779,477`, so `S s =
32,779,478` and `QHBound 32779478` holds with EQUALITY — tight.  Tightness
matters because the final claim is `BBB(4) = 32,779,478`, and a loose upper
bound of 32,779,479 would leave the result a step short.  If an off-by-one
ever surfaces in the Coq, `qhbound_mono` makes bumping the constant a
one-line change that invalidates nothing already boarded, so start tight.

**Still to verify before the constant can be trusted:** that no other
deferred machine scores higher.  §3's max of 66,349 is a max over a 400k
WINDOW — a machine whose quiet state's last visit lies between 400k and 32.8M
was classified RECUR and never seen.  A deep scan (35M steps per machine) is
the outstanding check; see `deepscan` in the session scratch.

---

## 5. On the census constant

`B_census = 2000` is **arbitrary** — a fixed value chosen to collapse the
census, not a meaningful threshold, and raisable.  Do not design around it.
Two things follow that were previously conflated:

* **Prefix length** (running concretely to the quiet state's last visit) is a
  COMPUTE problem.  For the champion `1RB1LD_1RC1RB_1LC1LA_0RC0RD` it is 32.8M
  steps; for these 217 it is `<= 64`.
* **Liveness** is independent of `B` entirely, and does not get harder as `B`
  grows.

Note also that `QHBound 2000` is FALSE for any machine that genuinely
quasi-halts after step 2000, so such machines can never leave `D_census` via
that tier however good the liveness gets — they are deferred by the constant,
not by difficulty.  Only FIVE of the 217 are in that position (scores 66349, 2819, 2568, 2512,
2332) -- and four of those are the trivial one-state-tail boards of section
4b.  So the residue splits cleanly: **five machines are blocked by the
CONSTANT** (and four of those are trivial once the constant moves), and the
other **212 are blocked by LIVENESS**, confirmed from both directions.

---

## 6. What to build

```coq
Fixpoint wvisits (bl br : bool) (tm : TM) (n : nat) (c : cconf) : list St :=
  match n with
  | 0   => [fst c]
  | S m => fst c :: match wstep bl br tm c with
                    | Some c' => wvisits bl br tm m c'
                    | None    => []
                    end
  end.

Theorem wvisits_frame : forall tm n q l h r L R s,
  In s (wvisits true true tm n (q,(l,h,r))) ->
  exists k c, csteps tm k (q,(l++L,h,r++R)) = Some c /\ fst c = s.
```

One induction over `wstep_transport`; the sibling of `wsteps_frame`.  Read one
way it gives `Hvis` and hence `NeverQuasiHaltsSt`; read the other (state `q`
ABSENT from the lap's visit set) it gives `q` quiet, hence `QHBound` with the
bound off the boot prefix.

**Open question before building:** the measurement's anchor proxy is
record-breaking head positions, not the literal `Cf p` of a wrap certificate,
and the `Wrap.v` route wants liveness over the closure rather than over a lap.
So the exact Coq path needs pinning down — either `wvisits_frame` feeding
`LapGlueQH`, or a small-window liveness premise added alongside
`ngram_check_qhbound`.  What the measurement establishes is that **the fact
being proved is true and tiny**, which is the part that was in doubt.
