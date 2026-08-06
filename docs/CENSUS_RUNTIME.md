# Why the census walk is slow, and how to make it fast

_Investigation notes, 2026-08-04.  Comparison target: Coq-BB5 (this
org's fork), whose BB(5) proof enumerates 181,385,789 machines in
~45 min on 13 cores (~10 core-hours) and whose BB(4) proof covers the
same 4-state halting space (858,909 machines) in ~30 seconds.  Our
census: 3,995,005 nodes, measured 16-24 h at `WALK_JOBS=2` (~32-48
core-hours, memory-capped at 2 jobs because heavy units peak ~11-12 GB
even on a 32 GB box).  Per machine that is ~30-40 ms vs BB5's
~0.19 ms — a 150-200x gap.  Untrusted analysis; nothing here touches
the proof.  Probe scaffolding: tools/probes/._

## Where BB5's speed comes from (per-decider counts from its README)

BB5 decides **96.7%** of all 181M machines with `loop1_decider 130`
(`Deciders/Decider_Loop.v`): ONE ≤130-step simulation pass that conses
each `(ListES, Z)` config onto a plain history list — no hashing, no
maps, no snapshot keys — then ONE backward scan (`find_loop1`) that
detects **both in-place and translated loops**, comparing state+read
symbol first so mismatched rewinds cost ~nothing.  The decider is
verified directly: what it computes is what the lemma consumes, so
nothing is ever re-derived.  The NGramCPS tiers that take the next 3%
are incremental-fixpoint (below).  Escalation (loop 4100, RepWL, FAR,
WFAR, table) touches 0.03%.

## Where our time goes (tier census from tools/census_ladder.c,
## measured over all 3,995,005 nodes)

| tier | nodes | share |
|---|---|---|
| halt | 249,692 | 6.2% |
| in-place cycles | 1,029,749 | 25.8% |
| translated cycles | 2,286,534 | 57.2% |
| n-gram ladder | 196,595 | 4.9% |
| deferred/proven lookups | ~232,435 | 5.8% |

Per popped machine, `Census/Decide.v : decide_easy` runs, in order:

1. `find_halt` gas 130 — simulation pass #1.
2. `scan_cycle` gas 512 — pass #2, and **per step**: two `N`-modular
   multiplications (rolling hash) + a `PositiveMap.find` + a
   `PositiveMap.add` storing a full config snapshot.
3. on a cycle hit, `cycle_leaf_check` re-simulates `n1` and `n1+p`
   steps from c0 — passes #3 and #4 (`2*n1+p` total steps).
4. otherwise `scan_records` gas 512 — pass #3 (full 512 steps for
   every non-halter).
5. up to 2 tcycler candidates per side, each re-simulating via
   `tc_measure_W` (`n1+P` steps) plus the verified lap check — and the
   whole candidate machinery AGAIN on `mirror_tm tm`.
6. three `PositiveMap` lookups (cheap).
7. the ngram ladder for whatever's left.

So the 83% bulk (cycles + translated cycles) pays 3-6 redundant
simulation passes with heavyweight per-step constants, where BB5 pays
one pass plus one scan.  That alone is a 10-30x per-node handicap on
the bulk.

The 4.9% ngram slice is worse.  `Checkers/NGram.v : ng_grow` runs
`ng_explore` — a **from-scratch** closure exploration (fuel 200,000)
materializing the entire visited list — once per growth round, up to
512 rounds, restarting whenever the gram sets grew; then
`closure_check_neverqh` (Closure.v) explores AGAIN, rebuilds the trie
(`apool`), and runs an O(n²) `compute_ranks` peeling per state.  Every
machine caught at rung k also pays rungs 1..k-1 failing first
(~46 ms/pop measured, NEXT_SESSION 2026-07-18).  BB5's
`Decider_NGramCPS.v` maintains ONE abstract state and feeds only the
newly-added midwords through `update_AES` to fixpoint — work
proportional to final closure size, once, no restarts.

**Memory:** each exploration holds the full `seen : list cconf` + a
fresh `PositiveSet` live; 512-round restarts churn that at high rate;
`compute_ranks` holds rank maps + stuck lists of the same order.  The
OCaml runtime never returns major-heap memory, so a unit's RSS
ratchets to its worst pop and stays there — hence 11-12 GB heavy
units, hence `WALK_JOBS=2`, hence CPU inefficiency converting 1:1
into wall-clock.

## What is intrinsic to quasihalting (the honest part)

- No `cnt=1` pruning and no free full-machine leaves: 4.65x more
  nodes than halting BB4 (3,995,005 vs 858,909), and the extra nodes
  are exactly the long-running ones.
- `QHBound` needs last-visit bounds, not just nonhalt: the cycle tiers
  must locate the cycle start, the tcycler needs the lap/window
  argument, and quasihalting machines need per-state bookkeeping.
- Call the intrinsic multiplier ~5-10x vs halting BB4.  The remaining
  ~20x+ is implementation, i.e. recoverable.

## Options, ranked by leverage

1. **Port BB5's one-pass loop decider** (attacks the 83% bulk,
   ~10-20x on that slice).  Single simulation pass with history;
   combined in-place/translated detection; track per-state last-visit
   indices in the same pass to discharge `QHBound n1`.  Soundness is a
   port of BB5's `verify_loop1` lemmas plus our existing
   `cycle_qhbound`/`tcycler_laps` machinery.  This also deletes the
   per-step hash+map allocation, which is a big slice of both time and
   the RSS ratchet.

2. **Make the ngram closure incremental** (attacks the 46 ms pops and
   the memory spikes).  Replace `ng_grow`'s restart rounds with a
   BB5-style worklist that carries `(gram sets, visited contexts,
   frontier)` across growth and re-explores only from newly enabled
   contexts; verify the final closure once.  The verified side
   (`closed_b` + ranks) is unchanged — only the untrusted search gets
   faster; alternatively keep `ng_grow` and only fix the restart
   (carry `seen`/`sp`/frontier between rounds).

3. **Winning-rung table** (kills failed-rung burn on the 196K ngram
   machines; BB5's `tm_decider_table` trick).  The sweep TSVs already
   record which rung catches each machine; emit a
   `PositiveMap tm_enc -> rung#` table, have `decide_easy` try the
   table's rung first, fall through to the full ladder on miss (so a
   wrong/missing entry costs nothing in soundness).  Also shrinks the
   25-30-min GG heavies toward container-window size.

4. **Cheap tactical fixes** (small, low-risk, additive):
   - move the three map lookups ahead of tiers C/T (lookup machines
     skip all scans);
   - escalate `loop_gas` 130 -> 512 in two rungs instead of flat 512
     (max halting step in this space is 107);
   - `cycle_leaf_check`: verify `csteps p a = Some a` from the stored
     anchor instead of re-running `csteps (n1+p) c0` (halves that
     check);
   - share one record walk between the two mirror sides (already
     half-done: `scan_records` returns both; the tcycler *checks*
     still duplicate).

5. **Memory mitigations, zero proof change** — MEASURED AND LANDED
   (2026-08-04, GG_1LC_1LB on a 32 GB desktop, 99% CPU throughout):

   | `OCAMLRUNPARAM` | peak RSS |
   |---|---|
   | (untuned) | ~11-12 GB, ratcheting |
   | `o=80,O=150` | 8.19 GB |
   | `o=40,O=60` | 6.76 GB, flat from minute 3 |

   The ratchet is real and mostly reclaimable garbage: compaction
   (`O`) is what returns memory to the OS.  `o=40,O=60` is now the
   Makefile default (`WALK_OCAMLRUNPARAM`), and `WALK_AUTO` assumes
   ~7 GB/unit -- a 32 GB box goes from `WALK_JOBS=2` to `4`, i.e.
   16-24 h -> ~8-12 h with zero proof changes.  Further still: split
   the remaining heavy units one level deeper
   (tools/gen_gsplit_heavy.py) — smaller subtrees also peak lower.

6. **Keep the proven-tier conveyor** as-is (it's the documented
   "right way" and already emptied the residue), but note it cannot
   speed up the generic bulk — only options 1-2 do that.

With 1+2+3 the walk should approach BB5-class per-node cost times the
intrinsic ~5-10x, i.e. **tens of minutes on a desktop instead of
16-24 h**, and option 5 alone may double throughput this week.

## Measured optimization results (2026-08-04, this branch)

All numbers vm_compute in the container probe harness (native scales
similarly); verified checkers untouched; corruption suite green.

| probe | before | after | change |
|---|---|---|---|
| rank-tier catch (rung (3,0)) | 0.73 s | 0.25 s | 3x |
| full pipeline, holdout-class | 1.08 s | 0.56 s | 2x |
| full pipeline, champion fallthrough | 1153 s | 85 s | 13.6x |
| pipeline, translated cycler | 48 ms | 11 ms | 4.4x |
| pipeline, in-place cycler | 8 ms | ~0 ms | -- |
| GG_1LC_1LB subtree walk, per pop | >=515 ms (never finished 8,192) | 71 ms (512 pops measured) | >=7x |

What landed:
1. `Decide.v`: lookup tiers moved ahead of the scans; cycle/TC block
   escalates gas 130 -> 512 (`scan_ct`).  One sound leaf-kind change
   (a wrap-QH machine TC-caught R_Leaf instead of R_QH; tree shape
   unchanged), tracked in Tests/Census_Corruption.v.
2. `RankSearch.v`/`RepWLSearch.v` (untrusted internals): Kosaraju SCC
   replacing per-node double-reach (O(V*E) -> O(V+E) per proc round);
   PositiveMap condensation ranks replacing list nth/set_nth
   (O(#comps) -> O(log) per edge); rfuel 4V+4 -> 8V+8 for the DFS
   event budget.

Reference desktop numbers (32 GB, `o=40,O=60`): GG_1LC_1LB complete
in 1:56:08 at 6.76 GB flat before these changes; projected ~15-20 min
after, x4 jobs => full walk ~2-3 h (from 16-24 h).

NOTE: any decider change invalidates the committed census .vo cache
(input-hash mismatch) -- certifying this branch requires one full
`make census-verify` walk on the box.

## Second-round measurements (same day, later)

The C mirror (tools/census_ladder.c) walks the ENTIRE 3,995,005-node
tree -- same tiers, same rungs -- in **60 s single-core at 3 MB RSS**.
That is the ceiling: ~2,000x the current native Coq walk.

Slice attribution on the heavy GG_1LC_1LB subtree (512 pops, vm):
scans/TC-checks 12.3 s over 437 cheap pops (~28 ms each; complex
guarded-window TCs fall through the one-pass scan to the old
fallback), ladder 21.4 s over 75 machines (~285 ms each, dominated by
the WINNING rung's own cost).  Consequences, measured:

- One-pass loop scan (landed): neutral so far in vm -- its candidates
  catch simple TCs but the guarded-window TCs still take the old
  path.  Anchor reduction (phase-equivalent early anchors) landed too.
- Winning-rung hint mechanism (landed, `HintMap` in Decide.v +
  tools/gen_hints.py): measured only ~10% on the heavy slice because
  hints cannot skip the winning rung itself.  Wired with an EMPTY map
  in Run.v; generate a table only if a targeted use appears.
- rank_tier lex-check dedup via `ngram_check_neverqh_lex_with`
  (landed): avoids the checker's internal re-grow.

## Remaining leverage (not yet landed)

1. **Incremental NGram closure** (BB5 `update_AES` port): the winning
   rung's grow-restart rounds are now the single largest ladder cost
   (~0.1-0.4 s vm per late-rung catch); a worklist fixpoint makes it
   proportional to final closure size, once.
2. ~~Window-aware one-pass candidates~~ LANDED: [lp_rec_cands]
   replicates tc_pairs' record-pair rule from the same one-pass
   history, so guarded-window TCs no longer fall through to the old
   scan block.  Measured: scan-side slice 12.3 -> 7.7 s (28 -> 17.6
   ms/pop vm); full heavy slice 36.4 -> 28.3 s.
3. LANDED (measured same-instance: rank catch 0.263 -> ~0.20 vm,
   walk slice ~3-7%): [close_root_spec] proves the exploration's
   closure invariant directly, deleting the runtime [closed_b] +
   [apool] x2 + [mem] re-verification from all three checkers; and
   [condensation_rank]/[node_rank] became one topological pass
   (Kosaraju order / DFS finish order) instead of fixed-point
   relaxation.  The remaining ladder cost is SPREAD (certs ~4x48ms
   vm, rules machinery, verified scan) -- no single hotspot is left,
   which is the signature of the allocation/representation floor.
   The next real multiplier is the primitive-representation rewrite
   (below), not more structure tweaks.

3b. **Primitive-representation rewrite (the flagship next arc)**:
   the C mirror runs the SAME closures/tiers over the whole tree in
   60 s; the Coq checkers are ~1000x slower per closure because
   every hot structure is persistent (PositiveMap/Set, lists, nat).
   Coq's Uint63/PArray primitives work under vm/native_compute;
   rewriting the NGram closure + rank machinery + scan tiers on them
   targets 10-50x on the ladder slice and would retire the .vo cache
   honestly.  Old plan text follows for reference:

   (superseded) **Closure.v verified-pass restructure** (next census multiplier,
   plan): (a) prove the worklist invariant of [close] directly
   (everything reachable is in [seen]; successors of processed nodes
   are in [seen ++ todo]; empty todo => closed) so [closed_b], both
   [apool] trie rebuilds, and [mem] become redundant and deletable;
   (b) have [close] also emit the edge list so [lex_ok]/[rank_ok]
   stop recomputing succs per state (currently up to 4 extra
   exploration-equivalents per catch).  Touches proved code:
   closure_check_neverqh/_lex/_fuel and their soundness sections.
   Estimated 2-3x on the ladder slice (the walk's dominant cost).
4. qhb-lex cert memoization across states (helps regen fallthroughs).
5. Machines tree beyond IRules: profile the slowest remaining batch
   families from a clean-build log (Bulk/ListC/Counters/NGramHist);
   the IRules experience says generated cert-replay families hide
   one-or-two allocation patterns each.

## Post-validation decision: the .vo cache

Base build measured 19m51s wall after the IRules fixes.  If the
re-walk lands <= ~2 h: drop the committed census .vo, CENSUS_VO_HASH,
tools/census_cache.py, and the census/census-verify split -- the
repo becomes clone -> make -> make census -> Print Assumptions, like
Coq-BB5, and the verification ladder's paranoid rung becomes the
default.  If it overshoots (4 h+), keep the cache until the Closure.v
round lands.

## Full re-walk, measured end-to-end (2026-08-05)

`time make census` on the 32 GB desktop, WALK_JOBS=4, this branch's
decider (without the reverted 97c7aa5 round): **real 819m50s
(13.7 h), user 3064m37s (51 core-hours)**.  Versus the pre-branch
16-24 h at 2 jobs (~32-48 core-hours): wall ~1.4x better, core-hours
WORSE.  Diagnosis: the solo-unit gains (~2.5-3.5x) are real but
4 workers x 6.8 GB of allocation churn saturate memory bandwidth,
inflating every unit -- the workload is allocation-bound, not
CPU-bound, so added parallelism bought little.  Consequences:
(a) the Uint63/PArray packed-representation arc is THE fix (less
allocation = faster solo AND less contention -- compounding);
(b) try WALK_JOBS=3 on the next rewalk (may match 4's wall time at
fewer core-hours); (c) the committed-.vo cache stays -- verifiers get
the ~20 min build, the ~14 h re-derivation is the documented paranoid
rung.  Projection discipline: future claims get measured under
4-way contention, not extrapolated from solo vm probes.

## The packed-representation arc, gated and measured (2026-08-05)

All numbers below: Coq 8.18.0 (stock apt, vm_compute), this container,
same machine and same gram sets on both sides of every A/B, each stage
looped 200-2000x so per-call cost clears timer noise.  New probes:
`ProbePack.v`, `ProbeSplit.v`, `ProbeRankAdj.v`, `ProbePackRank.v`,
`ProbeIntern.v`.

### Gate 1 -- does `coqchk` re-check primitives?  YES

`coqchk` 8.18 fully re-checks `Uint63` and `PArray`: a 250,000-op
int63 chain, a 100,000-update `PArray` chain, and an exhaustive
cross-validation of `land/lor/lxor/add/mul/sub/eqb/ltb/lsl/lsr`
against an independent `Z` model (all agree -- so the checker does not
merely accept the primitives opaquely, it computes them, correctly).
"Modules were successfully checked", and the three extra reports stay
`<none>` (type-in-type, unsafe (co)fixpoints, assumed positivity).
Cost: ~9 s on top of a ~36 s stdlib-closure baseline.  The
verification ladder's coqchk rung survives the arc.

### Gate 2 -- the axiom footprint.  DOES NOT survive

`Print Assumptions` lists the primitives THEMSELVES as axioms, for
purely computational use that never touches a spec lemma:

    int : Set          land, lor, lxor, lsl, lsr, add, sub, eqb
    array : Type       make, get, set, default

So `Print Assumptions BBB4_value` would go from
`functional_extensionality_dep` alone to that plus ~8 (ints only) or
~13 (ints + arrays) primitive declarations.  Separately, `coqchk -o`
reports assumptions **environment-wide, not by dependency**: merely
`Require`ing the modules makes it print all ~40 `Uint63`/`PArray`
spec axioms (`lsr_spec`, `land_spec`, `eqb_correct`, `get_set_same`,
...) -- verified by a file that requires them and proves only
`1 + 1 = 2`.  Both published checks (README.md:66, CLAIMS.md:62,
VERIFYING.md:74) change their output.

Note this is unavoidable, not a matter of proof style: the spec
axioms can be dodged (prove pack/unpack facts by conversion over the
finite context domain instead of by rewriting with `land_spec`), but
the primitive *declarations* cannot -- they have no body, so anything
computing with them depends on them.

### Where one n-gram catch actually goes

`ngram_check_neverqh m6 6 800` = 4.87 ms/catch (29-node closure),
split by stage:

| stage | ms | share |
|---|---|---|
| ranks + `rank_ok`, 4 states | 1.81 | 37% |
| `ng_grow` (untrusted search) | 0.66 | 14% |
| `cvisits` prefix rescan, 4 states | ~0.72 | 15% |
| `csteps` prefix, run twice | 0.36 | 7% |
| `closed_b` | 0.21 | 4% |
| `ng_explore` (one closure) | 0.19 | 4% |
| seed checks, `mem`, misc | ~0.92 | 19% |

Rows without a tilde are direct `Time Eval vm_compute` measurements of
that stage in isolation; the two tilde rows are inferred from the
residual (isolated stages sum to 2.79 of the 4.87 ms) and from
`csteps` costing 0.18 ms per `t`-step prefix pass.

Exploration is 4%.  The rank machinery is the hotspot, and
`cvisits` re-simulating the whole `t`-step prefix once per state is
free money (one pass suffices).

### The three-way A/B on the verified stage

Closure + `closed_b` + all four rank checks, same 29-node instance.
Each variant is quoted against the baseline measured in ITS OWN run
(the `cconf` baseline drifts 2.03-2.47 ms run to run, so cross-run
ratios would be worth ~20%):

| representation | baseline | variant | speedup |
|---|---|---|---|
| interned indices (NO primitives) | 2.03 ms | 0.82 ms | **2.5x** |
| packed int63 (primitives) | 2.47 ms | 0.34 ms | **7.4x** |

Rank stage alone: 1.81 -> 0.23 ms packed (7.9x).  So the primitives
buy roughly **3x over the best axiom-free alternative**, not 7x --
that ratio is the actual price of the footprint claim.  Both variants
are first cuts and both have headroom; the gap is the load-bearing
number, not either absolute.

Interning is item 3(b) done properly: assign each context an index
1..n once (paid per node, not per membership test), have the closure
emit `(index, state, successor indices)`, and key ranks by the short
index.  Two dead ends measured on the way: a prebuilt edge map still
keyed by `cconf_enc` buys only 1.14x (encoding the key costs what
recomputing `succs` costs), and swapping the trie for a list under
`ceqb` is 3.2x WORSE -- the trie is the right structure for `cconf`.
The win is short keys plus carried edges, not the container.

### LANDED: `theories/Checkers/ClosureIdx.v` (axiom-free, unwired)

The interned engine as a real checker, not a probe: one verified
`edges_of` pass computes `succs` once per node, resolves each
successor to (index, state), and fails if any successor escapes the
pool -- so its success IS closedness (`edges_closed`).  All four
states' rank checks then run off that one edge list, and the rank
assignment is a PARAMETER (`mkr`), so the untrusted search is
formally outside the soundness argument.  Soundness is not re-argued:
`edges_of` success is converted to `closed_b`/`rank_ok` and the
existing `closure_invariant`/`rank_find` finish it.
`Print Assumptions idx_check_neverqh_sound` = `functional_
extensionality_dep`, zero `Admitted`.

Measured on the REAL checkers (`ProbeIdxCheck.v`), same machine, same
gram sets, same `close` search, 200 iterations:

| rung | `closure_check_neverqh` | `idx_check_neverqh` | speedup |
|---|---|---|---|
| (6,800) on `1RB0LA_1RC1LA_1RD0LB_1LD1RC` | 3.01 ms | 1.79 ms | **1.68x** |
| (4,400) on `1RB0LA_1RC1LA_1RD1LB_1LD1RC` | 1.99 ms | 1.19 ms | **1.68x** |

Both agree on accept AND on reject (m6 at the too-weak (4,400) rung:
false/false).  Lower than the 2.5x stage figure because the full
check also pays `csteps` and the per-state `cvisits` rescan, neither
of which this round touches -- those are the next ~22%.

`theories/Tests/ClosureIdx_Corruption.v` carries the negative
controls the new machinery needs: differential accept/reject against
the engine it replaces, fuel exhaustion, and two deliberately corrupt
`mkr` rank searches that must not make the checker accept.

NOT WIRED into `Decide.v`: wiring is a census-input change, so it
belongs in the single batch that the next re-walk pays for.

### `PArray` is the wrong tool at this size

A `PArray` visited-set indexed by the packed key measured **8.8x
slower** than the current code: n-gram closures here are tens of
nodes, so one `PArray.make` of 2^15 slots per machine allocates ~1000x
the closure (3.4 s of the 3.9 s was sys time).  If arrays are used at
all they must be allocated once and threaded through the walk with
generation stamps, never per machine.  Ints alone carry the win; the
`PArray` half of the arc can be dropped without losing anything, which
also shrinks the footprint delta from ~13 declarations to ~8.

### Two measurement traps (both cost real time here)

1. **Unary-nat fuel literals.**  An inline `200000` is
   `Init.Nat.of_num_uint ...`, re-expanded into a 200,000-deep unary
   nat at every occurrence.  In a loop body that is ~96% of the
   measurement: the first A/B read 9.3 s vs 8.8 s (a nothing-burger)
   and became 0.40 s vs 0.17 s once the fuel was a named constant.
   The real walk is safe -- `Run.v`'s `decider` is a global constant,
   so its literals are built once -- but every probe must hoist them.
2. **VM constant hoisting.**  A closed application (`pk_stage_of p06`)
   is lifted into the VM's constant pool and evaluated ONCE: a loop
   over it reported 0.001 s at both 200 and 20,000 iterations.  Loops
   must take the varying input as a parameter.

### Census-wide tier cost: Amdahl, measured (2026-08-05)

The ~30% ladder share above is derived from the heavy `GG_1LC_1LB`
subtree, which is residue-rich by construction.  Replaced here with a
census-wide measurement: `tools/census_ladder.c --csv` classifies all
3,995,005 nodes, `tools/probes/gen_tier_cost.py` samples each tier,
and `ProbeTierCost.v` times the REAL decider (`ProbeWalkCommon`'s
`decider0`) on those machines.

| tier | census nodes | sampled | per machine | share of decided time |
|---|---|---|---|---|
| T translated cycle | 2,282,976 | 40 | 15.0 ms | **71.5%** |
| C in-place cycle | 1,029,749 | 40 | 5.35 ms | 11.5% |
| N n-gram (all 4 rungs) | 200,064 | 64 | 17-56 ms | 12.2% |
| H halt (expand) | 249,692 | 40 | 8.45 ms | 4.4% |
| residue + deferred | 232,523 | 56 | ~0 (lookup hit) | ~0% |

**The translated-cycle tier is 71.5% of the walk's decided-tier cost
and the n-gram ladder is 12%.**  That inverts the earlier estimate and
redirects the program: the packed/interned ladder work is worth ~12%
of the walk no matter how good it gets.

Two caveats, stated rather than buried.  (a) The residue's true cost
depends on it being served by the proven/provenqh/deferred lookups,
which `decide_easy` consults BEFORE any scan -- the D sample measured
~0 ms (lookup hit), and the alternative (fall-through) would cost
1550 ms/machine and blow past the observed walk total, so lookups it
is.  (b) The model sums to ~47,700 s single-core vm against an
observed 183,600 core-seconds native: uniform sampling within a tier
misses heavy tails, and walk overhead and 4-way contention are not in
the model.  Use the RATIOS, not the absolute total.

### CORRECTION (2026-08-05, later): the residue row was misread, and
### it changes everything above

Caveat (a) was wrong, and not subtly.  The residue row's own
measurement in the same probe run was **62.0 s for 40 machines --
1.55 s/machine**, not ~0: only 1 of the 40 sampled mirror-residue
machines hits the stand-in lookup tables (verified directly with
`deferred_lookup`); the other 39 fall through every scan and get
decided by the DEEP ladder tiers (rank, wrapped-QHBound-lex, RepWL)
in-walk.  The "~0 (lookup hit)" row in the table above described the
D tier (0.001 s) and was wrongly carried over to the residue.

The real walk's lookup tables hold only ~20k machines (proven +
provenqh + reroot + deferred), so of the 228,815 mirror-residue
machines about **209k are ladder-decided in-walk at ~1.55 s vm
each ≈ 330,000 s vm -- roughly 85% of the whole walk**, versus ~6%
for the T-tier scans the last two rounds optimized.

This also finally reconciles the model with reality: 330k + 35k
(scans, corrected) ≈ 365k s vm ≈ 75-120k s native single-core ≈ 21-34
core-hours, against the observed 51 core-hours with the measured
memory-bandwidth contention inflating it -- consistent.  The old
47.7k-second model was 12-20x short of the observed walk, and that
discrepancy was itself the loudest clue that the map was wrong.

Corrected shares (same probe data, residue row read correctly):

| slice | share of walk |
|---|---|
| mirror-residue, in-walk deep-ladder decided (~209k nodes) | **~85%** |
| T translated-cycle scans | ~6% |
| C + H + N + lookups | ~9% |

Consequences, in order:
1. The ladder arc (ClosureIdx wiring, qhb-lex gram-set memoization
   across states and rungs, incremental `ng_grow`) is BACK as the
   main event -- it targets the 85%, and `try_qhb_lex_at` re-running
   `ng_grow`+`ng_explore` per (state, rung) is the single biggest
   redundancy (up to ~36 grow/explore cycles per residue pop).
2. The scan work stays worth finishing (it is ~6% AND it deletes the
   per-step `PositiveMap` snapshot allocation that feeds the
   contention multiplier), but it was never where the 14x lived.
3. Every future probe table gets its per-row arithmetic written out
   (time / count = per-machine) so a 62-second row cannot be recorded
   as ~0 again.

### Inside the 85%: tier ablation on the residue sample

`ProbeResBurn` (scratch) re-ran the same 40 residue machines with one
rung list emptied at a time.  Ablations get SLOWER, not faster --
removing a tier pushes its machines into deeper, costlier tiers --
so the informative numbers are the catch counts and the no-rw run:

| pipeline | time | decided /40 |
|---|---|---|
| full ladder | 62.2 s | 40 |
| without n-gram rungs | 56.3 s | 40 |
| without rank rungs | 189.1 s | 37 |
| without QHB rungs | 144.9 s | 38 |
| without RepWL rungs | **8.2 s** | 33 |

Everything up to and including the failing-qhb attempts costs 8.2 s
TOTAL; the other 54 s of the full run is the RepWL tier deciding its
7 machines -- **~7.7 s per rw-caught machine** (4 rungs at closure
fuel 8192).  Scaled by census weight, `rw_tier` attempts on the ~18%
of residue-class machines that reach them are **~75% of the entire
walk**; the qhb attempts for the ~20% that reach those are most of
the rest of the 85%.

So the priority order inside the main arc is now measured, not
guessed:
1. make `rw_tier`'s closure cheap (ClosureIdx-style interning +
   incremental exploration inside RepWL/RepWLSearch) -- every 2x
   there is ~1.6x on the whole walk;
2. qhb-lex gram-set memoization across (state, rung);
3. only then the generic ladder polish (rungs, hints, dispatch).

### LANDED: scan_ct deleted -- the one-pass now subsumes it

The prediction postmortem in one line: BB5's 10-20x came from
REPLACING the multi-pass scan block, and the one-pass had been
shipped as an additive front-end with the old block kept as a
fallback -- every fall-through machine paid both.  The fallback
survived because it still caught machines (46 of 1,440 sampled) the
one-pass missed.  Two real gaps, found and closed:

1. **The record rule was approximate.**  `lp_rec_cands` fired on any
   edge-standing entry with the PRE-move state; `scan_records0` logs
   only steps OFF the extent, at the POST-move index and state.
   Widening the approximate rule plateaus (5/19, 10/23 covered) --
   replication, not widening, was needed.  `lp_records` now derives
   the EXACT record list from the history (both configs of every
   step are consecutive entries; direction is the sign of the
   position delta; the one step the history lacks is recovered from
   the head entry's transition), and `lp_tc_pairs` is `tc_pairs`
   verbatim on it.  Validated: bit-equality with `scan_records` on
   all 1,440 sampled machines at both gas rungs.
2. **Drifting cconf-cyclers.**  The model is head-relative, so a
   cycler that drifts but repeats in padded-`cconf` space (blank
   trail) is a plain `cycle_leaf_check` cycle that the TCycler
   window check can fail to certify; and several same-state records
   can fall inside one period, so the NEAREST same-state pair (the
   `tc_pairs` rule) can give a sub-period gap.  Fix: CYCLE twins on
   the `lp_cycle_K = 4` nearest same-state record pairs -- two plain
   re-simulations each, cheap.

Final gate over 600 T + 600 C + 240 N6: records bit-equal 1,440/1,440,
**lost catches 0, gained catches 0** -- exact subsumption.  scan_ct's
line in `decide_easy` is deleted (the definition stays for probes and
the soundness lemma), so every fall-through machine stops paying
42.6 ms and, more importantly for the contention story, the per-step
`PositiveMap` full-config snapshot allocation is out of the pipeline.
`Loop1Scan_Regression.v` gains the corruption controls: records
equality on a real TC pinned, the historical pre-move bug pinned as
DETECTED, and the twin rule unit-pinned.

Measured per tier (`ProbeCtGone.v`), same sampled machines, catches
identical, session start -> now (all of today's scan work compounded:
eager-andb fix, binary counters, exact records, scan_ct deletion):

| tier | start | now | speedup |
|---|---|---|---|
| T translated cycle | 15.0 ms | **1.9 ms** | **7.9x** |
| C in-place cycle | 5.35 ms | 1.35 ms | 4.0x |
| N2 (reaches ladder) | 17.3 ms | 4.3 ms | 4.0x |
| N6 (reaches ladder) | 50.1 ms | 36.5 ms | 1.4x |
| residue-class | 1,555 ms | 1,458 ms | 1.07x |
| H halt | 8.45 ms | ~12 ms | noise (map-build-laden first row) |

Which is exactly the corrected map's prediction: the scan tiers are
now nearly free, and the walk is ~97% the residue-class ladder burn.
The scans arc is CLOSED; the ladder arc (rw_tier closure cost, then
qhb-lex memoization, then ClosureIdx wiring) is the whole remaining
game.

### Inside rw_tier: the slow part of the big bulk, measured

`ProbeRwSplit.v`, on the rw-caught residue machines (closures 77-690
nodes), one winning (2,2,0) rung:

| stage | per machine | share |
|---|---|---|
| `close` (the fuel-8192 exploration) | **1 ms** | ~0.6% |
| `rw_procedure` (SCC + BF search) | ~100 ms | ~57% |
| verified checker (re-runs `close`, tries, per-state succs) | ~76 ms | ~43% |

The suspect everyone would pick -- the fuel-8192 closure -- is
innocent.  The cost was (a) `rconf_enc`, a positional encoding of
the whole run-length item list, recomputed on EVERY map and set
access inside Kosaraju, the rank relaxations and every Bellman-Ford
pass; (b) `rw_succs` recomputed per premise state by `rbuild_adj`;
(c) `rw_delta` recomputed per edge per BF pass; and (d) the verified
checker re-deriving everything again.

And the rung LADDER was upside down: per attempt over the 32
rw-catchable sample machines, (2,2,0) costs 0.166 s and catches
30/32; (3,2,0) costs 3.8 s and catches 16, with only 2/40 needing it
exclusively -- yet it ran second, so the hard machines burned it
before cheaper rungs got a look.  Also measured: direct-rw catches
32/40 residue machines (the deep tiers ahead of it catch 25 of them
more expensively), and the ngram rungs are net-negative on this
class (the no-ngram ablation is faster at equal catches).

### LANDED: interned RepWL search + rung reorder

`RepWLSearch.v` gains an interned core (`iintern`/`irows`/`iproc_*`):
nodes numbered once, `rconf_enc` paid once per node plus once per
emitted certificate entry, successors once per node, `rw_delta` once
per node per measure attempt, all graph work on dense positive
indices.  Same algorithms, same round structure, same certificate
format; untrusted as before.  `Run.v`'s `rw_rungs_census` reordered
to [(2,2,0);(4,2,0);(2,3,0);(3,2,0)] -- order changes no verdict.

Validated: rung2-exclusive count (2), all-rungs-fail count (8) and
the catchable union (32) identical old vs interned on the 40-machine
residue sample.  Measured on the WORST case -- failing attempts,
full search to exhaustion, no short-circuit -- old vs interned:

| rung | old | interned | speedup |
|---|---|---|---|
| (2,2,0) | 3.82 s | 2.65 s | 1.44x |
| (3,2,0) | 49.3 s | 21.2 s | 2.33x |
| (4,2,0) | 43.6 s | 9.9 s | **4.4x** |
| (2,3,0) | 5.0 s | 2.15 s | 2.33x |
| all four | 101.7 s | 35.9 s | **2.8x** |

(Both runs under container congestion; ratios approximate, direction
unambiguous.)

### The winning-attempt A/B closes the loop -- and reverses the reorder

`ProbeRwWin.v`, same 32 rw-catchable machines, interned code, all
five catch counts IDENTICAL to the old code (union 32; per-rung
30/16/30/30 -- the interned search is catch-for-catch equivalent):

| rung | old | interned |
|---|---|---|
| (2,2,0) | 5.32 s | 4.05 s |
| (3,2,0) | 121.9 s | **119.7 s** |
| (4,2,0) | 28.6 s | 20.5 s |
| (2,3,0) | 6.1 s | 4.07 s |

Winning (3,2,0) attempts barely moved while its FAILING attempts
improved 2.33x: on winning attempts over the big L=3 closures the
VERIFIED CHECKER dominates (it re-runs `close`, rebuilds the trie
twice, recomputes succs per state), and interning does not touch it.
That pins the next multiplier precisely: ClosureIdx-lex -- extend
`ClosureIdx.v` with the lex-certificate variant (rows carrying node
values for the measure components), feed the SEARCH's pool to the
checker, delete its duplicate `close` and per-state `lex_ok` succs
recomputation.  Then the same treatment for the qhb tier
(`try_qhb_lex_at` re-runs `ng_grow`+`ng_explore` per (state, rung)).

Two corrections from the same probe, recorded plainly:

1. **The rung reorder was wrong and is reverted.**  (2,2,0)'s only
   misses are exactly the (3,2,0)-exclusive machines, so any machine
   reaching the second rung either wins there or fails everything --
   the original order was already optimal, and demoting (3,2,0) only
   inserted failing (4,2,0)+(2,3,0) attempts in front of its wins.
   The Run.v comment now documents why the order stands.
2. **The probe's own "reordered pipeline" rows are eager-orb
   artifacts** -- `a || b` evaluates both sides under CBV, so those
   rows summed all four rungs (147.6 ≈ 4.05+119.7+20.5+4.07).  The
   real decider's `existsb` short-circuits correctly.  Hunting that
   same trap in the shipped pipeline found a REAL one:

### LANDED: try_qhb's eager orb

`try_qhb` computed `existsb (plain ladder) || existsb (lex ladder)`
-- so every machine the plain-acyclicity qhb ladder caught still
paid the full lex ladder (per-rung `ng_grow` + `ng_explore` per
state) for nothing.  Now a nested `if`; value unchanged, pinned
tests green.  Same trap, same fix shape as `lp_rewind`.

### Inside the translated-cycle tier

`ProbeScanSplit.v`, same sampled machines.  `decide_easy` runs
`scan_loops` at gas 130, then `scan_loops` at gas 512 (a fresh
`lp_run` -- the first 130 steps are simulated twice), then `scan_ct`
(the old block: `scan_cycle`'s per-step rolling hash + `PositiveMap`
insert of a full config snapshot, plus a separate `scan_records`
walk).

| stage | per machine (T tier) |
|---|---|
| `lp_candidates` @130 (simulate + scan) | 1.2 ms |
| `scan_loops` @130 (+ verified re-checks) | 1.85 ms |
| `lp_candidates` @512 (simulate + scan) | 16.1 ms |
| `scan_loops` @512 (+ verified re-checks) | 17.9 ms |
| `scan_ct` @512 (old hash+map block) | **42.6 ms** |

Two things fall out:

1. **The 130 -> 512 rung is superlinear**: 4x the gas costs 13.4x the
   time (~n^1.9).  `lp_scan`'s `lp_rewind` filter is O(P) per matched
   entry over an O(n) history, so the full-gas rung is quadratic in
   the history.  This is the single most expensive thing the bulk
   pays, and it is untrusted search -- the verified re-check is the
   authority either way, so capping the rewind is sound by
   construction.
2. **`scan_ct` is NOT redundant** -- the tempting deletion is wrong.
   Of the C/T machines that reach it (3/40 and 4/40), it catches
   3/3 and 4/4 respectively: the one-pass misses them because
   `lp_scan` is capped at 6 candidates, not for any deep reason.  So
   ~10% of the bulk pays 42.6 ms, which is ~41% of the T tier's total
   time.  The fix is to make the one-pass complete enough to subsume
   it (uncapped or better-anchored), THEN drop `scan_ct` -- not to
   drop it first.

### LANDED: the quadratic was an eager `andb`, not an algorithm

The cause turned out to be smaller and better than "cap the rewind".
Coq's `&&` is `andb`, a **function**, so under call-by-value BOTH
arguments are evaluated.  In

    st_eqb .. && sym_eqb .. && lp_rewind l0' l1' m          (lp_rewind)
    st_eqb .. && sym_eqb .. && (if .. then lp_rewind .. )   (lp_scan)

the rewind therefore ran to its full depth even when the head compare
had already failed, and it ran for EVERY history entry even when the
state or symbol already differed -- an O(n) rewind per entry over an
O(n) history.  That is the whole quadratic.

Both were rewritten with nested `if`s.  This is the SAME boolean
function, so no candidate, no catch and no census result can change:
`theories/Tests/Loop1Scan_Regression.v` proves
`lp_candidates_unchanged` against reference copies of the original
`&&` forms, closed under the global context.  No capping, no
heuristics, no re-validation of catches needed.

Measured, same sampled machines, before -> after:

| tier | before | after | speedup |
|---|---|---|---|
| T translated cycle | 0.601 s | 0.430 s | **1.40x** |
| C in-place cycle | 0.214 s | 0.173 s | 1.24x |
| N2 / N3 / N4 / N6 | 0.277/0.528/0.599/0.891 | 0.223/0.474/0.509/0.802 | 1.11-1.24x |
| H halt | 0.338 s | 0.298 s | 1.13x |

Weighted by the census tier counts that is **~1.33x on the whole
walk** (47,700 -> 35,900 s in the model's units) for a ~10-line
change that cannot alter the result.

On the isolated scan stage the same change is worth 2.6-3.9x; the
decider dilutes it with `find_halt`, the lookups, the verified
re-checks and (for the n-gram tier) the ladder.

The `&&`-under-CBV trap is worth grepping for elsewhere in the hot
path -- any `a && expensive` where `a` usually fails is paying for
`expensive` every time.

### LANDED: unary `nat` was the SECOND quadratic

Fixing the `andb` left the scan still superlinear -- measured 2.6x,
3.1x, 3.8x per gas doubling (linear would be 2.0x, and the ratio was
*growing*).  Cause: `lp_ent`'s step index `lp_k` was a `nat`, i.e. a
unary linked list, so `lp_k h0 - lp_k h1`, `2 * P <=? lp_k h0` and
`n1 mod P` were each O(gas) -- over ~gas history entries, O(gas^2) in
arithmetic alone.

`lp_k` is now binary `N` (matching `lp_pos`, already `Z`).
`lp_cand` deliberately still carries `nat`, so `lp_check` and every
verified checker are untouched; the `N.to_nat` conversions happen ~6
times per machine (candidates) rather than ~gas^2 times (history
entries).  One semantic detail: `N.modulo _ 0 = 0` where
`Nat.modulo _ 0 = n`, so the `P = 0` case is guarded explicitly to
compute what the unary form did.

Gas scaling, before -> after: 2.6/3.1/3.8 -> 1.58/1.79/2.26 per
doubling.  **The quadratic is gone** and candidate generation at gas
512 is 5.5x faster (0.427 -> 0.077 s over 40 machines).

| tier | original | after andb | after N | total |
|---|---|---|---|---|
| C in-place | 0.214 s | 0.173 s | 0.085 s | **2.52x** |
| T translated | 0.601 s | 0.430 s | 0.378 s | **1.59x** |
| N2 / N3 / N4 / N6 | | | | 1.13-1.51x |
| H halt | 0.338 s | 0.298 s | 0.320 s | 1.06x |

Amdahl-weighted: 47,700 -> 30,300 s in the model's units, i.e.
**~1.57x on the whole walk** so far (1.33x from the `andb` fix, a
further 1.18x from this).

Unlike the `andb` fix this is a REPRESENTATION change, so it is not
identical by construction.  Validated instead:
`tools/probes/ProbeNatRef.v` reimplements the original unary scan
standalone and diffs candidate lists against the shipped one over
1,440 machines (600 C, 600 T, 240 N6) at BOTH gas rungs -- 2,880
comparisons, **zero divergence**.  `Loop1Scan_Regression.v` still
proves the nesting did not change the guard's condition, now at the
binary types.

### Where the T tier's time goes now

Candidate generation is no longer the bottleneck; what is left is
VERIFICATION.  `lp_check` re-simulates from `c0` for every candidate:
`cycle_leaf_check n1 p` runs `csteps n1` AND `csteps (n1+p)`, and the
anchor reduction tries up to 3 anchors per candidate with up to 6
candidates -- so a machine can pay ~18 re-simulations of up to 512
steps against the ONE 512-step pass that produced the history.

That is the next lever, and it is the old option-4 item sharpened:
verify `csteps p a = Some a` from the anchor the scan already walked
past, instead of re-deriving it from `c0`.  It touches proved code
(`cycle_leaf_check`/`tcycler_leaf_check` and their soundness), which
is why it was deferred -- but it is now the dominant cost of the tier
that is 71.5% of the walk.

Next, still in order of Amdahl: widen the one-pass so `scan_ct` (42.6
ms, ~10% of the bulk reaches it) can be dropped -- that one DOES
change which candidates are proposed, so it needs the verdict diff
over a large sample, not just a proof.  Both belong in the batch with
the `ClosureIdx` wiring.

### Walk anchor for this container

`ProbeWalk_K1` (8,192 pop-slots of the heavy `GG_1LC_1LB` subtree,
realistic lookup maps): **934 s wall, 114 ms/pop, 0.82 GB peak RSS**,
vm_compute.  Native runs ~3-5x faster on this code, so treat 114 ms
as an upper bound and use it only for ratios.

### LANDED: ClosureIdx-lex, wired into rw_tier

`theories/Checkers/ClosureIdx.v` now carries the lexicographic half,
and `rw_tier` runs on it.  What the interned checker removes, per
attempt:

- `rw_succs` recomputed for every closure node once per premise state
  -- four sweeps become one, off the `edges_of` rows;
- inside `lex_edge_ok`, one `rconf_enc` plus one big-key
  `PositiveMap.find` per certificate component per EDGE ENDPOINT
  (`2*c*e` per state) -- now one `rconf_enc` per closure NODE, shared
  by every component (`vals_of`), materialised once per state into a
  small-key map (`vmap_of`), after which the check touches no context
  at all;
- the eager `||`/`&&` in `lex_edge_ok`/`comp_strict`/`comp_noninc`
  (nested `if`s: same boolean function, decided prefixes stop);
- the checker's own `close`.  `rw_tier` had already built that closure
  for the search, so `rw_check_neverqh_idx_pool` takes it as an
  argument.  The pool stays untrusted -- `edges_of` re-derives
  closedness (`edges_closed`) and `idx_of a0` re-derives root
  membership -- so a wrong pool can only make the check fail.

Not "sound relative to": `lex_check_idx_spec` proves the interned
checker **equal** to `closure_check_neverqh_lex` on the denoted
certificate, so `rw_tier_unchanged : rw_tier = rw_tier_ref` is a
theorem (`edges_of_closed`, the converse of `edges_closed`, is what
makes equality rather than an implication provable).  It is axiom-free;
`rw_tier_sound` still reduces to `rw_check_neverqh_sound`, so the
axiom footprint does not move.

#### Measured (`ProbeRwIdx`, vm_compute)

The 32 rw-catchable machines of `ProbeTierCost`'s residue sample --
the SAME sample as `ProbeRwWin`, so these rows sit next to its table.
Catch counts identical to the old code everywhere (30/16/30/30 per
rung; 0 on the 8 machines nothing catches).

| stage / rung | old | interned | |
|---|---|---|---|
| verified stage, (2,2,0) | 2.365 s | 1.197 s | **1.98x** |
| whole attempt, (2,2,0) | 3.986 s | 2.814 s | 1.42x |
| whole attempt, (4,2,0) | 22.67 s | 15.32 s | 1.48x |
| whole attempt, (2,3,0) | 4.319 s | 3.154 s | 1.37x |
| whole attempt, (3,2,0) | 126.0 s | 125.3 s | 1.006x |

Failing attempts (the 8 machines no rung catches) barely move --
0.99x / 1.06x / 1.02x at (2,2,0) / (4,2,0) / (2,3,0) -- which is
consistent: a failing attempt is dominated by the untrusted search
running to exhaustion, and that was already interned last round.

#### The number that scales to the walk: 1.14x on the rw ladder

Rungs in isolation are not what the walk pays: `existsb` over
`rw_rungs_census` short-circuits, so a machine caught at (2,2,0) never
reaches the expensive (3,2,0).  `ProbeRwLadder` runs the real ladder
over all 40 residue machines of the sample, old checker vs interned,
alternating and uncontended, twice each:

| | run 1 | run 2 | mean | per machine |
|---|---|---|---|---|
| `rw_tier_ref` ladder | 182.7 s | 192.4 s | 187.6 s | 4.69 s |
| `rw_tier` ladder | 165.0 s | 165.3 s | 165.2 s | 4.13 s |

**1.14x**, catches 32/32 identical on all four rows.  (The old rows
vary 5% run to run; the interned rows agree to 0.15%.  Read the ratio
as 1.14x +- ~0.03.)

Carried to the walk at this doc's ~75% rw-attempt share, that is
**~1.10x overall** -- 13.7 h to ~12.5 h.  Stated plainly because the
sketch this round came from projected ~2x on the dominant tier: the
2x is real and landed, but it landed on a stage that is not what the
tier is bound by.  The next section is why.

#### The flat (3,2,0) row is `close`, not the checker

`ProbeRwStage` splits that rung's verified stage over the same 32
machines.  Per-row arithmetic written out, per the rule this doc
adopted after the residue row was misread:

| stage, rung (3,2,0), 32 machines | total | per machine |
|---|---|---|
| `close` alone | 116.9 s | 3.65 s |
| `close` + `edges_of` | 109.0 s | 3.41 s |
| certificate denotation (`rpm_of`/`rps_of`), all 4 states | 0.116 s | 3.6 ms |
| the same as `epres` | 0.109 s | 3.4 ms |
| whole old checker (`ProbeRwIdx`) | 118.9 s | 3.72 s |

(`close` alone reading SLOWER than `close`+`edges_of` is a ~7%
container-contention artefact -- those two rows ran with different
numbers of sibling `coqc` processes.  It bounds the noise; it does not
change the conclusion.)

**~98% of that rung's verified stage is `close`**, and the certificate
handling everything downstream of it is ~0.1% -- so there was nothing
there for interning to remove.  `ProbeRwWin`'s reading ("on winning
attempts over the big L=3 closures the VERIFIED CHECKER dominates --
it re-runs `close`, rebuilds the trie twice, recomputes succs per
state") named the right stage and the wrong cause inside it: it is the
`close` re-run alone.  That is exactly what the pool-passing form
deletes, and it is the only part of this round that touches that rung.

The deeper fact the split exposes: at (3,2,0) roughly half the
machines that reach the rung burn all 8,192 fuel units and get `None`
back, and `rw_tier` then returns false without ever calling the
checker.  A fuel-exhausting closure search is the rung's real cost,
and no amount of verified-stage work can reach it.

#### Big-sample catch-diff

`gen_rwdiff.sh` over `ProbeTierBig`'s 600-machine residue sample
(`census_ladder --csv`, `TIER_SCALE=15`), `rw_tier` vs `rw_tier_ref`,
printing (disagreements, catches):

| rung | machines | result |
|---|---|---|
| (2,2,0) | 600 | **(0, 418)** |
| (3,2,0) | 200 | **(0, 107)** |
| (4,2,0) | 600 | **(0, 443)** |
| (2,3,0) | 600 | **(0, 424)** |

Rung (3,2,0) takes a 200-machine prefix rather than all 600: it is
~20x the cost of (2,2,0) per attempt.  Nothing else is capped.

These are cross-checks on `rw_tier_unchanged`, not the proof --
2,000 machine-rung comparisons, zero disagreements.  All 19
`Machines/RerootStage` files also rebuild, i.e. 77 `rw_tier ... = true`
kernel checks against the interned checker.

#### What is left in the rw tier

In Amdahl order, measured rather than guessed:

1. **The (3,2,0) closure search.** ~30% of residue machines fall
   through (2,2,0) into it (418/600 caught at rung 1), it costs ~3.9 s
   an attempt against 0.13-0.30 s for rung 1 (catching / failing), and
   ~98% of that is `close`.  It dominates the rw slice outright, and
   it is the reason the ladder moved 1.14x while its verified stage
   moved 1.98x.  Levers: make `rw_succs` at L=3 cheaper; or detect the
   diverging abstractions earlier instead of spending 8,192 fuel units
   to learn nothing.  The second changes which machines are caught, so
   it needs the catch-diff above, not just a proof.
2. The certificate's tables are still keyed by `rconf_enc`, so
   `vals_of` pays `#pool * #comps` big-key lookups per state.  Having
   the search emit index-keyed tables would halve that, but it changes
   the `rwcomp` denotation and therefore every `RerootStage` proof --
   not worth it until row 1 stops dominating.
3. The same ClosureIdx-lex treatment for the qhb tier
   (`try_qhb_lex_at` re-runs `ng_grow`+`ng_explore` per (state, rung)),
   which is the other half of the residue-class burn.

### What this means for the ~1 h goal

The n-gram ladder is ~4.9% of nodes and -- per the census-wide tier
measurement above, which supersedes the heavy-subtree estimate
originally written here -- **12%** of walk time, not ~30%.  Even 7.4x
on its verified stage is ~1.8x on a catch, ~2.7x with `ng_grow`
packed and `cvisits` single-passed, and under 1.1x on the whole walk.
13.7 h -> ~1 h needs ~14x, and that factor can only come from the
**translated-cycle tier, which is 71.5% of decided-tier cost** on its
own.  Order of work: scan tiers FIRST (specifically T), n-gram
packing second.

STALE, kept for the record: the T-tier conclusion in the paragraph
above is superseded twice over.  The residue row was misread (see
"CORRECTION" above): the walk is ~85% residue-class ladder burn, and
after the scan work landed the T tier is ~6%.  The scan arc IS
finished -- it just was not where the 14x lived.  The live order of
work is the one in "What is left in the rw tier" above.

## Measurement status

tools/probes/ has the vm_compute harness (per-tier timings on four
machine classes; bounded walks of the heavy `GGH_0RB_1LC_0LB` subtree
with realistic lookup maps, instrumented for time and peak RSS).
Numbers pending a Coq-capable environment; per the playbook these are
container-safe (minutes each, no native_compute, no full walk).
