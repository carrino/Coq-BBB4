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
   rows summed all four rungs (147.6 ≈ 4.05+119.7+20.5+4.07).  ~~The
   real decider's `existsb` short-circuits correctly.~~

   **WRONG, and it cost 4.5x on the rw ladder for three rounds.**
   `existsb` is `f a || existsb l`, so it is exactly as eager as the
   bare `||` -- the real decider summed all four rungs too, which is
   why that 147.6 matched.  See "CORRECTION (2026-08-07)" below.  The
   arithmetic was sitting in this very table and was read as a probe
   artifact instead of as the pipeline's behaviour.  Hunting that
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

CONFIRMED 2026-08-07: the re-walk came in at **12.15 h** walk-only,
i.e. 1.10-1.13x depending on how the baseline's base build is
treated.  See "Full re-walk #2" below -- it is the first projection
in this doc to survive contact with a full walk, and why it did is
the useful part.

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

Run twice -- once against the certificate-interning wiring, once
against the shipped pool-passing wiring -- with **identical catch
counts both times**, so the two wirings agree with `rw_tier_ref` and
with each other.  These are cross-checks on `rw_tier_unchanged`, not
the proof: 2,000 machine-rung comparisons per run, zero
disagreements.  All 19 `Machines/RerootStage` files also rebuild, i.e.
77 `rw_tier ... = true` kernel checks against the interned checker.

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
work is "Next steps, in Amdahl order" at the end of this doc.

## Full re-walk #2, measured end-to-end (2026-08-07)

`make -j4 census-verify WALK_JOBS=4` on the same 32 GB desktop, with
ClosureIdx-lex wired into `rw_tier`.  Wall clock taken from the
walk-stamp (`_census-prepare` writes it at walk start) to
`Census_Theorem.vo`, so this row is **walk-only** and excludes the
base build:

| | |
|---|---|
| walk start | 2026-08-06 10:30:10 -0700 |
| `Census_Theorem.vo` | 2026-08-06 22:38:58 -0700 |
| **walk-only wall** | **12 h 08 m 48 s (12.15 h)** |

Against the 13.7 h of "Full re-walk, measured end-to-end
(2026-08-05)": **1.13x** at face value, **1.10x** after subtracting
that run's ~20 min base build (it was `time make census`, which
includes `all`).  Projected was ~1.10x / ~12.5 h, so the walk came in
~20 min BETTER than projected.

`Print Assumptions census_decided` printed exactly
`functional_extensionality_dep` and nothing else.  154 walk units +
`CENSUS_VO_HASH` committed in `c93f3f1`.

Precision caveat, so the number is not over-read: one run per
configuration, twelve hours apart, on a desktop whose other load was
not controlled, and the old ladder rows vary ~5% run to run.  Read
1.10-1.13x as "about 1.1x", not as three significant figures.

### Why this projection held when the previous two did not

| round | projected from | projected | delivered |
|---|---|---|---|
| packed int63 | verified **stage** | 7.4x | <1.1x on the walk |
| ClosureIdx-lex | verified **stage** | ~2x | 1.14x on the tier |
| ClosureIdx-lex | `ProbeRwLadder`, real **ladder** | ~1.10x | **1.10-1.13x** |

Same round, two projections, and only the one measured at the level
of its claim survived.  The rule, now with a positive control rather
than only failures behind it:

> Project from a measurement taken at the level of the claim.  A
> stage speedup is not a tier speedup, and a tier speedup is not a
> walk speedup, until each is measured as such.

This is why row 3 below is gated on a probe rather than started.

## CORRECTION (2026-08-07): `existsb` is not a short-circuit, and it was the ladder

Every round in this document reasons about rung ladders as if a
machine caught at rung 1 stops there.  It does not, and never did.
Coq's

    Fixpoint existsb (l : list A) : bool :=
      match l with [] => false | a :: l => f a || existsb l end

builds an `orb` application, and `orb` is a FUNCTION, so under
call-by-value BOTH arguments are evaluated: `existsb` runs `f` on
EVERY element, always.  `forallb` is `f a && forallb l` and is eager
the same way -- it never stops at the first `false`.

Isolated (`tools/probes/ProbeOrb.v`, vm_compute; element 0 decides,
elements 1-3 are expensive):

| expression | value | time |
|---|---|---|
| `existsb f [0;1;2;3]` | `true` | 1.03 s |
| nested-`if` `anyb`, same value | `true` | 0.00 s |
| `f 0` alone | `true` | 0.00 s |
| `forallb g [0;1;2;3]` | `false` | 0.90 s |
| nested-`if` `allb`, same value | `false` | 0.00 s |

Every rung ladder in `Census/Decide.v` was an `existsb` whose elements
are whole tier attempts:

| ladder | one element costs |
|---|---|
| `try_rw` | a RepWL rung: closure + certificate search + verified stage |
| `try_qhb` (three nested) | a candidate state; 9 plain rungs; 9 lex rungs |
| `scan_loops` | one `lp_check`: full re-simulation of `n1` and `n1 + p` steps |

### How this hid for three rounds

The arithmetic was already in this document, in "The winning-attempt
A/B closes the loop": the reordered-pipeline row was 147.6 s and the
four rungs summed to 4.05 + 119.7 + 20.5 + 4.07 = 148.3 s.  That was
recorded as *the probe's* eager-orb artefact and the shipped
`existsb` was declared correct in the same sentence.  Both sides were
the same bug.  `ProbeRwLadder.v` then inherited it -- its header says
"Run.v's rung order with the existsb short-circuit" while its body is
`existsb` -- so the 1.10x ClosureIdx-lex projection was measured
against an eager ladder and *held for the right reason*: the probe
faithfully reproduced what the walk actually did.  Nothing above this
line is retracted; it was all measured on the eager pipeline.

One consequence worth stating: under eager `existsb`, **rung order
cannot change cost at all**.  The "do not reorder the rw rungs" rule
(719a245 / da893c8) was settled on catch-set grounds, which still
stand -- but any *timing* intuition about rung order collected before
today was measuring nothing.  Order is load-bearing for the first
time now.

### LANDED: `anyb`, and what it measured

`Census/Decide.v` gains

    Fixpoint anyb {A} (f : A -> bool) (l : list A) : bool :=
      match l with [] => false | x :: r => if f x then true else anyb f r end

    Lemma anyb_existsb : forall A f l, anyb f l = existsb f l.

and `try_rw`, `try_qhb` (all three levels), `scan_loops` and
`try_tc_cands` use it.  `anyb` is the SAME boolean function -- proved,
in the file -- so no candidate, no catch and no census verdict can
move, and every soundness proof goes through with one added
`rewrite anyb_existsb`.  **No catch-diff is needed for this change**
(cf. the rule below): nothing about *which* machines are caught can
differ.

Measured, vm_compute, this container, one run per configuration:

**The rw ladder** (`ProbeStrict.v`, the `ProbeTierCost` residue
sample, 40 machines).  Catch counts identical, 32 = 32:

| | time |
|---|---|
| rung (2,2,0) alone | 4.52 s (catches 30) |
| rung (3,2,0) alone | 127.49 s (catches 16) |
| rung (4,2,0) alone | 19.64 s (catches 30) |
| rung (2,3,0) alone | 4.46 s (catches 30) |
| **sum of the four** | **156.1 s** |
| shipped `existsb` ladder | **157.7 s** |
| `anyb` ladder | **34.7 s** |

The `existsb` ladder costs the sum of its rungs, to within noise.
That is the whole finding in one row.  **4.53x.**

**The C/T bulk block** (`ProbeScanStrict.v`, gas 130 then 512, catch
counts identical 40 = 40): C tier 0.040 s -> 0.017 s (**2.4x**), T
tier 0.064 s -> 0.018 s (**3.6x**).  Structurally: over 40 C machines
`lp_candidates` emits 695 candidates and the winning candidate sits at
index 88/40 = 2.2, so ~5.4x more `lp_check` re-simulations were run
than needed.

**The walk** (`ProbeWalk_K1`: 8,192 pop-slots of the heavy
`GG_1LC_1LB` subtree with realistic lookup maps -- the same probe as
the "Walk anchor for this container" row).  Both runs end at the
identical queue state `(33, 0)`:

| | wall |
|---|---|
| pre-fix (`existsb`) | **768.9 s** |
| `anyb` | **97.5 s** |
| | **7.9x** |

The pre-fix run reproduces the published 934 s anchor for this probe
on a different container, so the baseline is the documented one.

Read that 7.9x carefully, per the rule this document paid for.  It IS
a walk-level measurement -- a bounded real walk, real decider, real
lookup tables -- but of ONE subtree, and that subtree was chosen
because it is heavy, so it is residue-rich relative to the whole
census.  It is larger than the 4.53x rw-ladder figure because the walk
also pays the `scan_loops` block and the `try_qhb` ladders, and all of
them were eager.  **Expect the full walk to land below 7.9x.  The full
walk is the only thing that settles the full walk.**

### Round two of the same sweep: the guards, and the fuel

With the walk already owed, further catch-neutral work rides along
free, so the sweep continued into the checkers.

**The guard trap.**  `Closure.v`'s per-state gates are `implb` and
`orb` applications, i.e. functions, so BOTH sides always evaluated:

    Definition live_lex_ok (Sl : list A) (cert : St -> list lexcomp) : bool :=
      forallb (fun q' =>
        implb (appears Sl q')
              (rank_ok Sl q' (compute_ranks Sl q')
               || lex_ok Sl q' (cert q'))) all_St.

`cert q'` here IS `rank_procedure` -- the function the row-3 probe had
just measured at ~99% of the qhb lex tier.  It ran for every one of the
four states, including states absent from the closure (where the
implication is vacuous), and it ran even when `rank_ok` had ALREADY
discharged the state.  The same shape guards
`closure_check_neverqh`, `_lex`, `_fuel`, `live_ok`, `state_live_ok`,
`ClosureIdx`'s `idx_check_neverqh` and `lex_check_idx_pool`, plus
`lex_ok`'s per-edge test and `lex_edge_ok`'s component walk.

All rewritten as nested `if`s.  Note these are **definitionally
equal** -- `implb b x` IS `if b then x else true` and `orb b x` IS
`if b then true else x` -- so the value is unchanged and the proofs
went through untouched, except three `assert`s that named the guard in
its `||` form and had to be restated in the `if` form to keep a
syntactic `rewrite` working.

Measured, `ProbeQhbStage.v`, identical answers (36 = 36):

| | before | after |
|---|---|---|
| whole `try_qhb_lex_at` attempt | 20.73 s | **0.613 s** |

**33.8x on the qhb lex tier.**  Row 3b is largely answered not by making
`rank_procedure` faster but by not calling it.

**The fuel.**  `rw_fuel_census` 8192 -> 5120, per row 2 below.

### Walk-level, cumulative

`ProbeWalk_K1`, every run ending at the identical queue state `(33, 0)`:

| | wall | vs main |
|---|---|---|
| main (pre-fix) | 768.9 s | -- |
| `anyb` only | 97.5 s | 7.9x |
| `+` guards `+` fuel 5120 | **80.5 s** | **9.55x** |

Same caveat as before, and it matters more now that the number is big:
this is ONE deliberately-heavy subtree.  The qhb tier moved 33.8x but
the walk probe only moved 1.21x further, because this subtree is not
qhb-heavy -- which is exactly the sort of mismatch that makes
subtree-to-census projection unsafe.  **Expect the full walk below
9.55x.**

### A better catch-diff than sampling

Row 2 changes WHICH machines are caught, and the standing rule sends
that to `gen_rwdiff.sh` on a big sample.  A sample was not needed here,
and the technique generalises:

1. **Monotonicity.**  Lowering `close` fuel can only turn `Some` into
   `None`, so a catch can be LOST but never GAINED.  The gate is
   one-sided -- only currently-caught machines need re-checking.
2. **A census-wide census.**  `tools/repwl_residue_caught.tsv` already
   lists all 25,511 kept catches at the four walked rungs WITH their
   closure sizes.  The at-risk machines are known by name, not sampled.
3. **A closed bound.**  `Run.v`'s own `pops <= 2 * nodes + 1` means only
   a catch whose closure exceeds `(F-1)/2` nodes can be lost at fuel
   `F`.  At F = 4608 that is nodes > 2303, and the table has exactly
   **28** such machines census-wide.

`tools/probes/ProbeRwFuelDiff.v` re-checks the 60 largest closures per
rung (240 machines, a superset of all 28) at 4608 against 8192:

| rung | catches lost | still caught | max pops used |
|---|---|---|---|
| (2,2,0) | **0** | 60 | 3,581 |
| (2,3,0) | **0** | 60 | 3,300 |
| (3,2,0) | **0** | 60 | 3,664 |
| (4,2,0) | **0** | 60 | 4,132 |

Every machine that COULD lose a catch was tested and none did, so this
diff is exhaustive rather than statistical.  5120 ships (safe a
fortiori by monotonicity) leaving ~24% headroom over the largest
closure the census actually walks.

Where a future change is monotone in some parameter and the affected
population is tabulated, prefer this construction over a random
sample -- it is both cheaper and strictly stronger.

## Full re-walk #3, measured end-to-end (2026-08-09)

`time make census-verify` on the same 32 GB desktop, WALK_JOBS=4
(auto), with `anyb`, the checker guards and `rw_fuel_census = 5120`.
The base build was already present (`Nothing to be done for
'real-all'`), so the whole figure is walk, directly comparable to the
walk-only row above.  A full re-derivation, not a resume: `census-verify`
had already moved every unit to a backup, so all 144 units + the
theorem were walked from source.

| | |
|---|---|
| re-walk #2 (2026-08-06), walk-only | 12 h 08 m 48 s |
| **re-walk #3 (2026-08-09), walk-only** | **1 h 43 m 39 s** |
| | **7.03x** |
| core-time | 376 m user + 9 m sys = **385 core-min** |
| parallel efficiency | **93%** across 4 jobs |

`Print Assumptions census_decided` printed exactly
`functional_extensionality_dep` and nothing else.

**The fuel cut is confirmed at census scale.**  `rw_fuel_census`
8192 -> 5120 changes WHICH machines are caught, and a lost catch is
`R_Unknown` -- the queue would not empty and that unit's `Qed` would
fail.  All 144 units closed.  The exhaustive gate (28 at-risk machines,
all tested) held on the real census, not just on the sample.

### What the projections did, for the record

| projected from | projected | delivered |
|---|---|---|
| `ProbeWalk_K1`, one heavy subtree | 9.55x | -- |
| stated expectation in this doc | "below 9.55x", 2-4 h | **7.03x, 1.73 h** |

The subtree probe overshot by ~36%, exactly as its residue-rich
composition predicted it would; the hedge attached to it was the part
that turned out to be load-bearing.  A walk probe of ONE subtree is
worth about "the right order of magnitude, biased high" -- better than
a stage or tier measurement, still not a walk.

### The <1 h goal is now a MEMORY problem, not a CPU problem

385 core-min at 8 jobs is ~48 min ideal, ~52 min at the measured 93%
efficiency.  So the goal needs no further core-time work at all -- it
needs the parallelism the box already has.  On 8 cores / 32 GB:

    jobs = min(8, (32 - 2 GB) / RSS_per_unit)

| RSS/unit | jobs | wall (at 385 core-min, 93%) |
|---|---|---|
| 6.8 GB (today) | 4 | 1 h 43 m |
| 5.0 GB | 6 | ~69 m |
| **<= 3.75 GB** | **8** | **~52 m** |

One number: **per-unit peak RSS <= 3.75 GB**.  32 GB is the target
profile deliberately -- 64 GB is not regular hardware.  Note also that
WSL2 defaults to HALF the host, so a cloner on a 32 GB box gets a 16 GB
VM and only 2 jobs unless `.wslconfig` pins it; that alone is a 2x
reporting error waiting to happen.

`ng_fuel = 200000` is the prime suspect and the top item on the list
below: it bounds the n-gram / rank / qhb closures, so it caps CPU and
peak RSS together.  Cheapest decisive experiment: rebuild the heaviest
unit with `ng_fuel` lowered and read peak RSS off `/usr/bin/time -v`.
That is pure attribution, so the fact that it would move catches does
not matter until a bound is chosen -- and the exhaustive-gate recipe
from row 2 is now proven for choosing one.

## The memory round: attribution, measured (2026-08-09)

The suspect was wrong, and the way it is wrong is the useful part.

### Where a walk unit's 6.8 GB is NOT

Peak RSS is a whole-process high-water mark, so every configuration
needs its own `coqc`.  `tools/probes/gen_rss_probe.py` emits one probe
per (workload, fuel, engine) for exactly that.  All rows below ran
under the walk's own GC settings (`OCAMLRUNPARAM=o=40,O=60`) on a
4-core / 15 GB container, `vm_compute`, one at a time.

First, what `coqc` costs before deciding anything -- `Require` only,
no evaluation at all:

| loaded | peak RSS |
|---|---|
| `Coq.List` alone | 0.084 GB |
| `+ BBB4_Statement` | 0.144 GB |
| `+ Census.Deferred_Data` (16,115 machines) | 0.149 GB |
| `+ ProbeLookup` (14,606 machines) | 0.153 GB |
| `+ ProbeWalkCommon` (the decider and all three maps) | **0.207 GB** |

The lookup tables the walk carries cost about **5 MB each**.  They are
not the memory.

Then the workloads, each above that 0.205 GB floor:

| workload | peak RSS | above floor | eval | queue left |
|---|---|---|---|---|
| floor, nothing evaluated | 0.205 GB | -- | -- | -- |
| the three lookup maps, forced | 0.225 GB | 0.020 GB | 0.48 s | -- |
| C + T bulk tiers, 80 machines | 0.227 GB | 0.022 GB | 0.51 s | -- |
| the residue tier, 40 machines | 0.281 GB | 0.076 GB | 7.70 s | -- |
| `ProbeWalk_K1`: 8,192 pop-slots of the heavy `GG_1LC_1LB` subtree | 0.298 GB | 0.093 GB | 96.5 s | (33, 0) |
| 4x the pop-slots | 0.307 GB | 0.102 GB | 250 s | (17, 0) |
| **16x -- the subtree walked to EMPTY** | **0.307 GB** | **0.102 GB** | **439 s** | **(0, 0)** |
| `ProbeWalk_K1` with the GC untuned | 0.408 GB | 0.203 GB | 90.4 s | (33, 0) |

The last row that matters is the 16x one, and it is not a bounded
probe: the queue reaches `([], [])`, so that IS the whole computation
`Compute/GG_1LC_1LB.v` performs -- the same subtree, the same decider
parameters, realistic lookup tables, every pop of the heaviest unit in
the census, start to finish.  **It costs 0.307 GB, 0.10 GB above the
load floor.**  And the peak is FLAT in walk length: 4.6x the CPU of the
`K1` row moved it 3%.  The walk unit measured natively on the same
subtree peaks at 6.8 GB -- **22x** -- for the identical computation.

So the Makefile's note ("without compaction each unit's RSS is the
high-water mark of its worst pop's transient garbage") had the shape
right and the magnitude wrong by a factor of ~20: the high-water IS
per-pop and bounded, and it is ~0.1 GB.  The note has been corrected in
place.

The honest gap: these are `vm_compute` and the walk is
`native_compute`.  What transfers is not the byte count but the LIVE
SET -- how many values exist at once is a property of the algorithm,
identical in both engines; only bytes-per-value differ.  For the
decider's transient garbage to be 6.8 GB natively, native values would
have to be ~22x fatter than VM values, which they are not.  So the
memory is somewhere else -- and the next probe found it.

(A hazard worth knowing on its own: apt's Coq is built
`COQ_NATIVE_COMPILER_DEFAULT=no`, and `native_cast_no_check` then falls
back to VM conversion with a WARNING rather than an error -- so a "walk"
on the wrong Coq looks like it succeeded.  It is also what makes the
next section possible: the fallback lets a real walk unit's computation
run in this container, on the VM.)

### Where it IS: 2.74 GB of a walk unit is `Require`, not walking

`gen_rss_probe.py`'s `unit` workload is not a stand-in.  It is Run.v's
own `q_suc` -- the real `decider`, the real `proven` / `provenqh` /
`deferred` maps -- rooted at `Run_Split2.q_ggsub S1 DL StB`, i.e. the
exact computation `Compute/GG_1LC_1LB.v` performs, cut to `--iter` of
its 700 rounds.  `--iter 0` walks nothing at all:

| the real unit | peak RSS | eval | queue left |
|---|---|---|---|
| **`Require` Run + Run_Split + Run_Split2, evaluate NOTHING** | **2.743 GB** | 0.4 s | -- |
| + one round (8,192 pop-slots) | 3.667 GB | 146 s | (33, 0) |
| **+ sixteen rounds -- the unit's subtree walked to EMPTY** | **3.667 GB** | 744 s | **(0, 0)** |

The bottom row is the whole unit: `GG_1LC_1LB`'s computation, run to
`([], [])`, on Run.v's real decider and real tables.  **2.743 of its
3.667 GB is spent before the first machine is decided**, and every one
of the 154 files the walk compiles pays it.  Where:

| `Require` | peak RSS |
|---|---|
| `Census.Deferred_Data` (16,115 machines) | 0.149 GB |
| `Census.RerootQH_Data` | 0.228 GB |
| `Census.ProvenQH_Data` | 0.314 GB |
| **`Census.Proven_Data`** | **2.650 GB** |
| -- of which `Proven_00..07` | 1.735 GB |
| -- of which `Machines.ListCStage.LCStage_00..15` | 1.205 GB |
| -- of which `Machines.ListCStage2.LCS2_00..08` | 0.163 GB |
| `Census.Run` (all of the above) | 2.723 GB |

`Proven_Data.v` is 53 lines.  What costs 2.65 GB is its `Require`
line: the boarded-machine THEOREMS behind `proven_all`.  The walk
needs `proven_list` -- the machine data, for `dmap_of` -- and it needs
`decider_WF` as an opaque constant; it never looks inside
`proven_00_nqh` or any `LCStage` board.  Coq has no way to load part of
a library, so the whole thing comes in.

That also explains the rest of the number, and the explanation is
mechanical rather than mysterious.  OCaml's `space_overhead` (`o=40`)
is a target for heap slack *relative to live data*, so

    peak RSS  ~  live set x (1 + o/100)  +  transient

and with 2.74 GB of environment permanently live, `o=40` alone budgets
~1.1 GB of slack on top of it -- which is what the +0.92 GB from
`--iter 0` to the full walk is, not the decider's 0.09 GB of garbage.
Note it does not grow from there: one round and sixteen rounds have the
identical 3.667 GB peak.  Natively the live set is larger again (the
same `.vo` data plus linked `.cmxs` code), and 6.8 GB is what that
multiplier gives.  **The `WALK_OCAMLRUNPARAM` tuning that took 11-12 GB
down to 6.76 GB was never tuning the decider; it was tuning the
multiplier on an environment nobody had measured.**

The same walk in a LEAN environment is the control, and it is already
in the table above: `ProbeWalkCommon` carries data-only lookup tables
of the same size and no board proofs, its floor is **0.207 GB**, and
the identical subtree walked to an empty queue on it peaks at **0.307
GB**.  Same computation, same GC settings, 12x less memory.

So the target -- per-unit peak <= 3.75 GB -- is not a decider problem
at all.  It is:

1. **the environment a walk unit loads** (2.74 GB, ~40% of the native
   peak, and the walk half of a unit does not need most of it), and
2. **the GC multiplier applied to it** (`o`), which is the cheapest
   experiment anyone can run and needs no rebuild.

Neither is a fuel.  Row 2 below is closed on its own evidence; this is
why it was never going to be the answer.

#### Lever 1: the environment.  The same data, as DATA, costs 4 MB

`Proven_Data` costs 2.65 GB because of what is behind `proven_all`.
The unit's expensive half -- `Lemma gg_1LB_empty : Nat.iter 700 q_suc
... = ([], [])`, the `native_cast_no_check` that runs for minutes --
needs `q_suc`, hence `proven_list` as DATA.  `decider_WF`, the only
thing `proven_all` feeds, is used solely by the CHEAP half
(`gg_1LB_decided := ggsub_decided ... gg_1LB_empty`, an `exact` that
takes milliseconds).

The size of that gap is already sitting in the floor table above.
`ProbeLookup.v` is the same machine lists (`tools/proven_map.tsv`,
`provenqh_map.tsv`, the holdouts -- 14,606 machines) emitted as pure
data with no theorems, and it loads in **0.004 GB**.  Data-only: 4 MB.
Boarded: 2.65 GB.

So the shape of the fix is to split each walk unit in two, against a
`Run_Compute`-style module that exports `q_suc` and the `q_*sub` roots
and requires only the data:

- `..._walk.v` -- the `_empty` lemma, minutes of `native_compute`, in a
  ~0.2 GB environment instead of a 2.74 GB one;
- `....v` -- the `_decided` lemma, `Require`s `Run`/`Run_Split2` and
  the walk file, and is over in milliseconds.

Soundness is untouched: as long as `Run.v` takes its `q_suc` FROM that
module rather than defining a second one, both halves name the same
constant and the existing chain goes through verbatim.  What changes is
only which environment is resident while the expensive half runs.  The
work is in re-emitting `proven_list` / `provenqh_list` /
`reroot_qh_list` from `tools/*_map.tsv` as data-only files
(`tools/gen_proven.py` already generates their current form), and it
wants its own round with the walk that validates it.

#### Lever 2: the multiplier.  Measured, and it does NOT pay alone

`o` is the OCaml GC's space-overhead target, so it multiplies whatever
the live set is.  The same real unit computation (one round, queue to
(33,0)), one run per setting:

| `OCAMLRUNPARAM` | peak RSS | eval | vs shipped |
|---|---|---|---|
| untuned | 5.474 GB | 137.5 s | +49% RSS, -4% CPU |
| `o=80,O=150` | 4.539 GB | 136.3 s | +24% RSS, -5% CPU |
| **`o=40,O=60` (shipped)** | **3.667 GB** | **143.2 s** | -- |
| `o=20,O=30` | 3.323 GB | 157.1 s | **-9% RSS**, +10% CPU |
| `o=10,O=20` | 2.959 GB | 186.8 s | **-19% RSS**, +30% CPU |

The shipped setting is well chosen and tightening it further does not
pay **on its own**, because `WALK_JOBS` is integer.  Applying these
ratios to the native 6.8 GB: `o=20` gives ~6.2 GB, still 4 jobs on
32 GB, for +10% core-time -- strictly worse.  `o=10` gives ~5.5 GB,
which does reach 5 jobs, but +30% core-time eats it (502 core-min / 5
vs 385 / 4).

It pays only in combination, and that is the arithmetic to aim at:

| configuration | native peak (est.) | jobs on 32 GB | core-min | wall |
|---|---|---|---|---|
| today | 6.8 GB | 4 | 385 | 103 min |
| lever 1 alone | ~4.15 GB | 7 | 385 | **~59 min** |
| lever 1 + `o=20` | ~3.76 GB | 7-8 | 422 | ~57-65 min |
| lever 1 + `o=10` | ~3.35 GB | 8 | 502 | ~67 min |

Read those as estimates with a mechanism, not measurements: the GC
ratios are VM-measured and the 2.65 GB subtraction is a VM floor, while
6.8 GB is native.  Natively the saving should be larger, not smaller
(native also links `.cmxs` code for every library it loads).  The row
that matters is that **lever 1 alone plausibly clears the hour**, and
that the layer barriers below then become the thing between ~59 min and
~52 min.

### `ng_fuel = 200000` is a cap that is never reached

Row 2's premise was that `ng_fuel` bounds the n-gram / rank / qhb
closures and therefore caps CPU and RSS together.  A cap only costs
what it is actually charged for.  Cutting it 10x, holding everything
else fixed:

| `ng_fuel` | residue sample (40) | `ProbeWalk_K1` | answer |
|---|---|---|---|
| 200,000 (shipped) | 0.281 GB / 7.70 s | 0.298 GB / 96.5 s | (33, 0) |
| 20,000 | 0.278 GB / 7.89 s | 0.296 GB / 97.6 s | (33, 0) |
| 2,000 | 0.279 GB / 5.48 s | 0.296 GB / 94.2 s | (33, 0) |

Nothing moves at 20,000 -- not time, not memory, not one catch.  At
2,000 the time finally drops, which locates the binding point between
the two.  `tools/probes/ProbeNgFuel.v` then measures it directly:
`ng_explore` (inside `ng_grow`) and the n-gram `Closure.close`
instrumented to report (status, nodes seen, fuel LEFT), over the
residue sample plus all four n-gram tier samples, 104 machines:

| rung | explores that burned all 200,000 | max explore pops | closes that burned all 200,000 | max close pops |
|---|---|---|---|---|
| (2, 100) | **0** | 257 | **0** | 257 |
| (3, 200) | **0** | 693 | **0** | 693 |
| (4, 400) | **0** | 1,985 | **0** | 1,985 |
| (6, 800) | **0** | 17,665 | **0** | 17,665 |

Not one of the 416 explores and 416 closures exhausted the fuel; the
largest consumption census-side is **17,665 pops against a cap of
200,000**, an 11x margin.  **Row 2 is empty and should be closed, not
scheduled.**

This is the opposite of the `rw_fuel` story and the contrast is the
lesson.  There, half the machines reaching (3,2,0) burned the whole
8,192 -- the cap WAS the workload, so lowering it refunded real time.
Here nothing diverges, so `ng_fuel` is latent, like the `(S t <=? B)`
gates: a bound that is never tested costs exactly zero, and lowering it
buys exactly zero while risking catches.  Before sizing a parameter,
measure what it is charged, not what it permits.  Note also that fuel
consumption is counted in worklist pops, so this table is
engine-independent -- it holds under `native_compute` unchanged, which
is what lets it close the row despite everything above being VM.

### The tier split, re-measured -- and the old H row was a timer artefact

`ProbeTierCost` re-run at 6x the sample (1,440 machines: 240 each of
H / C / T / residue, 96 each of N2/N3/N4/D), with the same weighting by
census node counts as the 2026-08-05 table.

First, a bug in the instrument, because it changes a published number
by 100x.  `vm_compute` compiles the whole `decider0` closure -- the
pipeline plus all three lookup tables -- to bytecode on its FIRST use,
and charges that one-off to whichever `Time Eval` runs first.  That is
the H row.  The old table's "H halt: 8.45 ms/machine" was almost
entirely bytecode compilation; measured behind a warm-up, halting
machines cost **0.013 ms**.  `gen_tier_cost.py` now emits the warm-up
itself, so the row cannot lie again.

| tier | census nodes | per machine | modelled | share |
|---|---|---|---|---|
| **residue (ladder-decided)** | 228,815 | **221.7 ms** | 50,727 s | **93.7%** |
| T translated cycle | 2,282,976 | 0.542 ms | 1,237 s | 2.3% |
| N n-gram (all four rungs) | 200,064 | 2.8-31.0 ms | 1,703 s | 3.1% |
| C in-place cycle | 1,029,749 | 0.454 ms | 468 s | 0.9% |
| H halt (expand) | 249,692 | 0.013 ms | 3 s | 0.01% |
| D deferred lookup | 3,708 | 0.073 ms | 0 s | ~0% |

**The expectation going into this round was that the residue's share had
FALLEN**, since the residue tiers gained 4.5-33.8x last round while the
C/T bulk block gained only 2.4-3.6x.  It went the other way.  Against
2026-08-05, per machine: T is 27.7x faster (15.0 -> 0.542 ms), C is
11.8x (5.35 -> 0.454), the residue is 7.0x (1.55 s -> 0.222 s).  The
2.4-3.6x figure was the `anyb` fix in isolation; the bulk had also
already banked `scan_ct`'s deletion and the one-pass scan.  So the
residue's share went **85% -> 93.7%**, and the whole C+T+H bulk is now
**3.2%** of the walk.

Two consequences.  First, the model finally reconciles: 902 core-min of
modelled vm against 385 core-min of observed native is a vm/native
ratio of **2.34x**, right where a Coq VM-vs-native gap belongs -- the
2026-08-05 model was 12-20x short of the observed walk, which was
itself the loudest sign it was wrong.  Second, **there is nothing left
to win in the bulk.**  Every scan-side item -- `cvisits` in
`cycle_check_neverqh`, the `scan_loops` double simulation, the C/T
candidate ordering -- is competing for a 3.2% slice.  Anything that is
not the residue, or is not memory, is now noise.

### Where the rw fuel actually goes: 89% of it buys nothing

The contrast above raises the obvious question about the OTHER fuel, so
`tools/probes/ProbeRwFuelRungs.v` asks it: `ProbeRwFuel`'s instrumented
`close` at the shipped 5,120, per rung, over the machines that reach
that rung under the shipped ladder order.

| rung | reaching | converged | **exhausted** | max pops converged | pops burned |
|---|---|---|---|---|---|
| (2,2,0) | 40 | 34 | **6** | 777 | 36,984 |
| (3,2,0) | 10 | 6 | **4** | 796 | 23,318 |
| (4,2,0) | 8 | 4 | **4** | 1,023 | 22,122 |
| (2,3,0) | 8 | 4 | **4** | 353 | 21,105 |

(The (3,2,0) row reproduces `ProbeRwFuel`'s independently-measured
"10 machines still reach the rung, 6 converge, 4 diverge" exactly,
which is the probe's calibration check.)

18 diverging attempts burn 18 x 5,120 = 92,160 of the 103,529 closure
pops the tier spends: **89% of all RepWL closure work is closures that
diverge and return no verdict.**  Converged closures finish in 353-1,023
pops here, against a census-wide worst-case of 4,132 among CAUGHT
machines (`ProbeRwFuelDiff`).

Two conclusions, and the second is the useful one:

- A lower cap trims the 89% strictly linearly, and the room is small.
  `ProbeRwFuelDiff` already gated **4,608** exhaustively (240 machines,
  a superset of all 28 that could lose a catch, zero lost); 5,120 was
  then shipped a fortiori for margin.  Re-tightening to the number that
  was actually gated refunds 10% of the diverging burn and cuts the
  headroom over the largest walked closure from 24% to 11.5%.  That is
  a bad trade in a round where core-time is margin and memory is the
  binding constraint -- **not taken.**  A per-rung cap
  (`ProbeRwFuelDiff`'s 3,581 / 3,300 / 3,664 / 4,132 plus headroom)
  reaches ~16% instead of 10%, and costs a fourth tuple component
  through `try_rw` plus a fresh exhaustive gate per rung.  Also not
  taken, for the same reason -- but now it is sized rather than
  guessed.
- The lever that is NOT linear is deciding these closures diverge
  without walking them to the cap.  89% of the tier's pops are spent
  proving nothing, and no choice of cap changes that ratio.  That is
  the shape of a real round, and it wants its own scoping.

### `cvisits` is paying the eager-`orb` tax, and it is small

`Cycle.cvisits` -- "does state q occur in the next `len` steps" -- is
`st_eqb (fst c) q || <recurse>`, and `orb` is a function, so it walks
the full `len` even when q is the state of the very first
configuration.  It is reached from every closure checker's guard
(`Closure.closure_check_neverqh`: four states, `t` up to 1024, per
rung, per tier), from `Cycle.cycle_check_neverqh` in the C tier, and
from `Wrap.v`'s prefix-quiet gates in the qhb tier -- 21 files mention
it.  `tools/probes/ProbeCVisits.v` A/Bs it against the nested-`if`
form, at the prefix lengths the census actually asks for
(0/64/100/200/256/400/800/1024) and all four states:

| population | eager `\|\|` | nested `if` | ratio | counts |
|---|---|---|---|---|
| residue + n-gram, 104 machines | 0.600 s | 0.138 s | **4.35x** | 2912 = 2912 |
| C/T bulk, 80 machines | 0.415 s | 0.099 s | **4.19x** | 2233 = 2233 |

Same 4-5x as every other instance of this trap.  But the ABSOLUTE
number is what decides: one full sweep of every census prefix length
for all four states costs 5.8 ms/machine against the residue tier's
221.7 ms/machine, so `cvisits` is ~2.6% of that tier and
short-circuiting it recovers ~2% of the walk.  **Not taken this
round**: the win is inside the margin, the change lands in the file 21
others depend on, and the tactic sites that name the `||` shape
(`Cycle.v`'s `apply orb_prop` / `orb_true_intro`, `TCyclerN.v`'s
`cbn [cvisits]`) have to be restated against a full-tree rebuild.
Sized, recorded, and available the next time a walk is owed for another
reason.

The `scan_loops` double simulation (`decide_easy` runs gas 130, then a
fresh `lp_run` at 512 that re-simulates the first 130 steps) needs no
probe at all now: it wastes 130 of 642 steps for machines that fall
through the cheap rung, inside a C+T+H block that the re-measured split
puts at **3.2% of the walk**.  Its ceiling is ~0.6%.  Closed as not
worth a round.

### What the next walk measures by itself

Every walk now records, per unit, its peak RSS and its wall and user
seconds to `census_probes/walk-rss.tsv` (`/usr/bin/time` wrapping the
existing `coqc`; `WALK_RSS=` disables it).  This costs nothing, touches
no census input -- `tools/census_cache.py` hashes the census `.v` only
-- and replaces the one hand-measured unit from 2026-08-04 that the
entire `WALK_JOBS` formula rests on with 154 measurements.

`python3 tools/walk_rss_report.py` reads it back: the RSS distribution,
per-layer CPU, the heaviest units by name, and the wall time predicted
at each job count.  `WALK_RSS_GB=N` then feeds a measured peak straight
back into the Makefile's sizing.

It also models something the 93% figure hides.  **The walk is six
BARRIERS, not one pool**: `Run_Split` (1 unit), `Run_Split2` (1), the
`Run_Split_<tag>` layer (7), `GG_1LC_*` (16), `GGH_*` (104), `G_*`
(24).  A layer costs its makespan, and no job count above a layer's
unit count helps that layer.  93% was measured AT 4 JOBS; at 8 the two
single-unit layers and the 7-unit layer are twice as expensive
relatively, so 385 core-min / 8 / 0.93 = 52 min is a floor, not a
forecast.  The report's schedule model puts the same profile nearer 60
min at 8 jobs.  That does not change the memory target -- it says the
tail layers become the next thing worth splitting once the memory
target is met, and `tools/gen_gsplit_heavy.py` is the existing tool for
it.

### The native experiment this round could not run

apt's Coq has no native compiler (`native_cast_no_check` silently falls
back to VM conversion), so the split of the 6.8 GB between "engine
fixed cost" and "the walk itself" needs the census opam switch.  It is
four `coqc` runs and a few minutes, not a walk:

```sh
for it in 0 1 4 16; do
  python3 tools/probes/gen_rss_probe.py unit /tmp/U_$it.v --iter $it --native
  OCAMLRUNPARAM=o=40,O=60 /usr/bin/time -v \
    coqc -Q theories BBB4 -Q tools/probes BBB4 /tmp/U_$it.v
done
```

`unit` is the REAL walk unit's computation -- Run.v's own decider and
lookup maps, rooted at `Run_Split2.q_ggsub S1 DL StB`, i.e. exactly
what `Compute/GG_1LC_1LB.v` walks -- cut to `--iter` of its 700 `q_suc`
rounds.  `--iter 0` walks nothing, so its peak RSS IS the engine's
fixed cost: load, translate, `ocamlopt`, link.  The VM rows above give
the shape to expect the walk part to have (flat in `--iter`), so:

- if `--iter 0` is already most of 6.8 GB, the memory lever is the
  engine and the unit granularity, and no pipeline parameter will ever
  matter;
- if it is small and the number climbs with `--iter`, then native's
  per-pop high-water really is ~70x the VM's, and that ratio -- not any
  fuel -- is the thing to attack.

Either answer picks the next round.  Neither needs a census walk.

## Next steps, re-ranked by the memory round (2026-08-09)

This supersedes the 2026-08-07 list below, which is kept for its
reasoning.  Of that list: row 1 landed, row 2 (`ng_fuel`) is CLOSED as
empty and row 3 was already closed, row 4 is unchanged and repeated
here, and row 5's premise is re-measured above.

The goal is one number -- per-unit peak RSS <= 3.75 GB gets 8 jobs on
8 cores / 32 GB -- and it is now attributed.  Core-time is margin: 385
core-min at 8 jobs is under an hour with room to spare, and the whole
non-residue bulk is 3.2%.

**M1.  Split the walk units against a data-only compute module.**  The
round's main result: 2.74 of a unit's 3.667 GB (VM) is `Require`, and
2.65 GB of that is `Proven_Data`'s boarded-machine theorems, which the
expensive half of a unit never looks inside.  The same machine lists as
DATA cost 4 MB.  Estimated to take the native peak from 6.8 GB to
~4.15 GB -- 7 jobs on 32 GB, ~59 min -- with no change to the proof
chain, only to which environment is resident while `native_compute`
runs.  Wants its own round: it re-emits three generated data files and
re-wires `Run.v`, and it is a census-input change, so it is gated on
the walk that also validates it.

**M2.  Run the native decomposition first.  Four `coqc` runs.**  M1's
estimate is a VM floor applied to a native peak.  The recipe at the end
of the previous section settles it in minutes on the census switch, and
its `--iter 0` row IS M1's payoff, measured rather than estimated.  Do
this before committing to M1.

**M3.  The layer barriers.**  The walk is six barriers, and at 8 jobs
`Run_Split` (1 unit), `Run_Split2` (1) and `Run_Split_<tag>` (7) cannot
use the cores.  93% parallel efficiency was measured AT 4 JOBS; the
schedule model in `tools/walk_rss_report.py` puts the same profile
nearer 83% at 8.  This is what stands between M1's ~59 min and the
~52 min the core-time allows, and `tools/gen_gsplit_heavy.py` already
splits heavy subtrees.  Cheap, but pointless before M1: today the box
cannot run 8 jobs at all.

**M4.  Early divergence detection in the RepWL closure.**  89% of the
tier's closure pops are closures that diverge to the cap and return no
verdict (measured above).  No choice of cap changes that ratio -- a cap
only trims it linearly, and the room left is ~10-16%.  This is the only
remaining CPU item with real headroom, it is in the 93.7%, and it is
research rather than a parameter change.

**M5.  Index-keyed certificate tables -- still deferred.**  Unchanged
from the old row 4: `vals_of` pays `#pool * #comps` big-key lookups per
state because the certificate's tables are keyed by `rconf_enc`, and
having the search emit index-keyed tables would halve that at the cost
of every `RerootStage` proof.  Still not worth it.

**Closed, with the evidence, so they are not re-derived:** `ng_fuel`
(never reaches its cap: 17,665 pops against 200,000); the `scan_loops`
double simulation (ceiling ~0.6%); `cvisits`'s eager `orb` (4.2-4.4x on
the function, ~2% of the walk, 21-file blast radius) -- the last one
worth riding along the next time a walk is owed anyway, not worth
owing one for.

## Next steps, in Amdahl order (2026-08-07, superseded)

Rows 2-4 are "What is left in the rw tier" above, re-ordered by
expected value per unit of risk and with probe prerequisites made
explicit.  Row 1 is new.  Row 5 is the part that does not close.

### 1. DONE -- and it was not small

The sweep of `Decide.v` / `Run.v` and their hot-path callees found one
class of trap, everywhere, and it is the `existsb`/`forallb`
strictness above: 4.53x on the rw ladder, 2.4-3.6x on the C/T bulk
block, 7.9x on the walk probe, zero catch movement.  Landed.

Two further sites were read and deliberately NOT changed, with
reasons, so the next sweep does not re-derive them:

- **`Closure.v`'s checker internals** -- `lex_edge_ok` decides an edge
  with `comp_strict c || (comp_noninc c && lex_edge_ok rest)`, so it
  always walks the WHOLE component list; `lex_ok`/`rank_ok`/`closed_b`
  are `forallb`, so a failing node never stops the sweep; and
  `closure_check_neverqh*` guards its expensive check with
  `implb (appears) (lex_ok ...)`, so the check runs for all four
  states including absent ones.  All real, all the same shape.  Not
  taken this round because `ProbeRwStage` already showed the (3,2,0)
  attempt is ~98% `close` -- which has no eager boolean in it -- so
  the reachable win is small where the time actually is, and these
  edits carry real proof risk in a file every tier depends on.
  `ClosureIdx.v`'s interned path already fixed its own copy
  (`vlex_edge_ok` is nested-`if`), which is why the rw tier does not
  pay the worst of it.

- **`(S t <=? B) &&` in `try_qhb_at` / `try_qhb_lex_at`, and
  `(1 <=? L) && (2 <=? T) &&` in `rw_check_neverqh*`** -- eager, but
  the gates are true for every rung the census ships (max `t` = 1024
  against `B` = 2000; `L >= 2`, `T >= 2`), so the win is exactly zero.
  Latent only.

### 2. The (3,2,0) closure search -- sized, and the sizing moved it

`ProbeRwFuel.v` instruments the fuel exhaustion the old row 2 was
built on.  On the residue sample at (3,2):

| | |
|---|---|
| closures that CLOSE | 21/40 |
| closures that burn all 8,192 | 18/40 |
| **max pops among closures that converge** | **1,264** |
| **max pops among machines actually CAUGHT** | **1,264** |
| caught machines needing > 2,048 pops | **0** |
| machines still reaching the rung after fix #1 | 10 (6 converge, 4 diverge) |

So divergence is detectable early: a converged (3,2,0) closure never
needs more than ~1.3k pops against a cap of 8,192.

But the lever is not the one the old row 2 named.  It is not
"detect divergence and abort", it is **`rw_fuel_census` is sized for
rungs the walk does not run.**  `Run.v` justifies fuel 8192 with "the
largest kept catch closes in 7947 nodes / 8145 pops".  That catch is
at rung **(6,2,0)** -- a lever-C rung, deferred, NOT in the 19,735
walk (`tools/repwl2_caught.tsv`).  Across all 25,511 kept catches at
the four rungs the walk DOES run (`tools/repwl_residue_caught.tsv`),
census-wide:

| rung | catches | max closure nodes | > 4,096 nodes |
|---|---|---|---|
| (2,2,0) | 21,727 | 3,243 | 0 |
| (3,2,0) | 2,221 | 3,381 | 0 |
| (4,2,0) | 980 | 3,963 | 0 |
| (2,3,0) | 583 | 3,036 | 0 |

Not one walked catch exceeds 3,963 nodes (~4.1k pops at the measured
1.03-1.05 pops/node).  A lower `rw_fuel_census` is a ONE-LINE change
in `Run.v` with no proof impact at all -- fuel is a Section variable
and `rw_tier_sound` quantifies over it.

**Not shipped this round, deliberately.**  It changes WHICH machines
are caught, and in the census a lost catch is not a coverage
regression -- it is `R_Unknown`, i.e. the walk does not close.  The
table above is strong evidence and it is not the gate; the gate is
`gen_rwdiff.sh` on the big sample, adapted to diff fuel-8192 against
the candidate fuel.  Note also that fix #1 already shrank this lever:
only 10/40 residue machines now reach the rung at all, against 40/40
before.

### 3. The qhb tier -- probed, and it dies

`ProbeQhbStage.v`, the `ProbeRwStage` recipe pointed at
`try_qhb_lex_at`, over the residue sample (40 machines, 54
(state, rung) attempts -- the `qh_candidate` filter is doing a lot of
work):

| stage | time | share |
|---|---|---|
| `ng_grow` | 0.117 s | 0.6% |
| + `ng_explore` | 0.155 s | 0.7% |
| + `rank_procedure` (untrusted certificate search) | **21.51 s** | **~99%** |
| the whole attempt incl. the verified stage | 20.73 s | -- |
| the whole PLAIN (non-lex) 9-rung ladder | 0.298 s | -- |

The whole attempt costs no more than the certificate search alone, so
the verified stage is within noise of zero.  **The ClosureIdx-lex
treatment is worth ~nothing on the qhb tier** -- it removes duplicated
verified-stage work, and there is no verified-stage cost here to
remove.  Row 3 is closed for the cost of one probe instead of one
round, which is what it was gated for.

The hypothesis it was gated on was wrong in an interesting way: the
tier is not `ng_grow`/`ng_explore`-bound either (0.7%).  It is
**`rank_procedure`-bound**, and `rank_procedure` is UNTRUSTED search,
so it can be replaced outright with no soundness argument.  That is a
new row, below.

### 3b. NEW: `rank_procedure` is 99% of the qhb lex tier

Straight out of the probe above.  Untrusted, so it carries no proof
weight, and it is the same shape of target the interned `RepWLSearch`
core was (that one paid 2.33-4.4x on failing attempts).  Nothing has
been measured about *why* it is slow yet -- that is the next probe,
not the next round.  Note the lex ladder is ~70x the plain ladder
(20.7 s vs 0.298 s), so anything that lets the plain ladder decide
more machines is also worth real time.

### 4. Index-keyed certificate tables -- still deferred

`vals_of` pays `#pool * #comps` big-key lookups per state because the
certificate's tables are keyed by `rconf_enc`.  Having the search
emit index-keyed tables would halve that, but it changes the `rwcomp`
denotation and therefore every `RerootStage` proof.  Unchanged
verdict from last round: not worth it until row 2 stops dominating.

### 5. What does not close, stated plainly

Rows 1-4 plausibly total 1.3-2x.  13.7 h -> ~1 h is ~14x.  The
arithmetic does not close with rung-by-rung work, and saying so here
is cheaper than discovering it a fourth time.

The disproportion to attack is that **~85% of the walk is
residue-class ladder burn against ~4.9% of nodes**.  The bulk is
already fine; a few thousand hard machines eat the walk.  So the 14x
has to come from the residue getting SMALLER, not just faster -- a
cheap decider that catches a chunk of those machines before they
reach the expensive rungs at all.  That is the BB5-shaped insight
from the packed arc's write-up pointed at the tail instead of the
bulk: BB5 decides 96.7% of 181M machines in one <=130-step pass, and
our equivalent bulk is not what is costing us.

That is a different kind of round from rows 1-4 and should be scoped
deliberately rather than drifted into.

**Update (2026-08-09).**  The 14x arrived without any of this: the
`existsb`/`orb` sweep alone delivered 7.03x on the real walk, and
385 core-min is already an under-an-hour figure at 8 jobs.  The
disproportion this row names got WORSE, not better -- the residue is
now 93.7% of the walk against 3.2% for the whole bulk -- but it stopped
being the binding constraint, because the constraint moved to memory.
The row stands as the right description of where the CPU is; it is no
longer the thing between here and the goal.

## Measurement status

tools/probes/ has the vm_compute harness (per-tier timings on four
machine classes; bounded walks of the heavy `GG_1LC_1LB` subtree
with realistic lookup maps, instrumented for time and peak RSS).  Per
the playbook these are container-safe (minutes each, no
native_compute, no full walk).

The 2026-08-07 round ran under a stock Ubuntu `apt-get install coq`
(Coq 8.18.0), which is enough for every probe here -- no opam switch
and no `coq-native` needed, since nothing in tools/probes/ loads a
committed census `.vo`.  Numbers in the CORRECTION section above were
taken that way, one run per configuration, on a 4-core container whose
other load was controlled (probes run one at a time; the walk A/B in
particular was run with nothing else on the box).  Treat them as
"about", not as three significant figures.

The 2026-08-09 memory round ran the same way, plus one thing that had
never been tried: apt's Coq is built with the native compiler DISABLED,
so `native_cast_no_check` falls back to VM conversion with a warning
instead of failing.  That is a trap when you want a walk, and a gift
when you want to instrument one -- it is what let a real walk unit's
computation (`Run.v`'s decider, real tables, `Run_Split2`'s root) run
here to an empty queue for peak RSS.  The committed `Run_Split*.vo`
must be moved aside first: they were built under the census switch's
OCaml 4.14.2 and will not load under apt's 4.14.1 (that failure is loud
and immediate).

Nothing in this round pends a walk.  Every census `.v` is untouched, so
the committed `.vo` still certify the tree; the changes are the
Makefile's walk instrumentation, `tools/`, and documentation.  The next
walk is worth running as a MEASUREMENT rather than a validation: it now
writes `census_probes/walk-rss.tsv` and `tools/walk_rss_report.py`
turns that into the per-unit RSS distribution the whole `WALK_JOBS`
question rests on.

Two numbers this round would still like, in cost order: the native
`--iter 0` row (M2 -- minutes, no walk), and that walk-rss table (free,
whenever a walk happens for any reason).
