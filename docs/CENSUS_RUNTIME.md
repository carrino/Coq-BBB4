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

### Walk anchor for this container

`ProbeWalk_K1` (8,192 pop-slots of the heavy `GG_1LC_1LB` subtree,
realistic lookup maps): **934 s wall, 114 ms/pop, 0.82 GB peak RSS**,
vm_compute.  Native runs ~3-5x faster on this code, so treat 114 ms
as an upper bound and use it only for ratios.

### What this means for the ~1 h goal

The n-gram ladder is ~4.9% of nodes and (heavy-subtree attribution)
~30% of walk time.  Even 7.4x on its verified stage is ~1.8x on a
catch, ~2.7x with `ng_grow` packed and `cvisits` single-passed, and
only ~1.2-1.35x on the whole walk.  13.7 h -> ~1 h needs ~14x, and
**that factor can only come from the 83% cycle/translated-cycle
bulk** -- i.e. option 1 (the BB5 one-pass loop decider: no per-step
rolling hash, no `PositiveMap` snapshot insert), which is axiom-free.
Recommended reordering of the arc: scan tiers FIRST, n-gram packing
second.

## Measurement status

tools/probes/ has the vm_compute harness (per-tier timings on four
machine classes; bounded walks of the heavy `GGH_0RB_1LC_0LB` subtree
with realistic lookup maps, instrumented for time and peak RSS).
Numbers pending a Coq-capable environment; per the playbook these are
container-safe (minutes each, no native_compute, no full walk).
