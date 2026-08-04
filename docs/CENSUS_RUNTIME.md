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

## Measurement status

tools/probes/ has the vm_compute harness (per-tier timings on four
machine classes; bounded walks of the heavy `GGH_0RB_1LC_0LB` subtree
with realistic lookup maps, instrumented for time and peak RSS).
Numbers pending a Coq-capable environment; per the playbook these are
container-safe (minutes each, no native_compute, no full walk).
