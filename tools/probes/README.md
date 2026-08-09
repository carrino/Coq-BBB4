# Census runtime probes (untrusted, not part of the proof)

Measurement scaffolding for the census-walk runtime investigation
(why Coq-BB5 walks 181M machines in ~10 core-hours while our 4M-node
census takes ~32-48; see docs/CENSUS_RUNTIME.md).  Nothing here is in
`_CoqProject` and nothing loads into the proof.

Build (any Coq 8.18, vm_compute only — container-safe):

```sh
# dependency closure, ~16 lemma files + the Deferred tables
make Makefile.coq  # or coq_makefile -f _CoqProject -o Makefile.coq
make -f Makefile.coq theories/Census/Decide.vo theories/Census/Deferred_Data.vo \
  theories/Census/RankSearch.vo theories/Census/RepWLSearch.vo
# probes compile against the theories tree plus this dir on the same root
python3 tools/probes/gen_probe_lookup.py > tools/probes/ProbeLookup.v
coqc -Q theories BBB4 -Q tools/probes BBB4 tools/probes/ProbeLookup.v
coqc -Q theories BBB4 -Q tools/probes BBB4 tools/probes/ProbeTiers.v
coqc -Q theories BBB4 -Q tools/probes BBB4 tools/probes/ProbeWalkCommon.v
/usr/bin/time -v coqc -Q theories BBB4 -Q tools/probes BBB4 tools/probes/ProbeWalk_K1.v
```

- `ProbeTiers.v` — per-tier `Time Eval vm_compute` on four machine
  classes: in-place cycler, translated cycler, holdout #1 (full failing
  ladder), the champion.  Empty lookup maps, Run.v parameters verbatim.
- `ProbeLookup.v` — GENERATED stand-in lookup table (union of the
  proven/provenqh/holdout tools lists, 14,606 machines) so the walk
  probe's lookup tiers behave cost-wise like the real walk's.
- `ProbeWalkCommon.v` — Run.v's decider re-instantiated with that
  table + the real `D_census` map, rooted at the heavy
  `GG_1LC_1LB` subtree (`Run_Split2.ggchild S1 DL StB`; the walk
  unit of the same name -- NOT `GGH_0RB_1LC_0LB`, which is a different
  and much lighter family).
- `ProbeWalk_K<K>.v` — walk `K * 8192` pop-slots of that subtree under
  `Time`/`/usr/bin/time -v` for time-per-pop and peak-RSS curves.
- `ProbeTierCost.v` — GENERATED (committed, 240 machines): per-tier
  cost of the real decider on machines sampled from the C mirror's
  full-census classification.
- `ProbeOrb.v` — the isolated fact that `existsb`/`forallb` do NOT
  short-circuit under CBV (they are `f a || existsb l` / `f a &&
  forallb l`, and `orb`/`andb` are functions).  Run this one first if
  the finding ever looks doubtful; it needs no project build.
- `ProbeStrict.v` — the shipped rw rung ladder (`existsb`) against a
  short-circuiting one with the same boolean value, plus each rung in
  isolation.  The isolated rungs sum to the `existsb` ladder.
- `ProbeScanStrict.v` — the same A/B for the C/T bulk block
  (`scan_loops`), plus candidates-emitted vs index-of-winner.
- `ProbeRwFuel.v` — `Closure.close` instrumented to report (status,
  pool size, fuel left) at rung (3,2), so the fuel exhaustion can be
  split into converged/diverged and the pops a converged closure
  actually needs can be read off.
- `ProbeQhbStage.v` — the `ProbeRwStage` recipe pointed at
  `try_qhb_lex_at`: `ng_grow` / `+ ng_explore` / `+ rank_procedure` /
  whole attempt / the plain ladder, so the tier's cost can be
  attributed before committing a round to it.
- `ProbeRwIdx.v` / `ProbeRwStage.v` — the ClosureIdx-lex A/B on the
  RepWL tier: isolated verified stage (certificate replayed from data
  into both checkers), whole attempt per rung, and the rung ladder as
  the walk actually pays it.
- `gen_rss_probe.py` — GENERATOR for the peak-RSS attribution sweep.
  Peak RSS is a whole-process high-water mark, so each configuration
  needs its OWN `coqc`; this emits one probe per (workload, fuel,
  engine) so `/usr/bin/time -v` can be read off each. Workloads:
  `load` (floor), `tab` (+ lookup maps), `bulk`, `res`, `walk`
  (ProbeWalk_K1), and `unit` — the REAL unit's computation (Run.v's
  decider and maps, `Run_Split2.q_ggsub`), whose `--iter 0` row is the
  engine's fixed cost. `--native` emits `native_compute` for the census
  opam switch; apt Coq has no native compiler and falls back to the VM
  with a warning, so a `--native` run there measures nothing new.
- `ProbeNgFuel.v` — the n-gram analogue of `ProbeRwFuel`: `ng_explore`
  and the n-gram `Closure.close` instrumented to report (status, nodes
  seen, fuel LEFT), per rung, so it can be read off whether
  `ng_fuel = 200000` is ever approached. It is not: 17,665 pops is the
  largest consumption measured.
- `ProbeCVisits.v` — `Cycle.cvisits` (eager `||`, so it always walks
  the full `len`) against the nested-`if` form with the same boolean
  value, at the prefix lengths the census asks for. Counts must match.

### The big samples (generated, NOT committed — 24k lines)

`ProbeTierBig.v` is the validation-sized sample the catch-diffs run
on; `ProbeNatRef.v`, `ProbeExactRec.v` and `ProbeCtKill.v` import its
`grp_C` / `grp_T` / `grp_N6`, and the RepWL catch-diffs its `grp_RES`.
Regenerate with:

```sh
gcc -O2 -o /tmp/census_ladder tools/census_ladder.c
/tmp/census_ladder --holdouts tools/BBB4_holdouts_3713.txt --csv /tmp/T.csv
TIER_SCALE=15 TIER_ONLY=C,T,N6,- \
  python3 tools/probes/gen_tier_cost.py /tmp/T.csv tools/probes/ProbeTierBig.v
```

(600 C + 600 T + 240 N6 + 600 residue; the ladder walk is ~100 s
single-core, the sample compile ~8 min.)

`gen_rwdiff.sh` then emits `ProbeRwDiff_1..4.v`, one per RepWL rung, so
the four catch-diffs go on four cores.  Each prints
`(disagreements, catches)`; the first component must be 0.

vm_compute is ~3-5x native_compute on this code; treat absolute times
as upper bounds and ratios as transferable.
