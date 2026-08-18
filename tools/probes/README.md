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
- `ProbeRwFuelRungs.v` — `ProbeRwFuel`'s instrumented `close` at the
  shipped 5,120, per rung, over the machines that reach that rung under
  the shipped ladder order. Says how much of the tier's closure work is
  diverging closures (89%) and therefore what a lower cap can refund.

`ProbeTierCost.v`'s generator now emits a WARM-UP `Time Eval` before the
first tier row. `vm_compute` compiles the whole `decider0` closure to
bytecode on its first use and charged it to whichever row ran first —
which made the published "H halt: 8.45 ms/machine" ~100x too slow. Any
new timing probe over `decider0` needs the same warm-up.

The `unit` workload needs `theories/Census/Run{,_Split,_Split2}.vo`
built by the SAME Coq: the committed `Run_Split*.vo` come from the
census opam switch (OCaml 4.14.2) and will not load under apt's 4.14.1.
Move them aside, `coqc` the two sources (they are structural lemmas, not
walks — seconds each), and move them back.

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

## M4 sizing (2026-08-12)

- `ProbeRwDivTime.v` — the diverging/converging split of `close` in
  TIME rather than pops, per rung, at the shipped fuel 5120.
- `ProbeRwDivReach.v` — the correction the rest rests on: `rwr` is a
  parameter of `decide_easy`, so emptying it gives the tier's real cost
  by subtraction, and the machines it leaves undecided are exactly
  those that reach the tier.  7 of 40, all caught at the first rung,
  none diverging — so the residue sample cannot carry M4's premise.
- `ProbeRwDivSig.v` — is divergence signposted?  Max node size per
  closure, against status.  (`asz` counts run-length items; RepWL caps
  repeat counts at T, so item count is the only component that can
  grow.)
- `gen_rwdiv_probe.py` / `ProbeRwDivPop.v` — GENERATOR + probe for the
  population that actually pays a failing rw attempt in the walk:
  machines caught at a LATER rung, sampled by winning rung from
  tools/repwl_residue_caught.tsv, whose per-rung counts are exhaustive
  and supply the census weights.
- `ProbeRwDivSplit.v` — inside those failing attempts, diverging close
  against converging-but-not-catching, since only the first is M4's.
- `ProbeRwDivWalk.v` — the denominator: the real decider on
  `ProbeTierCost`'s groups, weighted by census tier counts, so the tier
  share is a ratio of vm seconds from one run rather than a conversion
  through the native walk.
- `ProbeRwDivCut2.v` — what a node-size cut at M costs (catches kept
  per group) and refunds (aborted close against un-aborted).

Note for anyone extending these: `sumf` over a per-machine value near
the fuel cap builds a ~90,000-deep unary `nat` and overflows the stack.
Sum the small side (`tpops`), not the large one (`tleft`).

`gen_rwcut_gate.py` is M4's exhaustive gate, and it is the reason the
cut can be gated at all: the cut is monotone (it can only turn a `Some`
into a `None`, so a catch can be lost and never gained) and every kept
catch is tabulated, so the obligation is finite and enumerable rather
than a sampled diff.

```sh
python3 tools/probes/gen_rwcut_gate.py /tmp/rwgate 2000
cd /tmp/rwgate && ls PRwGate_*.v | xargs -P3 -I{} sh -c \
  'coqc -Q /path/to/theories BBB4 -Q /tmp/rwgate BBB4 {} > {}.out 2>&1'
grep -ho "= (.*)" PRwGate_*.v.out
```

Each chunk prints (rows, max node size over the winning closures, how
many exceed 24, how many exceed 32).  The gate passes iff the third and
fourth components are 0 everywhere.  Measured 2026-08-12: 25,511 rows,
census-wide max 20, zero above either.
