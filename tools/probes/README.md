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
  `GGH_0RB_1LC_0LB` subtree.
- `ProbeWalk_K<K>.v` — walk `K * 8192` pop-slots of that subtree under
  `Time`/`/usr/bin/time -v` for time-per-pop and peak-RSS curves.

vm_compute is ~3-5x native_compute on this code; treat absolute times
as upper bounds and ratios as transferable.
