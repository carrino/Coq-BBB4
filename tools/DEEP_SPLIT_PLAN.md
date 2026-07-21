# Deep-split campaign plan (census walk, D_census=12,974)

The verified-tier shrink un-deferred +3,125 lever-B/C machines that now run
the full ngram->rank->qhb->rw ladder in-walk, concentrated in the
residue-heavy grandchild subtrees (0RB_1LC, 1RB_1LC, ...).  Several
great-grandchild walk units (Compute/GG_1LC_*.v, Compute/GGH_*.v) now exceed
the container preemption window and must be split ONE level deeper.

## Tooling
- `tools/gen_gsplit_deeper.py OUTDIR UNIT...` emits, per heavy unit:
  Run_Split_<UNIT>.v (cover lemma), GGGH_<UNIT>_<ft2>.v (12-16 native
  sub-walks), and a REPLACEMENT <UNIT>.v proving the SAME decided lemma.
  Mirrors Run_Split2 / gen_gsplit_heavy exactly; kernel re-checks all.
- Heavy units are collected by scratchpad/census_run.sh (CAP=300s ->
  scratchpad/heavy.txt).

## Procedure (on an idle box, native switch)
1. Runner exits CENSUS_QUARANTINED with heavy.txt complete.
2. `python3 tools/gen_gsplit_deeper.py theories/Census/Compute $(cat heavy.txt|xargs -n1 basename|sed s/.v//)`
   -- but Run_Split_<UNIT>.v files go in theories/Census/ (not Compute/);
   adjust: emit Run_Split_* to theories/Census/, GGGH_*/replacement to Compute/.
3. VALIDATE one unit first: coqc Run_Split_<U> (fast) + one GGGH sub-walk
   (native, confirm it closes in-window) before trusting the batch.
4. Add the new files to _CoqProject; compile Run_Split_* (fast), then the
   GGGH_* walks at P=2 (smaller RAM than monolith), then the replacements,
   then G_* assemblies, then Census_Theorem.
5. If a GGGH sub-walk is STILL heavy: feed it back into gen_gsplit_deeper
   (recursive; its spec has 4 defined transitions).

## Fallback if the heavy set is very large (>~30 units, multi-day compute)
Consider shipping proven-tier-only (D_census=16,099, -3,636, near-zero added
walk cost -> existing GGH split still fits) as a mergeable milestone, and
defer levers B/C (the +3,125 walk-cost machines) to a follow-up.  Decide
from heavy.txt size + measured sub-walk times.
