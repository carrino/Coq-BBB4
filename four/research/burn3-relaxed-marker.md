# Relaxed marker recurrence

The new checker proves **27 additional state bounds**, all at **0**, using a
preserved rightmost marker and the existing padded finite-tape potential.
It makes **no instruction-bound claim**. The 27 families belong to the exact
694 history-search misses and are disjoint from the 378 history candidates.
The [combined inventory](burn3-relaxed-marker-summary.json) deduplicates the
one-family example and the additional 26-family batch against the current
1,072-family state remainder.

## Why the earlier marker condition was too strong

For the concrete family `1LB2RA2RA1RA_2RB3LB0LB3LA`, the rightmost marker can be
1 or 3. Reading marker1 in B writes3 and moves left while staying in B. The
previous `MarkerPotential` checker requires every marked B instruction to
enter A immediately, so it rejects the tested mask 10 / weights (0,1,1,0) witness.
The new checker accepts it without that unnecessary immediate-exit condition.

The proof still checks every transition's effect on the invariant. A left move
from a marker must write a marker; a right move from a marker must enter A.
The same conditions apply when A reads a blank with an otherwise blank right
suffix, establishing the marker from the initial configuration. Thus a B-only
run cannot escape past the rightmost marker.

For B-only transitions, every left move removes at least one unit of total
symbol weight, while a right move adds at most one. Padding the finite tape
representation with sufficiently many blank cells on the left preserves the
actual infinite tape and establishes a positive capacity margin. That margin
prevents left-boundary escape. The existing mirrored radix potential strictly
decreases on each remaining B-only step, so the run reaches A. The independent
`ore_auto_goal ... StB` check supplies recurrence of B. Both states therefore
recur, giving state quasihalting bound 0.

This is a proved extension of the earlier checker:
`rmp_check_extends_mp` shows every old accepted parameter tuple is accepted by
the new one. The regression example supplies a strictness witness at its exact
mask and weights. The generic soundness theorem, preservation proof and
regressions are handwritten and tracked under
[`proof-sources/burn3-relaxed-marker`](../proof-sources/burn3-relaxed-marker/).
No existing core source was changed.

## Evidence and replay

The example passed an exact census inventory and all-completion bound, followed
by a full recursive audit of **275 modules**, with no reused modules. Its
[report](burn3-relaxed-marker-checked.json) records the frozen source and input
pins. Twelve Coq examples exercise acceptance, the earlier rejection,
preservation failures, capacity inequalities, partial tables and the other
state's recurrence gate.

A bounded search of the exact 694 misses recovered the example and found 26
additional candidates. All 26 subsequently passed the same Coq checker, exact
inventory, pending membership and full recursive audit of **274 modules**,
with no reused modules. Their [report](burn3-relaxed-marker-batch-checked.json)
is separate from the example report. Of the 27 selected witnesses, 26 fail the
old immediate-exit clause; one already satisfies the old predicate and was
recovered by this focused scan.

With the repository Coq toolchain on `PATH`, run from the repository root:

```bash
make -C four all
python3 four/tools/check_burn3_relaxed_marker.py \
  --timeout 300 --audit-timeout 1200
python3 four/tools/check_burn3_relaxed_marker_batch.py \
  --timeout 300 --audit-timeout 1200
```

The first command copies the three exact handwritten sources into an ignored
build namespace and adds an inventory wrapper tied to the compact input. The
second command consumes that theorem package without recompiling it and builds
only the disjoint 26-row batch. Both replay tools preserve published reports
and write fresh runtime receipts under `build/`. Generated Coq, objects and
verbose audit logs remain untracked. No native discovery binary, LP solver or
finite trace is needed for proof replay.

The discovery scan is separately reproducible with Python only:

```bash
python3 four/tools/search_burn3_relaxed_marker.py --check
```

Its input, witness range and exact candidate output are frozen in
`burn3-relaxed-marker-search-input.json` and
`burn3-relaxed-marker-search.json`. Native or Python search acceptance never
substitutes for the Coq proofs and recursive audits above.
