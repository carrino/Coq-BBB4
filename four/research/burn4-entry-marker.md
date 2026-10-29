# B-entry marker state recurrence

The entry-marker checker proves both states recur for a total two-state,
four-symbol machine, yielding state quasihalting bound 0. It does not establish
an instruction quasihalting bound.

The invariant is deliberately local to B excursions: while in B, some marked
symbol occurs at the head or to its right. Every A-to-B transition moves left
and writes a marker, establishing the invariant at entry. A-only transitions
are unrestricted. During B-to-B steps, a marked head must move left and write
a marker; markers farther right survive either direction. A right move at the
right boundary is therefore impossible. Blank padding and the existing symbol
weight inequalities preserve left capacity. The mirrored radix potential then
decreases strictly during a B-only run, forcing a return to A. The existing
`ore_auto_goal` checker supplies recurrence of B. Totality follows from checking
all eight transition cells, and census-family extension supplies the bound for
every completion of each selected family.

This is a separate sufficient condition from the previous global relaxed-marker
invariant. The proof does not claim that one checker subsumes the other. The
example `1LB2LA2RA1RA_2RB3RA0LB0LA`, marker set `{1}` and weights `(0,0,1,0)`
exercises an A-only rewrite that the old checker rejects at those parameters.
A second positive control exercises a marked B-left step that stays in B.
Fourteen Coq examples also isolate entry direction, unmarked entry, marker
erasure, right escape, capacity, totality and the other-state recurrence gate.

The exact input is the 667-family residual after the separately audited 378
history and 27 relaxed-marker rows. The finite search tests seven nonblank
marker masks and 125 weight tuples. It selects 121 distinct tuples, all outside
those earlier batches. Candidate discovery and proof evidence are separate:
`burn4-entry-marker-search.json` is untrusted; `burn4-entry-marker-checked.json`
is produced only after all four sources compile and the full recursive kernel
audit succeeds. `burn4-entry-marker-selection.json` records exact overlap checks.
Concurrent later batches must still be deduplicated by machine ID.
The published replay compiled all four sources and freshly audited all 275
dependency modules (zero reuse), taking 38.614 seconds for the kernel audit.
Its exact contribution is 121 state families and zero instruction families.

From the repository root, using the repository's Coq 8.18 toolchain:

```sh
python3 four/tools/search_burn4_entry_marker.py --check
python3 four/tools/check_burn4_entry_marker.py --timeout 300 --audit-timeout 1200
```

The replay copies the two frozen handwritten sources from
`proof-sources/burn4-entry-marker`, regenerates `Batch.v` and `Inventory.v`, and
checks the current compiled dependency closure with recursive `coqchk`.
It pins the compact input, source search report, residual list, handwritten
sources, generated sources and tooling. Existing published evidence is never
overwritten, and each repeat audit writes a fresh receipt under the ignored
build directory. The only logical assumption is the repository's existing
functional extensionality; the checker introduces no new axiom.

The descriptor's module is `BBB24Burn4EntryMarker.Inventory`, with
`small_sound`, `sound`, `was_pending` and `inventory_exact` covering exactly the
published inventory. Generated proof objects stay under
`build/burn4-entry-marker/proof`; the core theories and previous marker package
remain unchanged.
