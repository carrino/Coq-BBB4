# Twenty fresh instruction transports

Rechecking the instruction holdouts against the newer proved-source inventory
found **20 additional instruction families**. All 20 already have state bounds,
so this package contributes no new state coverage. Its common state and
instruction upper bound is **8,192**; this is not a claim of exact scores.

The starting screen used the frozen 31,495-family instruction residual from
checkpoint four. Ordinary relabeling/completion lookup and masked three-symbol
reduction found no new survivors to discharge. State-exchanged table lookup
found 1,521 matches: 641 were already queued, 816 had already been searched,
and 64 were fresh. Exact prefix search on those 64 produced the selected 20.
These discovery results only selected candidates; all proof credit comes from
the checked transport certificates.

## Proof

The compact input contains ten ordinary source certificates: five repeated-word,
three history and two ordinary n-gram certificates. Replay reconstructs them in
an isolated namespace. An eleventh source imports the previously audited
[paired-tail proof](burn3-tail-invariant.md). Each source supplies a nonhalting
proof and both upper bounds at 4,096; the paired-tail source's stronger bounds
are weakened to this common source budget.

The existing `IndexedConjugate` checker verifies table inclusion, symbol
permutation, optional reflection and equality of the two concrete reached
configurations. Destination prefixes are at most 101 steps, and source prefixes
are at most 135 steps. The checker explicitly proves the required budget
inequalities, including `4096 + destination_boot <= 8192`. Exchanging the two
states is used only after these actual blank-start prefixes have been checked;
it is not treated as a blank-start symmetry on its own.

The final board proves all-completion bounds, membership in the original pending
census predicate, and an exact inventory of the 20 family IDs. They are disjoint
from the 35-board checkpoint, the six swapped-counter families and the separate
21-family paired-tail template board. One overlapping paired-tail candidate was
kept in this transport board and excluded from that template board.

The initial replay compiled 15 modules and passed a full recursive `coqchk`
audit of **293 modules**, with no reused audit entries. Its printed assumptions
contain only the repository's existing functional-extensionality assumption.
The checked report pins all compact inputs, generated sources, shared sources
and proof objects. Current snapshots were compared with the successful audit
receipt before integration.

## Reproduce

After building the [shared Coq theories](../../docs/VERIFYING.md), run from the
repository root:

```bash
python3 four/tools/check_burn3_tail_invariant.py \
  --timeout 300 --audit-timeout 1200
python3 four/tools/check_burn5_structural_instructions.py \
  --timeout 300 --audit-timeout 1800
```

The second command always performs a full recursive audit. Published inputs,
reports and inventories are preserved; fresh execution evidence is written to
`build/burn5-structural-instruction/proof/current-proof-receipt.json`. Native
discovery files are not needed for replay. Generated Coq sources and runtime
receipts remain in ignored build directories.

The aggregate descriptor is `descriptor` in
[`burn5-structural-instruction-checked.json`](burn5-structural-instruction-checked.json),
with module `BBB24Burn5StructuralInstruction.Inventory`. The build plan must
place `burn3-tail-invariant` before this package.
