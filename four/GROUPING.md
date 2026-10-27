# Grouping the early BBB(2,4) search queue

**The full BBB(4) census pipeline has not run on (2,4).** The current checked
bootstrap stops at eight steps; the deeper exploratory survey runs 256 steps
with exact and translated-cycle checks. The affine search has run on 1,024
sampled families. None of these is a measurement of the final hard residue.

The old pipeline is described in
[`Census/Decide.v`](../theories/Census/Decide.v): after halt/cycle checks it
uses n-gram closures, ranking rules, wrapped quasihalting bounds, repeated-word
closures, and proven-machine lookup. The wider closeout also used history
n-grams, affine rules, and specialised families. These stages still need a
four-symbol sweep, with sound certificate checks and explicit budgets.

## Measured grouping, before those stronger sweeps

| Stage | Families / representatives | Status |
| --- | ---: | --- |
| 256-step survey, initial transition normalized | 611,360 | Exploratory early remainder |
| Remaining symbol permutations merged | 284,541 | Complete relabeling orbits checked by Python |
| Nonblank-start representatives | 273,969 | Candidate core work list |
| Blank-start representatives mapping to those cores | 10,572 | Shadow links found for every blank-start representative |

The symbol calculation fixes the blank symbol and the initial state. Direction
reflection and the first written nonblank symbol were already normalized in
the survey. The blank-write root still has all six permutations of `1,2,3`;
the nonblank-write root has only the swap of `2,3`. These give 10,572 and
273,969 representatives respectively. With only two states, fixing start state
`A` leaves no free state permutation.

The shadow calculation is stronger than relabeling. A blank-start row begins
`0LB`, so after one step it has an entirely blank tape in state `B`. Swapping
the state names at that point, then normalizing symbols/direction, produces a
table extending a nonblank-start representative in the existing queue. All
10,572 such links were found and checked as table inclusions.

These are **candidate proof dependencies**, not new discharged machines.
Transport needs a checked prefix and must retain its one-step offset. A bound
`B` for the core generally gives `B+1` for its shadow; it does not automatically
give the same global bound. Likewise, the formal census still needs the symbol
relabeling transport and coverage links. No certified pending count changes.

## Techniques already used in the repo

| Technique | Existing implementation / evidence | Application to (2,4) |
| --- | --- | --- |
| Tree normal form and unused-transition completion | [`TNF_QH.v`](../theories/Census/TNF_QH.v), [`tnf_canon.py`](../tools/nghist/tnf_canon.py) | Assign labels in discovery order and prove whole partial-table families. Our census already branches only at reached undefined cells; its `TM_le`/`extend_bounds` lemmas already cover completions. |
| Blank-prefix shadows and re-rooting | [`shadowlib.py`](../tools/closeout/shadowlib.py), [`Reroot.v`](../theories/Census/Reroot.v), [`ShadowBoard.v`](../theories/Census/ShadowBoard.v) | Reuse a core proof after a short blank-only prefix. The 10,572 links above are candidates for this route. |
| Conjugate runs after different prefixes | [`CConjCoverTr.v`](../theories/Counters/CConjCoverTr.v), [`conj_find.py`](../tools/closeouttr/le6/conj_find.py) | Relate runs once configurations coincide under a table transformation; the existing instruction-level proof checks prefix timing and recurrence. Swapping the start state without such a bridge is not sound. |
| Shared state-avoiding submachines | [`cluster.py`](../tools/reachst/cluster.py), [`REACHST_TIER.md`](../docs/REACHST_TIER.md) | Group by the machine remaining while a target state is avoided. The old burndown proved four patterns covering 127 rows. Shared templates can save many proofs without making the whole machines equivalent. |
| Shared recurrent core / counter encoding | [`CORE_3STATE.md`](../docs/CORE_3STATE.md), [`RESIDUE_MAP.md`](../docs/RESIDUE_MAP.md) | Reuse a parameterized lap or counter lemma with a separately checked startup. Previously, 23 of a 24-row population shared nine submachines. |
| Frozen census plus audited closeout | [`TERMINOLOGY.md`](../docs/TERMINOLOGY.md), [`audit.py`](../tools/closeout/audit.py) | Keep the source inventory stable and attach checked proofs and dependencies; do not regenerate the census merely to report progress. |

For a concrete measurement of the submachine route, the 256,806 **fully defined**
symmetry representatives give 513,612 `(machine, target state)` pairs. Their
one-state avoid tables have only **210 distinct patterns** under symbol
relabeling and reflection. The largest pattern occurs in 94,210 pairs.
This is a proof-template count, not a remaining-machine count. We have not proved
those patterns terminate or validated their liveness conditions. State recurrence
also does not by itself prove recurrence of every instruction.

Two lessons from the earlier work apply here:

- [`NGHIST_WAVE7.md`](../docs/NGHIST_WAVE7.md) records why halting-only
  enumerations that leave one transition unfilled miss non-halting machines
  using all eight transitions. Do not import that pruning into this BBB search.
- A transition not observed in a finite run is not thereby proved unused
  forever. Deleting it can suggest a family, but a non-halting certificate or
  another invariant must justify completion transport.

## Reproduction and next work

```bash
# Requires the ignored survey files produced by four/tools/triage.py:
python3 four/tools/group_families.py
python3 four/tools/group_families.py --check
```

The compact report is [`research/grouping-256.json`](research/grouping-256.json).
The full representative lists and 10,572 shadow links live under ignored
`four/build/grouping/`. Every relabeling orbit is checked for membership and
size against the original inventory; the report pins the input hashes.

Next: sweep the representative cores with the broader checker ladder, record
the survivors at each budget, and transfer accepted certificates to siblings
and shadows with checked bridges. Use the avoid-table and recurrent-core
groupings to choose shared lemmas for the remainder. Only then does it make
sense to call the resulting list the post-pipeline holdouts.
