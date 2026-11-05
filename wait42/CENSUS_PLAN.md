# State-first waiting census inventory

This is an untrusted coverage investigation for BBB_wait(4,2). No complete
waiting holdout list, TNF leaf count, or universal waiting bound is established.
The historical 5,156 state-deferred rows are one source of candidates; they are
not the new holdout universe. A state can recur forever with a long return gap,
so a legacy `NeverQuasiHaltsSt` leaf also needs a waiting certificate.

Reproduce the inventory, without Coq builds, downloads, or tree walks:

```sh
python3 wait42/tools/census_inventory.py --output wait42/research/census-inventory.json
python3 -m unittest discover -s wait42/tools -p test_census_inventory.py -v
```

The JSON includes exact source byte hashes, sorted distinct row hashes, duplicate
counts, full/partial counts and undefined-slot histograms. It contains no runtime
timestamp or absolute workspace path. All four parsing/consistency tests pass.
The Coq literal parser recognizes eight-slot rows only; it does not evaluate Coq
or validate proofs. The text tier snapshots are not freshly extracted.

| Existing local source | Distinct rows | Full | Partial |
| --- | ---: | ---: | ---: |
| `tools/census_holdouts_kept.txt` | 27 | 25 | 2 |
| `tools/census_residue.txt` | 5,129 | 3,594 | 1,535 |
| `theories/Census/Deferred_00.v` through `Deferred_07.v` | 5,156 | 3,619 | 1,537 |
| `tools/censustr/state_tiers/proven.txt` | 5,270 | 5,103 | 167 |
| `tools/censustr/state_tiers/provenqh.txt` | 6,517 | 3,705 | 2,812 |
| `tools/censustr/state_tiers/rerootqh.txt` | 2,792 | 875 | 1,917 |
| `censustr_deferred_v10.txt` | 10,924 | 9,941 | 983 |
| `theories/CensusTr/DeferredTr_00.v` and `DeferredTr_01.v` | 10,924 | 9,941 | 983 |
| `censustr_deferred_v7_inwalk.txt` | 9,657 | 9,657 | 0 |

The state Coq row set equals the union of the holdouts and residue, checked by
the script. The union of all inventoried lists has 29,617 distinct text rows.
Those are overlapping historical collections; they are not orbit counts or a
coverage denominator. The exact labelled table spaces have `17^8 = 6,975,757,441`
tables allowing undefined transitions and `16^8 = 4,294,967,296` total tables.
These arithmetic counts do not count TNF representatives.

## Best full-coverage construction

Reuse the existing **four-state** TNF construction in
`theories/Census/TNF_QH.v`: `TM_le`, `visits_le`, `stepn_swap`, `visits_swap`,
`node_expand`, the unused-state pointer and the queue coverage invariant.
`theories/Census/Run_Compute.v` supplies the all-undefined root and four
first-move-right children (`0RA`, `1RA`, `0RB`, `1RB`); reflection covers first
moves to the left. Preserve the special root case, state-first-use swaps and
don't-care completion. Prove waiting-specific transport from equal traces;
`qhbound_le`, `qhbound_swap` and `qhbound_mirror` establish only the old score
property. `theories/CensusTr/TNF_QHTr.v` shows the parallel instruction contract.

Crucially, `node_expand` does **not** prune the last undefined transition. Full
machines must remain in scope. This existing tree plus adapted leaf contracts
is the best available coverage route; there is no locally verified flat list
of all its stopped representatives.

`SearchQueue_upd` currently removes `R_NeverQH`, `R_QH`, `R_Leaf`, and
`R_Deferred` leaves, expands `R_Halt`, and saves `R_Unknown`. The contracts in
`TNF_QH.v` and tier order in `theories/Census/Decide.v:decide_easy` explain
which old certificates must change:

| Legacy leaf/tier | Existing assertion | Waiting work |
| --- | --- | --- |
| `R_Halt` / `find_halt` | Reached hole before score budget; expand children | Preserve expansion and prove the actual stopped completion's waiting bound |
| `R_Leaf` / `scan_loops` | `NonHalt` and `QHBound B` | Replay prefix and cycle to bound all return/terminal waits |
| `R_NeverQH` / proven lookup, n-gram, rank, RepWL | No visited state becomes permanently quiet | Add quantitative return-gap certificate; liveness alone is insufficient |
| `R_QH` / proven-QH, reroot, wrapped QHBound | `NonHalt`, last-visit bound, quasihalting | Bound recurrent-state return gaps as well as quiet-state terminal waits |
| `R_Deferred` / old explicit list | Membership only | Candidate family; generate and replay a waiting certificate or keep unresolved |
| `R_Unknown` | No assertion | Explicit unresolved family |

`theories/Census/Run.v` reattaches lookup proofs to data-only lists by kernel
conversion. `tools/gen_census_lists.py` documents that gate and the `tm_enc`
extraction recipe. `tools/censustr/classify_deferred.py` maps historical rows
to proven/proven-QH/deferred/partial/in-walk buckets for prioritization.
That mapping may guide a solver family; it supplies no waiting credit.

## External enumeration and native tools

`tools/nghist/BB4_verified_enumeration.README` points to
<https://docs.bbchallenge.org/CoqBB5_release_v1.0.0/BB4_verified_enumeration.csv>
(documented as approximately 45 MB). It is absent at that repository path and
was not downloaded. `tools/nghist/oracle_lookup.py` documents that the mxdys
halting enumeration uses `cnt>=1` pruning and has **zero full machines**.
Its historical residue mapping covers 1,535 partial rows and misses 3,594 full
ones. It therefore cannot serve as the full waiting candidate universe, even
if downloaded. Its upstream data license has not been verified; the repository
`LICENSE` is an ISC-style software grant and is not evidence of the external
CSV's license. Treat CSV verdicts/parameters as external untrusted hints only.

`tools/census_ladder.c` is an existing untrusted four-state TNF survey with no
last-hole pruning. Its cycle hash and old pruning tiers cannot yield waiting
certificates without adaptation. `make census-verify` is the supported existing
Coq native walk; `tools/census_walk.sh` documents why its serial fallback is not
the supported driver. Neither was run for this inventory.
The extracted pipeline probes under `four/tools/ExtractStatePipeline.v` and
`four/tools/state_pipeline_probe.ml`, and `four/tools/generate_census.py`, belong
to the **two-state, four-symbol** development (`BBB24`); their certificate shapes
are useful examples, but their rows and surveys are not four-state coverage.

## Concrete next adaptation

1. Define waiting `NodeDecided` and a leaf result contract with a quantitative
   state waiting bound, using the new waiting spec and transport lemmas. Keep
   the original sources frozen and put the adaptation under `wait42/`.
2. Reuse the four-state TNF root, expansion, and symmetry/completion invariant.
   Have an unresolved result preserve the whole partial-table family.
3. Adapt cycle detection to emit exact prefix/period certificates checked
   against the waiting contract. Keep old abstract/lookup verdicts unresolved
   until a new waiting certificate is replayed. Port state tiers before the
   instruction analogue.
4. Pilot bounded subtrees with an untrusted emitted leaf ledger containing
   machine code, unused-state pointer, stop reason, certificate kind, and
   checker result. Record visited/expanded/accepted/unresolved counts and the
   input/source hashes. Save rejected legacy leaves too: they are necessary
   new holdouts, even when absent from the 5,156 old rows.
5. Assemble checked subtree coverage with all residual families explicit.
   Only after the residual is proved empty can the census imply a universal
   upper bound. Request a runtime/output estimate before a whole-tree run;
   this inventory performs no expensive enumeration.
