# Stronger BBB(2,4) census closeout

The earlier **133,185** count was the remainder of a particular search ladder,
not a list of machines known to require individual proofs. This campaign adds
stronger generic checkers, wider searches, and reuse of recurring portions of
proved runs. State and instruction obligations have separate ledgers.

The exact champion score remains **205,770,076,433,044,242,247,860** for both
definitions. It is a global lower bound. No global BBB(2,4) upper bound follows
from these partial closeouts.

## What the counts mean

[`campaign-summary.json`](research/campaign-summary.json) records the combined
audited boards. Its `both_census_linked_families` counts distinct family IDs with
both bounds, and `state_census_linked_families` includes additional state-only
proofs. Each theorem covers every completion of the corresponding partial table.
Duplicate IDs across methods are counted once.

The first combined campaign checkpoint has **34,290 both-bound families** and
**111,345 state-bound families**. Within the original 133,185-row search cohort,
21,985 have both checked bounds and 99,040 have a checked state bound; its
remaining checked-proof obligations are therefore 111,200 and 34,145,
respectively. Later search successes are not included until their replay and
census closeout pass.

The report also intersects each checked inventory with the frozen 133,185-row
search cohort. Those counts describe that cohort, not the whole formal pending
predicate. The original eight-step census still has its original structural
weights and 1,756,620 leaves; removing a finer proved family does not subtract
one whole original leaf. The deeper exploratory survey has not become an
exhaustive formal census merely by being searched.

`BoardManifest.v` checks that each recorded ordered inventory is exactly its
imported Coq board. `DualCloseout.v` composes both-bound and state-only boards
without granting an instruction bound to a state-only result. `OrbitCloseout.v`
also covers blank-preserving symbol permutations and reflection without
materializing every image. Swapping the initial state requires a separately
checked prefix bridge.

## Added methods

| Method | What it establishes |
| --- | --- |
| Longer exact/translated cycles | Both bounds; complete branch certificates also cover the undefined/halting choice |
| Full affine replay | Both bounds and nonhalting, checked by the existing `ir_check` rather than trusting the external fitter |
| Weighted n-grams | Both bounds using nonnegative linear combinations and binary place-value measures with checked boundary conditions |
| Weighted state recurrence | A state bound from one checked recurrent instruction per live state; no instruction-bound claim |
| One-state avoidance ranking | State recurrence and state bound zero; no individual-instruction recurrence claim |
| State finite/history/repeated-word tiers | State bounds from graphs specialized to avoiding a state |
| Prefix and recurring-suffix reuse | Both bounds after checking the target's own blank-start prefix and its subsequent behavior |
| Closed or masked three-symbol alphabet | State bound 59 and instruction bound 67, using the completed BBB(2,3) theorem |
| Non-injective alphabet quotient | State bounds only; merged symbols do not preserve individual instruction identities |

The weighted producer can supply a finite graph and ranking certificate, but
Coq checks the start configuration, every successor, liveness, and all ranking
conditions. Solver output, floating-point optimization, hashes used for search,
and template matching are not mathematical assumptions.

The affine and weighted reuse searches match recurring portions of runs. They
can handle targets whose transient transition entries differ from a source.
A fresh checker call or a proved suffix transport verifies the target; mere
table similarity is insufficient.

## Frozen search checkpoints

The weighted full sweep starts from the following declared cohort. These are
search and preselection counts, not additional kernel-checked discharges:

| Step | Remaining core IDs |
| --- | ---: |
| Earlier advanced ladder | 133,185 |
| Stronger n-gram pass | 118,377 |
| Repeated-word fuel 512 | 106,221 |
| Also exclude successful full affine native replay | 62,670 |
| Also exclude 3,043 distinct IDs from checked both-bound inventories | **59,627** |

The affine native replay accepted 62,560 of the original 133,185 inputs. That
number overlaps other methods and cannot be added to their counts. All C
search misses, unsupported certificates, replay failures, and resource failures
remain eligible for subsequent methods.

The later finite/history passes remove another 3,656 IDs from that frozen
59,627-row cohort, leaving 55,971. Larger-budget timeout retries find another
2,382 candidates, leaving **53,589** before weighted results and later reuse.
The weighted input stays frozen so its progress and streamed proof batches have
a stable denominator. Reports pin the complete input, method parameters, and
the files used for exclusions. See
[`weighted-full-cohort.json`](research/weighted-full-cohort.json),
[`wave3-closure-full.json`](research/wave3-closure-full.json), and
[`wave3-timeout-full.json`](research/wave3-timeout-full.json).

## Rebuild and inspect

Activate the documented Coq 8.18.0 / OCaml 4.14.2 toolchain, then run from the
repository root:

```bash
make -C four check
make -C four list-campaign
make -C four check-campaign
```

The last target replays the exact dependency graph in
[`campaign-build.json`](research/campaign-build.json), then recursively audits
the combined coverage theorem. It uses tracked compact inputs and requires no
discovery search logs or external affine search executable. The three-symbol
stages build `SmallBB.Value23` automatically; the BBB(4) census is not needed.

Bulk replay takes substantially longer than the core library build. The default
is one replay process. On a 16 GiB machine, two processes can be requested:

```bash
make -C four check-campaign CAMPAIGN_JOBS=2
python3 four/tools/rebuild_campaign.py --only state-reach
python3 four/tools/rebuild_campaign.py --only affine-bulk4096a
```

Pull-request CI separately replays the affine and weighted pilots, one-state
ranking, state closure, state repeated-word pilot, and alphabet reduction.
The full combined campaign remains available through `check-campaign`; the
pilot matrix does not substitute for that larger replay.

Each selected step also rebuilds its prerequisites. Logs go to
`four/build/campaign-rebuild/`; individual checkers retain their own proof and
audit logs. Compatible proof receipts let supported stages resume. A failed
step prevents its dependents from starting.

Generated Coq shards and large deterministic ledgers are ignored by Git.
`replay_affine_wave.py` reconstructs a missing affine ledger from its frozen
bundle and report, then runs the original full audit. The weighted recorded
replayer preserves the published report while rebuilding its exact proof
objects; historical timing receipts are local cache metadata.

After the final combined audit, the readable per-machine lists are:

- `four/build/campaign/both-families.tsv` and `state-families.tsv`;
- `four/build/campaign/both-unproved-initial-cohort.txt` and
  `state-unproved-initial-cohort.txt`.

The latter two contain families still lacking the corresponding checked proof
in the selected boards, even when a search candidate exists. Their hashes are
recorded in the summary. This keeps candidate discovery, proof completion, and
the remaining global census obligation distinct.
