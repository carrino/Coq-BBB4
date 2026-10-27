# Stronger BBB(2,4) census closeout

The earlier **133,185** count was the remainder of a particular search ladder,
not a list of machines known to require individual proofs. This campaign adds
stronger generic checkers, wider searches, and reuse of recurring portions of
proved runs. State and instruction obligations have separate ledgers.

The exact champion score remains **205,770,076,433,044,242,247,860** for both
definitions. It is a global lower bound. No global BBB(2,4) upper bound follows
from these partial closeouts.

## What the counts mean

[`campaign-final-summary.json`](research/campaign-final-summary.json) records
the final combined audited boards: **122,895 distinct families with both
bounds**, and **153,629 with a state bound**. Each theorem covers every
completion of its partial table. Overlap between methods is counted once.

Within the original **133,185-row** search cohort:

| Obligation | Families in this checked closeout | Still outside this closeout |
| --- | ---: | ---: |
| Instruction bound (also state) | **99,693** | **33,492** |
| State bound | **130,427** | **2,758** |

The canonical champion remains a control in these comparison lists. Its exact
score is already proved separately in `Champion.v`; this small-bound closeout
does not yet register a champion board. A residual ID therefore means it has
not been discharged by these selected census boards.

The separate search ledger has **32,629** remaining candidates. It includes
successes whose proof replay is still pending, and does not incorporate every
later checked inventory. It is not interchangeable with either proof residual.

The earlier [`campaign-summary.json`](research/campaign-summary.json) remains
frozen as the first checkpoint: 34,290 both-bound and 111,345 state-bound
families. Scheduling manifests that reference it remain reproducible.

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
| Marker, potential and trail invariants | State recurrence from persistent tape structure; partial roots check every possible next transition |
| Capacity certificates and instruction portfolios | Weighted recurrence with checked capacity bounds or separate recurrence proofs for each instruction |

The weighted producer can supply a finite graph and ranking certificate, but
Coq checks the start configuration, every successor, liveness, and all ranking
conditions. Solver output, floating-point optimization, hashes used for search,
and template matching are not mathematical assumptions.

The affine and weighted reuse searches match recurring portions of runs. They
can handle targets whose transient transition entries differ from a source.
A fresh checker call or a proved suffix transport verifies the target; mere
table similarity is insufficient.

## Search results

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
2,382 candidates, leaving 53,589 before weighted results and later reuse.
After deduplicating the weighted results, stronger repeated-word checks and
pilots, the shared search remainder is **32,629**: **100,556 fewer** than the
starting cohort, a **75.5% reduction**.
The weighted input stays frozen so its progress and streamed proof batches have
a stable denominator. Reports pin the complete input, method parameters, and
the files used for exclusions. See
[`weighted-full-cohort.json`](research/weighted-full-cohort.json),
[`wave3-closure-full.json`](research/wave3-closure-full.json), and
[`wave3-timeout-full.json`](research/wave3-timeout-full.json). The final search
union is recorded in
[`repwl-search-union.json`](research/repwl-search-union.json).

The weighted sweep completed all 59,627 inputs and retained 19,950 candidates:
14,654 weighted certificates and 5,296 ordinary closure certificates. Its
30 immutable pools preserve all candidates, including those assigned to
another proof method. A separate state-weighted search retained 1,203 candidates
from 3,651 inputs; only its nine-family pilot is included in the checked ledger.
These overlapping candidate counts must not be added to the proved totals.

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
the complete dependency closure of the combined coverage theorem. The bootstrap,
smaller-alphabet dependencies, closure aggregates, and largest inventories are
audited in separate phases to limit peak memory; their verified objects are
then reused for the combined proof.
It uses tracked compact inputs and requires no
discovery search logs or external affine search executable. The three-symbol
stages build `SmallBB.Value23` automatically; the BBB(4) census is not needed.

The full campaign is a multi-hour replay, substantially longer than the core
library build. The default is one replay process. The final combiner keeps
large board definitions opaque locally and uses a conservative OCaml GC policy
when none is supplied; certificate contents and kernel checking are unchanged.
Keep replay serial on a 16 GiB machine. On a host with at least 32 GiB,
two processes can be requested:

```bash
make -C four check-campaign CAMPAIGN_JOBS=2
python3 four/tools/rebuild_campaign.py --only state-reach
python3 four/tools/rebuild_campaign.py --only affine-bulk4096a
```

Pull-request CI separately replays the affine and weighted pilots, capacity
and instruction-portfolio pilots, one-state ranking, state closure, state
repeated-word pilot, and alphabet reduction.
The full combined campaign remains available through `check-campaign`; the
pilot matrix does not substitute for that larger replay.

Each selected step also rebuilds its prerequisites. Logs go to
`four/build/campaign-rebuild/`; individual checkers retain their own proof and
audit logs. Compatible proof receipts let supported stages resume. A failed
step prevents its dependents from starting.

Generated Coq shards and large deterministic ledgers are ignored by Git.
`replay_affine_wave.py` reconstructs a missing affine ledger from its frozen
bundle and report, then runs the original full audit. The portable weighted
replayers require exact frozen source, certificate, and inventory bytes, then
freshly compile and recursively audit the proofs. They preserve the published
reports and record current object hashes separately: compiled `.vo` bytes can
differ between Coq installations. Historical object hashes and timing receipts
are local cache metadata.

After the final combined audit, the readable per-machine lists are:

- `four/build/campaign-final/both-families.tsv` and `state-families.tsv`;
- `four/build/campaign-final/both-unproved-initial-cohort.txt` and
  `state-unproved-initial-cohort.txt`.

The latter two contain families still lacking the corresponding checked proof
in the selected boards, even when a search candidate exists. Their hashes are
recorded in the summary. This keeps candidate discovery, proof completion, and
the remaining global census obligation distinct.

## Next burndown

1. **Finish replaying the existing candidates.** The deduplicated next-work
   list contains **4,352 instruction-bound candidates** (2,833 repeated-word
   and 1,519 timeout recoveries) and **661 state-bound candidates**. There are
   **4,592 distinct IDs**, with 421 shared by the two queues. The state queue
   includes 240 new state-weighted candidates; all 19,950 full weighted-search
   candidates already have both bounds in the final inventory. These queued
   certificates still require replay, and failures remain obligations. For
   expensive batches, prefer supplied graph/rank witnesses where the current
   checker repeats discovery work inside Coq; the state-history certificate
   tier already provides this approach. See
   [`campaign-next-summary.json`](research/campaign-next-summary.json).
2. **Expand the new certificate tiers.** Capacity and per-instruction portfolio
   checks produced 27 additional audited witnesses across their initial runs.
   Run them over the deduplicated residual with resumable batches and bounded
   budgets, then try larger n-grams and asymmetric windows.
3. **Separate expensive timeouts from structural misses.** The repeated-word
   residual profile identifies 5,841 timeouts in liveness checking. Improve
   that computation or schedule selected longer retries before increasing
   every machine's budget. Search misses remain candidates for affine rules,
   reusable tails and new marker invariants.
4. **Close the exhaustive census gap.** Transport proved families through the
   symmetry and shadow machinery and connect the deeper survey to a checked
   census walk, as in BBB(4), and attach the separately proved champion.
   The 32,629-row queue is a search workload, not the
   complete formal residual. The global upper bound still requires covering
   every remaining formal family, including halting completions.

After the campaign replay, reconstruct the next-work list with:

```bash
python3 four/tools/summarize_campaign_queue.py
```

It verifies the audited inventories and candidate sources, then writes
`four/build/campaign-next/queued.tsv` with the source certificates for each ID.
This scheduling report does not remove any proof obligation.

Each new batch should retain its input inventory, resource failures and exact
proof scope. The two final per-machine ledgers are the starting point for
future assignments; state-only successes must not erase instruction work.
