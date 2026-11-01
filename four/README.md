# Two states and four symbols

This development proves the exact state and instruction quasihalting scores of
`1RB2LA1RA1LB_0LB2RB3RB1LA`:

**205,770,076,433,044,242,247,860**, under this repository's last-index-plus-one
convention. The last state `A` visit and last instruction `A3` occur at index
205,770,076,433,044,242,247,859. Afterwards only `B0` executes, moving left forever.

The complete state proof now establishes the global maximum:
**state-based BBB(2,4) = 205,770,076,433,044,242,247,860**. Both full recursive
audits passed in the [verified WSL run](../docs/BBB24_VERIFIED_RUN.md).
The global instruction maximum remains open; the exact champion instruction
score supplies its lower bound. The public definitions are in
[`Spec.v`](theories/Spec.v); the machine model is in
[`Statement.v`](theories/Statement.v) and
[`StatementTr.v`](theories/StatementTr.v). The carrier has exactly two states
and four symbols, with unrestricted initial transitions and implicit blank
padding on both ends of the tape.

The [instruction burndown](INSTRUCTION_BURNDOWN.md) tracks the remaining historical
hard-cohort families and gives replay commands for the new instruction proofs.

## Build and audit

For the complete state equality, run from the repository root on a machine
with sufficient available RAM:

```sh
STATE24_AUDIT_RSS_GIB=40 STATE24_COQCHK_TRACE=1 \
STATE24_COQCHK_OCAMLRUNPARAM='o=40,O=60' \
make proof-2-4 BUILD_JOBS=8 STATE24_PROVIDER_LIGHT=1
```

The successful run used Coq 8.18.0 / OCaml 4.14.2 with 48 GiB allocated to WSL.
The [build guide](../docs/VERIFYING_BBB24.md) documents resources and exact
checkpoint resume; the [run record](../docs/BBB24_VERIFIED_RUN.md) includes the
source identifiers, assumptions, timings and sampled memory measurements.

To audit the champion and the earlier bootstrap/checker components separately,
activate the same toolchain and run:

```bash
eval "$(opam env --switch=census)"
make -C four check -j2
python3 four/tools/generate_champion.py --check
python3 four/tools/generate_census.py --check
python3 four/tools/generate_pipeline_examples.py --check
```

This component target builds the base `BBB24` namespace and recursively audits
it with `coqchk`; the complete selected-source assembly uses `make proof-2-4`.
Alphabet reduction also builds the completed `SmallBB.Value23` theorem;
the existing BBB(4) census and the unrelated (3,2) legacy dependencies are not needed.
See the [usage guide](../docs/VERIFYING.md#four-symbol-champion) for installation
and theorem inspection.

## How the large prefix is proved

The proof never executes 10^23 individual transitions or expands its enormous
working tape. [`Macros.v`](theories/Macros.v) proves three universal rules with
exact costs. In directional notation, `<A` scans the cell immediately to its
left, `P` and `Q` are untouched tape portions, and all exponents are natural.

| Rule | Input | Output | Cost |
| --- | --- | --- | --- |
| Pair of threes | `P 3^(2k) <q Q` | `P <q 1^(2k) Q` | `2k` |
| Grow twos | `P 2^(2k) <A 2^R 0^∞` | `P <A 2^(R+3k) 0^∞` | `6k² + (4R+8)k` |
| Consume ones | `P 2^k <A 2^R 1^k Q` | `P <A 2^(R+2k) Q` | `2k² + (2R+1)k` |

The pair rule works in either state. Ordinary moves and uniform chain moves
complete the instruction language. [`RLE.v`](theories/RLE.v) connects binary
run lengths to the ordinary infinite tape; [`Replay.v`](theories/Replay.v)
proves every accepted command has exactly its reported cost.

The generator emits 2,933 commands reaching the configuration just before the
final `A3`. A final ordinary step gives 2,934 operations total. Coq computes only
over binary integers and compressed blocks, checks the certificate, and proves
the final blank drift. The Python generator is untrusted and can be replaced.
No generated simulation trace or expanded tape is committed.

`champion_exact` proves non-halting, attainment, and a matching upper bound for
this particular machine at both levels. `BBB24_lower_bounds` exposes the two
global lower bounds. Their sole axiom is `functional_extensionality_dep`.

The published last-visit index and the repository score differ by one. This
proof states and checks both numbers explicitly; it does not change the score
convention used by the previously completed developments.

For the historical sources, [Drozd's February 11, 2022 results post](https://nickdrozd.github.io/2022/02/11/latest-beeping-busy-beaver-results.html)
reports 205,770,076,433,044,242,247,859. That number matches the last
configuration in state `A`, before its final `A3 -> 1LB` transition.
[Ligocki's February 27, 2022 analysis](https://www.sligocki.com/2022/02/27/bbb-search-process.html#chain-recurrence)
places the ensuing permanent `B0` drift at step
205,770,076,433,044,242,247,860, with exactly the terminal tape checked here.
Thus the extra one counts that final transition out of `A`; the two numbers
refer to adjacent configurations, and both are proved in `Champion.v`.

## Certified census coverage

The bootstrap below is an independently reproducible intermediate checkpoint.
The complete global state bound combines the later census and family proofs;
its successful verification is recorded [here](../docs/BBB24_VERIFIED_RUN.md).

`Bootstrap.bootstrap_coverage` proves that every two-state, four-symbol table
satisfies both candidate bounds **or belongs to an explicitly deferred family**.
All 17 choices at each of the eight cells are covered: 16 defined transitions
and one undefined transition. Initial blank writes and tables with no halting
transitions are included.

The current eight-step bootstrap has these kernel-checked structural weights:

| Classification | Table weight |
| --- | ---: |
| Bounded | 6,759,679,093 |
| Pending | 216,078,348 |
| Total | 6,975,757,441 = 17^8 |

The pending set consists of 1,756,620 partial-table leaves; each represents all
completions of its remaining undefined cells. It is not a list of proven
non-quasihalting machines. `census_upper_if_residue` states precisely what
remains necessary for an exhaustive upper bound.

The C++ survey and Python transcription are untrusted. Coq checks each cycle,
each undefined-cell branch, and its complete set of children. The 2,150,929-node
tree shares identical subtrees in 18,468 definitions. Only this certificate DAG
is committed; survey transcripts stay in the ignored `four/build/` directory.
`bootstrap_counts` checks the weights computed from that tree, and
`bootstrap_total` checks their sum. The coverage theorem is the semantic claim;
no population percentage is used as a proof premise.

The checker compares a small cycle anchor against binary candidate bounds. It
never simulates to the bound. This first checker requires the whole recurrent
suffix to start before both bounds; later-anchor certificates may need a more
precise prefix check. The base component build uses Coq's VM and disables native
compilation to avoid the native compiler's stack limit on the large shared DAG.

Regenerate the current certificate with
`python3 four/tools/generate_census.py`, then run `make -C four check -j2`.
`--check` reproduces without changing the committed certificate. A smaller
`--fuel 4` certificate can be generated for quick experiments; the checked-in
horizon is eight.

## Historical residual-family profiling

[`BURNDOWN.md`](BURNDOWN.md) tracks the 611,360-family search queue, the sampled
holdouts, and the separate certified remainder. It links a compact machine ledger
and commands to generate the full inventory locally.
[`GROUPING.md`](GROUPING.md) records the symmetry and shadow reductions, shared
submachine patterns, and the relation to the BBB(4) pipeline.
[`PIPELINE.md`](PIPELINE.md) records the new closure checker ports, sweep budgets,
and checked closeout. The 76-family closure pilot and four original affine
families are now linked through `bootstrap_pipeline_coverage`; the original
bootstrap's structural counts have not been recomputed.
The [second wave](WAVE2.md) adds finite/history and stronger repeated-word
sweeps, a 4,096-family kernel replay, and checked symmetry/shadow closeout.
That checkpoint attached 11,336 distinct families to census coverage and left
133,185 core representatives unresolved by its search sweeps.
`make -C four check-wave -j2` reconstructs the larger proof boards and audits
their combined coverage theorem from compact tracked inputs.

The [stronger campaign](WAVE3.md) adds weighted recurrence, state-only tiers,
deeper affine/closure passes, structural marker invariants, and reusable
recurring suffixes. Together with the [first supplementary round](NEXT_BURNDOWN.md)
and the later supplements through the [sixth checkpoint](BURN6.md),
the audited boards at that checkpoint covered **124,968 distinct families for
both bounds** and **155,853 for the state bound**. In the original 133,185-row
cohort, **31,419 instruction-bound** and **534 state-bound** obligations remained.
The later state proofs and global assembly have now discharged the state side.
`make -C four check-campaign` rebuilds the frozen 113-board checkpoint;
`make -C four check-burn6-campaign` rebuilds all 41 supplementary boards and
their coverage theorem. Earlier supplements remain separately reproducible
with `check-next-campaign` and `check-burn2-campaign` through `check-burn5-campaign`. The guides distinguish
these proved counts from the earlier **32,629-row search remainder** and the
current **2,740-ID instruction replay queue**, which has no state obligations.

[`research/triage-256.json`](research/triage-256.json) records a deeper,
untrusted survey at 256 steps and a deterministic sample of 512 surviving
partial-table families from each initial-write class. The upstream affine-rule
search reports candidate certificates for 786/1,024 sampled families; a
three-sample fitting variant reports 790. These candidates do not remove any
family from the certified pending set until Coq accepts a certificate.

Reproduce the baseline with a compiled `carrino/BBB` affine-rule search binary:

```bash
python3 four/tools/triage.py --irules /path/to/BBB/bin/irules
```

The script records a node budget, rejects incomplete fixed-root surveys,
selects the lowest SHA-256 machine hashes, and writes raw results under
`four/build/triage/`. The sample is unweighted and stratified by initial write;
its success rate is not an estimate of the fraction of all raw tables that the
affine checker will solve. The report separates failures to find a repeated
shape, fit an affine template, and prove the proposed symbolic recurrence.

## Checked affine examples

`IRuleCensus.ir_check_sound` now checks affine block recurrences over the
two-state, four-symbol carrier and proves non-halting plus **both** score bounds.
The checker replays the concrete prefix, proves each auxiliary rule for every
admissible counter value, and checks that the recurring instructions cover the
entire suffix. Its bound comparison uses binary integers.

Four certificates from the survey are retained in
[`research/affine/`](research/affine/) and checked in `AffineExamples.v`:

| Machine | Auxiliary rules | Feature exercised |
| --- | ---: | --- |
| `0LB2RA3RB2LA_1RA2RA3LB2RB` | 0 | Direct affine recurrence |
| `0LB1LB2RA0RB_3RA3RB1LA2LB` | 1 | Inductively proved auxiliary rule |
| `0LB3RB0LA1RB_3RA3LB0LA2LB` | 2 | Block `23` and multiple prefix rules |
| `0LB0LA---2RB_3RA1LB1RB1LB` | 2 | Partial table: every completion is bounded |

Each theorem proves both bounds at 4,096 and applies to every completion of its
table. `AffineCloseout.v` now proves these families were pending and excludes
their completions from a refined residual with exhaustive coverage.
The upstream claimed quasihalting flags and scores are ignored. In
particular, these examples do not certify the upstream claimed exact score of
the third machine. They establish that the proof method works on residual
families; they do not change the bootstrap's recorded pending weight.

```bash
python3 four/tools/generate_affine.py --check
make -C four check -j2
```

The generic engine is adapted from `small/theories/Checkers/IRules/`. The carrier
changes are the two-state visit mask, four-symbol instruction mask, and four
reserved singleton block IDs. Rejection checks cover corrupted anchors,
insufficient bounds, exhausted replay fuel, and the fourth symbol's mask and
block ID. The checked examples depend only on functional extensionality.

The [pipeline guide](PIPELINE.md) describes replay of the full 786-candidate
affine sample, n-gram/repeated-word sweeps, and the new symmetry and shadow
proofs. Search failures need alternative invariants as well as larger budgets.
These samples illustrate the certificate methods. The complete state proof
now discharges the global state obligations; the global instruction value
remains open. Sample acceptance rates alone do not establish a global bound.


