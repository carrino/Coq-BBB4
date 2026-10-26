# Two states and four symbols

This development proves the exact state and instruction quasihalting scores of
`1RB2LA1RA1LB_0LB2RB3RB1LA`:

**205,770,076,433,044,242,247,860**, under this repository's last-index-plus-one
convention. The last state `A` visit and last instruction `A3` occur at index
205,770,076,433,044,242,247,859. Afterwards only `B0` executes, moving left forever.

These are rigorous **lower bounds** on the two global BBB(2,4) values. There is
no claim that the champion is globally maximal. The public definitions are in
[`Spec.v`](theories/Spec.v); the machine model is in
[`Statement.v`](theories/Statement.v) and
[`StatementTr.v`](theories/StatementTr.v). The carrier has exactly two states
and four symbols, with unrestricted initial transitions and implicit blank
padding on both ends of the tape.

## Build and audit

With the repository's Coq 8.18.0 / OCaml 4.14.2 toolchain active, from the root:

```bash
eval "$(opam env --switch=census)"
make -C four check -j2
python3 four/tools/generate_champion.py --check
python3 four/tools/generate_census.py --check
```

This builds the isolated `BBB24` namespace and recursively audits it with
`coqchk`. It does not build the existing binary or small-machine censuses.
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

## Certified census coverage

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
precise prefix check. The four-symbol build uses Coq's VM and disables native
compilation to avoid the native compiler's stack limit on the large shared DAG.

Regenerate the current certificate with
`python3 four/tools/generate_census.py`, then run `make -C four check -j2`.
`--check` reproduces without changing the committed certificate. A smaller
`--fuel 4` certificate can be generated for quick experiments; the checked-in
horizon is eight.

## Residual-family profiling

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
