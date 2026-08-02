# Coq-BBB4

[![CI](https://github.com/carrino/Coq-BBB4/actions/workflows/ci.yml/badge.svg)](https://github.com/carrino/Coq-BBB4/actions/workflows/ci.yml)

A Coq formalization of the Beeping Busy Beaver problem on 4-state,
2-symbol Turing machines, culminating in the kernel-checked value
theorem **BBB(4) = 32,779,478** — built from the certificates of the
[BBB harness](https://github.com/carrino/BBB) on the patterns of
[Coq-BB5](https://github.com/carrino/Coq-BB5) and
[busycoq](https://github.com/carrino/busycoq).

## The result

**BBB(4) = 32,779,478.**

The claim is stated **census-free** in
[`theories/BBB4_Spec.v`](theories/BBB4_Spec.v) — that file plus the
machine model it imports (`theories/BBB4_Statement.v`) is the entire
trusted statement surface:

```coq
tm_champion    : TM                       (* 1RB1LD_1RC1RB_1LC1LA_0RC0RD  *)
champion_score : nat := N.to_nat 32779478

Attains tm B   : Prop := exists q s, QuietAfter tm q s /\ S s = B

BBB4_is B      : Prop :=
  (exists tm, Attains tm B)                       (* ATTAINED *)
  /\ (forall tm B', Attains tm B' -> B' <= B)     (* MAXIMAL  *)

BBB4_statement : Prop := BBB4_is champion_score
BBB4_is_unique : forall B B', BBB4_is B -> BBB4_is B' -> B = B'
```

`make proof` builds and reports the proof
(`theories/Closeout/BBB4_Value.v`, kernel-checked, `Qed`):

```coq
BBB4_value       : BBB4_statement
champion_attains : Attains tm_champion champion_score
```

Some state of some (4,2) Turing machine makes its last visit at
configuration index 32,779,477 — score exactly **32,779,478** in the
harness convention (last visit + 1) — and no state of any (4,2) machine
is ever quiet after a later index.  The witness is the champion
`1RB1LD_1RC1RB_1LC1LA_0RC0RD`, whose state `D` goes quiet at exactly
that index (kernel-checked by two binary-fuel `vm_compute` runs in
`theories/Machines/Counters/Champion_*.v`); the upper bound is the
census + closeout chain (`bbb4_target`) with its residue disjunct
discharged — as of 2026-08-01 the residue lists are **empty** (0 core
rows, 0 shadows; the frozen census's 5,156 deferred rows are settled
5,156-for-5,156), so `~ skipped [] tm` closes the last gap
(`not_skipped_nil`, `BBB4_Value.v`).

The two-disjunct reading survives as `bbb4_unconditional`: every (4,2)
machine either quasihalts with score at most 32,779,478 or never
quasihalts — no skips, no residue.

What "BBB" means here — the state-level quasihalting convention, and
what this does *not* claim (it is not BB(4), and machine-count
bookkeeping stays untrusted) — is stated precisely in
[`docs/CLAIMS.md`](docs/CLAIMS.md).

**Axiom footprint: `functional_extensionality_dep`, and nothing else**
(`BBB4_is_unique` is axiom-free).  There are zero `Admitted` in
`theories/`.  Verify with `Print Assumptions BBB4_value` (printed
during `make proof`) or independently with `coqchk -o`.

## The verification ladder

Four rungs, in increasing order of paranoia — each needs strictly less
trust than the one before.  No rung requires deleting anything by hand:
a fresh clone carries no binaries except the census `.vo`, and the walk
targets back up and re-derive those automatically.

1. **Read the claim.**  [`theories/BBB4_Spec.v`](theories/BBB4_Spec.v)
   (with `theories/BBB4_Statement.v`) is the complete formal statement,
   census-free; [`docs/CLAIMS.md`](docs/CLAIMS.md) states in prose
   exactly what is proved — and what is not.  Trust: the authors.
2. **`make`** (stock Coq 8.18, no opam, ~1–2 h).  Rebuilds every
   checker, every board theorem, the champion's exact score, and
   `closeout_partial` — the entire boarding argument — **from source;
   none of the committed `.vo` are in this closure**.  Trust: the Coq
   kernel.
3. **`make proof`** (the census opam switch, minutes).  Adds the
   census chain: loads the 154 committed census `.vo` (hash-guarded
   against the census sources) and yields `bbb4_target` and
   `BBB4_value`.  Trust: the kernel, plus that those `.vo` are honest
   output of the census walk.
4. **`make census-verify`** (~24 h, ≥16 GB RAM).  Removes that last
   trust: backs the committed `.vo` up automatically and re-walks the
   census from source.  The walk is resumable per-unit, so re-walking
   a *sample* of units and checking they reproduce the committed
   output is also meaningful.  Trust: the kernel alone.

For the extra-careful, `coqchk -o` re-verifies compiled proof terms
with the standalone checker at any rung.  Full instructions and the
expected outputs for every rung: [`docs/VERIFYING.md`](docs/VERIFYING.md).

## Building

Requires Coq 8.18 and Python 3 (the Python is reporting/generation
tooling only — it carries no proof weight).

```sh
make            # the full from-source build: every checker, board and
                # the closeout, on stock Coq -- no committed binaries
make proof      # + the census-backed top-level theorem and its report
```

High `-j` is fine on a big machine: the nine memory-heavy
`IRules_Batch_*` files (~6–8 GB each at peak) are throttled to at most
three concurrent builds by order-only chains in `Makefile.coq.local`,
so `make -j16` budgets ~24 GB for them while the rest of the tree fills
the remaining slots.  On a ~16 GB box use `make -j2`, or tighten the
chains in `Makefile.coq.local` to a single column.

`make proof` additionally loads the **committed census `.vo`**
(`theories/Census/Compute/`, the output of a ~7 h `native_compute`
enumeration of the whole (4,2) space).  Those binaries are
toolchain-specific: they load under the opam switch they were built
with (OCaml 4.14.2, Coq 8.18.0, `coq-native`) and are hash-guarded by
`tools/census_cache.py`.  To trust nothing but source, re-derive them
yourself:

```sh
make census-verify   # re-runs the census walk from source (~7 h at -P4,
                     # >=16 GB RAM; see docs/VERIFYING.md)
```

[`docs/VERIFYING.md`](docs/VERIFYING.md) walks through every
verification tier, from "check one machine" to "re-walk the census".

## What is in the tree

| Path | Contents |
| --- | --- |
| `theories/BBB4_Statement.v` | The (4,2) machine model and the quasihalting semantics: `VisitsAt`, `QuietFrom`, `QuietAfter`, `QuasiHaltsSt`, `NeverQuasiHaltsSt` |
| `theories/BBB4_Spec.v` | The census-free claim: `tm_champion`, `champion_score`, `Attains`, `BBB4_is`, `BBB4_statement`, `BBB4_is_unique` — with `BBB4_Statement.v`, the entire trusted statement surface |
| `theories/Checkers/` | The verified certificate checkers: cyclers, translated cyclers, n-gram closures with ranking/pattern measures, RepWL, fuel/drift rules, inductive-rules (irules) engines, quasihalt wrappers |
| `theories/Closure.v` | The generic covering-abstraction / liveness engine the n-gram and RepWL checkers instantiate |
| `theories/Machines/` | Per-machine theorems: the generated boards (`Bulk/`, batch files) plus individually proved counter machines (`Machines/Counters/`) — thousands of files; `tools/closeout/audit.py` prints the live count |
| `theories/Counters/` | The windowed-run toolkit for hand-proved machines: `WTape`, `LapGlue`/`WaveCounter`/`MeasureGlue` closers, shared counter encodings |
| `theories/Checkers/ReachSt.v`, `ReachStI.v` | The termination checker behind the REACHST tier: a machine's liveness obligation for one state, discharged as termination of the STATE-DELETED sub-machine (`docs/REACHST_TIER.md`) |
| `theories/Checkers/Ladder*.v`, `theories/Machines/Ladder/` | The ladder: counter segments carried as a value-indexed rule family, its fill law read off the machine rather than assumed (`docs/LADDER_PLAN.md`) |
| `theories/Census/` | The trusted census: TNF enumeration, the in-walk deciders, the frozen deferred tables, and (committed as `.vo`) the walk output ending in `census_decided` |
| `theories/Closeout/` | The assembly: generated stages bridging every decided frozen row to its board, `closeout_partial`, `census_boarded`, `bbb4_target`, and the hand-written `BBB4_Value.v` — the BBB(4) = 32,779,478 value theorem |
| `theories/Tests/` | Negative controls in the BBB corruption-test tradition: mutated certificates, periods, sides and claims must all fail |
| `tools/` | **Untrusted** certificate search, generators, and differential validators — a wrong certificate fails to compile, never proves a false theorem |
| `docs/` | The claim statement, verification guide, residue map, and per-wave development notes — [`docs/README.md`](docs/README.md) is the index |

## The trust story

* The kernel checks everything: every certificate emitted by the
  untrusted Python is re-derived or re-checked inside Coq
  (`vm_compute`/`native_compute`), so `tools/` need not be read to
  believe a theorem.
* Every checker feature ships with corruption tests
  (`theories/Tests/*_Corruption.v`) that must reject tampered
  certificates.
* The committed census `.vo` are genuine walk output, hash-guarded
  against census source edits; `make census-verify` re-derives them
  from source on demand.
* The partition audit (`tools/closeout/audit.py`) is untrusted Python —
  but with the residue empty it carries no weight for the value
  theorem: `not_skipped_nil` discharges the skip disjunct inside Coq,
  so no table edit can change `BBB4_value`.  It remains bookkeeping
  for the frozen tables and per-row attribution.

## Contributing

The burndown is DONE — `tools/closeout/core_rows.txt` and
`tools/closeout/shadow_rows.tsv` are empty, and
`python3 tools/closeout/audit.py` reports 5,156 of 5,156 settled.  What
remains valuable now is **verification**: independent re-runs of the
ladder above (especially `make census-verify` on hardware that can
afford it), `coqchk -o` over the full closure, and scrutiny of the
statement in [`docs/CLAIMS.md`](docs/CLAIMS.md).
[`docs/TERMINOLOGY.md`](docs/TERMINOLOGY.md) has the vocabulary and
[`NEXT_SESSION.md`](NEXT_SESSION.md) the accumulated traps;
[`docs/RESIDUE_MAP.md`](docs/RESIDUE_MAP.md) records how each family of
machines fell.

## Status and further reading

* [`docs/CLAIMS.md`](docs/CLAIMS.md) — what is proved, exactly,
  including what is **not**.
* [`docs/RESIDUE_MAP.md`](docs/RESIDUE_MAP.md) — the residue map,
  now closed out: how each shape and blocker fell.
* [`docs/REACHST_TIER.md`](docs/REACHST_TIER.md) — the tier with the
  shortest explanation: a counter's liveness is a TERMINATION question
  about the state-avoiding sub-machine, which is usually far simpler than
  the machine.  127 rows over two waves.
* [`docs/LADDER_PLAN.md`](docs/LADDER_PLAN.md) — the other live route, and
  the current producer: a counter segment carried as a value-indexed rule
  family whose fill law, code and step are read OFF the machine rather
  than assumed.
* [`docs/VERIFYING.md`](docs/VERIFYING.md) — how to check any of this
  yourself.
* [`SCOPING.md`](SCOPING.md) — the original inventory and phased plan
  (historical).
* [`NEXT_SESSION.md`](NEXT_SESSION.md) — the internal development log:
  per-wave findings, traps, and the compute playbook.  Kept verbatim as
  the project's lab notebook.
