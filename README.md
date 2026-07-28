# Coq-BBB4

A Coq formalization of the Beeping Busy Beaver problem on 4-state,
2-symbol Turing machines — BBB(4) — built from the certificates of the
[BBB harness](https://github.com/carrino/BBB) on the patterns of
[Coq-BB5](https://github.com/carrino/Coq-BB5) and
[busycoq](https://github.com/carrino/busycoq).

## The result

`make proof` builds and reports the top-level theorem
(`theories/Closeout/BBB4_Theorem.v`, kernel-checked, `Qed`):

```coq
bbb4_target : forall tm,
  QHBound 32779478 tm \/ NeverQuasiHaltsSt tm \/ Deferred D_remaining tm
```

Every (4,2) Turing machine either **quasihalts with score at most
32,779,478** — the champion's score — or **never quasihalts**, *except*
the **621 residue machines** in `D_remaining`
(`tools/closeout/frozen_unproven.txt`), which are still undecided and
are reported as **SKIPPED**.

Two honest caveats, stated precisely in
[`docs/CLAIMS.md`](docs/CLAIMS.md):

* The champion `1RB1LD_1RC1RB_1LC1LA_0RC0RD` is itself one of the 621,
  so this is **not** a proof that BBB(4) = 32,779,478 — any residue
  machine could, for all this development proves, quasihalt with a
  larger score.
* `Deferred D_remaining tm` means membership in the orbit of the 621
  frozen rows under completion of undefined transitions, non-start
  state swaps, and mirroring — not bare list membership.

**Axiom footprint: `functional_extensionality_dep`, and nothing else.**
There are zero `Admitted` in `theories/`.  Verify with
`Print Assumptions bbb4_target` (printed during `make proof`) or
independently with `coqchk -o`.

## Building

Requires Coq 8.18 and Python 3 (the Python is reporting/generation
tooling only — it carries no proof weight).

```sh
make            # the full from-source build: every checker, board and
                # the closeout, on stock Coq -- no committed binaries
make proof      # + the census-backed top-level theorem and its report
```

Use `make -j2`: one generated file peaks at ~6 GB of RAM, so higher
`-j` wants a correspondingly larger machine.

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
| `theories/BBB4_Statement.v` | The (4,2) machine model and the quasihalting semantics: `VisitsAt`, `QuietFrom`, `QuasiHaltsSt`, `NeverQuasiHaltsSt`, `QHBound` |
| `theories/Checkers/` | The verified certificate checkers: cyclers, translated cyclers, n-gram closures with ranking/pattern measures, RepWL, fuel/drift rules, inductive-rules (irules) engines, quasihalt wrappers |
| `theories/Closure.v` | The generic covering-abstraction / liveness engine the n-gram and RepWL checkers instantiate |
| `theories/Machines/` | Per-machine theorems: ~4,300 generated boards (`Bulk/`, batch files) plus individually proved counter machines (`Machines/Counters/`) |
| `theories/Counters/` | The windowed-run toolkit for hand-proved machines: `WTape`, `LapGlue`/`WaveCounter`/`MeasureGlue` closers, shared counter encodings |
| `theories/Census/` | The trusted census: TNF enumeration, the in-walk deciders, the frozen deferred tables, and (committed as `.vo`) the walk output ending in `census_decided` |
| `theories/Closeout/` | The assembly: generated stages bridging every decided frozen row to its board, `closeout_partial`, `census_boarded`, and `bbb4_target` |
| `theories/Tests/` | Negative controls in the BBB corruption-test tradition: mutated certificates, periods, sides and claims must all fail |
| `tools/` | **Untrusted** certificate search, generators, and differential validators — a wrong certificate fails to compile, never proves a false theorem |
| `docs/` | The claim statement, verification guide, residue map, and per-wave development notes |

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
* One number is reporting, not kernel-backed: that the proven/remaining
  tables exactly partition the frozen census list is checked by
  `tools/closeout/audit.py` (untrusted).  Padding `remaining_rows`
  would only *weaken* the theorem, never falsify it.

## Status and further reading

* [`docs/CLAIMS.md`](docs/CLAIMS.md) — what is proved, exactly,
  including what is **not**.
* [`docs/RESIDUE_MAP.md`](docs/RESIDUE_MAP.md) — the 621 undecided
  machines, mapped by shape and blocker.
* [`docs/VERIFYING.md`](docs/VERIFYING.md) — how to check any of this
  yourself.
* [`SCOPING.md`](SCOPING.md) — the original inventory and phased plan
  (historical).
* [`NEXT_SESSION.md`](NEXT_SESSION.md) — the internal development log:
  per-wave findings, traps, and the compute playbook.  Kept verbatim as
  the project's lab notebook.
