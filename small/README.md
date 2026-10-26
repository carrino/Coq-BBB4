# Small Beeping Busy Beaver proofs

This development uses the repository's quasihalting convention for both states
and instructions. It is isolated from the existing `(4,2)` proof.

| States, symbols | State value | Instruction value |
| --- | --- | --- |
| `(1,2)` | **1**, proved | **1**, proved |
| `(2,2)` | **6**, proved | **8**, proved |
| `(3,2)` | **55**, proved | **55**, proved |
| `(2,3)` | **59**, proved | **67**, proved |

The unconditional value theorems are [`BBB12_value`](theories/Value12.v),
[`BBB22_value`](theories/Value22.v),
[`BBB32_value`](theories/Value32.v), and
[`BBB23_value`](theories/Value23.v). Their statements are in
[`Spec.v`](theories/Spec.v). All six lower-bound witnesses are checked in
[`Champions.v`](theories/Champions.v).

## Completing the (2,3) instruction proof

The exhaustive census leaves 28 difficult instruction-recurrence cases.
[`Remaining23Symmetry.v`](theories/Remaining23Symmetry.v) reduces them to seven
representatives using tape reflection and exchange of symbols 1 and 2.
All seven now have unconditional proofs:

- [`RepA.v`](theories/RepA.v) and [`RepB.v`](theories/RepB.v) provide four checked
  affine symbolic loops, preserving the necessary run-length parity.
- [`Binary23Counter.v`](theories/Binary23Counter.v) and
  [`RepA_Binary.v`](theories/RepA_Binary.v) prove two binary-counter recurrences,
  including overflow jumps and instruction visits in each phase.
- [`Symbolic23Case.v`](theories/Symbolic23Case.v) closes the polynomial loop
  using a proved word-rotation identity and the sound replay library in
  [`Symbolic23Replay.v`](theories/Symbolic23Replay.v).

[`remaining23_all`](theories/Remaining23Solved.v) assembles these bounds.
[`BBB23_value`](theories/Value23.v) discharges the intermediate census's
premises and proves both values **59 and 67 without remaining hypotheses**.
`Census23Conditional.v` and `Value23Conditional.v` remain intermediate lemmas;
they are not the final exported claim. The case lists under `certificates/`
record the census decomposition, not unresolved cases.

## Model and counting convention

The common carrier has three states and three symbols.
[`Admissible`](theories/Size.v) restricts active table cells and transition
outputs to exactly the requested size. Inactive cells are undefined.
The tape is two-way infinite and initially blank; the initial state is A and
the blank symbol is 0. Each defined transition writes, moves left or right,
and enters an active state. An undefined transition halts.

A visit at configuration index `s` has score `s + 1`. The halting configuration
counts as a visit to its state and instruction slot. A never-visited state or
instruction is not a quasihalting witness. These details explain why the
state and instruction maxima can differ.

The state values agree with the [BusyBeaverWiki champion table](https://wiki.bbchallenge.org/wiki/Beeping_Busy_Beaver#Champions)
and [Drozd's 2020 results](https://nickdrozd.github.io/2020/10/09/beeping-busy-beaver-results.html).
Those sources tabulate beep states; they do not establish this development's
instruction column.

The first transition is unrestricted here. In particular, instruction `(2,2)`
has value **8**, whereas the related
[search harness validation report](https://github.com/carrino/BBB/blob/main/VALIDATION.md)
records **7** with the normalization `A0=1RB`. Our champion
`0LB1RB_1RA1LB` first makes a blank-writing move. Deleting that move and
exchanging A and B gives the harness's `1RB1LA_0LA1RA`, shifting the last
relevant visit from configuration index 7 to index 6.
[`BBB22_normalized_instruction_value`](theories/Normalized22.v) separately
proves that **7 is the exact restricted maximum when `A0=1RB`**. Thus this
normalization changes the instruction maximum; it cannot be imposed when
proving the unrestricted value.

## Build and audit

Use Coq 8.18 with native computation enabled, as for the repository's existing
census switch:

```sh
eval "$(opam env --switch=census)"
make -C small -j2
make -C small check
```

The build first compiles the selected existing binary recurrence certificates
listed in [`legacy/targets.txt`](legacy/targets.txt). It does not run the full
`(4,2)` exhaustive census. `check` runs `coqchk` recursively, without admitting
dependencies. Its bytecode conversion option keeps the computed census checks
practical; it may still take several minutes.

The proof footprint is the existing `functional_extensionality_dep` assumption.
There are no admitted proofs or new axioms. The intermediate census
parameters are discharged by the seven checked representative proofs. Native computation checks
certificate data; Python, C++, OCaml, SciPy, and certificate generators are not
assumed correct by the theorems.

## Reproduce the search

```sh
make -C small search
python tools/multisymbol/smoke.py
python tools/multisymbol/campaign.py 22
python tools/multisymbol/campaign.py 23-state
python tools/multisymbol/campaign.py 32-state
python tools/multisymbol/campaign.py 32
python tools/multisymbol/campaign.py 23-conditional
```

Run Python commands from the repository root. Campaigns write candidate
certificates under ignored `small/build/`; compile those candidates with Coq to
validate them. Search completion alone is not a proof. The `(2,3)` instruction
campaign regenerates the intermediate conditional census; `Value23.v` closes
its premises with the separate recurrence proofs. Campaigns retain machines
from a proved registry as census leaves and skip redundant searches for them;
Coq still checks every registry reference and the exhaustive tree.

The exhaustive trees enumerate transition choices lazily, when the run first
reaches an undefined slot. The checker proves that these branches cover every
admissible labeled table, including completions of partial nonhalting tables.
There are 6,561 labeled `(2,2)` tables and 4,826,809 tables of each other size.
The tree data has 297, 43,573, and 85,021 nodes respectively; it does not contain
one proof script per labeled table.

The extracted searcher deliberately retains arbitrary-precision Coq `positive`
and `Z` values. Mapping them to OCaml machine integers previously caused
configuration-key collisions. [`Regression.v`](theories/Regression.v) and
[`smoke.py`](../tools/multisymbol/smoke.py) check rejection of a former false
candidate; a second Coq regression rejects a state bound of 5 for `(2,2)`.

## Certificate provenance

- Most core semantics, n-gram, repeated-word, and counter libraries are adapted
  from this repository to the common three-symbol carrier.
- The `(3,2)` instruction census transports 228 machine results from selected
  existing binary proofs. `legacy/Counter32.v` contains 18 selected symbolic
  certificates; the other sources are imported without copying their proofs.
- The additional `(2,3)` ranking checker is proved in `WeightedNGram.v` and
  `WeightedCensus.v`, using finite-barrier and lexicographic lemmas under
  `Checkers/`. Its certificate collections are `Weighted23.v` and
  `Weighted23Deep.v`.
- `Counters23/` contains ten checked counter proofs used through tape
  reflection, and `IR23.v` contains twelve checked symbolic certificates.
- JSON under `certificates/` records search data and registry provenance.
  `tools/multisymbol/known32.py` and `known23.py` regenerate their registry
  sources. Proof builds do not require a network connection or `/tmp` files.

`render_weighted.py INPUT.jsonl OUTPUT.v` renders either weighted certificate
collection as a standalone candidate with a Coq checker lemma. The optional
`dump_graphs` executable and `weighted_certificates.py` support further ranking
search; the latter needs SciPy. The checked counter and symbolic certificates
are self-contained Coq sources.

The larger next plan should distinguish obtaining an exact champion time by
proved recurrences from proving an exhaustive upper bound. The completed
small proofs demonstrate the recurrence machinery, but do not establish that
the `(2,4)` census is tractable.

A pasteable MediaWiki table of the exact transition values is in
[`transition-table.wiki`](transition-table.wiki). The `Small BBB proofs`
workflow builds these sources and runs the recursive audit and extraction
regression on GitHub Actions.
