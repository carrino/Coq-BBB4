# Three binary-counter siblings

This isolated package proves `NonHalt` and `QHBound 0` for these complete
machines, with exact census membership and all-completion state bounds:

- S001: `1LB0LA0RB3LB_3RB1LB3RA2LB`
- S002: `1LB0LA0RB3LB_3RB2RA3RA2LB`
- S003: `1LB0LA0RB3LB_3RB3LB3RA2LB`

The core is parameterized by the three B1 transitions. All other transitions
are shared. A finite bit word is encoded nearest cell first on the left by
pairs `30` (false) and `33` (true), with the low bit nearest the head. Its
ordinary binary value is `bt_value`.

Selected returns have state A and one of five head/right forms, followed by
an arbitrary finite all-blank tail. Their invariants are:

| Head/right form | Required checksum |
| --- | --- |
| `0` | binary value modulo 3 is 0 |
| `1` | binary value modulo 3 is 1 |
| `3` | bit-word length is odd |
| `21` | length is even for S001; value modulo 3 is 2 for S002/S003 |
| `23` | binary value modulo 3 is 1 |

The blank initial configuration is exactly the first form with the empty
bit word, so the universal return induction starts at time zero. Separate
regressions also check the first nonempty returns: S001 at time 6 with bit
word `[true]` and head 1; S002 at time 5 with the same word and head; S003 at
time 6 with word `[true]` and head 3.

The proof establishes shared universal macros in arbitrary finite right
contexts. B traverses `n` true pairs in `2n` steps, replacing them with `2n`
twos on its right. A consumes `n` right-hand `22` pairs in `2n` steps and
prepends `n` false bit pairs on its left. If B reaches a false bit after `n`
true bits, the combined macro increments the binary word in `4n+3` steps:

```text
true^n false tail  ->  false^n true tail
```

All-true overflow is proved separately, including an empty-word overflow
before `21` or `23`. The checksum controls those branches. In particular,
an all-true word never has value 2 modulo 3; a value of 0 forces even length,
and a value of 1 forces odd length. These facts prevent an overflow from
exposing a B scan over an unmarked blank suffix.

`bt_main_next` combines the carry, overflow, and pair-scan lemmas to prove a
positive return satisfying the same five-form invariant for every admissible
bit word and blank tail. `bt_returns` gives arbitrarily late selected A
returns from the actual blank tape. B recurs independently: an A-only episode
can only erase a finite leftward run of 1s before returning to B. Totality
proves nonhalting, and recurrence of both states proves `QHBound 0`.

The checksum is necessary. With a single false bit and head 1, the required
value-1 checksum fails; in eight steps the machine reaches B on blank with
only blanks to its right. A regression checks this invalid boundary for all
three machines. The twelve Coq controls also cover the actual blank entries,
carry and overflow contexts, the forbidden all-true value-2 case, odd length,
and a malformed physical bit pair.

Reproduce from the repository root with Coq 8.18 available on `PATH`:

```sh
python3 four/tools/check_burn19_binary_trio_native.py --check
python3 four/tools/check_burn19_binary_trio.py
```

Native controls check 2,728 normalized cases through eight bits, plus the
universal macro formulas over short arbitrary tape contexts. They provide
no proof credit. The proof runner compiles the core, twelve regressions,
three exact complete-table wrappers, the all-completion state-zero board,
and its exact census inventory. It then performs a fresh recursive kernel
audit of the inventory, including the regressions. Generated sources and
objects remain under `four/build/burn19-binary-trio/proof`.

The core theorem reports only the repository's existing functional
extensionality axiom from finite-tape lifting. No instruction-bound or global
census-closeout claim is made. Holdout credit requires independent review and
tracker registration. The earlier accepted packages remain unchanged.
