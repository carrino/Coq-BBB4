# S006: a counter in equal pairs

This isolated package proves `NonHalt` and `QHBound 0` for the complete machine
`1LB0LB0LA0RA_3RB3RA1RB2LB` (S006), with an exact all-completion census wrapper.

Selected configurations have A scanning blank, a blank right tail, and the
nearest-first left word `3 enc(bits) 3`, where false is encoded by `11` and
true by `33`. Every finite bit word is admissible. The actual blank tape
reaches the empty-word configuration in three steps.

The universal return argument has two branches:

| Bit word | Next bit word | Steps |
| --- | --- | --- |
| `true^n false tail` | `true^n true tail` | `24n+22` |
| `true^n` | `false^(n+1)` | `4n+7` |

The first branch sets the first false bit and leaves the lower true bits and
remaining context intact. The second branch grows an all-false word by one
bit. Both costs are positive, so induction gives arbitrarily late A returns.
The next step always visits B. Totality proves nonhalting; recurrence of both
states proves a state bound of zero.

The proof first establishes universal local macros over arbitrary finite
contexts. B walks left over a run of 3s, replacing them by 2s, and right over
a run of 2s, replacing them by 1s. With an actual 3 immediately left of A,
each scanned right-hand 2 takes five steps to become 3 and move A right.
This support cell is preserved at each iteration. Two phase lemmas then
combine those scans to prove the first-false branch. Overflow uses the
separate all-3 left scan; the blank right tail ensures the final A head is
again blank.

The ten Coq regressions check the actual blank entry, empty-word overflow,
a first-false branch in a nonblank outer context, a longer carry, explicit
blank padding, and an A scan in arbitrary context. Negative controls remove
the supporting 3, the outer boundary 3, or the paired false bit, and replace
the required blank tail by a nonblank cell.

Reproduce from the repository root with Coq 8.18 available on `PATH`:

```sh
python3 four/tools/check_burn20_run_counter_native.py --check
python3 four/tools/check_burn20_run_counter.py
```

Native controls check all 511 bit words through length eight and local macro
formulas over short arbitrary contexts. They provide no proof credit. The
proof runner compiles the core, ten regressions, exact complete-table
wrapper, all-completion state-zero board, and exact census inventory. It
performs a fresh recursive kernel audit of the inventory including the
regressions. Generated sources and objects remain under
`four/build/burn20-run-counter/proof`.

The core theorem reports only the repository's existing functional
extensionality axiom from finite-tape lifting. No instruction-bound or global
census-closeout claim is made. Holdout credit requires independent review
and tracker registration. Earlier accepted packages remain unchanged.

## Bounded neighboring probes

An exploratory probe used `1LB0LB1LA3RA_3RB3RA1RB2LB`, which is **not**
the frozen S009 holdout. It used A3=3RA rather than the actual A3=3RB.
Its paired-word and complement controls therefore provide no evidence for S009.
The exact frozen S009 is `1LB0LB1LA3RB_3RB3RA1RB2LB`; that machine requires
its own checked macros and wrapper.

The original S014/S015/S016 lane reproduced the supplied A0 boundary words
and diverged at the B2 transition. The bounded attempt found no universal
regular grammar that rules out a marker-free B right tail. Those three
machines remain open. S030's simple `3 2^n` left-boundary family also fails
to give a single closed return rule across all synthetic lengths; no proof
credit is claimed for that probe.
