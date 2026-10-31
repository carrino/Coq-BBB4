# S059: four phases implement binary increment

The exact complete machine is `1LB2LB3RA0RA_2RB3RA2LB3LA`. The new proof
establishes `NonHalt` and `QHBound 0`, followed by the exact all-completion
state census wrapper. It makes no instruction claim.

All left words below are written nearest cell first. Put

```
P = 3330       Z = 00       O = 03.
```

A main cut `C(n,bits)` has state A, a blank head and right half-tape, and
left word `P^n 32 enc(bits)`. The binary digits are little endian, with
`enc(0)=Z` and `enc(1)=O`. Every finite binary word is permitted, including
the empty word. Its value need not equal the independent unary length `n`.

The universal return rule is

```
C(n,1^j 0 ds) -> C(n+1,0^j 1 ds)
C(n,1^j)      -> C(n+1,0^j 1)
```

and both cases take exactly `64n+72+12j` steps. The implicit blank end
serves as a zero token. For the first rule, the suffix after the explicit
zero token may be any symbol list, so the theorem is stronger than the
binary grammar requires.

The proof crosses each `P` block to the left in 12 steps and restores it
to the right in four. The local carry crosses each `O` token in two steps
and restores it as `Z` in ten. Four boundary phases combine these sweeps
into the full increment. All outside contexts in the local lemmas are
arbitrary. Structural induction factors every binary word into leading
one tokens and either an explicit zero or the implicit blank end; hence
the main grammar is closed under positive returns.

The exact blank tape reaches `C(0,[])` after three steps. Every main cut
visits A, and its next transition visits B. Positive closed returns give
arbitrarily late visits to both states. Totality gives nonhalting, and
both-state recurrence gives quiet-state bound zero. No assertion about a
finite original-orbit quiet bound is used.

The regressions retain the earlier step-18 entry with left word `33032`.
They also prove the two unsafe synthetic boundaries from the old partial
obligation: left `33` enters a permanent-B guard after five steps, and
left `333033` does so after 17 steps despite its distant 3 marker. The
guard theorem is proved universally in this package, and both unsafe
words are excluded from every main cut. The old partial source and its
objects are not replay prerequisites.

The independent native checker decodes the transition text and checks
324 bounded increments, both actual entries, and the two negative guards
followed by 65 guard-preserving steps each. These checks grant zero proof
credit. The frontier input is a frozen copy; the mutable live tracker is
not read during replay.

Replay from the repository root with Coq 8.18:

```sh
export PATH=/workspace/.opam/census/bin:$PATH
python3 four/tools/check_burn36_s059_counter_native.py --check
python3 four/tools/check_burn36_s059_counter.py --timeout 600 --audit-timeout 1800
```

The formal driver freshly compiles all five package modules and runs full
recursive `coqchk`, including regressions, without a reused receipt. It
requires this package's own frozen sources and inputs and the public Coq
source closure. No historical object-byte identity or unrelated accepted
report is a prerequisite. The only axiom used is the existing functional
extensionality from the finite-tape denotation.

The author replay passed: all five modules compiled in 5.137 seconds in
total, and a fresh recursive audit checked 265 modules, reused zero, and
took 43.198 seconds. Independent review and registration belong to the
coordinator.
