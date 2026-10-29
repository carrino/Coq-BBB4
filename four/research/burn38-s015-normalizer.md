# S015: a shared token normalizer closes a fixed-prefix grammar

The exact complete machine is `1LB0RA0LB2RB_3RB3LA0RA1RA` (S015).
The package proves `NonHalt` and `QHBound 0`, then its exact all-completion
state census family. S014 and S016 are not classified by this package.

Use nearest-first left tokens

```
a = 13312       b = 012       c = 312       d = 13313312.
```

Define a function on arbitrary finite token lists:

```
F([])   = ab          F(a x) = a F(x)
F(b x)  = d x         F(c x) = b F(x)
F(d x)  = aac x.
```

The shared theorem `bn_normalize` is universal for all three B2 variants.
Starting in B at the back of `enc(x)3`, with right word `0·31313·r`, it
reaches A3 with left word `enc(F(x))3` and right word `r`. The right
continuation `r` is arbitrary. The terminal left 3 has a blank half-tape
beyond it. This explicit boundary guard is needed.

The proof is a structural induction on `x`. A left `a` scan takes 29
steps and a matching right emission takes nine; `c` takes 23 and three.
The stopping cases `b`, `d`, and the terminal 3 take 10, 46, and 30 steps.
Thus its exact cost is

```
cost([])=30, cost(a x)=38+cost(x), cost(b x)=10,
cost(c x)=26+cost(x), cost(d x)=46.
```

For S015, let `C(x)` be A0 with blank right tape and left word
`ab·enc(x)·3`. A 191-step header, the shared normalizer, and an eight-step
finish reach `C'(F(x))`, with left prefix `12bb`. A 161-step second header,
the same normalizer, and a twelve-step finish give the universal cycle

```
C(x) -> C(F(F(x)))
```

in exactly `372+cost(x)+cost(F(x))` positive steps. The blank tape reaches
`C([])` after 56 steps. Every finite token list is admitted, so this
supplies arbitrarily late A visits, followed one step later by B visits.
Totality gives nonhalting; both-state recurrence gives quiet-state bound
zero. The proof uses the original RightZero B2 transition exactly.

The regressions include the empty cycle and all four leading-token
branches. They also retain a universal infinite exclusion, for all three
variants:

```
A0(left=12(13)^(4n+3)3, right=blank)
  -> permanent B0/rightblank after 192n+231 steps.
```

Its full B suffix is proved for every `n`, not inferred from controls.
These seeds lie outside S015's guarded fixed-`ab` grammar. A normalizer
with an empty right continuation also leads to B drift after its A3
return; the actual cycle uses the two explicit continuation guards.

The independent native checker grants zero proof credit. It checks 8,184
normalizer instances across all three tables and eight right contexts,
341 exact S015 cycles, and 18 paired drift seeds with 65 further B steps
each. Its source and inputs are pinned; the frontier is a copied file.

Replay after building the public core, from the repository root:

```sh
export PATH=/workspace/.opam/census/bin:$PATH
python3 four/tools/check_burn38_s015_normalizer_native.py --check
python3 four/tools/check_burn38_s015_normalizer.py --timeout 600 --audit-timeout 1800
```

All six modules are compiled freshly and full recursive `coqchk` includes
the regressions. There are no historical object-byte or unrelated report
prerequisites. The shared normalizer and negative transducers introduce
no axioms; recurrence lifting uses only the existing functional
extensionality axiom.

The author replay passed: six modules compiled in 6.260 seconds total;
full recursive `coqchk` checked 266 modules, reused zero, and took 38.294
seconds. Independent review and registration belong to the coordinator.
