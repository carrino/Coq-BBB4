# S014: a guarded token grammar closes under finite normalizer passes

The exact complete machine is `1LB0RA0LB2RB_3RB3LA0LB1RA` (S014). This
package proves `NonHalt`, `QHBound 0`, and the exact all-completion state
census family. It makes no instruction claim.

Use nearest-first left tokens

```
a = 13312       b = 012       c = 312       d = 13313312.
```

For a token word `w`, let `C(w)` be A0 with blank right tape and left word
`enc(w)3`. The admitted main grammar consists exactly of

```
[a], ab x, ad x, aa x
```

where `x` is an arbitrary finite token list. In particular, `ac x` is
excluded. This guard is a structural condition on the word, rather than
a relation to a measured trace length or a distant marker.

The shared function and its exact cost are

```
F([])=ab, F(a x)=a F(x), F(b x)=d x, F(c x)=b F(x), F(d x)=aac x;
cost([])=30, cost(a x)=38+cost(x), cost(b x)=10,
cost(c x)=26+cost(x), cost(d x)=46.
```

The byte-identical frozen `Normalizer.v` is copied into this package's
own namespace. Its universal theorem runs from B at the back of
`enc(x)3`, with right word `0·31313·r`, to A3 with left word `enc(F(x))3`
and right word `r`. The right continuation is arbitrary, and the terminal
left 3 is followed by implicit blanks. The proof uses structural
induction on the token list and adds no axioms.

S014's four grammar branches have universal positive returns:

- `C([a])` reaches `C(adab)` in 444 steps.
- `C(ab x)` reaches `C(aac F(x))` in `354+cost(x)` steps.
- `C(ad x)` reaches `C(aab F²(x))` in `522+cost(x)+cost(F(x))` steps.
- `C(aa x)` reaches an auxiliary B cut carrying `F³(x)` after three
  normalizer passes. Structural induction proves `F³(x)=aa y` for some
  finite word `y`. A further two-pass lemma sends this cut to
  `C(a F²(y))`. The latter is admitted because `F²(y)` always starts with
  `a` or `d`.

The last branch need not be the first main return. Its explicit positive
finite composition is enough to prove closure. Every header and finish
is a context-parametric finite-step theorem; all token-list passes are
universal. The blank tape reaches `C(ab)` after 56 steps. Closed positive
returns give arbitrarily late A visits, followed one step later by B.
Totality gives nonhalting, and both-state recurrence gives bound zero.

The guard matters. The regression proves that `C(ac)` reaches B0 with a
blank right tape after 225 steps, and universal B drift makes this
permanent. It also preserves the stronger infinite exclusion, for all
three original sibling tables:

```
A0(left=12(13)^(4n+3)3, right=blank)
  -> permanent B0/rightblank after 192n+231 steps.
```

The new proof does not admit these synthetic seeds. The existing partial
packages and the accepted S015 sources remain unchanged.

The independent native controls grant zero proof credit. They replay
1,024 guarded macros, 18 paired negative seeds, the `ac` negative, and
65 further drift steps for every negative. They check the exact blank
entry and decode the transition strings independently. The frozen
frontier is a copied file, rather than the mutable live tracker.

Replay after building the public core:

```sh
export PATH=/workspace/.opam/census/bin:$PATH
python3 four/tools/check_burn39_s014_normalizer_native.py --check
python3 four/tools/check_burn39_s014_normalizer.py --timeout 600 --audit-timeout 1800
```

The driver checks the frozen parent source hash for `Normalizer.v`,
recompiles its byte-identical local copy and all other package modules,
and runs full recursive `coqchk` including regressions. It requires no
old S015 objects or reports. Only the existing functional extensionality
axiom is used for finite-tape lifting and recurrence.

The author replay passed: all six modules compiled in 6.160 seconds total;
full recursive `coqchk` checked 266 modules, reused zero, and took 41.712
seconds. Independent review and registration belong to the coordinator.
