# Local counter lemmas and unresolved closure obligations

This package does not classify either original blank orbit. It contributes
zero state families and zero instruction families. Its universal local macros,
finite actual entries, and excluded synthetic drift seeds are kernel checked.
No census inventory or aggregate descriptor is provided.

For S056, `1LB2LB1RA3RA_3RB3LA2RB2LB`, the blank run reaches A0 with left tape
`33` at step 5. A local B carry accepts a prefix of tokens `3` or `11`, followed
by `12` or `13`. The tokens produce `1` or `31`; the stopping pair produces
`31` or `33`. The exact duration is twice the number of token cells plus three,
and both outer contexts are arbitrary. This is proved by structural induction
on the token list in `s56_local_carry`.

A0 with synthetic left tape `13` reaches B2 with a blank right tail at step 10.
The theorems `s56_B0_drift` and `s56_B2_drift` prove permanent B motion from
that boundary. Thus an unrestricted word over `1,3` is unsafe. The proposed
checksum twice the binary value of positions containing `1` or `2`, modulo
three, also fails on the actual step-101 boundary: the computed checksum is
zero and the actual head is one. Both failures are reproducible native controls.

The remaining S056 obligation is a preserved invariant relating the boundary
head/phase to successive local carry passes and the case with no stopping
pair. A0 writes `1`, so a completed local carry returns to A1 and may require
a second carry before A2 advances to a new A0 boundary. The actual initial
word `33` has no stopping pair, so the local theorem alone cannot initialize
or close recurrence. A separate bounded observation, recorded in the handoff,
suggests the all-`3` fallback `A0 3^n -> A0 31 2^(n-1)3` in `2*n+5` steps for
positive `n`; it has not been formalized here.

For S059, `1LB2LB3RA0RA_2RB3RA2LB3LA`, the blank run reaches A0 with left tape
`33032` at step 18. The theorem `s59_prefix33` universally replaces a leading
`33` by `00` and returns A1 in four steps. The theorem `s59_left_sweep` crosses
an arbitrary `0,2` word to the left while the immediate right neighbor is `2`.
Each `0` costs three steps, each `2` costs one, and every crossed cell becomes
`2`. Both outside contexts are arbitrary.

The prefix rule needs a stronger guard. Synthetic A0 left `33` reaches a
permanent-B guard at step 5. Even requiring an additional `0,3` suffix ending
in `3` is insufficient: left `333033` reaches that guard at step 17. The guard
requires only `0,2` symbols on the left, with either head `2`, or head `0` and
immediate right neighbor `2`. The right tail may contain further `3` markers.
`s59_guard_forever_B` proves the guard is preserved and every future state is
B. These are excluded synthetic configurations, with no claim that either
lies on the original blank orbit.

The remaining S059 obligation is a preserved reachable invariant excluding
those B guards while connecting the prefix rewrite, weighted B sweep, and
rightward A restoration into positive main returns. A distant `3` marker by
itself does not provide that guard. Alternatively, a finite original-orbit
entry into the B guard would support a finite quiet bound; no such entry is
proved here.

The selected hypotheses and their refinement were recorded before
formalization in `burn18-counter-obligations-hypotheses.json`. Native controls
replayed 55,566 S056 carry macros, 56,007 S059 sweeps and 441 prefix macros,
with arbitrary contexts of length at most two. They also replay actual entries
and all excluded seeds. These finite controls receive no classification credit.
The generated `ExactTables.v` proves both Coq tables equal their exact encoded
transition tables. A full recursive audit includes both modules; all listed
local and drift theorems are closed under the global context and introduce
no axioms.

After building the core, run from the repository root:

```sh
python3 four/tools/check_burn18_counter_obligations.py
python3 four/tools/check_burn18_counter_obligations.py --check
```

The frozen checked report pins the local sources, input hypotheses, exact-table
wrapper, objects and recursive audit receipt. Accepted proof packages, census
counts and aggregate files are unchanged.
