# SBCv1 is a portable theorem, not a decider

_John, 2026-07-27: "and also look at this one:
`github.com/ccz181078/busycoq/blob/BB6/verify/SBCv1.v`".  It is the most
useful thing anyone has pointed at in this whole thread, and not for the
reason the wiki page suggested._

## What it actually is

`SBCv1.v` is **not a decider**.  It is a hypothesis-style Coq section in
exactly the architecture of our own `LapDecider.v`:

* `Section SBCv1` opens with `Hypothesis tm : TM` and twelve unknown WORDS
  (`d0 d1 d1' d1a d d' w0 w0' w10 w11 r0 r1`) plus two states `QL QR`;
* sixteen `Hypothesis` rewrite rules constrain them;
* `Theorem nonhalt : ~halts tm c0` follows;
* `Ltac solve_SBCv1` discharges every rule by **concrete stepping**
  (`steps`, `execute`) -- no search, no reflection, no extraction.

So a certificate is a finite object -- twelve short words and two states --
and the whole theorem is something we could **port** rather than extract.
That is a completely different proposition from `RRBA`, which cost 25 minutes
of extraction, needed `Unset Extraction AutoInline` to terminate at all, and
decided none of our machines.

It is also upstream's single most productive shape:

| theorem | machines closed (6x2) |
|---|---:|
| **SBCv1** | **416** |
| SOCv1 | 287 |
| SBCv2 | 197 |
| BECv1 | 132 |
| SOCv2 | 113 |
| FractalType1v1 | 79 |

## The shape

    S0 n m  =  LeftBinaryCounter (xI n) <{{QL}} d' *> w0^(3+m) *> w10 *> 0^inf
    BigStep:   S0 n m -->+ S0 (xI n) (2*|n| - m - 3)      for `full n`

`full n` means `n = 2^k - 1`, so the left binary counter is all-ones exactly
at the overflow and `m` is its complement.  This is the wiki's `C'(a,b,k)`
with `a + b + 1 = 2^k` verbatim: one overflow costs `Theta(2^k)` increments.

**This is the answer to the gap named in `BOUNCER_COUNTER_READING.md`.**  Our
`sside = pre ++ rep u (a*j + b) ++ post ++ X` is indexed by the carry-run
length `j` alone, so it cannot say "this side's length is proportional to the
value the OTHER side encodes".  SBCv1 does not need a cleverer single index --
it carries the two counters as **two separate indices**, `n` binary on one
side and `m` unary on the other, coupled only by the side condition
`m + 2 <= |n|`.  That is a much smaller ask than the nested lap.

## The checker (`tools/counters/sbcfit.py`)

Because every hypothesis is discharged by stepping, a certificate can be
validated without Coq.  The soundness gate is the one Coq itself imposes: a
rule quantified over an abstract side `l` can only be proven by `step` while
the head is over CONCRETE symbols, so a run that must read into the abstract
tail is a failure here exactly as it is there.  Tails written `const 0` are
readable, which is why `RL2` and `L_overflow` may wander off the written
window and the other eight rules may not.

Tape conventions were read off the source, not assumed:

* `Notation "xs *> r" := (Str_app xs r)` (Helper.v:179)
* `Notation "l <* xs" := (Str_app xs l)` (Helper.v:180) -- the SAME operation,
  so `l <* X <* Y` puts Y nearer the head and `X *> Y *> r` puts X nearer;
* `l <{{q}} r` reads `hd l`, `l {{q}}> r` reads `hd r` (TM.v:101-102).
  Note this is a READING of any config, not a claim about which way the head
  last moved -- an early version of the search assumed the latter and lost
  every certificate.

**Positive control: 416 / 416** of `SBCv1_6x2_solved.v` accepted, in 0.4 s.

## The searcher

Words are derived from a real run, not guessed:

* the two sweeps are shift rules -- `R_carry` gives `w0'` from `(QR, d, w0)`,
  `L_carry` gives `d1'` from `(QL, d1, d')`;
* `L_return` is the same rightward shift with a different block, and yields
  `d0`;
* `RL0` yields `w11`;
* one scan resolves `n0`, `m0` and `d1a` together, because
  `LeftBinaryCounter (xI n)` for `full n = 2^k - 1` is `d1` repeated k times
  followed by `d1a` -- so the count of leading `d1` copies IS k.

**Positive control: 15 / 15** sampled upstream certificates re-found
independently, several DIFFERENT from the ones mxdys wrote (machine 0 gets
`F D`, upstream has `E D`).

Three things the controls caught, each worth keeping:

1. **Uniform time-sampling loses certificates.**  On
   `1LB1RE_0LC0LB_1RD1LB_0RA---_0RF0LC_1RA0RD` every derivation succeeds in
   isolation, but `d1 = [0;1;0;1]` never lands in a uniformly spaced
   snapshot.  Collect DISTINCT local windows instead; the set is small
   because a sweep repeats the same few neighbourhoods.  14/15 -> 15/15.
2. **The rules are short.**  Instrumenting the checker over all 416
   certificates gives the worst case of any hypothesis on any machine:
   `R_reset` 41 steps, `L_overflow` 29, everything else <= 16.  A 400-step
   cap is a 10x margin; the original 2000-step cap with per-step cycle
   detection spent the entire search budget on junk candidates.
3. **The search ranges are bounded by the same 416 certs**, not invented:
   `|d| = |d'| <= 2`, `|d1| = |d1'| = |d0|` in {2,4,6}, `|w0| = |w0'|` in
   {3,4,5}, `|w10| = |w11| <= 3`.

## Do not repeat

* Do **not** treat `l <{{q}} r` as "the head just moved left" and restrict
  the S0 scan to turning points.  It is a notation for splitting the tape;
  any config admits both readings.  This scored 0/15 on the control.
* Do **not** copy the whole tape per snapshot.  At `T = 200k` that is ~10^7
  dict entries per machine and dwarfs the search itself.

## What it says about our machines

MEASUREMENT IN FLIGHT at the time of writing -- numbers land in the section
below.  The interesting diagnostic is not the hit count but WHERE a machine
falls out, which `--debug` reports per stage:

| field | meaning |
|---|---|
| `rc` | rightward shift rules found (`R_carry` candidates) |
| `lc` | leftward shift rules found (`L_carry` candidates) |
| `part` | pairs surviving the join: `L_return` gives a `d0 != d1`, `RL0` gives `w11` |
| `s0` | candidates whose machine actually REACHES a sync bouncer counter config |

Read as a funnel this says something our shape recognizers never could.
`rc`/`lc` say "this machine sweeps"; `part` says "and its two sides carry a
consistent carry/return discipline"; `s0` says "and it really is a binary
counter against a unary one".

One reading is already firm, on the machine John named
(`1RB0RB_1LC1RA_1RA0LD_0LB0LD`, `docs/BOUNCER_COUNTER_READING.md`): both
sweeps are found (`rc=32, lc=24`) and the join is empty because every
`L_return` derivation returns `d0 == d1`.  That is not an arbitrary filter --
with `d0 = d1` the `L_carry` and `LR` hypotheses would both have to fire from
the same configuration and travel in opposite directions.  It says the LEFT
side has no distinct 0-digit and 1-digit, i.e. it is a UNARY bouncer, which
is exactly the run of 1s of length `3n` measured off its tape.  Consistent
with it being one of the 27 genuine mxdys holdouts.

## SBCv2 is the next target, and its rule table is already validated

`SOCv1` (287) is NARROWER, not broader -- it hardcodes its digit alphabet
(`d0 = [0;1]`, `d1 = [1;1]`, `d1a = [1]`) and parameterizes only states and a
few lists, so it only fits machines whose tape already uses those digits.

**`SBCv2` (197) is the one that generalizes the side we fail.**  It discharges
five rules instead of sixteen, keeps `LInc` -- the left binary counter --
exactly as SBCv1 has it, and replaces the whole right-hand mark/carry family
with two ABSTRACT families supplied by the certificate:

    R0 n   = w^n *> tail *> 0^inf                  (a plain run, NO marker)
    R1 n m = w^m *> mark *> w^n *> tail *> 0^inf   (ONE marker, not two)

    LInc : L n <| r        -->+ L (succ n) |> r     (not_full n)
    RInc0: l |> R0 n       -->+ l <| R0 (c1+n)      c1 in {1,2}
    RInc1: l |> R1 (1+n) m -->+ l <| R1 n (1+m)
    ROv1 : l |> R1 0 m     -->+ l <| R0 (c2+m)      c2 in {1,2}
    LOv  : ...the overflow...

`RInc0` is a BOUNCER sweep -- grow a run by one or two blocks per pass, no
marker involved -- where SBCv1 insists on `w10 -> w11 -> w0` two-phase
marking.  And `RInc1` moves a single marker one block right, where SBCv1
needs `RL0` and `RL1` in sequence.  `RL1` is precisely the rule our machines
die on.

The right side decomposes into five LOCAL rules, all checkable with the
abstract-tail gate this file already implements:

    Rshift : l <* qR {{QR}}> w *> r         -->* l <* w' <* qR {{QR}}> r
    Rreturn: l <* w' <{{QL}} qL *> r        -->* l <{{QL}} qL *> w *> r
    Rturn0 : l <* qR {{QR}}> tail *> 0^inf  -->* l <{{QL}} qL *> w^c1 *> tail *> 0^inf
    Rmark  : l <* qR {{QR}}> mark *> w *> r -->* l <{{QL}} qL *> w *> mark *> r
    Rov    : l <* qR {{QR}}> mark *> tail *> 0^inf
                                            -->* l <{{QL}} qL *> w^c2 *> tail *> 0^inf

because `w^n ++ w^c1 = w^(n+c1)`, so `RInc0` is `Rshift`^n, `Rturn0`,
`Rreturn`^n, and the other two go the same way.

**This decomposition is CHECKED, not conjectured.**  Run against two upstream
`SBCv2_6x2_solved.v` certificates using `sbcfit`'s `cfg` / `check_rule` /
`derive_shift` unchanged, all five rules verify on both:

| machine | w' | Rshift | Rreturn | Rturn0 | Rmark | Rov |
|---|---|---|---|---|---|---|
| `1RB1RF_0RC0RA_1RD0LE_0LC1RA_1LC1LE_---0RB` | `[0;1]` | OK | OK | OK | OK | OK |
| `1LB1RE_0LC0RF_1RD0LF_0RA---_0RB1RD_0RA0LF` | `[0;1;1]` | OK | OK | OK | OK | OK |

So building the SBCv2 fitter is a rule-table swap plus an S0 reader, against a
197-certificate positive control -- not a research question.  `w`, `tail` and
`mark` are read off the run the same way `w0` and `w10` are here.
