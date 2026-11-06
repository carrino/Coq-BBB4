# Beep patterns of the current four-state waiting records

The two current waiting records have exponential growth in the number of
rounds, with different rhythms: the state witness has bursts separated by
increasingly long silences; the instruction witness has isolated beeps.
These machines are lower-bound witnesses, not proved global waiting maxima.

Times below are configuration indices, with the blank initial configuration
at time zero. A beep means being in state B, or being about to execute D0,
respectively. All tape outside the displayed finite word is blank.

The finite windows at the BBB cutoff are proved in
[WitnessRecord.v](../theories/WitnessRecord.v) and
[Examples.v](../theories/Examples.v). The general recurrences below are
mathematical derivations from the transition tables, checked against concrete
simulations; they have **not yet been formalized in Coq**.

## State witness: bursts, with silences growing by a factor tending to nine

Machine: `1RB1RC_1LA0LA_0RD0RC_1LD1LA`. Beeper: **B**.

There is an initial beep at time 1. Starting at time 10, the machine repeats
the following pattern. At a burst's beginning its tape is a block of `n` ones,
and its head is on the second one in state B. There are exactly `n-1` beeps,
five steps apart, moving the head rightward across that block.

After the last beep, the next burst begins after

```text
3*n^2 - 4*n + 3 steps,
```

with a block of `3*n-2` ones. This rule applies for `n>=2`.
The initial block has length 5, so successive
lengths are `5, 13, 37, 109, 325, 973, 2917, 8749, 26245, ...`.

| Burst | First beep | Last beep | Number of beeps |
| ---: | ---: | ---: | ---: |
| 0 | 10 | 25 | 4 |
| 1 | 83 | 138 | 12 |
| 2 | 596 | 771 | 36 |
| 3 | 4,733 | 5,268 | 108 |
| 4 | 40,478 | 42,093 | 324 |
| 5 | 357,671 | 362,526 | 972 |
| 6 | 3,198,824 | 3,213,399 | 2,916 |
| 7 | 28,728,401 | 28,772,136 | 8,748 |
| 8 | 258,372,146 | 258,503,361 | 26,244 |
| 9 | 2,324,798,459 | 2,325,192,114 | 78,732 |

For a zero-based burst number `k`, every beep in that burst is given by

```text
n_k = 4*3^k + 1
T_k = 6*9^k + 14*3^k - 3*k - 10
beep times = T_k + 5*j, for 0 <= j < 4*3^k.
```

The count of beeps per burst triples. The silence between bursts grows
quadratically in the block length, so successive silences have a ratio
tending to nine. This is exponential in the burst number; consecutive beeps
within a burst are still just five steps apart.

The cutoff **32,779,478** lies after burst 7. The first subsequent beep is
**258,372,146**, giving the proved extra-wait lower bound **225,592,668**.
The full gap between consecutive beeps around that cutoff is **229,600,010**;
the waiting record measures only the part after the cutoff.

### Derivation of the state recurrence

Number the block's cells `0,...,n-1`. For a B head on an interior one, the
five transitions B1, A1, C0, D1, A0 restore the tape and move the B head one
cell right. On the final one, the first six transitions instead leave A at
cell `n-3` with a block of `n+1` ones.

If A is on a one with `r` further ones to its right, it erases that suffix
using C, restores it using D, adds two ones at the right, and ends in A one
cell left. This takes `2*r+5` steps. In the current run the suffix lengths
are `3,6,...,3*(n-2)`. Finally A reaches the left blank, writes one, and enters
B on the new block's second cell. The time from the last B to the next B is

```text
6 + sum(j=1..n-2, 6*j+5) + 1 = 3*n^2 - 4*n + 3.
```

No intermediate transition enters B. The new block length is `3*n-2`.
This derivation also covers `n=2`, with an empty sum.

## Instruction witness: isolated beeps, with gaps growing by a factor tending to sixteen

Machine: `1RB0LD_1RC1RB_1LA1LC_0RC1LA`. Beeper: **D0**.

At each beep the head is on a blank in state D, with blank tape to its left
and `(01)^n` to its right. For `n>=1`, the next such configuration occurs with

```text
n_next = 4*n + 2
time to next beep = 20*n^2 + 30*n + 8.
```

There are no D0 beeps between these configurations. Starting at time 28
with `n=4`, the observed sequence is:

| Beep time | n | Steps since preceding beep |
| ---: | ---: | ---: |
| 28 | 4 | — |
| 476 | 18 | 448 |
| 7,504 | 74 | 7,028 |
| 119,252 | 298 | 111,748 |
| 1,904,280 | 1,194 | 1,785,028 |
| 30,452,828 | 4,778 | 28,548,548 |
| 487,181,856 | 19,114 | 456,729,028 |
| 7,794,655,204 | 76,458 | 7,307,473,348 |

The repeated tape block roughly quadruples, and the time needed is quadratic
in its length. Thus successive gaps have a ratio tending to sixteen. There
is no tower or iterated-exponential growth in this recurrence.

The cutoff **32,779,478** lies between beeps at **30,452,828** and
**487,181,856**, giving the proved extra-wait lower bound **454,402,378**.

### Derivation of the instruction recurrence

Write `H(k,m)` for a blank left half-tape, A scanning a zero, and right word
`1^k(01)^m`. For `m>=1`, direct sweeps through B and C give

```text
H(k,m) -> H(k+4,m-1) in 2*k+6 steps.
```

The head moves two cells left. When `m=0`, another `2*k+5` steps give:

- for even `k`, A on zero with right word `1(01)^((k+2)/2)`;
- for odd `k`, D on zero with right word `(01)^((k+3)/2)`.

From the D0 configuration with right word `(01)^n`, two setup steps lead
to `H(2,n-1)`. The first sweep stage ends at `H(1,2*n)` after another
`4*n^2+6*n-1` steps. The second ends at D0 with `(01)^(4*n+2)` after another
`16*n^2+24*n+7` steps. Including setup, the sum is
`20*n^2+30*n+8`. No earlier D0 occurs.

## Validation scope

The state macro was additionally checked on arbitrary block lengths 2 through
100, and the instruction macro on parameters 1 through 128. Concrete blank-tape
simulation reached 2.4 billion state-machine steps and 8 billion
instruction-machine steps, reproducing the tables above. The trace tables and
the exact Coq windows agree. General recurrence
lemmas would strengthen the formal account, but are not needed to give the
already checked lower bounds their proof credit.
