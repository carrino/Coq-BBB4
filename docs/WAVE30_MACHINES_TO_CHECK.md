# Machines to check — wave-30, five open classes

Every dump below is `tools/counters/spacetime.py --rests --mark --ruler` with
**fixed `--lo/--hi`**, so the columns are absolute and comparable row to row.
Rows are blank-head rests only; the letter sits AT the head cell; `p=` is the
head's absolute column.

I have measured each class mechanically — what I cannot tell is what the
machine is DOING. One sentence per class is what I am after; the sibling
lists let you spot-check whether the read carries.


## 1. Fifty-one machines whose counter reads DOWNWARD  (biggest class)

`tailcert.two_form` finds a pair of anchor keys whose values cover 8..255 with
no gaps and split by octave parity. But walking the real run, the values are
visited **descending**:

    t=220 p=31 A   t=224 p=30 A   t=226 p=15 D   t=232 p=29 A
    t=236 p=28 A   t=238 p=14 D   t=248 p=27 A   t=252 p=26 A

so `E p -> E (p+1)` never happens and every route we have is stated the other
way round. Note `p=30` (frame A) and `p=15` (frame D) are two readings of the
SAME tape two steps apart, so the "gap-free union" may be the reader pairing a
value with its own half. The other mirror has no family at all.

**Q: is this counter actually counting down, or is our digit order / msb end
inverted — i.e. is there a reading in which it counts up?**

Exemplar `0RB1LA_0LC1RD_1LD0RB_1RB0LA`, `Ip@A` tail `[0,1,0]`, t=200..330:

```
            col  1234567890123456789
201      D p=1    0000111111d10100000
203      D p=3    000011111111d100000
205      D p=5    00001111111111d0000
206      B p=6    000011111111111b000
208      B p=6    000011111111110b000
209      C p=5    00001111111111c0000
220      A p=-6   000a111111111010000
224      A p=-6   000a101111111010000
226      D p=-4   00001d1111111010000
232      A p=-6   000a111011111010000
236      A p=-6   000a101011111010000
238      D p=-4   00001d1011111010000
240      D p=-2   0000111d11111010000
248      A p=-6   000a111110111010000
252      A p=-6   000a101110111010000
254      D p=-4   00001d1110111010000
260      A p=-6   000a111010111010000
264      A p=-6   000a101010111010000
266      D p=-4   00001d1010111010000
268      D p=-2   0000111d10111010000
270      D p=0    000011111d111010000
280      A p=-6   000a111111101010000
284      A p=-6   000a101111101010000
286      D p=-4   00001d1111101010000
```

Siblings (all 51 measure the same way):

    0RB1LA_0LC1RD_0LD1LD_1RB0LA
    0RB1LA_0LC1RD_1LD0RB_1RB0LA
    0RB1LA_0LC1RD_1LD1LD_1RB0LA
    0RB1LA_0LC1RD_1RB1LD_1RB0LA
    0RB1LA_1LC1RD_0RB1LD_1RB0LA
    0RB1LA_1LC1RD_1LD1RC_1RB0LA
    0RB1LA_1LC1RD_1RB0LD_1RB0LA
    0RB1LA_1RC0LA_1LD1RB_1LB1LD
    0RB1LA_1RC0LA_1LD1RB_1LB1RD
    0RB1LA_1RC0LA_1RD1RB_1LB0RD
    0RB1LA_1RC0LA_1RD1RB_1LB1RD
    0RB1LA_1RC1RD_1LD0RC_1RB0LA
    ... (39 more)
## 2. Eight machines where the carry's RETURN trip is state-period 2

These have an affine lap and a clean leftward carry, and still no chain. On
`1RB---_0LC1RD_0LB1RD_1LB0RD` (`Kp@D`, tail `[0]`, far `[1]`) the interior lap
is exactly `2j+6` from D to D:

    2 window steps, then a leftward carry across 1^(j+1) with the state
    CONSTANT at D, then a turn, then a rightward return across the deposited
    0^(j+1) alternating  B > C > B > C ...  one step per cell

Our cycle primitive needs ONE unit of the block to restore the state, so the
return needs the block re-unitised from `rep [0] (j+1)` to `rep [0,0] k` — and
`j+1` has no known parity. The parity cancels only in the lap's LAST TWO steps,
which is why the COST is affine while no chain exists.

**Q: is there a place to cut the lap where the return is not 2-periodic — or is
a parity split of the carry index the only way to say this?**

Siblings:

    1RB---_0LC1RB_0LB1RD_1LC0RD
    1RB---_0LC1RD_0LB1RC_1LB0RD
    1RB---_0LC1RD_0LB1RD_1LB0RD
    1RB---_0LC1RD_0LB1RD_1LC0RD
    1RB---_1LC0RB_0LD1RB_0LC1RB
    1RB---_1LC0RB_0LD1RB_0LC1RD
    1RB1LA_0LA0RC_0LD0RB_1LD1RC
    1RB1LA_0LC0RD_1LC1RD_0LA0RB
## 3. Eight machines whose crossing never returns to its entry state

Same dead-end shape as class 2, but the rightward crossing does not come back
to its entry state within 8 units at all — it drifts. `ovfshape` calls these
HIGHER (5, all `Dp`), EXP3 (2) and QUAD (1), so the lap is probably not affine
and this may not be a counter question at all.

**Q: what is this one doing? (If it is a bouncer or a two-counter, that alone
retires the class — it is not a lap-chain machine.)**

Exemplar `1RB---_0LB1RC_1LB0RD_1LC0RD`, t=60..260:

```
            col  789012345678901
60       D p=6    000100000d00000
61       C p=5    00010000c100000
62       B p=4    0001000b1100000
63       B p=3    000100b01100000
64       B p=2    00010b001100000
65       B p=1    0001b0001100000
67       C p=1    0001c0001100000
70       D p=2    00010d001100000
71       C p=1    0001c1001100000
75       D p=3    000100d01100000
76       C p=2    00010c101100000
77       B p=1    0001b1101100000
79       C p=1    0001c1101100000
84       D p=4    0001000d1100000
85       C p=3    000100c11100000
86       B p=2    00010b111100000
87       B p=1    0001b0111100000
89       C p=1    0001c0111100000
92       D p=2    00010d111100000
93       C p=1    0001c1111100000
101      D p=7    0001000000d0000
102      C p=6    000100000c10000
103      B p=5    00010000b110000
104      B p=4    0001000b0110000
```

Siblings:

    1RB---_0LB1RC_1LB0RD_1LC0RD
    1RB---_0LB1RC_1LD0RC_1LB1RC
    1RB---_1LC0RB_1LD1RB_0LD1RB
    1RB---_1LC0RD_0LC1RB_1LB0RD
    1RB---_1LC1RD_0LC1RD_1LB0RD
    1RB1LA_0LA1RC_0LD0RC_1LD0RB
    1RB1LC_1LB1RA_0LC0LD_0RA0RD
    1RB1LC_1LC1RA_0LC0LD_0RA0RD
## 4. Twenty-six machines no anchor family reaches

For these I probed EVERY anchor family in both mirrors — the flat enumeration,
`restscan`'s tolerant key (which reads the family off the machine's own rests),
and `tailcert`'s parity-split pair — and the interior target is in no form at
any of them. So this is not a framing gap: we are not reading the right
quantity.

**Q: what is the repeating unit here, and where is 'home' for the head?**

Exemplar `1RB0RB_0LC0LD_1LC1LD_1RA0RA`, t=100..420:

```
            col  12345678901234
100      A p=0    000001001a0000
101      B p=1    0000010011b000
105      B p=1    0000010000b000
106      C p=0    000001000c0000
107      C p=-1   00000100c10000
108      C p=-2   0000010c110000
109      C p=-3   000001c1110000
111      D p=-5   0000d111110000
114      D p=-4   00001d01110000
115      A p=-3   000011a1110000
118      A p=-2   0000110a110000
121      A p=-1   00001100a10000
124      A p=0    000011000a0000
125      B p=1    0000110001b000
127      D p=-1   00001100d10000
129      B p=1    0000110010b000
130      C p=0    000011001c0000
132      D p=-2   0000110d110000
135      D p=-1   00001101d00000
136      A p=0    000011011a0000
137      B p=1    0000110111b000
141      B p=1    0000110100b000
142      C p=0    000011010c0000
143      C p=-1   00001101c10000
```

Siblings:

    1RB---_0LB1RC_0RD0RC_1LB1LD
    1RB---_0LB1RC_1LB0RD_1LB0RC
    1RB---_0LB1RC_1LB0RD_1LC0RC
    1RB---_0LC1RD_1LB1RC_1LB0RD
    1RB---_0LC1RD_1LB1RD_1LB0RD
    1RB---_0RC0RB_1LD1LC_0LD1RB
    1RB---_1LC0RB_0LD1RB_1LC1RB
    1RB---_1LC0RB_0LD1RB_1LC1RD
    1RB---_1LC0RD_0LC1RB_1LB0RB
    1RB---_1LC0RD_0LC1RB_1LC0RB
    1RB---_1LC0RD_0LC1RD_1LC0RB
    1RB---_1LC1LB_0LC1RD_0RB0RD
    ... (14 more)
## 5. Sixteen machines that now clear the interior gate and die on the
   REGISTER STEP

These are the good news of the wave: with `lift` allowed on the interior split,
all 19 ascending two-form rows derive both interior halves at both octave
parities. 16 of them then stop at `register step does not close` — the
exponential overflow arm, where the machine appears to re-count the whole
counter to move one mark, and our inner carrier runs to the all-ones fill
while the machine stops HALFWAY (`2^(K+1)+4 .. 2^(K+1)+2^K-1`).

**Q: on the exponential arm, what tells the machine when to stop? If the
stopping point is readable off the tape, the carrier can be stated against it
instead of against the fill.**

Exemplar `1RB1RD_1LC1RA_0RB0LC_1LA0RD`, t=150..430:

```
            col  678901234567890123456
151      A p=1    00001a101010010000000
153      A p=3    0000111a1010010000000
155      A p=5    000011111a10010000000
157      A p=7    00001111111a010000000
158      B p=8    000011111111b10000000
167      C p=-1   000c00000000110000000
168      B p=0    0000b0000000110000000
169      C p=-1   000c10000000110000000
171      A p=1    00001a000000110000000
172      B p=2    000011b00000110000000
175      C p=-1   000c00100000110000000
176      B p=0    0000b0100000110000000
177      C p=-1   000c10100000110000000
179      A p=1    00001a100000110000000
181      A p=3    0000111a0000110000000
182      B p=4    00001111b000110000000
187      C p=-1   000c00001000110000000
188      B p=0    0000b0001000110000000
189      C p=-1   000c10001000110000000
191      A p=1    00001a001000110000000
192      B p=2    000011b01000110000000
195      C p=-1   000c00101000110000000
196      B p=0    0000b0101000110000000
197      C p=-1   000c10101000110000000
```

Siblings:

    0RB0LC_1LC1RB_1RD1LA_0LD1LB
    0RB0LC_1LC1RB_1RD1LA_1LD1LB
    0RB0RD_1LA1RC_1RD1LC_0LC1RA
    0RB0RD_1RC---_1RD1LC_0LC1RA
    0RB1LC_1LA1RB_0LD0LA_1LB---
    0RB1LC_1LA1RB_0LD0LA_1RC1LB
    0RB1LC_1LA1RB_0LD0LA_1RD0RB
    1RB---_1RC1LB_0LB1RD_0RA0RC
    1RB0LA_1LC1LA_1RD1LB_0LC0RD
    1RB1LA_0LA1RC_0RD0RB_1LC1RA
    1RB1LA_0LA1RC_0RD0RB_1LD0LA
    1RB1LA_0LA1RC_0RD0RB_1RA---
    ... (7 more)
## Confirmed from your last note, for the record

`1RB0LC_0LA0RB_0RD1LC_1LA1RD` — "a regular counter, but it does a carry bit
using bouncing, so if it needs to carry across x 1's it does x bounces".
Measured under `Kp@B`, tail `[0]`, far `[]`:

| j | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|--:|--:|--:|--:|--:|--:|--:|--:|
| interior lap | 6 | 12 | 20 | 30 | 42 | 56 | 72 | 90 |
| head reversals | 3 | 5 | 7 | 9 | 11 | 13 | 15 | 17 |

Reversals `= 2j+1`, so `j` bounces per carry, and the lap is exactly
`(j+1)(j+2)`. Quadratic — which is why the lap language (cost `a*j+b`) can
never express it, and why `no interior chain` on a QUAD row is not a missing
step. That read generalises: 28 of the 51 `no interior chain` rows are
HIGHER/EXP/QUAD and belong to the QUAD or bouncer routes.
