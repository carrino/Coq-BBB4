# S010: a nine-phase supported word cycle

This isolated package proves `NonHalt` and `QHBound 0` for the exact frozen
S010 table:

```text
1LB0LB1RB2LA_3RB3RA1RA0LA
```

The complete code vector is `[5;1;7;8;15;14;6;0]`. Native controls and the
proof runner verify the exact frozen row and vector. The Coq wrapper
separately proves complete-table equality, the state bound for every
completion, and an exact census inventory.

Let `P=3311331`, written nearest-first. The selected `s10_main n` has A
scanning 0, left word `P^n 33`, and five explicit blank cells on the right.
The actual blank tape reaches `s10_main 8` in exactly 2079 steps. Its
universal return is:

```coq
forall n,
 csteps s10_tm (448*n+2076) (s10_main n) =
 Some (s10_main (n+8)).
```

The core proves the stronger version preserving an arbitrary right suffix
after those five blank cells. Positive returns give arbitrarily late A
visits; their following step visits B. Totality proves nonhalting, and
recurrence of both states proves `QHBound 0`.

The explicit blank padding matters for exact CTape equality. The nine
phases place the head at different positions within the same six-cell
right boundary. Phase 5 reaches its rightmost position, while phase 8 is
six cells to its left. The proof retains those cells rather than silently
trimming trailing zeroes. The 2079-step entry directly matches this padded
representation.

The main crossing gate starts B on the nearest cell of the nonempty finite
left word `P^n33`, with arbitrary right context r. In `16n+6` steps it
returns B scanning 0, with left word `1 P^n33` and the same right context r.
A second gate starts A on that left word and in `16n+7` steps reaches A
reading the first cell of r, with left word `11 P^n33`.

The B gate factors into a nine-step left scan per P word, a six-step turn
at the terminal 33 wall, and a seven-step right scan per emitted word. The
left scan emits `E=0220120`; the right scan builds `V=1331133`. The word
identity `V^n 1 = 1 P^n` restores the original P word. Both scans are proved
by induction for arbitrary tape contexts. The A gate has a checked
seven-step wall case, and a nine-step program plus the B gate and an
eight-step finish for each nonzero word count.

Write `C_i(n,r)` for A scanning 0 with left word `F_i P^n33` and right word
`0^k r`. The fixed phase data and universal transitions are:

| i | F_i | k | Destination | Steps |
| --- | --- | --- | --- | --- |
| 0 | empty | 5 | `C_1(n,r)` | `16n+9` |
| 1 | 331 | 4 | `C_2(n+1,r)` | `32n+33` |
| 2 | 3 | 3 | `C_3(n,r)` | `32n+25` |
| 3 | 333331 | 2 | `C_4(n,r)` | `16n+21` |
| 4 | 331111331 | 1 | `C_5(n+2,r)` | `80n+165` |
| 5 | 333111 | 0 | `C_6(n+4,r)` | `240n+707` |
| 6 | 1133331 | 1 | `C_7(n,r)` | `16n+21` |
| 7 | 111331 | 4 | `C_8(n,r)` | 6 |
| 8 | 3331 | 6 | `C_0(n+1,r)` | `16n+17` |

Every row holds for every natural n and every suffix r. Their composition
adds eight P words and costs `448n+2076`. Each phase is a finite composition
of the supported gates and short context programs. The gate counts are
`[1,2,2,1,5,15,1,0,1]`; phase 2 uses one A gate, and all other gates are B
gates. The 37 finite programs are universally quantified over the unread
left and right contexts and checked by ordinary Coq reduction. They do not
assume finite native traces establish an unbounded scan.

The 23 Coq regressions cover actual blank entry, zero and nonmultiple word
counts, arbitrary outer context, both gates including wall cases, both
scans, the long five- and fifteen-gate phases, late phase boundaries,
missing-wall failure, and exact A3/B3 target states. Concrete fixtures use
checked VM computation; the universal gates, phase composition, and
recurrence are separately proved in the core.

Reproduce from the repository root with Coq 8.18 available on `PATH`:

```sh
python3 four/tools/check_burn26_s010_crossing_native.py --check
python3 four/tools/check_burn26_s010_crossing.py
```

The 27,409 native controls independently replay all finite programs in
short arbitrary contexts, both scan inductions' finite instances, both
gates, all nine phases, complete cycles, actual blank entry, and negative
wall/table controls. The pinned programs JSON records the finite program
boundaries. Cost metadata is derived from the tested native functions and
checked against the Coq phase formulas by the proof runner. Native data
supplies no proof credit.

The runner pins the frozen checkpoint, native report, program data,
templates, complete source closure, and generated objects. It compiles the
core, regressions, exact-table wrapper, all-completion board, and exact
inventory, then performs a fresh recursive kernel audit including the
regressions. Generated sources and objects remain under
`four/build/burn26-s010-crossing/proof`.

The only axiom reported for the core theorem is the repository's existing
functional extensionality axiom from finite-tape lifting. This package
claims one state family and no instruction family. Independent review and
tracker registration are separate; earlier accepted and frozen partial
packages remain unchanged.
