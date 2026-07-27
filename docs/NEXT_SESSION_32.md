# Next session: board double #32

_Written 2026-07-27 at the end of the holdout wave (branch
`claude/coq-bbb4-holdouts-proofs-pqgv89`, PR #42).  Six of the eleven live
holdouts landed; #32 is decoded down to nine step identities and is the
cheapest of the remaining five.  Everything below is measured, not guessed._

Paste the block.

---

```
Board double #32, `1RB1LD_1RC0RB_1LA0RC_0LD0LA`, in carrino/Coq-BBB4 on a new
branch off main.  It is the last (4,2) holdout whose proof is already fully
decoded -- the job is writing Coq against a measured table, not finding the
mathematics.

READ FIRST, in this order:
  docs/HOLDOUTS_MXDYS_SN.md  -- section 5b, "double #32".  The nine step
                                gadgets, the three rule assemblies with their
                                step counts, the anchor table, and the
                                abstract state + invariant for the closer.
                                This is the whole specification.
  theories/Machines/Counters/BCtr_28.v  -- the shape to copy.  Same skeleton:
                                gadgets as one-line reflexivity lemmas, two
                                sweep inductions, a rule composition, then a
                                LapGlue/wglue instance.  ~250 lines.
  theories/Counters/WaveCounter.v -- read `wglue_neverqh` only.  It takes an
                                ARBITRARY anchor type with a total successor
                                and a preserved invariant, which is why #32
                                needs no closed form for its anchor and no
                                new closer.

ENV: apt coq 8.18.0 (`apt-get install -y coq`), then
`coqc -native-compiler no -Q theories BBB4 <file>`.  Build the four
dependencies first (BBB4_Statement, CTape, Counters/WTape, Counters/
WaveCounter) -- about 10 s.  Do NOT run bare `make`: it pulls the census.

NON-NEGOTIABLE: never touch theories/Census/; `python3 tools/census_cache.py
--check` must stay MATCH.  A board counts only when its file compiles and
`Print Assumptions` shows functional_extensionality_dep only.  Everything
under tools/ is UNTRUSTED; the kernel re-checks every board.

THE SHAPE

  anchor:  (StA, ([], chd W, ctl W))   with  W = (001)^j ++ <block word>
           head on the leftmost visited cell, comb of j blocks `001`

  abstract state for wglue_neverqh:  (j, L) with L a block word
           [(a1,b1); (a2,b2); ...]  denoting  0^a1 1^b1 0^a2 1^b2 ...
           and an implicit blank tail

  successor:  (j, (1,m) :: (p,q) :: rest) -> (S j, norm ((1,4)::(m-4,2)::(p-2,q)::rest))
              (j, [(1,m)])               -> (S j, norm [(1,4); (m-4,2)])
           `norm` merges a zero-length 0-run into the previous 1-run; that is
           a DENOTATIONAL identity (wden ((a,b)::(0,c)::t) = wden ((a,b+c)::t)),
           so it costs one rewrite, not a normalisation theory.

  invariant:  L = (1,m) :: rest, m even and >= 4, every block of rest with
           both runs even and >= 2.  Checked against all four normalisation
           branches in section 5b.

ORDER OF WORK

  1. The nine gadgets, verbatim from the table.  Each is `Proof. reflexivity.
     Qed.`  Run `python3 tools/counters/gadgets32.py` first and keep it green
     -- it is the differential check for exactly these nine statements.
  2. Two sweep inductions: rc5 iterated (the 8j) and b1/d0 iterated (R1's 2m).
     Both are induction on the count with the tail universally quantified.
  3. The three rule lemmas R1/R2/R3, composing gadgets by csteps_add.  Their
     step counts are 8j+2m+5, 8j+5, 8j+11 -- if your composition does not add
     up to those, the composition is wrong, not the count.
  4. The composed lap (R1;R2;R3), the wglue_neverqh instance, boot, visits.
  5. Corruption controls in theories/Tests/ (see CountersBCtr_Corruption.v for
     the tradition: the constants that are NOT free, plus one one-transition
     mutant that breaks a named gadget).
  6. Wire in: _CoqProject, tools/counters_manifest.tsv, then
       python3 tools/closeout/inventory.py
       python3 tools/closeout/gen_stages.py
       python3 tools/closeout/audit.py
       coq_makefile -f _CoqProject -o Makefile.coq
       make -f Makefile.coq -j2 theories/Closeout/Closeout.vo
     -j2, NOT -j4.  IRules_Batch_02 peaks around 6.3 GB and four of those in
     flight gets one OOM-killed; at -j2 the whole closure builds with memory
     flat at 1-2 GB.  Rebuild after a board is ~3 min because the other
     boards are already compiled.

DONE = `Print Assumptions nqh_1RB1LD_1RC0RB_1LA0RC_0LD0LA` is
functional_extensionality_dep only, audit OK, census_cache MATCH, and
D_remaining 1010 -> 1009.

FIVE TRAPS, ALL OF WHICH COST ME A WRONG LEMMA THIS WAVE

  1. Verify every lemma statement in Python against a CTape-FAITHFUL mirror
     before writing any Coq.  Not a loose simulator -- one that reproduces
     chd/ctl on empty lists.  tools/counters/probe32b.py is that mirror and
     gadgets32.py is the harness.  Two of the nine gadgets were wrong on
     first reading and the checker caught both.
  2. `change (csteps tm 1 X) with (Some Y)` leaves an unreduced `match Some Y
     with ...` and the next `rewrite` fails to find its subterm.  State a
     one-step lemma and `rewrite` it instead.  This bit me in three files.
  3. The right-sweep unit consumes [1;0;1;0] and leaves [1].  It LOOKS like
     "delete a 001 at position 3" in the raw traces; that reading is wrong
     and only agrees on the first iteration.
  4. `la2` consumes TWO cells from the left, not one -- same shape as lc3.
  5. Step counts hide off-by-ones in the carry.  In #28 a carried digit cost
     4, not 2, because the leftward walk lays debris that the rightward walk
     has to re-cross; the analogous piece here is the EXTRA rc5 before tn4 in
     R2, which is what makes 0^a -> 0^(a-3) rather than 0^(a-2).

WHY THIS IS CHEAP, AND WHAT NOT TO DO

  BBB models #32 as a comb counter with a Theta(m^2) quadratic bounce, and
  tools/counters/lap32.py sits on the a = 2^j-1 anchor that BBB's own notes
  record as having TIMED OUT.  Do not go back to either.  The macro lap is
  36k^2 + 29k - 4 steps and never has to be modelled: wglue_neverqh chains
  the MICRO laps, which are O(j) each, and the doubling of the macro anchor
  (k = 2^n) falls out as a consequence.  That is the same move that took
  blockdbl #11/#13/#28 and the two wrap machines off the board this wave --
  in every case BBB's macro anchor was the expensive reading and a finer
  phase made one sweep a complete lap.

AFTER #32, take wave4 #15 (1RB0RC_0LC1LB_0LD1LC_1RD0RA).  It is the mod-4
wave odometer; WaveCounter.v is the mod-2 closer and its header already names
#15 as a customer, so the port is the mod-4 arithmetic layer replacing
carry/nextf/fp/pbits/WInv/carry_ok (~80 lines) plus the per-machine lap.  No
new closer there either.  Section 5b sizes it and the remaining three.
```
