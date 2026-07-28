# Next-session prompt — tower #20 is the LAST (4,2) holdout, and it is ONE lemma

_Rewritten 2026-07-28 at the end of wave-20 (branch
`claude/board-tower-20-coq-t0578y`), which proved the MIDDLE of tower #20's
long lap and reduced the machine to a single open invariant.  Full write-up:
`NEXT_SESSION.md` section 2k; the reconnaissance itself is the docstring of
`tools/counters/inv20.py`._

_**Correction to the previous revision of this file.**  The wave-18 RESIDUE
prompt said "THE HOLDOUTS ARE DONE -- the (4,2) holdout list CLOSED on
2026-07-27 (wave4 #15, fractal #3/#5, tower #20)".  Three of those four are
right.  **Tower #20 was never boarded.**  It has no `NeverQuasiHaltsSt`
theorem, no row in `tools/counters_manifest.tsv`, and it is still line 622 —
the last line — of `tools/closeout/frozen_unproven.txt`.  The (4,2) holdout
list is NOT closed; it has exactly one machine left.  `D_remaining` is 622,
and #20 is one of the 622._

_Two tasks are live and they are disjoint.  **This file is the #20 task.**  The
residue task — the other 621 machines — is unchanged and its prompt is the
previous revision of this file: `git show 02fd80b:docs/NEXT_SESSION_PROMPT.md`.
Everything in it about the residue still stands; only its holdout status line
is wrong, in the way described above._

**Before pasting, check:** substitute the branch the session should develop on,
and name any files a concurrent residue session owns.

---

```
Close tower #20 in carrino/Coq-BBB4, on a new branch off main.  It is the LAST
(4,2) holdout and the whole machine is proved except one invariant.

  1RB0RD_1LC1LB_1RA0LB_1LC1RA

STATUS, precisely.  #20 is NOT boarded.  No NeverQuasiHaltsSt theorem, no row
in tools/counters_manifest.tsv, still line 622 of
tools/closeout/frozen_unproven.txt.  Boarding it takes D_remaining 622 -> 621
and CLOSES the (4,2) holdout list.  Do not write, anywhere, that #20 is closed
until `Print Assumptions` on its NeverQuasiHaltsSt says so.

READ FIRST, in this order:
  theories/Machines/Counters/Tower_20.v -- the header comment is the machine's
                               whole story: the b=110 / a=10 alphabet, the
                               A/B alternation, the four phases of the long
                               lap, and the "WHAT IS AND IS NOT PROVED"
                               paragraph.  Read it before any code.
  tools/counters/inv20.py   -- the docstring IS the reconnaissance on the open
                               problem: 5 established facts, 7 refuted
                               candidates with witnesses.  Run it (`python3
                               inv20.py`, ~1 min).  Everything it prints is
                               checked, not conjectured.
  NEXT_SESSION.md 2k        -- the same material plus the three traps this
                               wave added.  Section 2i is the wave before it
                               (assembly, the closed-form successor).

ENV: apt coq 8.18.0 -- `apt-get install -y coq`, then
`coqc -native-compiler no -Q theories BBB4 <file>`.  No opam bootstrap.
The #20 closure is five files and about a minute:
  BBB4_Statement, CTape, Counters/WTape, Counters/WaveCounter,
  Machines/Counters/Tower_20.v
Do NOT run `make all` -- it pulls in the census.

NON-NEGOTIABLE: never touch theories/Census/; `python3 tools/census_cache.py
--check` must stay MATCH.  A board counts only when the file compiles and
`Print Assumptions` is clean (Tower_20.v is functional_extensionality_dep only
-- keep it that way).  Everything under tools/ is UNTRUSTED; the kernel
re-checks every board.  And the rule this machine has punished twice: CHECK
EVERY GADGET EXHAUSTIVELY, in the exact form you will state it in Coq, over
all 961 (L,R) with |L|,|R| <= 4, BEFORE writing the Coq.  A sampled check is
not a check -- wave4 #15's deposit passed a 42-context sample and failed 496
of the 961.  lap20.py / mid20.py are the harness; copy their shape.

WHAT IS ALREADY PROVED -- the whole long lap, for every tail with an odd entry:

    lapB_full_ne : Forall (fun x => x <> 0) K ->
      csteps tm_20 ((10 + 5*r) + ((rcostK K + (2*k+8))
                    + (pcost (Dmid K k) + rcost (lay r E))))
        (CfB (r, wruns (wev K ((2*k+1) :: S n2 :: t2))))
      = Some (CfA (S r, enc (Dmid K k) (wruns ((S n2 + 3) :: t2))))

plus lapB_full_z for the nothing-beyond branch.  `wev K t` is the word whose
even prefix is 2k for each k in K, so the hypothesis IS the decomposition
"(even prefix) ++ (odd entry) ++ (rest)" -- i.e. exactly the condition that
the sweep TURNS.  ruleA (A -> B, 10 steps, uniform in the tail) and boot20_W
are proved.  The abstract successor nv is in closed form (nv20.py) and
validated against the simulator on every anchor reachable in 400,000 steps
(asm20.py).

THE ONE OPEN THING.  An all-even word sends the sweep rightward for ever, so
the lap needs "the word has an odd entry".  That is TRUE on the orbit and
FALSE as a closure property of nv on arbitrary words (nv [5;1] = [2;1;1;4] ->
[2;2;4;4], all even).  What is missing is an invariant that holds at the boot,
is preserved by nv, and implies hasodd.  Nothing else.

FIVE THINGS THAT ARE ESTABLISHED -- use them, do not re-derive them:
 1. THE ALPHABET IS FINITE.  Every entry of every reachable word is in
    {1,2,4,5,8} (7 occurs once, at lap 1, never again).  1 and 2 are FRESH,
    laid by the return sweep; 4=1+3, 5=2+3, 8=5+3 are BUMPED, and an entry is
    bumped at most twice (1->4, 2->5->8).  Alphabet closure is exactly "the
    entry just after the first odd is in {1,2,5}".
 2. THE LEADING 2-RUN IS THE LAP INDEX.  nv (2^r ++ v) = 2^(r+1) ++ nv0 v, so
    the abstract dynamics is v |-> nv0 v and aliveness does not depend on r.
 3. POOR IS A 2-LAP INVARIANT.  Call 2^a ++ [1] ++ t POOR.  A POOR word's
    image has an odd IFF Cond(t) = hasodd(X t), and two laps later the word is
    POOR again with tail T([]) = [], T(1::u) = 2 :: nv0 u,
    T(2::u) = 1 :: nv0 (1::u).  One map, one obligation.
 4. THE ENGINE -- the real handhold.  With E(u) = "last entry odd" and
    B(u) = "the first odd sits at |u|-2",

        E(u) /\ ~B(u)  ==>  E(nv0 u)

    (200,000 random words, 9-letter alphabet).  So "E and never-B" SUFFICES,
    and the obligation drops from the semantic "hasodd for ever" to the
    SYNTACTIC "never B" -- a condition on ONE position.
 5. THE SYSTEM IS SELF-SIMILAR, which is why every natural candidate fails.
    The phase is 4-periodic in r -- [1;1]++U, [4]++U, [1;2]++S, [5]++S with
    S = nv0 U -- and

        U_{k+1} = X(nv0 U_k),   and with U = 4::x,   U_{k+1} = 4 :: nv x.

    FOUR LAPS AT ONE LEVEL ARE ONE LAP ONE LEVEL DOWN, and hasodd at the
    r = 3 mod 4 phase is exactly hasodd of the level-below word.  The
    obligation reproduces itself.

WHERE TO GO, in order.
 1. ANCHOR AT LEVEL 1, not level 0.  The level-1 orbit is visibly better
    behaved: over 3000 laps it always ends [2;1] and its d is never 1 or 2
    (level 0 ends [2;1]/[5;1]/[8;1] and does hit d = 2).  The candidate
    "ends [2;1] /\ d not in {1,2}" survives 2000 laps there and fails closure
    ONLY on words the orbit does not reach.  Closing that reachability gap IS
    the problem, but it is much the smaller formulation.
 2. THE SHAPE MUST BE RECURSIVE, because of (5).  What fits a self-similar
    system is a predicate defined by well-founded recursion on the DESCENT
    (level k to level k+1), or a CoInductive safety predicate discharged by a
    productive cofix -- four laps of finite obligations per level, then the
    next level.  Either way, what you need is an invariant for the DESCENT
    MAP, not for nv.
 3. ONLY THEN, the boarding chores (all mechanical, half a day):
    wglue_neverqh at the level-1 boot -- recompute t0, boot20_W's vm_compute
    pattern works at any t; corruption controls in theories/Tests/ in
    CountersW15_Corruption.v's tradition; tools/counters_manifest.tsv;
    gen_stages.py; tools/closeout/audit.py; then
    `make -f Makefile.coq -j2 theories/Closeout/Closeout.vo` (-j2, NOT -j4).
    Finally drop #20 from frozen_unproven.txt and fix every "the holdout list
    is closed" line in NEXT_SESSION.md and this file -- at that point they
    become true.

DO NOT RETRY.  Every candidate below was refuted by EXHAUSTIVE closure
checking over the 5-letter alphabet to length 8 plus tens of thousands of
random words -- never by sampling the orbit.  inv20.py re-runs all of them; if
one ever comes back NOT REFUTED it is the invariant and the file is stale.

    contains an odd                       nv [5;1] = [2;1;1;4] -> [2;2;4;4]
    ends in 1                             nv [1;1] = [2;4]
    ends in 1, first odd not at |w|-2     nv [1;2;1] = [2;5;1]
    the Scan/After DFA (every odd's
      successor in {1,2,5})               nv [4;1] = [2;1;2;2;1]; it also
                                          REJECTS the reachable lap-3 word
                                          [2;2;2;4;1;2;1] outright
    alphabet & (rich | >= 2 odds)         nv [5;1] = [2;1;1;4]
    ends [2;1] & first odd not at |w|-3   nv [1;2;2;1] = [2;5;2;1]
    ends [2;1], d not in {1,2}, plus the
      POOR/odd-head refinements (C3,C4)   nv [5;2;2;1] = [2;1;1;5;2;1]

(d(x) = the number of entries after the first odd.)  ALSO do not look for a
regular/DFA invariant or a bounded-depth one: (5) rules out both as a class,
and the deepest death over the 5-letter alphabet at |v| <= 5 is 111 laps, so
no depth cutoff you pick will be safe.

TRAPS (this machine's, earned):
 1. The turn's bounce is at 2k+4, NOT 2k+3 -- cross5 (5 steps for k=0) is the
    bounce PLUS one StB step.  mid20.py diffs the cost as well as the config
    for exactly this reason.
 2. dbl 0 [S1] = [S1] is not RevP.  A ride over an EMPTY run breaks the return
    sweep's decode, so Forall (fun x => x <> 0) K is a real hypothesis, not
    bookkeeping -- it is this family's version of the side condition
    WaveCounter carries.
 3. State lap costs RIGHT-NESTED (a + (b + c)), not (a + b) + c.  csteps_add
    peels one + at a time and left-nesting lands the first rewrite on the
    wrong split.
 4. Gadgets that READ the context must be stated through chd/ctl, not by
    matching on the list.

WHEN STUCK: dump the orbit in absolute coordinates (tools/counters/spacetime.py)
and ASK JOHN, with the tape.  Hand-inspection is 22-for-22 across waves 8-14,
and it is what produced this machine's alphabet reading in the first place.
Ask about the SHAPE of the invariant, not about a single word.

CI NOTE, so you do not spend an hour on it: ci.yml on main is red and has been
since 2026-07-26, on every run.  It is not a proof failure -- the runner is
killed ~9 min into `make -j4` (no Coq error, only abstract-large-number
warnings, then "The runner has received a shutdown signal").  The workflow
uses `make -j4` over the whole tree while this repo's own playbook says -j2,
and PR #47 added ~300 heavy files.  Diagnosed in carrino/Coq-BBB4#48; fixing
it is a main concern, not yours unless John asks.

Commit + push per validated batch.  Name new files so they cannot clash with a
concurrent residue session's (waves 10-18 used ILS1_*/ILS4_*/ILS4F_*,
ILS1M_*/ILS4M_*/ILS4FM_*, IXP_*/IXPM_*, WLS_*/WLSM_*, WLJ_*, LAPC_*, LAPG_*,
NLAP_*, Alph_*).
```
