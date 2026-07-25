# Next-session prompt — continue the residue reduction

_Paste the block below into a fresh session.  It is deliberately self-contained:
it carries the environment facts, the first milestone with concrete machines, the
verification bar, and the measured do-not-retry list, so the next session does not
re-derive any of it.  Written 2026-07-25 at the end of the big-block-RepWL /
residue session (PR #29); the full reasoning behind every line is in
`docs/COUNTER_CLOSEOUT.md`._

**Before pasting, check two things:**

1. **Scope.** Step 1 writes into `theories/Machines/Counters/`.  A sibling session
   owned that directory plus `theories/Counters/ILC*` and
   `tools/counters/emit_*.py` during wave 8.  If it is still active, add a line to
   the prompt naming which files are theirs.
2. **Branch.** The prompt says "a new branch off main"; substitute the branch the
   session is supposed to develop on.

---

```
Continue the (4,2) residue reduction in carrino/Coq-BBB4, on a new branch off main
(PR #29 has merged; its work is in main).

READ FIRST: docs/COUNTER_CLOSEOUT.md — §10 is the ordered plan, §5b is why the
emitter currently boards almost nothing, §5 is the do-not-retry list, §3 is the
measured encoding zoo. Then docs/COUNTER_CODEGEN_BLOCKERS.md and
docs/MACHINE_NOTES_WAVE8.md (the human hand-inspection log).

ENV: apt coq 8.18.0 is sufficient — `apt-get install -y coq`, then
`coqc -native-compiler no -Q theories BBB4 <file>`. Do NOT spend 35 minutes on an
opam bootstrap; nothing here needs native_compute. Build a checker's dependency
closure by coqdep-ordering its deps and compiling them individually (Makefile's
`all` would pull in the census).

NON-NEGOTIABLE: never touch theories/Census/; `python3 tools/census_cache.py --check`
must stay MATCH. A board counts only when its file compiles and `Print Assumptions`
shows functional_extensionality_dep only. Everything under tools/ is UNTRUSTED —
the kernel re-checks every board, so a wrong constant fails to typecheck.

THE TASK (§10 step 1) — hand-author ONE counter board for lap shape 1, then clone it.

Lap shape 1 is `-CC|+CD|-DC|+CD` — 4 phases, 20-step lap, 31 machines, all with
enc=Jp, edge=C, tail=[0], p0=1. Members: tools/counter_lapshapes.tsv where
shape_rank == 1. Start with 1RB0RB_1LA1LC_1LB0RD_0LC1RD.

Clone theories/Machines/Counters/Interleave_TGT.v structurally, but with a FOUR-window
chain instead of six: one `wsteps ... = Some ...` unit lemma per traced phase, each
framed by its shape (plain run => wsteps_frame / wsteps_frame_l; repeated cycle =>
cycL / cycR), chained with csteps_chain across the two cview branches, then
glue_neverqh tm Cc p0 boot lap vis. Get the phase list from
`python3 tools/counters/lapshape.py`. Nothing in the kernel requires six windows —
that count lives only in emit_interleave.py's template string and its skeleton
search. cview (MonoCounter.v) and tovf are encoding-independent, and pair_rot is
generic in its symbols.

CHECKPOINT: one new counter board compiling with clean assumptions. That is the
milestone — do not build a generic emitter before one board of this shape exists by
hand, because the rep-algebra junctions for a non-6-window chain have never been
worked out.

THEN: (2) clone shape 1 across all 31 (anchor params already derived; encodings in
tools/counter_encodings.tsv); (3) shapes 2-4 = +82 machines (`+AB|-BA|+AB` 29,
`-DD|+DC|-CD|+DC` 28, `-DA|+AB` 25), then generalize to phase-generic, covering all
243 traceable machines; (4) then the 133 machines whose anchor needs a non-blank far
side (they hold the counter against a wall; glue_neverqh already accepts an arbitrary
Cc p, so zero new soundness surface), then the 306 needing more encodings. The 1,080
growth=R machines transfer via the mirror route.

DO NOT RETRY (each measured, grid recorded in §5): widening the emitter's anchor
search (tail cap 6->24, scan 200k->3M, nmax 60->240, floor 12->8) = 0 gain; adding
the Ip encoding alone = 0 new derives; ripple unit ulen (2,)->(2,1,3,4) = 0/85;
big-block RepWL over the 1,677 recognized counters = 0/1677; TCycler screen over the
same = 0/1677. The wall is the lap's SHAPE, not any constant.

ONE-OFF, LOWEST PRIORITY: 0RB1LC_1LC0LC_0RD1LA_1RD1RB is a carry-shifted counter
(§3) — D scans right filling 1s (writes 1 on both branches), so the carry's zero
lands one cell PAST the standard position and the digit frame advances per carry.
Its anchor must be Cc (p, k) carrying the frame offset k, not Cc p alone. One
machine; do it last.

OPTIONAL, ~15 MIN: resume tools/kcopy_classify.py over the remaining open machines
(it covered 1,323 of 2,713 and is resumable, skipping completed ones) if a complete
encoding table is wanted. Purely diagnostic.

DEFERRED TO STABLE HARDWARE (not this container): folding boards into the proven tier
(gen_proven.py + Deferred regen + make census-verify + census_cache --update). This is
the only step that lowers D_census — batch it, don't pay it per wave. Also the
champion 1RB1LD_1RC1RB_1LC1LA_0RC0RD (needs `exists B, QHBound B` plus a
32.8M-step prefix).

WHEN STUCK ON A CLASS: print a few machine strings and ask the human. Hand-inspection
on bbchallenge out-diagnosed the automated analysis 7 times out of 7 last session, and
every "this lever is dead" verdict turned out to be a parameter artifact.

Commit + push per validated batch. Name new files so they cannot clash with a
concurrent session's (last session used RWL8_*/TCyc8_*).
```

---

## Why the first milestone is a hand-authored board, not a generic emitter

Three parameter widenings were tried on the emitter last session and each gained
**exactly zero** derives (§5).  The reason is structural: most laps have 2-4
phases while the emitted template is a fixed six-window chain, so no setting of
its constants can fit them (§5b).  The rep-algebra junctions for a non-six-window
chain have never been worked out in Coq — `Interleave_TGT.v` settled them for the
six-window shape only.  Hand-authoring one board of shape 1 produces a board
immediately **and** establishes those junctions empirically; generalising first
means guessing them inside a code generator, which is how the previous three
attempts failed.

## The scoreboard the next session inherits

| | |
|---|---|
| boards landed in PR #29 | 44 (36 `RWL8_*` RepWL, 8 `TCyc8_*` TCycler) |
| counter core | 2,480 = 1,738 recognized (658 L / 1,080 R) + 742 residue |
| counters boarded | 160 (61 `ILC_*` + 99 `ILCM_*`) |
| growth=L still to board | 597, of which 243 have a traceable lap over 52 shapes |
| residue machines with no diagnosed mechanism | **0** |
| `D_census` reduction so far | **none** — the 44 boards are Class-1 only (§10) |
