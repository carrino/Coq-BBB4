# Next-session prompt — continue the residue reduction (post-wave-10)

_Rewritten 2026-07-25 at the end of the shape-template session (branch
`claude/residue-reduction-4-2-07rtlv`).  That session executed
`COUNTER_CLOSEOUT.md` §10 steps 1–3 and harvested every AFFINE traceable
machine; the full record is `docs/WAVE10_SHAPES.md`.  The prompt below is
paste-ready for a fresh session._

**Before pasting, check two things:**

1. **Scope.**  This writes into `theories/Machines/Counters/` and
   `tools/counters/`.  If a sibling session owns them, name its files.
2. **Branch.**  Substitute whatever branch the session should develop on.

---

```
Continue the (4,2) residue reduction in carrino/Coq-BBB4 (branch off main if
wave-10 has merged; else off claude/residue-reduction-4-2-07rtlv).

READ FIRST: docs/WAVE10_SHAPES.md -- what is boarded and what the remaining
wall is; docs/COUNTER_CLOSEOUT.md section 5 -- the measured do-not-retry
list; docs/WAVE9_FINDINGS.md section 3 -- the orientation cube.

ENV: apt coq 8.18.0 -- `apt-get install -y coq`, then
`coqc -native-compiler no -Q theories BBB4 <file>`.  No opam.  Build a
checker's dependency closure by coqdep-ordering its deps; never `make all`.

NON-NEGOTIABLE: never touch theories/Census/; `python3 tools/census_cache.py
--check` must stay MATCH.  A board counts only when its file compiles and
`Print Assumptions` shows functional_extensionality_dep only.  tools/ is
UNTRUSTED; the kernel re-checks every board.

STATE: 309 wave-10/11 boards (ILS1_*/ILS4_*/ILS4F_* direct; ILS1M_*/
ILS4M_*/ILS4FM_* mirror via Mirror.mirror_never_qh; wall anchors via
derive_tail_far).  Emitters: tools/counters/emit_shape1.py and
emit_shape4.py (--flip auto, --mirror); each derives windows by exact
symbolic replay, validates differentially on both cview branches, compiles,
checks assumptions, deletes on failure.  Of the frozen 5,156 deferred,
~1,598 machines remain unproven (docs/WAVE11_MIRROR.md section 5); the
route-A closeout (Assembly.v boarded app-chain vs the FROZEN list, NO
census walk) is the finish line and is container-safe.

THE TASK -- the EXPONENTIAL-OVERFLOW family (~70-90 machines, the largest
residue block with a diagnosed mechanism).  Their interior laps are affine
and template-shaped, but the overflow 2^k-1 -> 2^k costs ~c*2^k: the
all-ones tape is rewritten to 101010... by repeated sweeps.  A finite
window chain cannot express it; glue_neverqh does not care -- it needs one
existential csteps witness per lap, which an INNER induction provides:

  1. Hand-author ONE board: machine 1RB1LA_0LA1RC_0LD0RB_0LA1RD (shape
     +AB|-BA|+AB, overflow cost 10*2^j'+4j'+4).  MEASURED (WAVE11 section
     3): the overflow IS an inner interleaved counter -- the (A, blank-head)
     snapshots inside the p=15->16 lap count 11010101 -> 11010111 ->
     11011101 -> ... -> 11111111 with the same anchor discipline.  So:
     define the inner anchor family Ci, prove inner laps with the SAME
     cview/window lemmas, compose by the same well-founded induction, and
     plug the composite in as the outer overflow's existential witness.
     The interior chain is the ILS4F flip template verbatim.
  2. Clone across the family (the members are the 'laps not affine'
     failures of emit_shape4.py over tools/counter_lapshapes.tsv machines).

CHECKPOINT: one exponential-overflow board with clean assumptions before
any emitter work -- the inner-induction junctions have never been written.

THEN, in order of measured size (mirror + wall-anchor + NOFIT harvests
are DONE for everything the current skeletons fit -- WAVE11 section 5):
  (3) the wall-LAP skeletons (~300 L+R): far anchors now derive
      (derive_tail_far) but the laps bounce off the wall with window
      chains the affine templates lack -- derive their shapes by replay,
      extend the skeleton search;
  (4) the B-row-1RB overflow-return stragglers (6) + the flip third-close
      variant (8): second RET/FIN pair per branch -- mechanical;
  (5) far-thread emit_shape4.py (Ip side) the way emit_shape1 was done,
      and re-sweep the pools; wire emit_kp.py emission (Kp, ~33+ machines);
  (6) the 318 non-core unproven: one triage pass (fingerprint + lapshape),
      then route by family.

DO NOT RETRY (measured, grids in COUNTER_CLOSEOUT.md section 5): emitter
anchor-search widenings; Ip-encoding-alone; ripple ulen widening; big-block
RepWL and TCycler over the recognized counters.  ALSO measured in wave 10:
the lapshape signature does NOT gate templates (one template per
encoding-side covers every affine shape) and affine-vs-exponential overflow
splits WITHIN shapes, member by member -- always profile the overflow
branch before assuming a member fits.

DEFERRED TO STABLE HARDWARE: folding boards into the proven tier
(gen_proven.py + Deferred regen + make census-verify + census_cache
--update) -- batch it once, it is the only step that lowers D_census.  Also
the champion 1RB1LD_1RC1RB_1LC1LA_0RC0RD (needs `exists B, QHBound B` plus
a 32.8M-step prefix) and the carry-shifted one-off
0RB1LC_1LC0LC_0RD1LA_1RD1RB (anchor Cc (p, k) with a frame offset).

WHEN STUCK ON A CLASS: print a few machine strings and ask the human.
Hand-inspection is 11-for-11 across waves 8-9.

Commit + push per validated batch.  Name new files so they cannot clash
with a concurrent session's (wave 10 used ILS1_*/ILS4_*/ILS4F_*).
```
