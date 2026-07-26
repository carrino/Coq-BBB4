# Next-session prompt — mxdys' deciders

_Rewritten 2026-07-26 at the end of wave-14 (branch
`claude/residue-reduction-4-2-5syxph`).  Wave-14 boarded 90, measured that the
overflow wall is EXPONENTIAL rather than a missing encoding, and — at the very
end — mxdys pointed John at his implementation, which turns out to carry
exactly the count language we are blocked on.  Full assessment and the staged
plan: `docs/MXDYS_DECIDERS_PLAN.md`.  Paste-ready below._

**Before pasting, check:** substitute the branch the session should develop on,
and name any files a concurrent session owns.

---

```
Continue the (4,2) residue reduction in carrino/Coq-BBB4, on a new branch off
main.

READ FIRST, in this order:
  docs/MXDYS_DECIDERS_PLAN.md -- THE TASK.  mxdys' Inductive/RRBA deciders,
                               what they do and do not give us, and a staged
                               plan with a measure-first decision gate.
  docs/WAVE14_FINDINGS.md   -- sections 2, 3 and 5b: what the overflow wall
                               actually is (EXPONENTIAL, measured three ways),
                               why wave-13's section 10c build is retired, and
                               why inferring the alphabet bought diagnosis
                               rather than boards.
  docs/LAPDECIDER.md        -- our checker's design, and why the model is
                               AFFINE in the carry index.  That affineness is
                               the binding constraint -- read it as a limit.
  docs/WHY_NO_HAMMER.md     -- why exactness is required at all, and why the
                               LIVENESS half is the hard half here.
  docs/CLOSEOUT_ROUTE_A.md  -- how boards become D_remaining shrinkage.

ENV: apt coq 8.18.0 -- `apt-get install -y coq`, then
`coqc -native-compiler no -Q theories BBB4 <file>`.  No opam bootstrap.  Build
a checker's dependency closure by coqdep-ordering its deps and compiling them
individually; `make all` pulls in the census.

mxdys' code is a PUBLIC repo, not one of this session's sources; add_repo
refuses cross-owner adds, so just clone it:
  git clone --depth 1 --branch BB6 https://github.com/ccz181078/busycoq.git
(that works through the agent proxy; it is ~55 MB).

NON-NEGOTIABLE: never touch theories/Census/; `python3 tools/census_cache.py
--check` must stay MATCH.  A board counts only when its file compiles and
`Print Assumptions` shows functional_extensionality_dep only (LapDecider and
LapCertGlue are axiom-FREE -- keep them that way).  Everything under tools/ is
UNTRUSTED; the kernel re-checks every board.

STATE: 3,980 of the frozen 5,156 settled (77.2%); D_remaining = 1,176.
The residue's failure profile, measured over all of it:
  532  no overflow chain   (the exponential wall)
  433  no interior chain
  164  no visit witness    (the quasi-halting bucket)
   47  no anchor family at all
Per-machine cost is a vm_compute:
  python3 tools/counters/emit_lapcert.py --list FILE --emit   (24 alphabets)
  python3 tools/counters/emit_graycert.py --list FILE --emit  (Gray)
After a wave, inventory.py + gen_stages.py + audit.py shrink D_remaining by
exactly what you boarded (the Closeout.vo compile needs the ~719-file board
.vo closure, ~85 min once).

THE TASK -- STAGE 0 FIRST, AND IT IS A GATE.

  Verified already (docs/MXDYS_DECIDERS_PLAN.md section 1, do not re-derive):
  their top-level theorem is `~halts` only and there is NO quasi-halting layer
  anywhere in that tree, so it does not answer our question directly.  But the
  model they build to prove it is exposed as first-class rules
  `multistep_expr (a b : config_expr) (n : nat_expr)` where config_expr
  carries its state Q, and the count language has nat_mul and
  powsum k x = ((k+2)^x - 1)/(k+1) -- a geometric sum.  powsum 0 = 2^x - 1.
  That is precisely our wall.  No Axiom, no Admitted; Coq 8.18; the framework
  is a functor and Individual52.v is 26 lines; their tape (Stream Sym) and
  ours (nat -> Sym) are isomorphic; verify/Extraction.v gives a native decider.

  STAGE 0 (hours, no Coq of ours):
    1. Write BB42 + Individual42.v (~30 lines, pattern on Individual52.v).
    2. Build the extracted OCaml decider.
    3. Run Inductive and RRBA over all 1,176 of
       tools/closeout/frozen_unproven.txt.
    4. Report THREE numbers:
       (i)   how many are decided ~halts at all;
       (ii)  of those, how many have a rule chain whose configurations cover
             ALL FOUR states -- for those, liveness is free and they are
             boards;
       (iii) how many need a nat_powsum / nat_mul rule (this cross-checks our
             own ovfshape.py buckets: 496 EXP2, 25 QUAD, 19 EXP4, 17 ~3^j).

  DECISION GATE on (ii).  Large -> do Stages 1-3, that is the wave.  Near zero
  but (i) large -> the chains exist but their endpoints do not cover the
  states; the work moves INSIDE a rule, which is bigger but still bounded --
  re-plan before building.  (i) small -> their search is tuned for BB(6)
  shapes; say so plainly and fall back to the nested lap below.

  STAGE 1 (1-2 days): theories/Bridge/BusyCoqTM.v -- Stream Sym <-> nat -> Sym,
  their config <-> our cconf, and
     multistep_csteps : BC.multistep (tr_tm tm) n (tr a) (tr b) ->
                        csteps tm n a = Some b.
  Axiom-free apart from the standing functional_extensionality_dep.  This is
  the only genuinely new mathematics and it is one theorem.

  STAGE 2 (2-3 days): theories/Bridge/RulesToLap.v --
     rules_to_never_qh : chain_valid -> chain_returns_shifted ->
                         states_covered = true -> NeverQuasiHaltsSt tm
  built on Stage 1 plus the existing glue_neverqh, and a glue_qh variant for
  the 164 quasi-halters.  ONE theorem, not one per machine -- same
  architecture as srun_sound.

  STAGE 3: emit one small .v per machine (TM table, rule chain as data, a
  vm_compute, the closing theorem), then the usual closeout.

  DECIDE WITH JOHN before vendoring: either bring their code in-tree, or keep
  it OUT of tree as a search ORACLE and re-prove each rule with our own
  checker extended by powsum counts.  The second keeps our axiom story and
  provenance simple; the first is less work.

IF STAGE 0 FAILS, the fallback is unchanged and section 1c of the plan still
paid for itself: it tells us the count language a nested LapDecider needs is
`a*j + b` extended by `powsum k` and one multiplication, and that
side_binary/side_binary_Pos/side_BL are the right tape constructors.  Build
that into LapDecider rather than inventing a design.

THEN, in ranked order (all independent of the above):

  (1) The 164 QUASI-HALTING machines (WAVE13 section 6).  John: "qh is fine, we
      just need to know it qh before 32M."  One of its two blockers is gone --
      mirrorize learned the QH closing shape (WAVE14 section 4.2).  The ones
      with StA targeted need ONE new fact: "the lap visits only states in S",
      which needs a states-visited variant of wsteps_frame / cycL / cycR
      (today they state only their ENDPOINTS).  One theorem, not one per
      machine.  NOTE: this is the same shape as Stage 2 above -- if you do the
      bridge, do these with it.

  (2) Two small localized leads (WAVE14 section 3):
      * 13 PARITY-AFFINE machines are IN model -- affine on each parity class
        of j (WAVE13 section 9b's two-pass carry).  They need the m=2 re-index
        (j = 2i+r, block unit u^2).  MEASURED: only 3 of the 13 derive both
        parity branches with the naive re-index, so this is worth ~3 boards,
        not 13.  Do not oversize it.
      * 8 machines whose EXP4-at-a-binary-anchor marks them as GRAY (11 of the
        19 EXP4 are exactly wave-14's Gray boards).  On
        0RB0LA_1LA1RC_0RD1RD_1LB0LB the Gp anchor family is present and closes
        affinely at 4j+8, yet all five symbolic branches fail in derive_chain.
        Ruled out: tail depth (a 4-way x,y peel does not help) and search
        budget (depth 24 / nmax 64 against a 12-step lap).  The lap opens by
        stepping RIGHT into blank tape, so the chain must start with SWinR --
        instrument _win_candidates on that configuration.

  (3) The 47 with NO anchor family at all.  alphabet_infer.py +
      gen_alphabet.py INFER a counter's word family from its own tape as a
      triple (A,B,C) and generate the Coq module; 18 families are wired.

  (4) The 27 genuine mxdys holdouts (tools/census_holdouts_kept.txt) -- the
      real endgame, and what John actually wants to be working on.

DO NOT RETRY (measured; grids in COUNTER_CLOSEOUT.md section 5, WAVE12 section
8, WAVE13 sections 4 and 8, WAVE14 section 7):
  * NGramHist/NGramCPS liveness over this residue at any (k,n,t); RepWL over
    the counter core; more per-machine lap emitters; ripple ulen widening.
  * Maximal-only window cuts in the chain search -- must be target-aware.
  * Reaching an anchor's syntactic form by rotations alone -- impossible in
    principle; the constant offset needs SFold.
  * Widening the ENCODING table hoping for boards.  Wave-14 INFERRED 18
    alphabets from the tapes (not guessed) and it bought 9 boards against 234
    machines decoded.  The alphabet has never been the binding constraint --
    but the inference is still worth running, for DIAGNOSIS.
  * Peeling the overflow block to fix the wall -- tried, 0 of 385.
  * enc_src/enc_dst from two ENCDATA rows to break the overflow wall (WAVE13
    section 10c).  The wall is the overflow's COST, not its target word.
  * A HEAD-RELATIVE frame decode as a test of a frame hypothesis:
    MB(m) ++ [S1] = [S1] ++ MA(m) identically, so the verdict is an artifact of
    head position.  Use absolute column parity (frame_probe.py, spacetime.py).
  * Believing a negative from an emitter run that RAISED.  A crash in
    emit_lapcert's reporting path cost 46 finished certificates and looked
    exactly like "the search finds nothing".  Survey with wall_survey.py,
    which keeps the best outcome per machine, before concluding anything.
  * (RETIRED) "mxdys' implementation is not available."  It IS -- that is this
    session's task.

ALSO: ovfshape.py measures cost-vs-j on BOTH branches and classifies
AFFINE / PARITY-AFFINE / QUAD / EXP2 / EXP3 / EXP4 / HIGHER.  Run it before
templating anything.  The interior version of that measurement was missing for
five waves and hid a quadratic family; the overflow version was missing for six
and hid the exponential one.

WHEN STUCK ON A CLASS: print a few machine strings WITH AN ABSOLUTE-COORDINATE
TAPE DUMP (tools/counters/spacetime.py) and ask John.  Hand-inspection is
22-for-22 across waves 8-14.  In wave-14 he corrected the frame measurement
(which turned out to BE the overflow mechanism) and read a blank-separated
counter off a tape that no recognizer could see, which became a seventh
alphabet and 24 boards.  ASK EARLY, ask with a TAPE, and ask about a CLASS not
a machine: cluster with wall_survey.py or alphabet_infer.py first so one
reading covers many machines.

DEFERRED TO STABLE HARDWARE: census fold-in (gen_proven.py + Deferred regen +
make census-verify + census_cache --update) -- batch once, it is the only step
that lowers D_census.  Also the champion 1RB1LD_1RC1RB_1LC1LA_0RC0RD (needs
`exists B, QHBound B` plus a 32.8M-step prefix) and the carry-shifted one-off
0RB1LC_1LC0LC_0RD1LA_1RD1RB.  The Closeout.vo COMPILE needs the ~719-file
board .vo closure (~85 min in a fresh container); inventory.py, gen_stages.py
and audit.py all run in minutes and produce the numbers above.

Commit + push per validated batch.  Name new files so they cannot clash with a
concurrent session's (waves 10-14 used ILS1_*/ILS4_*/ILS4F_*, ILS1M_*/ILS4M_*/
ILS4FM_*, IXP_*/IXPM_*, WLS_*/WLSM_*, WLJ_*, LAPC_*, LAPG_*, Alph_*).
```
