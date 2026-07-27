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

STAGE 0 IS DONE.  IT WAS RUN 2026-07-26/27; THE GATE CAME BACK ZERO.
Full write-up and reproduction commands: docs/MXDYS_INDUCTIVE_STAGE0.md.
Do NOT re-run it, and do NOT start Stage 1 below as written.

  What was built (both committed on the busycoq mirror, branch
  claude/coq-bbb4-residue-removal-lt5yac):
    * The oracle.  The dependency closure of Inductive_inf.v is FIFTEEN files
      and compiles in 35 s under stock `apt-get install coq` 8.18 -- the
      README's "~1 month" is for the whole repo and was never our cost.  It
      instantiates at BBinf (Q = Sym = N), so BB42.v / Individual42.v are NOT
      needed for measurement, and TM'_from_str parses bbchallenge notation
      with `---` as halt.
    * verify/InductiveDump.v -- prints the rule chain, the states carried by
      every config_expr, and which count-language constructors the proof used.
      Also separates "step budget exhausted" from "search failed", which the
      stock binary prints identically as "failed to decide".

  HARNESS VALIDATED: 60 machines lifted out of mxdys' own Indv1.v come back
  60/60 `nonhalting` at his exact settings (default_config, T=100000).
  Negatives below are real negatives.

  (ii) IS ZERO, AND IT IS ZERO STRUCTURALLY.  On those 60 machines -- ones his
  decider DECIDES -- the rule chain's config_expr endpoints carry 1 or 2
  distinct states, never more, on SIX-state machines.  This is not tuning:
     check_nonhalt x = match x with
       | ([],[multistep_lb_expr s1 s2 (nat_var v1)]) => s1 == (0inf,0inf,q0,R)
  is the ONLY accepted certificate shape -- one proposition naming exactly two
  configurations.  It cannot mention more.  Our collector also swept every
  subordinate layer and still found <= 2.  So `vis_via_ovf`-style "read the
  visit witnesses off the rule endpoints" (MXDYS_DECIDERS_PLAN section 1b)
  CANNOT WORK.  The exact forward model is real -- mxdys is right that his
  decider only wins when it models the behaviour exactly -- but the
  certificate it EMITS is a lossy projection of that model, keeping only what
  ~halts needs.  The state-visit information exists during the search and is
  discarded at emission time.

  (i) The hint-free black box decides ~none of the residue: 0/30 on the head
  sample, and more budget is not the lever (maxT 5e6, 50x, finishes in 142 s
  and still returns budget-exhausted).  A full-population run is in
  scratch as full_i.tsv if it matters; it does not change the gate, because
  (ii) decides the gate on its own.

  (iii) The count language IS exercised and IS observable: a hinted counter
  cert reports flags = nat_mul + nat_powsum + a counter-side tape
  constructor.  Section 1c of the plan survives intact.

  WHY THE BLACK BOX WAS ALWAYS THE WRONG HALF OF THE TOOL.  mxdys' counter
  certs are HUMAN-HINTED, not searched: IndSBCv1.v passes a hand-built
  config_SBC in 106 of 107 lemmas, IndBECv1.v a config_BEC in 100 of 122.
  The ~6,400 hint-free lemmas (Indv1-7, IndBGAS, HLv1/2) are other shapes.
  Our residue is counters.  The hint is an `ExtraRules` -- seven constructors
  of counter increment/decrement rules stated as -[tm]->+ progress facts over
  (d0, d1, d1a, qL, qR, QL, QR).  THAT IS OUR ANCHOR FAMILY PLUS LAP
  CERTIFICATE IN HIS NOTATION, and our inferred alphabets map onto it
  exactly: alphabet_infer.py's (A,B,C) IS his (d0,d1,d1a), and his
  `const s0 <* d1a` clause IS our overflow-at-the-blank-far-side lap.
  InductiveDump.v now has --bec/--becpos/--dec/--ov0/--ov1 to drive it;
  validated by reproducing IndSBCv1.v nonhalt3 (hint-free: budget-exhausted
  at 9.15 s; hinted: nonhalting in 0.067 s).  Note it still reports
  nstates=2 there -- even when you HAND it the anchor states, the emitted
  certificate names only two.

  THE GATE'S OWN ANSWER, THEREFORE: this is the middle branch -- the chains
  exist but their endpoints do not cover the states, so the work moves INSIDE
  a rule.  Bigger, still bounded, and it is OUR theorem, not theirs.  See
  "THE ONE THEOREM" below, which is now the top of the board.

  THE ONE THEOREM -- this is now the whole job, and it is ours.

  Both open fronts need the SAME missing fact, which is why it is the highest
  value single piece of work on the board:

     "this lap visits only states in S"

  Today wsteps_frame / cycL / cycR state their ENDPOINTS only.  Add a
  states-visited variant.  It is one theorem, not one per machine, same
  architecture as srun_sound.  It closes:
    * the 164 quasi-halters (ranked (1) below) -- that front has wanted
      exactly this since WAVE13 section 6; and
    * the liveness half of anything the rule engine gives us, since after
      Stage 0 we KNOW the liveness cannot come from rule endpoints.

  Do NOT build theories/Bridge/BusyCoqTM.v first.  Its one theorem
  (multistep_csteps : BC.multistep (tr_tm tm) n (tr a) (tr b) ->
  csteps tm n a = Some b) is still correct and still eventually wanted, but on
  its own it buys ZERO while (ii) is zero -- it would import chains whose
  endpoints name two states.  Bridge second, after the visits theorem exists
  to consume it.

  VENDORING IS DECIDED BY THE MEASUREMENT: keep their code OUT of tree, as a
  search ORACLE only.  Two independent reasons, both now established rather
  than assumed:
    * BBinf.v carries the tree's only two Admitted lemmas (all_qs_spec,
      all_syms_spec -- they cannot hold for an unbounded alphabet) and
      extraction warns about exactly these.  The generic-arity binary can
      never be load-bearing.  A real BB42 context (45 lines, pattern BB52.v)
      would be required for anything that is.
    * The ExtraRules the oracle uses are consumed WITHOUT proof --
      ExtraRules_WF is a separate obligation discharged per machine by step
      evaluation.  So every hint has to be re-proved on our side regardless,
      which is exactly the emit_lapcert.py board we already know how to make.

  THE PRODUCTIVE USE OF THEIR CODE, concretely:
    (a) As a DESIGN SPEC for extending LapDecider.  Our lap model is affine
        (docs/LAPDECIDER.md); the extension needed is `powsum k` plus one
        multiplication, on the OVERFLOW branch, with the far side pinned to
        `const s0` exactly as side_binary_Pos_inc_rule's second clause does.
        This is MXDYS_DECIDERS_PLAN section 5's fallback -- but now with a
        verified reference implementation to copy instead of a design to
        invent.  side_binary / side_binary_Pos / side_binary_dec / side_BL are
        the right tape constructors.
    (b) As an ORACLE for the counter families, driven by OUR alphabets:
        alphabet_infer.py -> (A,B,C) -> --becpos/--dec d0 d1 d1a, plus a small
        grid over qL/qR/QR.  Do not run the hint-free black box again; it is
        not the mode that decided the counter families in his own tree.

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
  * RRBA, at all, for this project.  Its verdict type is a bare bool
    (decide_loop2 : ... -> bool, spec yields ~halts tm c0) and its record
    structure is loop1_t := int*int*int*int -- four machine words, no state,
    no symbolic configuration.  There is nothing to read liveness off of EVEN
    ON A SUCCESS.  It also targets shift-recursive / sync bi-counter
    (Skelet10) shapes, not ours.  A session churned on it and got nothing;
    that is the expected outcome, not bad luck.  Same for RWLAcc
    (decide_nonhalt T : bool).  UBRRBA is halting-only by its own README.
    Inductive is the ONLY decider in that suite whose certificate carries a
    state at all, and it carries at most two.
  * Running mxdys' hint-FREE extracted decider over the residue hoping for
    boards.  Measured: 0/30 on the head sample, and his own counter certs do
    not use that mode either (IndSBCv1 106/107 and IndBECv1 100/122 are
    hand-hinted).  If you use their engine, drive it with hints.
  * Raising --maxT to force a decision.  50x (5e6) finishes in 142 s and still
    returns budget-exhausted.  T is not the binding constraint.
  * Expecting per-state visit witnesses from ANY certificate that tree emits.
    See the check_nonhalt shape above -- it is structurally two states.
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
