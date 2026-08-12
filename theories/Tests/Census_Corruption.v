(** * Tests/Census_Corruption: negative controls for the census pipeline.

    Every census checker must REJECT tampered parameters, and the
    pipeline must classify known machines correctly.  All checks are
    closed by [vm_compute]; a regression here means a checker was
    weakened. *)

From Coq Require Import Arith Bool List.
From BBB4 Require Import BBB4_Statement.
From BBB4.Checkers Require Import NGram.
From BBB4.Census Require Import TNF_QH Decide Deferred_Defs RankSearch
  RepWLSearch.
Import ListNotations.

Definition T (w : Sym) (d : Dir) (n : St) := Some (mkTrans w d n).
Definition mk8 (a0 a1 b0 b1 c0 c1 d0 d1 : option Trans) : TM :=
  fun q s => match q, s with
  | StA, S0 => a0 | StA, S1 => a1 | StB, S0 => b0 | StB, S1 => b1
  | StC, S0 => c0 | StC, S1 => c1 | StD, S0 => d0 | StD, S1 => d1 end.

(** the 0RA blank-tape spinner: an in-place cycle at (0, 1) *)
Definition spin0 : TM := mk8 (T S0 DR StA) None None None None None None None.

(** the 1RA right runner: a translated cycle, anchor 1 period 1 *)
Definition run1 : TM := mk8 (T S1 DR StA) None None None None None None None.

(** A -> B, then B spins: quasihalts (state A quiet after index 0) *)
Definition qh1 : TM :=
  mk8 (T S1 DR StB) None (T S0 DR StB) (T S0 DR StB) None None None None.

(** ** In-place cycle checker *)

(* the genuine parameters pass *)
Example cycle_ok : cycle_leaf_check spin0 0 1 = true.
Proof. vm_compute. reflexivity. Qed.

(* zero period must fail *)
Example cycle_zero_p : cycle_leaf_check spin0 0 0 = false.
Proof. vm_compute. reflexivity. Qed.

(* a non-cycling machine must fail at any offset *)
Example cycle_not_cyclic : cycle_leaf_check run1 3 5 = false.
Proof. vm_compute. reflexivity. Qed.

(* the halting root must fail (no configuration at n1 + p) *)
Example cycle_halts : cycle_leaf_check (fun _ _ => None) 0 1 = false.
Proof. vm_compute. reflexivity. Qed.

(** ** Translated-cycle checker *)

(* the genuine parameters pass *)
Example tc_ok : tcycler_leaf_check run1 1 1 0 = true.
Proof. vm_compute. reflexivity. Qed.

(* retargeted period must fail: the lap ends in the wrong state on a
   two-state alternator *)
Definition alt2 : TM :=
  mk8 (T S1 DR StB) None (T S1 DR StA) None None None None None.
Example tc_wrong_period : tcycler_leaf_check alt2 1 1 0 = false.
Proof. vm_compute. reflexivity. Qed.

(* the in-place spinner is not a translated cycle in guarded form with
   a displaced window: wrong window must not crash, only fail or pass
   soundly -- here period 1 passes at W = 0 because the relative
   configuration genuinely recurs; tampering the anchor into the
   pre-write configuration of qh1 must fail (state mismatch) *)
Example tc_wrong_anchor : tcycler_leaf_check qh1 0 1 0 = false.
Proof. vm_compute. reflexivity. Qed.

(** ** The n-gram tier must NOT claim a quasihalting machine *)

Example ngram_rejects_qh : ngram_check_neverqh qh1 2 100 10000 64 = false.
Proof. vm_compute. reflexivity. Qed.

Example ngram_rejects_halting :
  ngram_check_neverqh (fun _ _ => None) 2 10 1000 16 = false.
Proof. vm_compute. reflexivity. Qed.

(** ** Deferred lookup: only listed machines answer *)

Example deferred_miss :
  deferred_lookup (dmap_of [spin0]) run1 = false.
Proof. vm_compute. reflexivity. Qed.

Example deferred_hit :
  deferred_lookup (dmap_of [spin0; run1]) run1 = true.
Proof. vm_compute. reflexivity. Qed.

(** ** row_to_tm decodes the bbchallenge slot order correctly *)

Example row_decode :
  tm_eqb (row_to_tm [T S1 DR StB; tN; T S0 DR StB; T S0 DR StB;
                     tN; tN; tN; tN]) qh1 = true.
Proof. vm_compute. reflexivity. Qed.

(** ** The rank tier

    [qh1] quasihalts (state A goes quiet after index 0), so the rank
    tier -- which proves NEVER-quasihalting -- must reject it: the
    checker requires liveness certificates for every prefix-visited
    state, exactly the premise a looser search could miss. *)

Example rank_rejects_qh : rank_tier qh1 3 4 10000 64 = false.
Proof. vm_compute. reflexivity. Qed.

Example rank_rejects_halting :
  rank_tier (fun _ _ => None) 3 0 1000 16 = false.
Proof. vm_compute. reflexivity. Qed.

(* a residue-class machine the ranking rules genuinely kill
   (validated against tools/bulk_prover.py) *)
Definition rankm : TM :=
  mk8 (T S1 DR StB) (T S0 DL StC) (T S0 DL StA) (T S0 DR StD)
      (T S1 DL StA) (T S1 DL StB) (T S1 DR StC) (T S1 DL StA).
Example rank_kills :
  rank_tier rankm 3 0 200000 512 = true.
Proof. vm_compute. reflexivity. Qed.

(** ** Pipeline classification on knowns *)

Definition rungs_t : list (nat * nat) := [(2, 100); (3, 200)].
Definition rrungs_t : list (nat * nat) := [(3, 0)].

Example pipe_halt :
  decide_easy 2000 130 1030 200000 512 rungs_t rrungs_t [] [] 0 32 (dmap_of [])
    (dmap_of []) (dmap_of []) (hmap_of [])
    (fun _ _ => None) = R_Halt StA S0.
Proof. vm_compute. reflexivity. Qed.

Example pipe_spin :
  decide_easy 2000 130 1030 200000 512 rungs_t rrungs_t [] [] 0 32 (dmap_of [])
    (dmap_of []) (dmap_of []) (hmap_of [])
    spin0 = R_Leaf.
Proof. vm_compute. reflexivity. Qed.

Example pipe_runner :
  decide_easy 2000 130 1030 200000 512 rungs_t rrungs_t [] [] 0 32 (dmap_of [])
    (dmap_of []) (dmap_of []) (hmap_of [])
    run1 = R_Leaf.
Proof. vm_compute. reflexivity. Qed.

Example pipe_qh_leaf :
  decide_easy 2000 130 1030 200000 512 rungs_t rrungs_t [] [] 0 32 (dmap_of [])
    (dmap_of []) (dmap_of []) (hmap_of [])
    qh1 = R_Leaf.
Proof. vm_compute. reflexivity. Qed.

(** ** The wrapped-QHBound and RepWL tiers *)

(* 0RB---_0LC---_0LD1LC_1RC1LD: wrap-QH, plain acyclicity gate
   (tools/qhbound_caught.tsv row 1: quiet B, s=1, n=2, t=64) *)
Definition qhbm : TM :=
  mk8 (T S0 DR StB) None (T S0 DL StC) None
      (T S0 DL StD) (T S1 DL StC) (T S1 DR StC) (T S1 DL StD).

(* 0RB---_0LC---_1LD1RC_1RC1LD: wrap-QH, needs the lex gate
   (tools/qhbound_lex_caught.tsv row 1: quiet B, s=1, n=2, t=64) *)
Definition qlxm : TM :=
  mk8 (T S0 DR StB) None (T S0 DL StC) None
      (T S1 DL StD) (T S1 DR StC) (T S1 DR StC) (T S1 DL StD).

(* 0RB---_0LC0RD_1RD1LB_1RB1LA: never-QH residue-core machine the
   RepWL tier decides at (L,T,t) = (2,2,0)
   (tools/repwl_residue_caught.tsv) *)
Definition rwm : TM :=
  mk8 (T S0 DR StB) None (T S0 DL StC) (T S0 DR StD)
      (T S1 DR StD) (T S1 DL StB) (T S1 DR StB) (T S1 DL StA).

Definition qhb_rungs_t : list (nat * nat) := [(2, 64)].
Definition rw_rungs_t : list (nat * nat * nat) := [(2, 2, 0)].

(* the tiers catch their machines *)
Example qhb_catches : try_qhb 2000 200000 512 qhb_rungs_t qhbm = true.
Proof. vm_compute. reflexivity. Qed.

Example qhb_lex_catches : try_qhb 2000 200000 512 qhb_rungs_t qlxm = true.
Proof. vm_compute. reflexivity. Qed.

Example rw_catches : rw_tier rwm 2 2 0 200000 = true.
Proof. vm_compute. reflexivity. Qed.

(* a quasihalter must never pass the never-QH RepWL tier (small fuel:
   the abstraction diverges on it, so the closure is fuel-bounded) *)
Example rw_rejects_qh : rw_tier qhbm 2 2 0 2000 = false.
Proof. vm_compute. reflexivity. Qed.

(* a halting machine must fail the RepWL closure *)
Example rw_rejects_halt : rw_tier (fun _ _ => None) 2 2 0 2000 = false.
Proof. vm_compute. reflexivity. Qed.

(* tampered parameters must fail the checker's gates (1 <= L, 2 <= T) *)
Example rw_gate_L : rw_tier rwm 0 2 0 2000 = false.
Proof. vm_compute. reflexivity. Qed.

Example rw_gate_T : rw_tier rwm 2 1 0 2000 = false.
Proof. vm_compute. reflexivity. Qed.

(* [rw_tier] now feeds the INTERNED checker (ClosureIdx-lex).
   [rw_tier_unchanged] proves the two agree everywhere; these pin it by
   computation on the machines above, so a future edit that breaks the
   agreement is caught here and not only by the proof. *)
Example rw_idx_same_catch :
  (rw_tier rwm 2 2 0 200000, rw_tier_ref rwm 2 2 0 200000) = (true, true).
Proof. vm_compute. reflexivity. Qed.

Example rw_idx_same_reject_qh :
  (rw_tier qhbm 2 2 0 2000, rw_tier_ref qhbm 2 2 0 2000) = (false, false).
Proof. vm_compute. reflexivity. Qed.

Example rw_idx_same_reject_halt :
  (rw_tier (fun _ _ => None) 2 2 0 2000,
   rw_tier_ref (fun _ _ => None) 2 2 0 2000) = (false, false).
Proof. vm_compute. reflexivity. Qed.

(* --- the M4 node-size cut ---------------------------------------

   [rw_tier_cut] is [rw_tier] with the closure abandoned as soon as it
   pops a node carrying more than M run-length items.  Three things need
   pinning by COMPUTATION, not only by [rw_tier_cut_le]:

   1. at the shipped cut it still catches what the uncut tier catches
      -- the whole point, and the thing an over-tight cut breaks;
   2. the cut actually BITES at a small M, so a future edit that
      silently disables it (wrong comparison direction, cut read off
      the wrong component) is caught here rather than by a walk that
      merely gets slower;
   3. it never accepts what the uncut tier rejects -- which
      [rw_tier_cut_le] proves in general, pinned here on the halter and
      the quasihalter because a corrupt cut is exactly the edit that
      would make the pool something [close] never produced. *)
Example rw_cut_keeps_catch :
  rw_tier_cut rwm 2 2 0 200000 32 = true.
Proof. vm_compute. reflexivity. Qed.

Example rw_cut_bites :
  rw_tier_cut rwm 2 2 0 200000 0 = false.
Proof. vm_compute. reflexivity. Qed.

Example rw_cut_rejects_qh_and_halt :
  (rw_tier_cut qhbm 2 2 0 2000 32,
   rw_tier_cut (fun _ _ => None) 2 2 0 2000 32) = (false, false).
Proof. vm_compute. reflexivity. Qed.

(* the gates survive the cut too *)
Example rw_cut_gates :
  (rw_tier_cut rwm 0 2 0 2000 32, rw_tier_cut rwm 2 1 0 2000 32)
  = (false, false).
Proof. vm_compute. reflexivity. Qed.

Example rw_idx_same_gates :
  (rw_tier rwm 0 2 0 2000, rw_tier_ref rwm 0 2 0 2000,
   rw_tier rwm 2 1 0 2000, rw_tier_ref rwm 2 1 0 2000)
  = (false, false, false, false).
Proof. vm_compute. reflexivity. Qed.

(* a never-QH machine must never pass the quasihalting QHBound tier *)
Example qhb_rejects_neverqh :
  try_qhb 2000 200000 512 qhb_rungs_t rwm = false.
Proof. vm_compute. reflexivity. Qed.

(* pipeline classification with the new ladders live.  Since the
   gas-escalated cycle/TC block (scan_ct at 130 first), qhbm -- a
   wrap-QH machine whose post-quiet behavior is a translated cycle --
   is soundly caught R_Leaf by the cheap TC rung (its quiet state's
   last visit precedes the anchor, so QHBound holds); qlxm still
   reaches the wrapped-QHBound tier in-pipeline, so it carries the
   R_QH wiring coverage. *)
Example pipe_qhb_tc_leaf :
  decide_easy 2000 130 1030 200000 512 rungs_t rrungs_t qhb_rungs_t
    rw_rungs_t 2000 32 (dmap_of []) (dmap_of []) (dmap_of []) (hmap_of []) qhbm = R_Leaf.
Proof. vm_compute. reflexivity. Qed.

Example pipe_qhb :
  decide_easy 2000 130 1030 200000 512 rungs_t rrungs_t qhb_rungs_t
    rw_rungs_t 2000 32 (dmap_of []) (dmap_of []) (dmap_of []) (hmap_of []) qlxm = R_QH.
Proof. vm_compute. reflexivity. Qed.

Example pipe_rw :
  decide_easy 2000 130 1030 200000 512 rungs_t rrungs_t qhb_rungs_t
    rw_rungs_t 2000 32 (dmap_of []) (dmap_of []) (dmap_of []) (hmap_of []) rwm = R_NeverQH.
Proof. vm_compute. reflexivity. Qed.

(** ** Proven-machines tier (lever A)

    [proven_lookup] answers only for machines actually in the list, and
    the [tm_enc] key + [tm_eqb] re-check makes it machine-exact: a
    one-transition mutation of a proven machine is rejected.  A weakened
    lookup (dropping the [tm_eqb] guard, or hashing too coarsely) would
    flip one of these [false]s and let an unproven machine be reported
    NeverQuasiHaltsSt without a theorem. *)

(* provm = 1RB0LA_0LB0RC_1LD0RD_1LA1LB, a Bulk-proven holdout
   (theories/Machines/Bulk/Bulk_001.v : nqh_1RB0LA_0LB0RC_1LD0RD_1LA1LB) *)
Definition provm : TM :=
  mk8 (T S1 DR StB) (T S0 DL StA) (T S0 DL StB) (T S0 DR StC)
      (T S1 DL StD) (T S0 DR StD) (T S1 DL StA) (T S1 DL StB).

(* the genuine member is found *)
Example proven_hit : proven_lookup (dmap_of [provm]) provm = true.
Proof. vm_compute. reflexivity. Qed.

(* a residue survivor (tools/repwl_residue_survivors.txt line 1,
   0RB---_0LC0RA_0LD---_1RA1LC) is NOT in the proven list *)
Definition surv1 : TM :=
  mk8 (T S0 DR StB) None (T S0 DL StC) (T S0 DR StA)
      (T S0 DL StD) None (T S1 DR StA) (T S1 DL StC).
Example proven_miss_survivor : proven_lookup (dmap_of [provm]) surv1 = false.
Proof. vm_compute. reflexivity. Qed.

(* mutating one transition (D1: 1LB -> 1LC) must break the lookup *)
Definition provm_mut : TM :=
  mk8 (T S1 DR StB) (T S0 DL StA) (T S0 DL StB) (T S0 DR StC)
      (T S1 DL StD) (T S0 DR StD) (T S1 DL StA) (T S1 DL StC).
Example proven_miss_mutant : proven_lookup (dmap_of [provm]) provm_mut = false.
Proof. vm_compute. reflexivity. Qed.

(** ** Proven-QH tier (lever A, R_QH sibling)

    The [qhmap] lookup (Run.v) is the [pmap] machinery reused (tm_enc key +
    tm_eqb re-check), so it is machine-exact: only a machine whose [tm_enc]
    key AND full transition table match a proven-QH list member is answered
    R_QH.  The R_QH verdict is EARNED by that member's committed
    [NonHalt /\ QHBound B /\ QuasiHaltsSt] theorem (see ProvenQH_Data's
    [provenqh_all]); the pipeline never fabricates it -- the SAME machine,
    absent from the map, is not reported R_QH.  A weakened lookup would flip
    one of these controls. *)

(* qhm = 1RB---_0LC0LC_1RC0RD_1LB1RD, a proven-QH holdout
   (theories/Machines/QHBoard/QHB_00.v : qhb_00001, lex gate) *)
Definition qhm : TM :=
  mk8 (T S1 DR StB) None (T S0 DL StC) (T S0 DL StC)
      (T S1 DR StC) (T S0 DR StD) (T S1 DL StB) (T S1 DR StD).

(* the genuine member is found *)
Example provenqh_hit : deferred_lookup (dmap_of [qhm]) qhm = true.
Proof. vm_compute. reflexivity. Qed.

(* a machine not in the list is not answered *)
Example provenqh_miss_nonmember : deferred_lookup (dmap_of [qhm]) spin0 = false.
Proof. vm_compute. reflexivity. Qed.

(* mutating one transition (D1: 1RD -> 1LD) must break the lookup *)
Definition qhm_mut : TM :=
  mk8 (T S1 DR StB) None (T S0 DL StC) (T S0 DL StC)
      (T S1 DR StC) (T S0 DR StD) (T S1 DL StB) (T S1 DL StD).
Example provenqh_miss_mutant : deferred_lookup (dmap_of [qhm]) qhm_mut = false.
Proof. vm_compute. reflexivity. Qed.

(* end-to-end: with qhm in the proven-QH map (the 2nd map slot), the pipeline
   reports R_QH -- the tier fires ahead of the deferred fallthrough *)
Example pipe_provenqh :
  decide_easy 2000 130 1030 200000 512 rungs_t rrungs_t [] [] 0 32
    (dmap_of []) (dmap_of [qhm]) (dmap_of []) (hmap_of []) qhm = R_QH.
Proof. vm_compute. reflexivity. Qed.

(* the SAME machine, ABSENT from the proven-QH map, is NOT reported R_QH by
   the lookup tier: with empty ladders it falls through to R_Unknown.  So the
   R_QH verdict is carried by the committed theorem, never by the pipeline *)
Example pipe_provenqh_absent :
  decide_easy 2000 130 1030 200000 512 rungs_t rrungs_t [] [] 0 32
    (dmap_of []) (dmap_of []) (dmap_of []) (hmap_of []) qhm = R_Unknown.
Proof. vm_compute. reflexivity. Qed.

(** ** Lever B: the extended QHBound ladder still REJECTS non-quasihalters

    The larger-prefix rungs (t up to 1999, kept under B = 2000) must not
    let the wrapped-QHBound tier claim a never-quasihalting or a halting
    machine as R_QH.  [try_qhb]'s soundness forbids it; these controls
    would fail if a deeper rung's gate were loosened. *)
Definition qhb_rungs_new : list (nat * nat) :=
  [(2, 1280); (2, 1536); (2, 1999)].

(* rwm is repwl-decided never-QH (rw_catches, above): never a quasihalter *)
Example qhb_new_rejects_neverqh :
  try_qhb 2000 200000 512 qhb_rungs_new rwm = false.
Proof. vm_compute. reflexivity. Qed.

(* a halting machine is never a prefix-quiet quasihalter *)
Example qhb_new_rejects_halt :
  try_qhb 2000 200000 512 qhb_rungs_new (fun _ _ => None) = false.
Proof. vm_compute. reflexivity. Qed.

(** ** Lever C: the extended RepWL ladder still REJECTS a wrong-class machine

    The block-width extension adds rungs (5, 2, 0), (7, 2, 0), (6, 2, 0) to
    the RepWL never-quasihalting ladder (Run.v's [rw_rungs_census]).  The
    wider rungs must not let [try_rw] certify a machine that is NOT never-
    quasihalting: neither a genuine QUASIHALTER, nor a never-QH residue
    SURVIVOR whose block-list search fails to produce a certificate.
    [try_rw]'s soundness ([try_rw_sound]: every rung re-derived by
    [rw_check_neverqh], the closure fail-closed on divergence) forbids both;
    these controls would flip to [true] if a wider rung's closure guard or
    its search-certificate check were weakened. *)

(* the extended ladder, identical to Run.v's [rw_rungs_census]; kept inline
   so this negative-control file stays independent of the regenerated tables *)
Definition rw_rungs_ext : list (nat * nat * nat) :=
  [(2, 2, 0); (3, 2, 0); (4, 2, 0); (2, 3, 0);
   (5, 2, 0); (7, 2, 0); (6, 2, 0)].

(* [qhbm] (above) is a genuine wrapped-QHBound quasihalter; the extended
   never-QH ladder must reject it -- every rung, the new ones included *)
Example rwext_rejects_qh : try_rw rw_rungs_ext 2000 32 qhbm = false.
Proof. vm_compute. reflexivity. Qed.

(* survivor 0RB---_0LC0RA_0LD---_1RA1LC (tools/repwl2_survivors.txt): a
   never-QH residue machine the RepWL search cannot certify even at the wider
   rungs -- it must stay non-R_NeverQH, i.e. [try_rw] = false *)
Definition surv_repwl : TM :=
  mk8 (T S0 DR StB) None (T S0 DL StC) (T S0 DR StA)
      (T S0 DL StD) None (T S1 DR StA) (T S1 DL StC).
Example rwext_rejects_survivor : try_rw rw_rungs_ext 2000 32 surv_repwl = false.
Proof. vm_compute. reflexivity. Qed.
