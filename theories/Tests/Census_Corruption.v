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
  decide_easy 2000 130 1030 200000 512 rungs_t rrungs_t [] [] 0 (dmap_of [])
    (fun _ _ => None) = R_Halt StA S0.
Proof. vm_compute. reflexivity. Qed.

Example pipe_spin :
  decide_easy 2000 130 1030 200000 512 rungs_t rrungs_t [] [] 0 (dmap_of [])
    spin0 = R_Leaf.
Proof. vm_compute. reflexivity. Qed.

Example pipe_runner :
  decide_easy 2000 130 1030 200000 512 rungs_t rrungs_t [] [] 0 (dmap_of [])
    run1 = R_Leaf.
Proof. vm_compute. reflexivity. Qed.

Example pipe_qh_leaf :
  decide_easy 2000 130 1030 200000 512 rungs_t rrungs_t [] [] 0 (dmap_of [])
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

(* a never-QH machine must never pass the quasihalting QHBound tier *)
Example qhb_rejects_neverqh :
  try_qhb 2000 200000 512 qhb_rungs_t rwm = false.
Proof. vm_compute. reflexivity. Qed.

(* pipeline classification with the new ladders live *)
Example pipe_qhb :
  decide_easy 2000 130 1030 200000 512 rungs_t rrungs_t qhb_rungs_t
    rw_rungs_t 2000 (dmap_of []) qhbm = R_QH.
Proof. vm_compute. reflexivity. Qed.

Example pipe_rw :
  decide_easy 2000 130 1030 200000 512 rungs_t rrungs_t qhb_rungs_t
    rw_rungs_t 2000 (dmap_of []) rwm = R_NeverQH.
Proof. vm_compute. reflexivity. Qed.
