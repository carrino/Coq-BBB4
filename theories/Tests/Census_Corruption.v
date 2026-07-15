(** * Tests/Census_Corruption: negative controls for the census pipeline.

    Every census checker must REJECT tampered parameters, and the
    pipeline must classify known machines correctly.  All checks are
    closed by [vm_compute]; a regression here means a checker was
    weakened. *)

From Coq Require Import Arith Bool List.
From BBB4 Require Import BBB4_Statement.
From BBB4.Checkers Require Import NGram.
From BBB4.Census Require Import TNF_QH Decide Deferred_Defs.
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

(** ** Pipeline classification on knowns *)

Definition rungs_t : list (nat * nat) := [(2, 100); (3, 200)].

Example pipe_halt :
  decide_easy 2000 130 1030 200000 512 rungs_t (dmap_of [])
    (fun _ _ => None) = R_Halt StA S0.
Proof. vm_compute. reflexivity. Qed.

Example pipe_spin :
  decide_easy 2000 130 1030 200000 512 rungs_t (dmap_of []) spin0 = R_Leaf.
Proof. vm_compute. reflexivity. Qed.

Example pipe_runner :
  decide_easy 2000 130 1030 200000 512 rungs_t (dmap_of []) run1 = R_Leaf.
Proof. vm_compute. reflexivity. Qed.

Example pipe_qh_leaf :
  decide_easy 2000 130 1030 200000 512 rungs_t (dmap_of []) qh1 = R_Leaf.
Proof. vm_compute. reflexivity. Qed.
