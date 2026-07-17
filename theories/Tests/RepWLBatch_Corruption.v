(** * RepWLBatch_Corruption: negative controls for the RepWL
    boarding pipeline (tools/gen_repwl_certs.py ->
    [rw_check_neverqh]).

    Test subject: tm_rwl_00001 = 1RB0LB_0LC0LA_1RC0RD_1LB1LA, the
    first boarded neverqh_rwlrank holdout (L=2 T=2 t=0, 489 abstract
    configurations).  The genuine run is the positive control; every
    corruption a buggy or adversarial generator could emit -- a
    mutated transition, swapped state certificates, gutted rank
    tables, a starved closure budget, or out-of-gate parameters
    (L = 0, T = 1: the latter would break the capped witness bits'
    determinism, which is exactly why the checker gates 2 <= T) --
    must make the checker compute [false]. *)

From Coq Require Import List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import RepWL.
From BBB4.Machines Require Import RepWL_Batch_01.
Import ListNotations.

(* The genuine parameters pass (the boarded theorem relies on it). *)
Example rwl_accept_genuine :
  rw_check_neverqh tm_rwl_00001 2 2 0 3976 cert_rwl_00001 = true.
Proof. vm_compute. reflexivity. Qed.

(* One-transition mutant (StD,S0: 1LB -> 1RB): the closure the
   checker re-derives no longer matches the certificate's world. *)
Definition tm_rwl_mutant : TM := fun q s =>
  match q, s with
  | StD, S0 => Some (mkTrans S1 DR StB)
  | q, s => tm_rwl_00001 q s
  end.
Example rwl_reject_mutant :
  rw_check_neverqh tm_rwl_mutant 2 2 0 3976 cert_rwl_00001 = false.
Proof. vm_compute. reflexivity. Qed.

(* Certificates swapped between two states. *)
Example rwl_reject_swapped :
  rw_check_neverqh tm_rwl_00001 2 2 0 3976
    (fun q => cert_rwl_00001
                (match q with StA => StB | StB => StA | q => q end))
  = false.
Proof. vm_compute. reflexivity. Qed.

(* Wrong measure certificate: gutting every rank table leaves edges
   with no strict decrease anywhere in the lex chain. *)
Definition gut_rank (c : rwcomp) : rwcomp :=
  match c with
  | RwRankE _ => RwRankE []
  | c => c
  end.
Example rwl_reject_gutted :
  rw_check_neverqh tm_rwl_00001 2 2 0 3976
    (fun q => map gut_rank (cert_rwl_00001 q)) = false.
Proof. vm_compute. reflexivity. Qed.

(* The empty certificate is rejected. *)
Example rwl_reject_empty :
  rw_check_neverqh tm_rwl_00001 2 2 0 3976 (fun _ => []) = false.
Proof. vm_compute. reflexivity. Qed.

(* Starved closure budget fails closed. *)
Example rwl_reject_starved :
  rw_check_neverqh tm_rwl_00001 2 2 0 1 cert_rwl_00001 = false.
Proof. vm_compute. reflexivity. Qed.

(* Out-of-gate parameters fail closed: block length 0 ... *)
Example rwl_reject_L0 :
  rw_check_neverqh tm_rwl_00001 0 2 0 3976 cert_rwl_00001 = false.
Proof. vm_compute. reflexivity. Qed.

(* ... and threshold 1 (capped witness bits would be ambiguous). *)
Example rwl_reject_T1 :
  rw_check_neverqh tm_rwl_00001 2 1 0 3976 cert_rwl_00001 = false.
Proof. vm_compute. reflexivity. Qed.
