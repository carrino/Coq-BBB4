From Coq Require Import NArith List.
Import ListNotations.
From BBB4 Require Import BBB4_Statement.
From BBB4.Census Require Import TNF_QH.
From BBBWait42 Require Import Spec.
From BBBWait42 Require Import FiniteObservation.
Definition terminal4 : TM := fun q _ => match q with
 | StA=>Some(mkTrans S0 DR StB)|StB=>Some(mkTrans S0 DR StC)
 | StC=>Some(mkTrans S0 DR StD)|StD=>None end.
Example inclusive_endpoint_accept : finite_observation_check terminal4 (fun _=>false) 0%N 3%N=true.
Proof. vm_compute; reflexivity. Qed.
Example too_short_reject : finite_observation_check terminal4 (fun _=>false) 0%N 2%N=false.
Proof. vm_compute; reflexivity. Qed.
Example all4_accept_after_partial_halt : finite_observation_check terminal4 (fun _=>false) 0%N 4%N=true.
Proof. vm_compute; reflexivity. Qed.
Example final_configuration_is_absent : fst(observation_window terminal4 0%N 4%N)=None.
Proof. vm_compute; reflexivity. Qed.
Example terminal4_not_nonhalt : ~NonHalt terminal4.
Proof. intro H; apply(H 4); reflexivity. Qed.
Theorem all4_every_completion : forall tm', TM_le terminal4 tm' -> WindowBound tm' 0 4.
Proof. exact(finite_observation_check_completion terminal4 (fun _=>false) 0%N 4%N all4_accept_after_partial_halt). Qed.
Definition closed_pair : TM := fun q _ => Some(mkTrans S0 DR
 (match q with StA=>StB|StB=>StC|StC=>StB|StD=>StD end)).
Definition pair q := match q with StB|StC=>true|_=>false end.
Example closed_pair_accept : finite_observation_check closed_pair pair 0%N 2%N=true.
Proof. vm_compute; reflexivity. Qed.
Example unseen_extra_tail_state_reject : finite_observation_check closed_pair (fun q=>negb(st_eqb q StA)) 0%N 2%N=false.
Proof. vm_compute; reflexivity. Qed.
Example nonclosed_tail_reject : finite_observation_check closed_pair (fun q=>st_eqb q StB) 0%N 2%N=false.
Proof. vm_compute; reflexivity. Qed.
Definition partial2 : TM := fun q _=>match q with StA=>Some(mkTrans S0 DR StB)|_=>None end.
Example partial_stop_does_not_close_family : finite_observation_check partial2 (fun _=>true) 0%N 3%N=false.
Proof. vm_compute; reflexivity. Qed.
Print Assumptions all4_every_completion.

Definition small_batch :=
 (mkObservationCase terminal4 (fun _=>false) 3%N)::
 (mkObservationCase closed_pair pair 2%N)::nil.
Example batch_accepts_local_widths : observation_batch_check small_batch 0%N 4%N=true.
Proof. vm_compute; reflexivity. Qed.
Example batch_rejects_global_width_below_local :
 observation_batch_check (mkObservationCase closed_pair pair 2%N::nil) 0%N 1%N=false.
Proof. vm_compute; reflexivity. Qed.
Theorem batch_checked_widening : forall e, List.In e small_batch -> forall tm',
 TM_le (observation_machine e) tm' -> WindowBound tm' 0 4.
Proof. exact(observation_batch_completion small_batch 0%N 4%N batch_accepts_local_widths). Qed.
Print Assumptions batch_checked_widening.
