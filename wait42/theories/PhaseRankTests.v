From Coq Require Import Arith Bool List NArith.
From BBB4 Require Import BBB4_Statement.
From BBB4.Census Require Import TNF_QH.
From BBBWait42 Require Import Spec.
From BBBWait42 Require Import PhaseRank.
Definition scanner : TM := fun q h => match q,h with
 | StA,S0 => Some (mkTrans S1 DR StB)
 | StA,S1 => Some (mkTrans S1 DR StA)
 | StB,S0 => Some (mkTrans S1 DL StA)
 | StB,S1 => Some (mkTrans S1 DL StB)
 | _,_ => None end.
Definition inv q := st_eqb q StA || st_eqb q StB.
Definition cert q := mkPhaseRank
 (fun s => match q,s with StA,StB | StB,StA => 1 | _,_ => 0 end)
 (fun n => if Nat.eqb n 1 then 1 else 0)
 (fun n => Nat.eqb n 1)
 (fun _ => match q with StA=>DL | _=>DR end).
Definition bad_cycles q := mkPhaseRank (ph_label (cert q))
 (fun _ => 0) (ph_cyclic (cert q)) (ph_dir (cert q)).
Definition bad_direction q := mkPhaseRank (ph_label (cert q))
 (ph_cycles (cert q)) (ph_cyclic (cert q)) (fun _ => DR).
Definition bad_level q := mkPhaseRank
 (fun s => if st_eqb s q then 0 else 5)
 (fun _ => 1) (fun _ => true) (ph_dir (cert q)).
Example growing_scanner_accepted : control_phase_check scanner inv cert 0 10%N 130%N = true.
Proof. vm_compute; reflexivity. Qed.
Example rejects_small_width : control_phase_check scanner inv cert 0 10%N 129%N = false.
Proof. vm_compute; reflexivity. Qed.
Example rejects_zero_cycle_budget : control_phase_check scanner inv bad_cycles 0 10%N 130%N = false.
Proof. vm_compute; reflexivity. Qed.
Example rejects_wrong_direction : control_phase_check scanner inv bad_direction 0 10%N 130%N = false.
Proof. vm_compute; reflexivity. Qed.
Example rejects_large_phase_level : control_phase_check scanner inv bad_level 0 10%N 130%N = false.
Proof. vm_compute; reflexivity. Qed.
Example rejects_invariant_hole : control_phase_check scanner (fun _ => true) cert 0 10%N 130%N = false.
Proof. vm_compute; reflexivity. Qed.
Example rejects_late_anchor : control_phase_check scanner inv cert 1 0%N 100%N = false.
Proof. vm_compute; reflexivity. Qed.
Example scanner_completion : forall tm', TM_le scanner tm' ->
 NonHalt tm' /\ WindowBound tm' (N.to_nat 10%N) (N.to_nat 130%N).
Proof. exact (control_phase_check_completion scanner inv cert 0 10%N 130%N growing_scanner_accepted). Qed.
Print Assumptions scanner_completion.
