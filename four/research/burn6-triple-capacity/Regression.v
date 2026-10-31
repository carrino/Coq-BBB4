From Coq Require Import List NArith ZArith.
From BBB24 Require Import Statement CTape WeightedCensus InstructionPortfolio.
From BBB24Burn3Pair Require Import PairCapacity GraphCertificate.
From BBB24Burn6TripleCapacity Require Import TripleCapacity GraphCertificate.
Import ListNotations.
Module Old := BBB24Burn3Pair.GraphCertificate.
Module New := BBB24Burn6TripleCapacity.GraphCertificate.

Definition test_left:TM:=fun _ _=>Some(mkTrans S0 DL StA).
Definition test_right:TM:=fun _ _=>Some(mkTrans S0 DR StA).
Example left_popped_third_from_successor:
 tc_sides_delta test_left New.capacity
  (StA,([S1;S2],S0,[S0;S0]))(StA,([S2;S1],S1,[S0;S0]))=(-2)%Z.
Proof. vm_compute;reflexivity. Qed.
Example left_other_third_changes_delta:
 tc_sides_delta test_left New.capacity
  (StA,([S1;S2],S0,[S0;S0]))(StA,([S2;S0],S1,[S0;S0]))=0%Z.
Proof. vm_compute;reflexivity. Qed.
Example right_popped_third_from_successor:
 tc_sides_delta test_right New.capacity
  (StA,([S0;S0],S0,[S0;S1]))(StA,([S0;S0],S0,[S1;S3]))=(-1)%Z.
Proof. vm_compute;reflexivity. Qed.
Example right_other_third_changes_delta:
 tc_sides_delta test_right New.capacity
  (StA,([S0;S0],S0,[S0;S1]))(StA,([S0;S0],S0,[S1;S0]))=0%Z.
Proof. vm_compute;reflexivity. Qed.

Definition old_capacity:TCapacity:=mkTCapacity
 (pc_scale Old.capacity)(pc_terms Old.capacity)
 (fun a b _=>pc_score Old.capacity a b)(fun _ _ _=>0)(pc_bias Old.capacity).
Example pair_positive_control:
 tc_graph_check Old.family 2 4096 Old.nodes(StB,S3)old_capacity(wc_components Old.target_7)=true.
Proof. vm_compute;reflexivity. Qed.

Example old_boundary_rejected:
 wp_graph_check New.actual 2 4096 New.nodes[(StA,S2)]New.certificate=false.
Proof. vm_compute;reflexivity. Qed.
Definition pairs_only:TCapacity:=mkTCapacity 1 [] (fun _ _ _=>0)
 (fun a b _=>match a,b with S1,S0=>2|S1,S1=>3|_,_=>0 end)(tc_bias New.capacity).
Example omitted_triples_rejected:
 tc_graph_check New.actual 2 4096 New.nodes(StA,S2)pairs_only(wc_components New.target_2)=false.
Proof. vm_compute;reflexivity. Qed.
Definition bad_left_blank:TCapacity:=mkTCapacity 1 []
 (fun _ _ _=>1)New.right_score(tc_bias New.capacity).
Example left_blank_charge_rejected:
 tc_graph_check New.actual 2 4096 New.nodes(StA,S2)bad_left_blank(wc_components New.target_2)=false.
Proof. vm_compute;reflexivity. Qed.
Definition bad_right_blank:TCapacity:=mkTCapacity 1 []
 New.left_score(fun _ _ _=>1)(tc_bias New.capacity).
Example right_blank_charge_rejected:
 tc_graph_check New.actual 2 4096 New.nodes(StA,S2)bad_right_blank(wc_components New.target_2)=false.
Proof. vm_compute;reflexivity. Qed.
Example width_one_rejected:
 tc_graph_check New.actual 1 4096 New.nodes(StA,S2)New.capacity(wc_components New.target_2)=false.
Proof. vm_compute;reflexivity. Qed.
Definition zero_scale:TCapacity:=mkTCapacity 0 [] New.left_score New.right_score(tc_bias New.capacity).
Example zero_scale_rejected:
 tc_graph_check New.actual 2 4096 New.nodes(StA,S2)zero_scale(wc_components New.target_2)=false.
Proof. vm_compute;reflexivity. Qed.
