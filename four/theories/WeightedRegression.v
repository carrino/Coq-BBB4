(** Four-symbol guards, explicit graph coverage, and prefix-bound checks. *)
From Coq Require Import List ZArith NArith.
From BBB24 Require Import Statement StatementTr CTape Bounds WeightedNGram WeightedCensus NGramRegression.
Import ListNotations.

Definition oscillator_graph:list cconf :=
 [(StA,([S0],S3,[S3]));(StB,([S3],S3,[S0]))].
Example graph_accepts_s3 :
 wc_graph_check 2%N 2%N s3_oscillator 1 2 oscillator_graph (fun _=>None)=true.
Proof. vm_compute. reflexivity. Qed.
Theorem graph_s3_bounds: NonHalt s3_oscillator /\ Bounds 2%N 2%N s3_oscillator.
Proof. eapply wc_graph_check_sound;exact graph_accepts_s3. Qed.

Example graph_rejects_missing_successor :
 wc_graph_check 2%N 2%N s3_oscillator 1 2 (firstn 1 oscillator_graph) (fun _=>None)=false.
Proof. vm_compute. reflexivity. Qed.
Example graph_rejects_late_anchor :
 wc_graph_check 1%N 1%N s3_oscillator 1 2 oscillator_graph (fun _=>None)=false.
Proof. vm_compute. reflexivity. Qed.
Example graph_rejects_s3_halt :
 wc_graph_check 2%N 2%N s3_halts 1 2 oscillator_graph (fun _=>None)=false.
Proof. vm_compute. reflexivity. Qed.

(** This positivity check would wrongly pass if the S3 pair were omitted. *)
Definition bad_s3_potential:wncomp := WBinary
 (wc_score 0 0 0 0) (wc_score 0 0 0 (-1))
 (wc_score 0 0 0 0) (wc_score 0 0 0 0)
 (fun _=>0%Z) (fun _=>false).
Example fourth_symbol_positivity_checked:wn_good [] bad_s3_potential=false.
Proof. vm_compute. reflexivity. Qed.
Example binary_potential_requires_wall:wn_linear bad_s3_potential=false.
Proof. reflexivity. Qed.
