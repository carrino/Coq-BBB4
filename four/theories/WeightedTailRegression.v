(** The tail certificate is shared between independently checked boots.
    These regressions exercise live-instruction agreement, boot membership,
    and rejection of an invalid fixed gram set. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Bounds Census CTape Mirror CycleCensus
  WeightedReuse WeightedSuffix WeightedTail WeightedSuffixRegression.
From BBB24.Checkers Require Import NGram.
Import ListNotations.
Definition fixed_tail := weighted_tail source 2 (gadds [[S0;S0];[S0;S2];[S1;S0];[S1;S2];[S3;S2];[S2;S1];[S2;S3];[S2;S2]] gempty) (gadds [[S0;S0];[S1;S2];[S2;S0];[S2;S1];[S2;S2]] gempty) nodes certificate.
Example fixed_ready : wt_ready fixed_tail=true.
Proof. vm_compute. reflexivity. Qed.
Example target_boot : wt_use_check 4096%N 4096%N fixed_tail(mirror_tm target)8=true.
Proof. vm_compute. reflexivity. Qed.
Example changed_live_rejected : wt_use_check 4096%N 4096%N fixed_tail(mirror_tm changed_tail)8=false.
Proof. vm_compute. reflexivity. Qed.
Example wrong_start_rejected : wt_use_check 4096%N 4096%N fixed_tail(mirror_tm target)0=false.
Proof. vm_compute. reflexivity. Qed.
Definition empty_tail := weighted_tail source 2 gempty gempty nodes certificate.
Example invalid_tail_rejected : wt_ready empty_tail=false.
Proof. vm_compute. reflexivity. Qed.
Definition target_row := weighted_reuse_row [5;3;3;7;10;13;9;0] true 8.
Example fallback_checked : wt_hybrid_check 4096%N 4096%N empty_tail[target_row]=true.
Proof. vm_compute. reflexivity. Qed.
Theorem shared_target_run : NonHalt target /\ Bounds 4096%N 4096%N target.
Proof. destruct(wt_use_sound _ _ _ _ _ fixed_ready target_boot)as[Hnh Hb].
 split;[apply mirror_nonhalt;exact Hnh|apply mirror_bounds;exact Hb]. Qed.
Print Assumptions shared_target_run.
