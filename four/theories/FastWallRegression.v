(** Exercise the accelerated checker against the existing nontrivial wall
    transport regression, including invalid boots and changed live rules. *)
From Coq Require Import List NArith.
From BBB24 Require Import Mirror WeightedTail WeightedTailRegression
 WeightedSuffixRegression FastWall.
Import ListNotations.

Example fast_tail_ready : fast_wt_ready fixed_tail=true.
Proof. vm_compute. reflexivity. Qed.
Example fast_invalid_tail : fast_wt_ready empty_tail=false.
Proof. vm_compute. reflexivity. Qed.
Example fast_suffix_accepts :
 fast_weighted_suffix_check 4096%N 4096%N (mirror_tm target) source 2 8 nodes certificate=true.
Proof. vm_compute. reflexivity. Qed.
Example fast_changed_live_rejects :
 fast_weighted_suffix_check 4096%N 4096%N (mirror_tm changed_tail) source 2 8 nodes certificate=false.
Proof. vm_compute. reflexivity. Qed.
Example fast_wrong_boot_rejects :
 fast_weighted_suffix_check 4096%N 4096%N (mirror_tm target) source 2 0 nodes certificate=false.
Proof. vm_compute. reflexivity. Qed.
Example fast_original_wall_rejects :
 fast_wc_graph_check 4096%N 4096%N (mirror_tm target) 2 8 nodes certificate=false.
Proof. vm_compute. reflexivity. Qed.
Example fast_fallback_accepts :
 fast_wt_hybrid_check 4096%N 4096%N empty_tail[target_row]=true.
Proof. vm_compute. reflexivity. Qed.
