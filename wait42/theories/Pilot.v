(** A bounded, checked census walk. Its remaining obligations are not solved. *)
From Coq Require Import List.
From BBB4.Census Require Import TNF_QH.
From BBBWait42 Require Import Run.

Definition checked_pilot_frontier := pilot_walk 10.

Theorem checked_pilot_sizes :
  (length (fst checked_pilot_frontier), length (snd checked_pilot_frontier)) = (53,338).
Proof. native_compute; reflexivity. Qed.

Theorem checked_pilot_is_unfinished : checked_pilot_frontier <> (nil,nil).
Proof.
  intro H. pose proof checked_pilot_sizes as HS.
  rewrite H in HS. discriminate.
Qed.

Print Assumptions checked_pilot_sizes.
