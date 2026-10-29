(** A completion is not evidence that the original partial run is infinite. *)
From Coq Require Import List.
From BBB24 Require Import Statement Spec Census.
From BBB24Burn12CompletionTransfer Require Import CompletionTransfer.
Import ListNotations.
Definition halted : TM := fun _ _=>None.
Definition filled : TM := fun q _=>Some(mkTrans S0 DR(match q with StA=>StB|StB=>StA end)).
Example halted_extends_to_filled : TM_le halted filled.
Proof. intros q s;left;reflexivity. Qed.
Example original_is_not_nonhalting : ~NonHalt halted.
Proof. intro H;apply(H 1);reflexivity. Qed.
Example closure_rejects_halted_seed : ct_nonhalt_check halted 1 1 0 16 2=false.
Proof. vm_compute;reflexivity. Qed.
Example closure_rejects_halted_prefix : ct_nonhalt_check halted 1 1 1 16 2=false.
Proof. vm_compute;reflexivity. Qed.
