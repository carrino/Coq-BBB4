(** Generic non-halting projection for checked closure batches. Keeping the
    batch symbolic avoids reducing a concrete checker during elaboration. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Pipeline.

Theorem batch_nonhalt : forall bs bi batch,
  batch_check bs bi batch = true -> forall codes cert,
  In (codes,cert) batch -> NonHalt (machine_of_codes codes).
Proof.
  intros bs bi batch H codes cert Hin.
  unfold batch_check in H.
  apply forallb_forall with (x:=(codes,cert)) in H; [|exact Hin].
  exact (proj1 (stage_check_sound _ _ _ _ H)).
Qed.

Print Assumptions batch_nonhalt.
