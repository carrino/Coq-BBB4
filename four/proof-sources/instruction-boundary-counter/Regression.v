(** Negative controls and arbitrary-context regressions. *)
From Coq Require Import List Arith NArith.
From BBB24 Require Import Statement StatementTr CTape Instructions.
From BBB24BoundaryNeighbors Require Import BoundaryKernel Cases.
Import ListNotations.
Example generic_block_arbitrary_slot_and_context:forall b2 l r,
 csteps(bc_tm b2)28(at_one(S3::S1::l)(w12 1++S1::S3::r))=
 Some(at_one l(w12 2++S1::S3::r)).
Proof. intros b2 l r;exact(one_block b2 1 l r). Qed.
Example incorrect_gap_rejected:
 csteps(bc_tm None)15(main 0)<>Some(main 1).
Proof. vm_compute;discriminate. Qed.
Example erased_machine_halts_from_blank:csteps(bc_tm None)14 c0=None.
Proof. vm_compute;reflexivity. Qed.
Example erased_machine_survives_each_suffix:forall n,exists d,
 csteps(bc_tm None)n(main 0)=Some d.
Proof. apply every_from. Qed.
Example incorrect_entry_rejected:csteps case_4 63 c0<>Some(main 1).
Proof. vm_compute;discriminate. Qed.
Example B2_absent_after_entry:forall n,64<=n->~FiresAt case_4(StB,S2)n.
Proof. exact(B2_quiet _ 64 1 entry_4). Qed.
Example B0_recurrent_after_entry:forall N,exists k,N<=k/\FiresAt case_4(StB,S0)k.
Proof. intro N;eapply seven_recurrent;[exact entry_4|discriminate]. Qed.
