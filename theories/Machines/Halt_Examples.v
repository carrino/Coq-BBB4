(** * Halt_Examples: 1RB---_------_------_------ halts at step 2. *)
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import Halt.

Definition tm_halt : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | _, _ => None
  end.

Theorem tm_halt_decided : Halts tm_halt /\ QuasiHaltsSt tm_halt.
Proof. apply (halt_check_sound _ 1). vm_compute. reflexivity. Qed.

(* corruption: wrong halt index rejected *)
Example halt_reject : halt_check tm_halt 0 = false.
Proof. vm_compute. reflexivity. Qed.
Example halt_reject2 : halt_check tm_halt 2 = false.
Proof. vm_compute. reflexivity. Qed.
