From Coq Require Import List.
From SmallBB Require Import Statement Size Census Census22 StateCheckers.
Import ListNotations.
(** The (2,2) state bound cannot be lowered while keeping the same exhaustive certificate. *)
Example rejects_state_bound_5:verify 2 2 5 8 5 empty certificate22=false.
Proof. native_compute. reflexivity. Qed.
(** This machine exposed collisions when positive keys were extracted to 63-bit OCaml integers. *)
Definition overflow_regression:TM:=machine_of_codes 2 3 [5;8;7;3;9;6].
Example rejects_colliding_repwl:rw_state_check 59 overflow_regression 3 2 67 512=false.
Proof. native_compute. reflexivity. Qed.
