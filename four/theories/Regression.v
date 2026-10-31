(** Rejection checks at the untrusted-certificate boundary. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec RLE Replay Certificate.
Import ListNotations.
Local Open Scope N_scope.
Example invalid_growth :
  apply_op (Grow2 2) (RC StA DL [(S2,3)] [(S2,1)]) = None.
Proof. reflexivity. Qed.
Example invalid_consumption :
  apply_op (Consume1 2) (RC StA DL [(S2,5)] [(S2,2);(S1,1)]) = None.
Proof. reflexivity. Qed.
Example chain_changes_state :
  apply_op (Chain 1) (RC StA DR [] [(S0,1)]) = None.
Proof. reflexivity. Qed.
Example wrong_direction :
  apply_op (Pair3 1) (RC StA DR [(S3,5)] []) = None.
Proof. reflexivity. Qed.
Example corrupt_first_command : replay (Grow2 1 :: tl certificate) initial = None.
Proof. reflexivity. Qed.
(** Exceeds both signed and unsigned 64-bit machine integers. *)
Example large_binary_cost :
  apply_op (Chain scoreN) (RC StA DL [(S1,scoreN)] []) =
  Some (scoreN,RC StA DL [(S1,0)] [(S2,scoreN)]).
Proof. vm_compute. reflexivity. Qed.
