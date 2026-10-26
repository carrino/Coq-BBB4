From Coq Require Import Arith Lia List.
From SmallBB Require Import Statement StatementTr Size Bounds Codes23 StateCheckers.
Import ListNotations.
Definition remaining23:list TM:= [machine_of_codes 2 3 [5;9;10;6;9;7];machine_of_codes 2 3 [5;10;1;7;6;4];machine_of_codes 2 3 [5;10;1;11;6;4];machine_of_codes 2 3 [5;10;4;6;8;9];machine_of_codes 2 3 [5;10;4;6;10;9];machine_of_codes 2 3 [5;11;3;6;8;3];machine_of_codes 2 3 [5;11;10;6;9;7];machine_of_codes 2 3 [7;8;3;5;4;6];machine_of_codes 2 3 [7;8;3;9;4;6];machine_of_codes 2 3 [7;8;6;4;8;11];machine_of_codes 2 3 [7;8;6;4;10;11];machine_of_codes 2 3 [7;9;1;4;10;1];machine_of_codes 2 3 [7;9;8;4;11;5];machine_of_codes 2 3 [7;11;8;4;11;5];machine_of_codes 2 3 [9;1;6;7;8;10];machine_of_codes 2 3 [9;1;6;11;8;10];machine_of_codes 2 3 [9;3;7;10;3;4];machine_of_codes 2 3 [9;6;5;10;11;5];machine_of_codes 2 3 [9;6;7;10;11;5];machine_of_codes 2 3 [9;8;6;10;5;4];machine_of_codes 2 3 [9;8;6;10;5;6];machine_of_codes 2 3 [11;1;5;8;1;6];machine_of_codes 2 3 [11;3;4;5;10;8];machine_of_codes 2 3 [11;3;4;9;10;8];machine_of_codes 2 3 [11;4;5;8;9;7];machine_of_codes 2 3 [11;4;7;8;9;7];machine_of_codes 2 3 [11;10;4;8;7;4];machine_of_codes 2 3 [11;10;4;8;7;6]].
Lemma remaining23_state_checked:forallb(fun tm=>ng_state_check 59 tm 2 128 4096 32)remaining23=true.
Proof. native_compute. reflexivity. Qed.
Lemma remaining23_nth:forall i tm,nth_error remaining23 i=Some tm->NonHalt tm /\ QHBound 59 tm.
Proof.
 intros i tm H. pose proof(nth_error_In remaining23 i H)as Hin.
 pose proof remaining23_state_checked as HC;rewrite forallb_forall in HC.
 apply(ng_state_check_sound 59 tm 2 128 4096 32);exact(HC tm Hin).
Qed.
