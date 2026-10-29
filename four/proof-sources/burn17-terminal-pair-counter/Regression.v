From Coq Require Import List Arith Bool.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn17TerminalPairCounter Require Import TerminalPair.
Import ListNotations.
Example actual_entry : csteps tp_tm 3 c0=Some(tp_main[]T21).
Proof. reflexivity. Qed.
Example direct_increment_context :
 csteps tp_tm 2(StA,([S1;S3;S0],S1,[S2;S0]))=Some(StA,([S2;S3;S0],S2,[S2;S0])).
Proof. reflexivity. Qed.
Example prefix_carry : csteps tp_tm 6(tp_main[true;false]T11)=Some(tp_main[false;true]T11).
Proof. reflexivity. Qed.
Example terminal_eleven : csteps tp_tm 6(tp_main[true]T11)=Some(tp_main[false]T21).
Proof. reflexivity. Qed.
Example terminal_twentyone_head_zero : csteps tp_tm 5(tp_main[]T21)=Some(tp_main[true]T2).
Proof. reflexivity. Qed.
Example terminal_twentyone_head_one : csteps tp_tm 13(tp_main[true]T21)=Some(tp_main[false;true]T2).
Proof. reflexivity. Qed.
Example terminal_two : csteps tp_tm 8(tp_main[true]T2)=Some(tp_main[false]T11).
Proof. reflexivity. Qed.
Example wrong_head_invalid_and_excluded :
 csteps tp_tm 5(StA,([S2;S1],S2,[]))<>Some(tp_main[true]T2) /\
 (forall n,tp_head(repeat true n)T21<>S2).
Proof. split;[discriminate|intros n H;destruct(tp_head_max_21 n)as[E|E];congruence]. Qed.
