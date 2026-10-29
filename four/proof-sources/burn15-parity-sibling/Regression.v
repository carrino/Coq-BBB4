From Coq Require Import List.
From BBB24 Require Import Statement CTape.
From BBB24Burn15ParitySibling Require Import ParitySibling.
Import ListNotations.
Example even_head_zero_allowed : ps_ok false S0.
Proof. left;reflexivity. Qed.
Example even_head_two_allowed : ps_ok false S2.
Proof. right;reflexivity. Qed.
Example odd_head_one_required : ps_ok true S1.
Proof. reflexivity. Qed.
Example even_head_one_rejected : ~ps_ok false S1.
Proof. intros[H|H];discriminate. Qed.
Example ordinary_even_head_two :
 csteps ps_tm 4(ps_main[S0]S2)=Some(ps_main[S2]S1).
Proof. reflexivity. Qed.
Example ordinary_odd_head_one :
 csteps ps_tm 4(ps_main[S2]S1)=Some(ps_main[S1]S2).
Proof. reflexivity. Qed.
Example overflow_resets_even_head :
 csteps ps_tm 9(ps_main[S1]S2)=Some(ps_main[S2;S2]S0).
Proof. reflexivity. Qed.
Example invalid_overflow_reaches_blank_B :
 csteps ps_tm 7(StA,([S1;S1],S1,[]))=Some(StB,([S1;S0;S1;S2],S0,[])).
Proof. reflexivity. Qed.
