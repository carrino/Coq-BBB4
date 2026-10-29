From Coq Require Import List Arith.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn23S069Transducer Require Import CrossingParity.
Import ListNotations.
Example actual_blank_cut : csteps s69_tm 6 c0=Some(StA,([S1;S2],S2,[])).
Proof. reflexivity. Qed.
Example initial_invariant : s69_inv c0.
Proof. exact s69_inv_initial. Qed.
Example A0_arbitrary_positive_left : forall l,s69_left l->s69_inv(StA,(l,S0,[])).
Proof. intros l H;split;[exact H|split;[constructor|reflexivity]]. Qed.
Example A2_arbitrary_positive_left : forall l,s69_left l->s69_inv(StA,(l,S2,[])).
Proof. intros l H;split;[exact H|split;[constructor|reflexivity]]. Qed.
Example B1_blank_boundary_return :
 csteps s69_tm 6(StB,([],S1,[S2;S1]))=Some(StA,([S1;S2],S3,[S2;S1])).
Proof. reflexivity. Qed.
Example B2_blank_boundary_return :
 csteps s69_tm 3(StB,([],S2,[S1]))=Some(StA,([S1;S2],S1,[])).
Proof. reflexivity. Qed.
Example B1_odd_phase_allowed : s69_inv(StB,([S2],S1,[])).
Proof. split;[unfold s69_left;repeat(apply Forall_cons;[auto|]);constructor|split;[constructor|reflexivity]]. Qed.
Example B2_even_phase_allowed : s69_inv(StB,([S1;S2;S2],S2,[])).
Proof. split;[unfold s69_left;repeat(apply Forall_cons;[auto|]);constructor|split;[constructor|reflexivity]]. Qed.
Example B1_even_phase_rejected : ~s69_inv(StB,([S2;S2],S1,[])).
Proof. intros[_[_ H]];discriminate H. Qed.
Example B2_odd_phase_rejected : ~s69_inv(StB,([S2],S2,[])).
Proof. intros[_[_ H]];discriminate H. Qed.
Example interior_A3_marker_allowed : s69_inv(StA,([S2],S3,[S3])).
Proof. split;[unfold s69_left;repeat(apply Forall_cons;[auto|]);constructor|split;[repeat constructor;discriminate|reflexivity]]. Qed.
Example boundary_A3_rejected : forall l,~s69_inv(StA,(l,S3,[])).
Proof. intros l[_[_ H]];discriminate H. Qed.
Example blank_B_tail_rejected : forall l,~s69_inv(StB,(l,S0,[])).
Proof. intros l[_[_ H]];discriminate H. Qed.
Example left_threes_rejected : ~s69_inv(StA,([S3],S0,[])).
Proof. intros[H _];inversion H as[|? ? [E|E] _];discriminate E. Qed.
Example right_explicit_zero_rejected : ~s69_inv(StA,([],S0,[S0])).
Proof. intros[_[H _]];inversion H as[|? ? E _];apply E;reflexivity. Qed.
Example blank_B_tail_drifts : forall n l,
 csteps s69_tm n(StB,(l,S0,[]))=Some(StB,(repeat S2 n++l,S0,[])).
Proof.
 induction n;intro l;[reflexivity|].
 change(csteps s69_tm n(StB,(S2::l,S0,[]))=Some(StB,(S2::(repeat S2 n++l),S0,[]))).
 rewrite IHn.
 assert(E:forall m r,repeat S2 m++S2::r=S2::(repeat S2 m++r)).
 {intro m;induction m;intro r;cbn;[reflexivity|now rewrite IHm]. }
 now rewrite E.
Qed.
Example boundary_A3_really_escapes :
 csteps s69_tm 5(StA,([S2;S1],S3,[]))=Some(StB,([S2;S2;S2;S2;S1;S2;S1],S0,[])).
Proof. reflexivity. Qed.
Print Assumptions s69_sound.
