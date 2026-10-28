From Coq Require Import List Arith.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn18S012Rightmost Require Import RightmostOne.
Import ListNotations.
Example actual_blank_cut : csteps r12_tm 3 c0=Some(StA,([S2;S3],S0,[])).
Proof. reflexivity. Qed.
Example initial_invariant : r12_inv c0.
Proof. exact r12_inv_initial. Qed.
Example A_blank_suffix_is_allowed : r12_inv(StA,([S2;S3],S0,[])).
Proof. right;split;[reflexivity|repeat constructor]. Qed.
Example trailing_zero_marker : r12_marker[S3;S2;S0;S1;S0;S0].
Proof. apply r12_skip;apply r12_skip;apply r12_skip;apply r12_at;repeat constructor. Qed.
Example B1_consumes_terminal_marker :
 csteps r12_tm 1(StB,([S3],S1,[S0;S0]))=Some(StA,([S2;S3],S0,[S0])).
Proof. reflexivity. Qed.
Example B2_zero_bounce :
 csteps r12_tm 6(StB,([],S2,[S1]))=Some(StA,([S2;S3],S2,[S1])).
Proof. reflexivity. Qed.
Example B3_left_return :
 csteps r12_tm 3(StB,([],S3,[S1;S0]))=Some(StA,([S2;S3],S1,[S0])).
Proof. reflexivity. Qed.
Example B0_right_padding :
 csteps r12_tm 3(StB,([],S0,[S0;S1;S0;S0]))=Some(StA,([S2;S3;S3],S0,[S0])).
Proof. reflexivity. Qed.
Example left_marker_does_not_replace_right_marker : ~r12_inv(StB,([S1],S0,[])).
Proof.
 intros[H|[H _]];[apply(r12_drop_unmarked S0[]ltac:(discriminate))in H;inversion H|discriminate].
Qed.
Example wrong_terminal_symbol : ~r12_marker[S1;S2;S0].
Proof.
 intro H;inversion H as[r Hz|h r Hm];subst.
 - apply r12_zero_cons in Hz as[Hz _];discriminate.
 - apply(r12_drop_unmarked S2[S0]ltac:(discriminate))in Hm.
   apply(r12_drop_unmarked S0[]ltac:(discriminate))in Hm;inversion Hm.
Qed.
Example blank_B_tail_drifts :
 csteps r12_tm 8(StB,([S1],S0,[]))=Some(StB,(repeat S3 8++[S1],S0,[])).
Proof. reflexivity. Qed.
