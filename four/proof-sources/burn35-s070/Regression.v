From Coq Require Import List Arith Bool.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn35S070 Require Import Core Grammar Return.
Import ListNotations.
Example exact_blank_entry : csteps st_tm 35 c0=Some(st_main(st_odd++[S1])[]).
Proof. exact st_entry. Qed.
Example odd_to_even_context : forall w r,
 exists t,0<t /\csteps st_tm t(st_main(st_odd++w)r)=Some(st_front StA(st_even++w)r).
Proof. intros w r;apply st_T_sound,st_odd_even. Qed.
Example first_full_return : csteps st_tm 38(st_main(st_odd++[S1])[])=
 Some(st_main(st_odd++[S0;S0;S2;S2;S1])[]).
Proof. reflexivity. Qed.
Example second_full_return : csteps st_tm 50(st_main(st_odd++[S0;S0;S2;S2;S1])[])=
 Some(st_main(st_odd++[S0;S1;S1;S0;S0;S0;S2;S2;S1])[]).
Proof. reflexivity. Qed.
Example untouched_right_context : csteps st_tm 11(st_main[S2;S1][S3;S1])=
 Some(st_front StA[S2;S0;S2;S2;S1][S3;S1]).
Proof. reflexivity. Qed.
Example B_zero_bounce_context : csteps st_tm 3(st_back StB[S0;S1;S2][S3;S2;S1])=
 Some(st_back StB[S1;S2][S3;S2;S2;S1]).
Proof. reflexivity. Qed.
Example A_zero_relaunch_context : csteps st_tm 1(st_back StA[S0;S2;S1][S1;S3;S2])=
 Some(st_back StB[S2;S1][S1;S1;S3;S2]).
Proof. reflexivity. Qed.
Example scan_seed : st_G[S1]=Some[S0;S0;S2;S2;S1].
Proof. reflexivity. Qed.
Example scan_second_seed : st_G[S0;S0;S2;S2;S1]=Some[S0;S1;S1;S0;S0;S0;S2;S2;S1].
Proof. reflexivity. Qed.
Example empty_pending_three_rejected : st_G[]=None.
Proof. reflexivity. Qed.
Example missing_one_rejected : st_G[S2;S2]=None.
Proof. reflexivity. Qed.
Example outside_left_alphabet_rejected : st_G[S3]=None.
Proof. reflexivity. Qed.
Example DFA_excludes_empty : ~st_valid[].
Proof. intros[_ H];discriminate. Qed.
Example DFA_excludes_missing_one : ~st_valid[S2;S2].
Proof. intros[_ H];discriminate. Qed.
Example DFA_accepts_seed : st_valid[S1].
Proof. exact st_seed_valid. Qed.
Example DFA_accepts_first_image : st_valid[S0;S0;S2;S2;S1].
Proof. split;[unfold st_digits;repeat constructor;discriminate|reflexivity]. Qed.
Example unsupported_marker_grammar : st_T[S2;S1;S0;S0;S1]=Some[S2;S0;S2;S2;S1;S1].
Proof. reflexivity. Qed.
Example actual_A_returns : forall N,exists t,N<=t /\VisitsAt st_tm StA t.
Proof. exact st_A_recurrent. Qed.
Example actual_B_returns : forall N,exists t,N<=t /\VisitsAt st_tm StB t.
Proof. exact st_B_recurrent. Qed.
Example exact_state_zero : NonHalt st_tm /\QHBound 0 st_tm.
Proof. exact st_sound. Qed.
