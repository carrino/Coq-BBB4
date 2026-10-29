From Coq Require Import List Arith.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn18S065Rightmost Require Import RightmostReturn.
Import ListNotations.
Example actual_entry : csteps rr_tm 7 c0=Some(StA,([S1;S0;S1],S0,[])).
Proof. reflexivity. Qed.
Example zero_suffix_in_A : rr_inv(StA,([S2],S0,[S0;S0])).
Proof. right;split;[reflexivity|repeat constructor]. Qed.
Example B1_preserves_marker_without_entering_A :
 cstep rr_tm(StB,([S2],S1,[]))=Some(StB,([],S2,[S3])) /\rr_inv(StB,([],S2,[S3])).
Proof. split;[reflexivity|left;apply rr_skip;apply rr_at;[right;reflexivity|constructor]]. Qed.
Example A1_can_leave_a_blank_suffix :
 cstep rr_tm(StA,([S3],S1,[]))=Some(StA,([S2;S3],S0,[])) /\rr_inv(StA,([S2;S3],S0,[])).
Proof. split;[reflexivity|right;split;[reflexivity|repeat constructor]]. Qed.
Example protected_A2_keeps_right_marker :
 cstep rr_tm(StA,([S0],S2,[S1]))=Some(StB,([],S0,[S0;S1])) /\rr_inv(StB,([],S0,[S0;S1])).
Proof. split;[reflexivity|left;apply rr_skip;apply rr_skip;apply rr_at;[left;reflexivity|constructor]]. Qed.
Example isolated_A2_is_excluded : ~rr_inv(StA,([S0],S2,[])).
Proof.
 intros[H|[_ H]].
 - inversion H as[h r Hmark Hz|h r Htail];subst.
   + destruct Hmark;discriminate.
   + inversion Htail.
 - inversion H;discriminate.
Qed.
Example isolated_A2_escapes : csteps rr_tm 2(StA,([S0],S2,[]))=Some(StB,([S1],S0,[])).
Proof. reflexivity. Qed.
Example blank_B_is_excluded_and_drifts : ~rr_inv(StB,([],S0,[])) /\
 (forall n,csteps rr_tm n(StB,([],S0,[]))=Some(StB,(repeat S1 n,S0,[]))).
Proof.
 split.
 - intros[H|[H _]];[|discriminate].
   inversion H as[h r Hmark Hz|h r Htail];subst;[destruct Hmark;discriminate|inversion Htail].
 - intro n;rewrite rr_B0_drift,app_nil_r;reflexivity.
Qed.
