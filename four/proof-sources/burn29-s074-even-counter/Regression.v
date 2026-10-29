From Coq Require Import List Arith Lia.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn29S074EvenCounter Require Import Programs Grammar Final.
Import ListNotations.
Example s74_reg_original : c0=s74_cut[] /\s74_even[].
Proof. split;reflexivity. Qed.
Example s74_reg_forward_context : forall r,csteps s74_tm 5
 (s74_front StA(s74_wall[2;1;0])(S1::repeat S0 3++S1::r))=
 Some(s74_front StA(s74_wall[3;2;1;0])r).
Proof. exact(s74_forward 3 2[1;0]). Qed.
Example s74_reg_merge_context : forall l r,csteps s74_tm 20
 (StA,(S3::repeat S2 4++S3::S2::l,S0,r))=
 Some(StA,(S3::repeat S2 4++l,S0,S1::S1::r)).
Proof. exact(s74_merge 3). Qed.
Example s74_reg_unwind_context : forall r,csteps s74_tm 53
 (StA,(s74_wall[3;1;2],S0,r))=
 Some(s74_cut(repeat S0 6++S1::S0::S1::(repeat S1 4++r))).
Proof. exact(s74_unwind[1;2]3). Qed.
Example s74_reg_odd_boundary : forall n,csteps s74_tm(4+n)(s74_cut[S1])=
 Some(StB,(repeat S2 n++[S2;S3;S2],S0,[])).
Proof. intro n;rewrite csteps_add;change(csteps s74_tm n(StB,([S2;S3;S2],S0,[]))=Some(StB,(repeat S2 n++[S2;S3;S2],S0,[])));apply s74_B_drift. Qed.
Example s74_reg_missing_wall_cell : csteps s74_tm 3(StA,([S3],S0,[]))<>
 Some(s74_cut[S1;S0;S1]).
Proof. vm_compute;discriminate. Qed.
Example s74_reg_A_recurs : forall N,exists k,N<=k /\VisitsAt s74_tm StA k.
Proof. exact s74_A_late. Qed.
Example s74_reg_B_recurs : forall N,exists k,N<=k /\VisitsAt s74_tm StB k.
Proof. exact s74_B_late. Qed.
