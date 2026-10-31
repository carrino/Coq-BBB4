(** Two nonzero reset residues close under m -> 2m+3. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census.
From BBB24Burn18CounterObligations Require Import CounterObligations.
From BBB24Burn24S056Counter Require Import Phase Fallback.
Import ListNotations.
Definition sf_tail1 k := sf_p k++true::true::false::(sf_p k++[false]).
Definition sf_tail2 k := sf_p(S k)++false::(sf_p(S k)++[false]).
Lemma sf_pairs_app : forall a b,sf_pairs(a++b)=sf_pairs a+sf_pairs b.
Proof. induction a as[|x a IH];intro b;cbn;[reflexivity|rewrite IH;destruct x;cbn;lia]. Qed.
Lemma sf_p_pairs : forall k,sf_pairs(sf_p k)=k.
Proof. induction k;cbn;lia. Qed.
Lemma sf_tail1_in : forall k,s56_in(sf_tail1 k)=
 sf_P k++S1::S1::S1::S1::S3::(sf_P k++[S3]).
Proof.
 intro k;unfold sf_tail1;rewrite !sf_in_app,sf_p_in;cbn[s56_in];
 rewrite sf_in_app,sf_p_in;cbn[s56_in];repeat rewrite <-app_assoc;reflexivity.
Qed.
Lemma sf_tail2_in : forall k,s56_in(sf_tail2 k)=
 sf_P(S k)++S3::(sf_P(S k)++[S3]).
Proof.
 intro k;unfold sf_tail2;rewrite !sf_in_app,sf_p_in;cbn[s56_in];
 rewrite sf_in_app,sf_p_in;cbn[s56_in];repeat rewrite <-app_assoc;reflexivity.
Qed.
Lemma sf_tail1_length : forall k,length(s56_in(sf_tail1 k))=6*k+6.
Proof. intro k;rewrite sf_tail1_in,app_length,sf_P_length;cbn[length];rewrite app_length,sf_P_length;cbn;lia. Qed.
Lemma sf_tail2_length : forall k,length(s56_in(sf_tail2 k))=6*k+8.
Proof. intro k;rewrite sf_tail2_in,app_length,sf_P_length;cbn[length];rewrite app_length,sf_P_length;cbn;lia. Qed.
Lemma sf_tail1_pairs : forall k,sf_pairs(sf_tail1 k)=2*k+2.
Proof. intro k;unfold sf_tail1;rewrite sf_pairs_app,sf_p_pairs;cbn[sf_pairs];rewrite sf_pairs_app,sf_p_pairs;cbn;lia. Qed.
Lemma sf_tail2_pairs : forall k,sf_pairs(sf_tail2 k)=2*k+2.
Proof. intro k;unfold sf_tail2;rewrite sf_pairs_app,sf_p_pairs;cbn[sf_pairs];rewrite sf_pairs_app,sf_p_pairs;cbn;lia. Qed.
Lemma sf_X_step : forall k b l,
 csteps s56_tm(18*k+11)(StA,(sf_X k(S b)l,S0,[]))=Some(StA,(sf_Y k b l,S0,[])).
Proof. intros;exact(sf_X_pass k S2(repeat S2 b++l)[](or_introl eq_refl)). Qed.
Lemma sf_Y_step : forall k b l,
 csteps s56_tm(18*k+15)(StA,(sf_Y k(S b)l,S0,[]))=Some(StA,(sf_Z k b l,S0,[])).
Proof. intros;exact(sf_Y_pass k S2(repeat S2 b++l)[](or_introl eq_refl)). Qed.
Lemma sf_Z_step : forall k b l,
 csteps s56_tm(18*k+21)(StA,(sf_Z k(S b)l,S0,[]))=Some(StA,(sf_X(S k)b l,S0,[])).
Proof. intros;exact(sf_Z_pass k S2(repeat S2 b++l)[](or_introl eq_refl)). Qed.
Lemma sf_cap_one : forall k,csteps s56_tm(52*k+47)(StA,(sf_X k 1[S3],S0,[]))=
 Some(sf_G(6*k+5)).
Proof.
 intro k.
 assert(E2:csteps s56_tm(18*k+15)(StA,(sf_Y k 0[S3],S0,[]))=
 Some(StA,(s56_in(sf_tail1 k),S0,[]))).
 {rewrite sf_tail1_in;exact(sf_Y_pass k S3[][](or_intror eq_refl)). }
 pose proof(sf_fallback(sf_tail1 k))as EF;rewrite sf_tail1_length,sf_tail1_pairs in EF.
 specialize(EF(ltac:(lia)));replace(2*(6*k+6)+2*(2*k+2)+5)with(16*k+21)in EF by lia.
 replace(6*k+6-1)with(6*k+5)in EF by lia.
 replace(52*k+47)with((18*k+11)+((18*k+15)+(16*k+21)))by lia.
 rewrite csteps_add,sf_X_step,csteps_add,E2;exact EF.
Qed.
Lemma sf_cap_two : forall k,csteps s56_tm(70*k+72)(StA,(sf_X k 2[S3],S0,[]))=
 Some(sf_G(6*k+7)).
Proof.
 intro k.
 assert(E3:csteps s56_tm(18*k+21)(StA,(sf_Z k 0[S3],S0,[]))=
 Some(StA,(s56_in(sf_tail2 k),S0,[]))).
 {rewrite sf_tail2_in;exact(sf_Z_pass k S3[][](or_intror eq_refl)). }
 pose proof(sf_fallback(sf_tail2 k))as EF;rewrite sf_tail2_length,sf_tail2_pairs in EF.
 specialize(EF(ltac:(lia)));replace(2*(6*k+8)+2*(2*k+2)+5)with(16*k+25)in EF by lia.
 replace(6*k+8-1)with(6*k+7)in EF by lia.
 replace(70*k+72)with((18*k+11)+((18*k+15)+((18*k+21)+(16*k+25))))by lia.
 rewrite csteps_add,sf_X_step,csteps_add,sf_Y_step,csteps_add,E3;exact EF.
Qed.
Lemma sf_triple : forall k b,csteps s56_tm(54*k+47)(StA,(sf_X k(b+3)[S3],S0,[]))=
 Some(StA,(sf_X(S k)b[S3],S0,[])).
Proof.
 intros;replace(b+3)with(S(S(S b)))by lia.
 replace(54*k+47)with((18*k+11)+((18*k+15)+(18*k+21)))by lia.
 rewrite csteps_add,sf_X_step,csteps_add,sf_Y_step,sf_Z_step;reflexivity.
Qed.
Lemma sf_iter : forall n k b,
 csteps s56_tm(27*n*n+(54*k+20)*n)(StA,(sf_X k(3*n+b)[S3],S0,[]))=
 Some(StA,(sf_X(k+n)b[S3],S0,[])).
Proof.
 induction n as[|n IH];intros k b.
 - replace(27*0*0+(54*k+20)*0)with 0 by lia;replace(3*0+b)with b by lia;replace(k+0)with k by lia;reflexivity.
 - replace(3*S n+b)with((3*n+b)+3)by lia.
   replace(27*S n*S n+(54*k+20)*S n)with
   ((54*k+47)+(27*n*n+(54*S k+20)*n))by nia.
   rewrite csteps_add,sf_triple,IH;replace(S k+n)with(k+S n)by lia;reflexivity.
Qed.
Theorem sf_reset_one : forall n,csteps s56_tm(27*n*n+72*n+47)(sf_G(3*n+1))=
 Some(sf_G(6*n+5)).
Proof.
 intro n;replace(27*n*n+72*n+47)with((27*n*n+(54*0+20)*n)+(52*n+47))by nia.
 change(csteps s56_tm((27*n*n+(54*0+20)*n)+(52*n+47))
 (StA,(sf_X 0(3*n+1)[S3],S0,[]))=Some(sf_G(6*n+5))).
 rewrite csteps_add,sf_iter;cbn[Nat.add];apply sf_cap_one.
Qed.
Theorem sf_reset_two : forall n,csteps s56_tm(27*n*n+90*n+72)(sf_G(3*n+2))=
 Some(sf_G(6*n+7)).
Proof.
 intro n;replace(27*n*n+90*n+72)with((27*n*n+(54*0+20)*n)+(70*n+72))by nia.
 change(csteps s56_tm((27*n*n+(54*0+20)*n)+(70*n+72))
 (StA,(sf_X 0(3*n+2)[S3],S0,[]))=Some(sf_G(6*n+7))).
 rewrite csteps_add,sf_iter;cbn[Nat.add];apply sf_cap_two.
Qed.
Definition sf_safe cc := exists n,cc=sf_G(3*n+1) \/cc=sf_G(3*n+2).
Lemma sf_safe_next : forall cc,sf_safe cc->exists t cc',0<t /\sf_safe cc' /\
 csteps s56_tm t cc=Some cc'.
Proof.
 intros cc(n&[E|E]);subst cc.
 - exists(27*n*n+72*n+47),(sf_G(6*n+5));split;[nia|split;[|apply sf_reset_one]].
   exists(2*n+1);right;f_equal;lia.
 - exists(27*n*n+90*n+72),(sf_G(6*n+7));split;[nia|split;[|apply sf_reset_two]].
   exists(2*n+2);left;f_equal;lia.
Qed.
Lemma sf_entry : csteps s56_tm 14 c0=Some(sf_G 1).
Proof. reflexivity. Qed.
Lemma sf_returns : forall N,exists t cc,N<=t /\sf_safe cc /\csteps s56_tm t c0=Some cc.
Proof.
 intro N;induction N as[|N IH].
 - exists 14,(sf_G 1);split;[lia|split;[exists 0;left;reflexivity|exact sf_entry]].
 - destruct IH as(t&cc&Ht&Hsafe&E);destruct(sf_safe_next cc Hsafe)as(k&cc'&Hk&HS&E').
   exists(t+k),cc';repeat split;try lia;auto;rewrite csteps_add,E;exact E'.
Qed.
Lemma sf_cut_form : forall cc,sf_safe cc->exists l,cc=(StA,(l,S0,[])).
Proof. intros cc(n&[E|E]);subst cc;eexists;reflexivity. Qed.
Theorem sf_A_recurrent : forall N,exists t,N<=t /\VisitsAt s56_tm StA t.
Proof.
 intro N;destruct(sf_returns N)as(t&cc&Ht&HS&E);destruct(sf_cut_form cc HS)as(l&->).
 exists t;split;[exact Ht|];exists(lift(StA,(l,S0,[])));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem sf_B_recurrent : forall N,exists t,N<=t /\VisitsAt s56_tm StB t.
Proof.
 intro N;destruct(sf_returns N)as(t&cc&Ht&HS&E);destruct(sf_cut_form cc HS)as(l&->).
 exists(t+1);split;[lia|];exists(lift(co_back StB l[S1]));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;reflexivity.
Qed.
Theorem sf_nonhalt : NonHalt s56_tm.
Proof.
 intros n Hnone;destruct(sf_returns n)as(t&cc&Ht&HS&E).
 pose proof(csteps_lift s56_tm t c0 cc E)as Er;rewrite lift_c0 in Er.
 destruct(stepn_prefix s56_tm n t InitES(lift cc)Ht Er)as(c&Ec&_);congruence.
Qed.
Theorem sf_state_zero : QHBound 0 s56_tm.
Proof.
 intros q s[_ Hquiet];destruct q.
 - destruct(sf_A_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
 - destruct(sf_B_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
Qed.
Theorem sf_sound : NonHalt s56_tm /\QHBound 0 s56_tm.
Proof. split;[exact sf_nonhalt|exact sf_state_zero]. Qed.
Print Assumptions sf_sound.
