(** Universal odd normalizers over the frozen S052 foundation. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn26S052Counter Require Import Core.
Import ListNotations.
Definition so_F a b r:=sh_front StA(repeat S1 a++repeat S3 b++[S0])r.
Lemma so_drain10 : forall l r,
 csteps sh_tm 10(sh_front StA(S1::S1::S1::S3::S3::l)(S3::r))=
 Some(sh_front StA(S1::S1::S1::l)(S3::S2::S2::r)).
Proof. reflexivity. Qed.
Lemma so_drain : forall j r,
 csteps sh_tm(10*j+6)(so_F 3(2*j)(S3::r))=
 Some(sh_front StA[S1;S0](S3::(repeat S2(2*j+2)++r))).
Proof.
 induction j;intro r.
 - change(csteps sh_tm 6(sh_front StA(repeat S1(1+2)++[S0])(S3::r))=
   Some(sh_front StA[S1;S0](S3::(repeat S2 2++r))));exact(sh_fall 1 r).
 - replace(10*S j+6)with(10+(10*j+6))by lia.
   unfold so_F at 1;replace(2*S j)with(S(S(2*j)))by lia;cbn[repeat app].
   rewrite csteps_add,so_drain10.
   change(csteps sh_tm(10*j+6)(so_F 3(2*j)(S3::S2::S2::r))=
   Some(sh_front StA[S1;S0](S3::(repeat S2(S(S(2*j))+2)++r)))).
   rewrite IHj.
   replace(S(S(2*j))+2)with(S(S(2*j+2)))by lia;cbn[repeat app].
   rewrite sh_repeat_shift,sh_repeat_shift;reflexivity.
Qed.
Lemma so_pair10 : forall l r,
 csteps sh_tm 10(sh_front StA(S1::S3::S3::l)(S3::S3::r))=
 Some(sh_front StA(S1::l)(S3::S3::S2::S2::r)).
Proof. reflexivity. Qed.
Lemma so_pair_scan : forall j r,
 csteps sh_tm(10*j)(so_F 1(2*j)(S3::S3::r))=
 Some(sh_front StA[S1;S0](S3::S3::(repeat S2(2*j)++r))).
Proof.
 induction j;intro r;[reflexivity|].
 replace(10*S j)with(10+10*j)by lia.
 unfold so_F at 1;replace(2*S j)with(S(S(2*j)))by lia;cbn[repeat app].
 rewrite csteps_add,so_pair10.
 change(csteps sh_tm(10*j)(so_F 1(2*j)(S3::S3::S2::S2::r))=
 Some(sh_front StA[S1;S0](S3::S3::(repeat S2(S(S(2*j)))++r)))).
 rewrite IHj;replace(2*S j)with(S(S(2*j)))by lia;cbn[repeat app].
 rewrite sh_repeat_shift,sh_repeat_shift;reflexivity.
Qed.
Lemma so_carry : forall m r,
 csteps sh_tm(m+6)(sh_front StA[S1;S0](S3::S3::(repeat S2 m++r)))=
 Some(sh_front StA(repeat S1(S m)++[S3;S3;S0])r).
Proof.
 intros m r;replace(m+6)with(6+m)by lia;rewrite csteps_add.
 change(csteps sh_tm m(sh_front StA[S1;S3;S3;S0](repeat S2 m++r))=
 Some(sh_front StA(repeat S1(S m)++[S3;S3;S0])r)).
 rewrite sh_A_right_twos,sh_repeat_shift;reflexivity.
Qed.
Lemma so_two_threes : forall j r,
 csteps sh_tm(12*j+6)(so_F 1(2*j)(S3::S3::r))=
 Some(sh_front StA(repeat S1(2*j+1)++[S3;S3;S0])r).
Proof.
 intros j r;replace(12*j+6)with(10*j+(2*j+6))by lia.
 rewrite csteps_add,so_pair_scan,so_carry.
 replace(S(2*j))with(2*j+1)by lia;reflexivity.
Qed.
Lemma so_prefix49 : forall r,
 csteps sh_tm 49(sh_front StA[S1;S3;S0](repeat S3 6++r))=Some(sh_H 2 r).
Proof. reflexivity. Qed.
Lemma so_H_reduce : forall n r,
 csteps sh_tm(2*n+58)(sh_H(n+3)r)=
 Some(sh_H 2(repeat S3(2*n)++S2::S2::r)).
Proof.
 intros n r;replace(2*n+58)with(((2*n+6)+3)+49)by lia;unfold sh_H at 1.
 replace(2*(n+3)+1)with(S(2*n+6))by lia.
 rewrite csteps_add,sh_launch.
 replace(2*n+6)with(6+2*n)by lia.
 rewrite repeat_app,<-app_assoc;apply so_prefix49.
Qed.
Fixpoint so_costs k:nat*nat:=match k with
 |0=>(16,0)
 |S k=>let '(b,u):=so_costs k in
  let b':=u+b+78*k+166 in
  let a':=b'+6*S k+17 in
  (b',u+b+114*k+153+a')end.
Definition so_bad_cost k:=fst(so_costs k).
Definition so_train_cost k:=snd(so_costs k).
Definition so_A_cost k:=so_bad_cost k+6*k+17.
Definition so_B_cost k:=2*so_A_cost k+36*k+27.
Lemma so_bad_next : forall k,
 so_bad_cost(S k)=so_train_cost k+so_bad_cost k+78*k+166.
Proof. intro k;unfold so_bad_cost,so_train_cost;cbn[so_costs];destruct(so_costs k);reflexivity. Qed.
Lemma so_A_next : forall k,
 so_A_cost(S k)=so_train_cost k+so_bad_cost k+84*k+189.
Proof. intro k;unfold so_A_cost;rewrite so_bad_next;lia. Qed.
Lemma so_train_next : forall k,
 so_train_cost(S k)=so_train_cost k+so_bad_cost k+114*k+153+so_A_cost(S k).
Proof.
 intro k;unfold so_A_cost,so_train_cost,so_bad_cost;cbn[so_costs];destruct(so_costs k);reflexivity.
Qed.
Definition so_bad k:=forall r,
 csteps sh_tm(so_bad_cost k)(sh_H(3*k+1)r)=
 Some(sh_front StA[S1;S0](S3::(repeat S2(6*k+4)++r))).
Definition so_A k:=forall r,
 csteps sh_tm(so_A_cost k)(sh_H(3*k+2)r)=Some(so_F 5(6*k+3)r).
Definition so_B k:=forall r,
 csteps sh_tm(so_B_cost k)(sh_H(3*k+3)r)=Some(so_F 7(6*k+3)r).
Definition so_train k:=forall r,
 csteps sh_tm(so_train_cost k)(so_F 5 3(repeat S3(6*k)++r))=
 Some(so_F 5(6*k+3)r).
Lemma so_guard : forall k,so_bad k->forall r,
 csteps sh_tm(so_bad_cost k+42*k+37)(so_F 5(6*k+3)(S3::r))=
 Some(so_F 3(6*k+6)r).
Proof.
 intros k HB r;replace(so_bad_cost k+42*k+37)with
 ((12*(3*k+1)+13)+(so_bad_cost k+((6*k+4+6)+2)))by lia.
 unfold so_F at 1;replace(6*k+3)with(2*(3*k+1)+1)by lia.
 rewrite csteps_add,sh_five_odd_bridge,csteps_add,HB.
 rewrite csteps_add,sh_blank_single.
 change(csteps sh_tm 2(sh_front StA(S1::(repeat S3(6*k+4+2)++[S0]))(S2::S2::r))=
 Some(so_F 3(6*k+6)r)).
 pose proof(sh_A_right_twos 2(S1::(repeat S3(6*k+4+2)++[S0]))r)as E;cbn[repeat app]in E;rewrite E.
 unfold so_F;replace(6*k+4+2)with(6*k+6)by lia;reflexivity.
Qed.
Lemma so_five_threes : forall k,so_bad k->forall r,
 csteps sh_tm(so_bad_cost k+114*k+153)(so_F 5(6*k+3)(repeat S3 5++r))=
 Some(sh_front StA(repeat S1(6*k+11)++[S3;S3;S0])r).
Proof.
 intros k HB r;replace(so_bad_cost k+114*k+153)with
 ((so_bad_cost k+42*k+37)+((10*(3*k+3)+6)+((6*k+8+6)+(12*(3*k+5)+6))))by lia.
 cbn[repeat app];rewrite csteps_add,so_guard;[|exact HB].
 replace(6*k+6)with(2*(3*k+3))by lia.
 rewrite csteps_add,so_drain.
 replace(2*(3*k+3)+2)with(6*k+8)by lia.
 rewrite csteps_add,sh_blank_single.
 change(csteps sh_tm(12*(3*k+5)+6)(so_F 1(6*k+8+2)(S3::S3::r))=
 Some(sh_front StA(repeat S1(6*k+11)++[S3;S3;S0])r)).
 replace(6*k+8+2)with(2*(3*k+5))by lia;rewrite so_two_threes.
 replace(2*(3*k+5)+1)with(6*k+11)by lia;reflexivity.
Qed.
Lemma so_prefix_train : forall k,so_train k->forall d r,
 csteps sh_tm(so_train_cost k+6*k+93+2*d)(sh_H(3*k+4+d)r)=
 Some(so_F 5(6*k+3)(repeat S3(2+2*d)++S2::S2::r)).
Proof.
 intros k HT d r;replace(so_train_cost k+6*k+93+2*d)with
 ((2*(3*k+1+d)+58)+(33+so_train_cost k))by lia.
 replace(3*k+4+d)with((3*k+1+d)+3)by lia.
 rewrite csteps_add,so_H_reduce,csteps_add.
 change(match csteps sh_tm 33(sh_H 2(repeat S3(2*(3*k+1+d))++S2::S2::r))with
 |Some cc=>csteps sh_tm(so_train_cost k)cc|None=>None end=
 Some(so_F 5(6*k+3)(repeat S3(2+2*d)++S2::S2::r))).
 assert(E:forall r,csteps sh_tm 33(sh_H 2 r)=Some(so_F 5 3 r))by(intro;reflexivity).
 rewrite E.
 replace(2*(3*k+1+d))with(6*k+(2+2*d))by lia.
 rewrite repeat_app,<-app_assoc;apply HT.
Qed.
Lemma so_bad_step : forall k,so_bad k->so_train k->so_bad(S k).
Proof.
 intros k HB HT r;unfold so_bad_cost at 1;fold(so_bad_cost(S k)).
 replace(so_bad_cost(S k))with
 ((so_train_cost k+6*k+93+2*0)+((so_bad_cost k+42*k+37)+(10*(3*k+3)+6)))
 by(rewrite so_bad_next;lia).
 replace(3*S k+1)with(3*k+4+0)by lia.
 rewrite csteps_add,(so_prefix_train k HT 0 r).
 replace(2+2*0)with 2 by lia;cbn[repeat app].
 rewrite csteps_add,(so_guard k HB).
 replace(6*k+6)with(2*(3*k+3))by lia;rewrite so_drain.
 replace(6*S k+4)with(S(S(2*(3*k+3)+2)))by lia;cbn[repeat app].
 rewrite sh_repeat_shift,sh_repeat_shift;reflexivity.
Qed.
Lemma so_A_step : forall k,so_bad k->so_train k->so_A(S k).
Proof.
 intros k HB HT r.
 replace(so_A_cost(S k))with
 ((so_train_cost k+6*k+93+2*1)+((so_bad_cost k+42*k+37)+
 ((10*(3*k+3)+6)+((6*k+8+6)+(5+2)))))by(rewrite so_A_next;lia).
 replace(3*S k+2)with(3*k+4+1)by lia.
 rewrite csteps_add,(so_prefix_train k HT 1 r).
 replace(2+2*1)with 4 by lia;cbn[repeat app].
 rewrite csteps_add,(so_guard k HB).
 replace(6*k+6)with(2*(3*k+3))by lia;rewrite csteps_add,so_drain.
 replace(2*(3*k+3)+2)with(6*k+8)by lia.
 rewrite csteps_add,sh_blank_single.
 replace(6*k+8+2)with(S(6*k+9))by lia.
 change(csteps sh_tm(5+2)(sh_front StA(S1::S3::(repeat S3(6*k+9)++[S0]))(S3::S2::S2::r))=
 Some(so_F 5(6*S k+3)r)).
 rewrite csteps_add,sh_small_one.
 pose proof(sh_A_right_twos 2(S1::S1::S1::(repeat S3(6*k+9)++[S0]))r)as E;
 cbn[repeat app]in E;rewrite E.
 unfold so_F;replace(6*S k+3)with(6*k+9)by lia;reflexivity.
Qed.
Lemma so_B_step : forall k,so_bad k->so_train k->so_A(S k)->so_B(S k).
Proof.
 intros k HB HT HA r.
 replace(so_B_cost(S k))with
 ((so_train_cost k+6*k+93+2*2)+((so_bad_cost k+114*k+153)+(so_A_cost(S k)+2)))
 by(unfold so_B_cost;rewrite so_A_next;lia).
 replace(3*S k+3)with(3*k+4+2)by lia.
 rewrite csteps_add,(so_prefix_train k HT 2 r).
 replace(2+2*2)with 6 by lia;cbn[repeat app].
 rewrite csteps_add.
 pose proof(so_five_threes k HB(S3::S2::S2::r))as E5;cbn[repeat app]in E5;rewrite E5.
 replace(6*k+11)with(2*(3*S k+2)+1)by lia.
 change(csteps sh_tm(so_A_cost(S k)+2)(sh_H(3*S k+2)(S2::S2::r))=
 Some(so_F 7(6*S k+3)r)).
 rewrite csteps_add,HA.
 exact(sh_A_right_twos 2(repeat S1 5++repeat S3(6*S k+3)++[S0])r).
Qed.
Lemma so_train_step : forall k,so_bad k->so_train k->so_A(S k)->so_train(S k).
Proof.
 intros k HB HT HA r.
 replace(so_train_cost(S k))with
 (so_train_cost k+((so_bad_cost k+114*k+153)+so_A_cost(S k)))by(rewrite so_train_next;lia).
 replace(6*S k)with(6*k+6)by lia;rewrite repeat_app,<-app_assoc.
 rewrite csteps_add,HT.
 replace(6*k+6+3)with(6*S k+3)by lia.
 change(csteps sh_tm((so_bad_cost k+114*k+153)+so_A_cost(S k))
 (so_F 5(6*k+3)(repeat S3 5++S3::r))=Some(so_F 5(6*S k+3)r)).
 rewrite csteps_add,(so_five_threes k HB).
 replace(6*k+11)with(2*(3*S k+2)+1)by lia.
 change(csteps sh_tm(so_A_cost(S k))(sh_H(3*S k+2)r)=Some(so_F 5(6*S k+3)r)).
 apply HA.
Qed.
Theorem so_mutual : forall k,so_bad k /\so_A k /\so_B k /\so_train k.
Proof.
 induction k as[|k[HB[HA[HC HT]]]].
 - repeat split;intro r;reflexivity.
 - pose proof(so_bad_step k HB HT)as HB'.
   pose proof(so_A_step k HB HT)as HA'.
   repeat split.
   + exact HB'.
   + exact HA'.
   + exact(so_B_step k HB HT HA').
   + exact(so_train_step k HB HT HA').
Qed.
Theorem so_bad_prefix : forall k,so_bad k.
Proof. intro k;apply so_mutual. Qed.
Theorem so_normalize_A : forall k,so_A k.
Proof. intro k;apply so_mutual. Qed.
Theorem so_normalize_B : forall k,so_B k.
Proof. intro k;apply so_mutual. Qed.
Theorem so_train_normalize : forall k,so_train k.
Proof. intro k;apply so_mutual. Qed.
Lemma so_cost_balances : forall k,
 so_bad_cost k+60*k+97=113*3^k /\
 so_train_cost k+78*k+226=226*3^k.
Proof.
 induction k as[|k[HB HU]].
 - split;reflexivity.
 - split.
   + rewrite so_bad_next;cbn[Nat.pow];nia.
   + rewrite so_train_next,so_A_next;cbn[Nat.pow];nia.
Qed.
Lemma so_bad_cost_closed : forall k,so_bad_cost k=113*3^k-60*k-97.
Proof. intro k;destruct(so_cost_balances k);lia. Qed.
Lemma so_train_cost_closed : forall k,so_train_cost k=226*3^k-78*k-226.
Proof. intro k;destruct(so_cost_balances k);lia. Qed.
Lemma so_A_cost_closed : forall k,so_A_cost k=113*3^k-54*k-80.
Proof. intro k;unfold so_A_cost;destruct(so_cost_balances k);lia. Qed.
Lemma so_B_cost_closed : forall k,so_B_cost k=226*3^k-72*k-133.
Proof. intro k;unfold so_B_cost,so_A_cost;destruct(so_cost_balances k);lia. Qed.
Theorem so_A_closed : forall k r,
 csteps sh_tm(113*3^k-54*k-80)(sh_H(3*k+2)r)=
 Some(sh_front StA(repeat S1 5++repeat S3(6*k+3)++[S0])r).
Proof. intros k r;rewrite <-so_A_cost_closed;exact(so_normalize_A k r). Qed.
Theorem so_B_closed : forall k r,
 csteps sh_tm(226*3^k-72*k-133)(sh_H(3*k+3)r)=
 Some(sh_front StA(repeat S1 7++repeat S3(6*k+3)++[S0])r).
Proof. intros k r;rewrite <-so_B_cost_closed;exact(so_normalize_B k r). Qed.
Theorem so_bad_guard : forall k r,
 csteps sh_tm(so_bad_cost k+6*k+12)(sh_H(3*k+1)(S3::S2::S2::r))=
 Some(so_F 3(6*k+6)r).
Proof.
 intros k r;replace(so_bad_cost k+6*k+12)with(so_bad_cost k+((6*k+4+6)+2))by lia.
 rewrite csteps_add,so_bad_prefix,csteps_add,sh_blank_single.
 replace(6*k+6)with(6*k+4+2)by lia.
 exact(sh_A_right_twos 2(S1::(repeat S3(6*k+4+2)++[S0]))r).
Qed.
Print Assumptions so_A_closed.
Print Assumptions so_B_closed.
Print Assumptions so_train_normalize.
