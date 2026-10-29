(** Outer wrappers for the two admitted odd residues. All remaining helper
    premises stay explicit until the independently owned Odd module closes them. *)
From Coq Require Import List Arith Lia.
From BBB24 Require Import Statement Spec CTape Census.
From BBB24Burn26S052Counter Require Import Core.
Import ListNotations.
Definition sh_word a b := repeat S1 a++repeat S3 b++[S0].
Definition sh_AF a b r := sh_front StA(sh_word a b)r.
Definition sh_carry a b r := sh_back StB(repeat S3 b++[S0])(repeat S3 a++r).
Definition sh_reach c d := exists t,csteps sh_tm t c=Some d.
Lemma sh_reach_refl : forall c,sh_reach c c.
Proof. intro c;exists 0;reflexivity. Qed.
Lemma sh_reach_trans : forall a b c,sh_reach a b->sh_reach b c->sh_reach a c.
Proof. intros a b c(n&E)(m&F);exists(n+m);rewrite csteps_add,E;exact F. Qed.
Lemma sh_right_twos_reach : forall a b n r,
 sh_reach(sh_AF a b(repeat S2 n++r))(sh_AF(n+a)b r).
Proof.
 intros;exists n;unfold sh_AF,sh_word;rewrite sh_A_right_twos.
 rewrite sh_repeat_join;reflexivity.
Qed.
Lemma sh_small_pair : forall n r,
 csteps sh_tm 10(sh_AF 1(S(S n))(S3::S3::r))=
 Some(sh_AF 1 n(S3::S3::S2::S2::r)).
Proof. intros;reflexivity. Qed.
Lemma sh_two_even : forall n r,
 csteps sh_tm(12*n+6)(sh_AF 1(2*n)(S3::S3::r))=
 Some(sh_AF(2*n+1)2 r).
Proof.
 induction n;intro r.
 - exact(sh_blank_single 0 r).
 - replace(12*S n+6)with(10+((12*n+6)+2))by lia.
   replace(2*S n)with(S(S(2*n)))at 1 by lia.
   rewrite csteps_add,sh_small_pair,csteps_add,IHn.
   unfold sh_AF,sh_word;change(csteps sh_tm 2
   (sh_front StA(repeat S1(2*n+1)++[S3;S3;S0])(S2::S2::r))=
   Some(sh_front StA(repeat S1(2*S n+1)++[S3;S3;S0])r)).
   change(csteps sh_tm 2(sh_front StA(repeat S1(2*n+1)++[S3;S3;S0])(repeat S2 2++r))=Some(sh_front StA(repeat S1(2*S n+1)++[S3;S3;S0])r)).
   rewrite sh_A_right_twos,sh_repeat_join.
   replace(2+(2*n+1))with(2*S n+1)by lia;reflexivity.
Qed.
Lemma sh_two_odd : forall n r,
 csteps sh_tm(10*n+11)(sh_AF 1(2*n+1)(S3::S3::r))=
 Some(sh_AF 1 0(S3::(repeat S2(2*n+2)++r))).
Proof.
 induction n;intro r.
 - replace(2*0+1)with 1 by lia;replace(2*0+2)with 2 by lia;reflexivity.
 - replace(10*S n+11)with(10+(10*n+11))by lia.
   replace(2*S n+1)with(S(S(2*n+1)))by lia.
   rewrite csteps_add,sh_small_pair,IHn.
   replace(2*S n+2)with(S(S(2*n+2)))by lia.
   unfold sh_AF,sh_word;rewrite !sh_repeat_shift;reflexivity.
Qed.
Lemma sh_three_two : forall n r,
 csteps sh_tm(12*n+26)(sh_AF 3(2*n+2)(S3::S3::r))=
 Some(sh_AF 1(2*n+6)r).
Proof.
 intros;replace(12*n+26)with(5+((10*n+11)+(2*n+10)))by lia.
 unfold sh_AF,sh_word at 1;replace(2*n+2)with(S(2*n+1))by lia.
 rewrite csteps_add.
 change(csteps sh_tm((10*n+11)+(2*n+10))
 (sh_AF 1(2*n+1)(S3::S3::S2::S2::S3::r))=Some(sh_AF 1(2*n+6)r)).
 rewrite csteps_add,sh_two_odd.
 replace(2*n+10)with((2*n+4)+6)by lia.
 assert(Ew:repeat S2(2*n+2)++S2::S2::S3::r=repeat S2(2*n+4)++S3::r).
 {replace(2*n+4)with((2*n+2)+2)by lia;rewrite (repeat_app S2(2*n+2)2),<-app_assoc;reflexivity. }
 unfold sh_AF,sh_word;rewrite Ew;change(csteps sh_tm((2*n+4)+6)
 (sh_front StA[S1;S0](S3::(repeat S2(2*n+4)++S3::r)))=
 Some(sh_front StA(S1::(repeat S3(2*n+6)++[S0]))r)).
 rewrite sh_blank_single;replace(2*n+4+2)with(2*n+6)by lia;reflexivity.
Qed.
Lemma sh_seven_odd_bridge : forall j r,
 csteps sh_tm(12*j+15)(sh_AF 7(2*j+1)(S3::r))=
 Some(sh_H j(S3::S3::S3::S2::S2::r)).
Proof.
 intros;replace(12*j+15)with(8+(10*j+(2*j+7)))by lia;rewrite csteps_add.
 change(csteps sh_tm(10*j+(2*j+7))
 (sh_back StB(repeat S3(2*j+1)++[S0])(S3::S3::S3::S3::S3::S3::S2::S2::r))=
 Some(sh_H j(S3::S3::S3::S2::S2::r))).
 rewrite repeat_app,<-app_assoc;cbn[repeat app];rewrite csteps_add,sh_pairs,sh_odd_boundary.
 unfold sh_H;replace(S(2*j))with(2*j+1)by lia;reflexivity.
Qed.
Lemma sh_start_zero : forall a b r,
 csteps sh_tm(a+1)(StA,(sh_word a b,S0,r))=Some(sh_carry a b(S1::r)).
Proof.
 intros;replace(a+1)with(1+a)by lia;rewrite csteps_add.
 change(csteps sh_tm a(sh_back StB(repeat S1 a++repeat S3 b++[S0])(S1::r))=
 Some(sh_carry a b(S1::r))).
 rewrite sh_B_left_ones;reflexivity.
Qed.
Lemma sh_start_one : forall a b r,
 csteps sh_tm(a+1)(sh_AF a b(S1::r))=Some(sh_carry a b(S2::r)).
Proof.
 intros;replace(a+1)with(1+a)by lia;rewrite csteps_add.
 change(csteps sh_tm a(sh_back StB(repeat S1 a++repeat S3 b++[S0])(S2::r))=
 Some(sh_carry a b(S2::r))).
 rewrite sh_B_left_ones;reflexivity.
Qed.
Lemma sh_finish_two : forall a b,
 csteps sh_tm 1(sh_AF a b[S2])=Some(sh_main(S a)b).
Proof. intros;reflexivity. Qed.
Lemma sh_carry_two : forall n r,
 csteps sh_tm(12*n+13)(sh_carry 2(2*n)(S1::r))=
 Some(sh_AF 2(2*n)(S2::r)).
Proof.
 intros;replace(12*n+13)with(10*n+(5+((2*n+2)+6)))by lia.
 unfold sh_carry;cbn[repeat app];rewrite csteps_add,sh_pairs,csteps_add.
 change(csteps sh_tm((2*n+2)+6)
 (sh_front StB[S0](S2::S2::(repeat S2(2*n)++S1::r)))=
 Some(sh_AF 2(2*n)(S2::r))).
 replace(2*n+2)with(S(S(2*n)))by lia.
 pose proof(sh_B_right_twos(S(S(2*n)))[S0](S1::r))as E;cbn[repeat app]in E.
 rewrite csteps_add,E;reflexivity.
Qed.
Lemma sh_carry_one : forall b r,
 csteps sh_tm 6(sh_carry 1(b+2)(S2::r))=Some(sh_AF 3 b(S2::r)).
Proof. intros;replace(b+2)with(S(S b))by lia;reflexivity. Qed.
Lemma sh_carry_three_even : forall n r,
 csteps sh_tm(12*n+8)(sh_carry 3(2*n)r)=Some(sh_AF 1(2*n+2)r).
Proof. intros;apply sh_even. Qed.
Lemma sh_carry_four_even : forall n r,
 csteps sh_tm(12*n+13)(sh_carry 4(2*n)r)=Some(sh_AF 3(2*n+1)r).
Proof.
 intros;replace(12*n+13)with((12*n+8)+5)by lia;rewrite csteps_add.
 unfold sh_carry;change(match csteps sh_tm(12*n+8)
 (sh_back StB(repeat S3(2*n)++[S0])(S3::S3::S3::S3::r))with
 |Some c=>csteps sh_tm 5 c|None=>None end=Some(sh_AF 3(2*n+1)r)).
 rewrite sh_even;replace(2*n+2)with(S(2*n+1))by lia;reflexivity.
Qed.
Lemma sh_big_even_prepare : forall a r,
 csteps sh_tm 50(sh_carry(a+5)2 r)=Some(sh_AF 5 2(repeat S3 a++r)).
Proof.
 intros;replace(a+5)with(3+(2+a))by lia;unfold sh_carry;cbn[repeat app].
 replace 50 with(20+30)by lia;rewrite csteps_add.
 change(match csteps sh_tm 20
 (sh_back StB(repeat S3(2*1)++[S0])(S3::S3::S3::(repeat S3(2+a)++r)))with
 |Some c=>csteps sh_tm 30 c|None=>None end=Some(sh_AF 5 2(repeat S3 a++r))).
 pose proof(sh_even 1(repeat S3(2+a)++r))as E;cbn[repeat app Nat.mul Nat.add]in E;cbn[repeat app Nat.mul Nat.add];rewrite E;change(csteps sh_tm(12*2+6)
 (sh_AF 1(2*2)(S3::S3::(repeat S3 a++r)))=Some(sh_AF 5 2(repeat S3 a++r))).
 apply sh_two_even.
Qed.
Lemma sh_repeat_split : forall(x:Sym)n m r,
 repeat x(n+m)++r=repeat x n++repeat x m++r.
Proof. intros;rewrite repeat_app,<-app_assoc;reflexivity. Qed.
Lemma sh_before_even_five : forall n r,
 sh_reach(sh_AF 5 2(repeat S3(S n)++r))(sh_AF 5 3(repeat S3 n++r)).
Proof. intros;exists 33;exact(sh_five_even 1(repeat S3 n++r)). Qed.

Section ConditionalOdd.
Variable HH2 : forall k r,sh_reach(sh_H(3*k+2)r)(sh_AF 5(6*k+3)r).
Variable HH3 : forall k r,sh_reach(sh_H(3*k+3)r)(sh_AF 7(6*k+3)r).
Variable HHP : forall k r,sh_reach(sh_H(3*k+1)r)
 (sh_AF 1 0(S3::(repeat S2(6*k+4)++r))).
Variable HHT : forall k r,sh_reach(sh_AF 5 3(repeat S3(6*k)++r))(sh_AF 5(6*k+3)r).
Lemma sh_bad_first : forall k r,
 sh_reach(sh_H(3*k+1)(S3::r))(sh_AF 1(6*k+6)r).
Proof.
 intros;eapply sh_reach_trans;[apply HHP|].
 exists(6*k+4+6);replace(6*k+6)with((6*k+4)+2)by lia;apply sh_blank_single.
Qed.
Lemma sh_bad_guard : forall k r,
 sh_reach(sh_H(3*k+1)(S3::S2::S2::r))(sh_AF 3(6*k+6)r).
Proof.
 intros;eapply sh_reach_trans;[apply sh_bad_first|].
 exact(sh_right_twos_reach 1(6*k+6)2 r).
Qed.
Lemma sh_carry_three_odd_two : forall k r,
 sh_reach(sh_carry 3(6*k+5)r)(sh_AF 5(6*k+3)r).
Proof.
 intros;eapply sh_reach_trans with(b:=sh_H(3*k+2)r);[|apply HH2].
 exists(12*(3*k+2)+7);unfold sh_carry;replace(6*k+5)with(2*(3*k+2)+1)by lia;apply sh_odd_prepare.
Qed.
Lemma sh_carry_three_odd_zero : forall k r,
 sh_reach(sh_carry 3(6*k+7)r)(sh_AF 7(6*k+3)r).
Proof.
 intros;eapply sh_reach_trans with(b:=sh_H(3*k+3)r);[|apply HH3].
 exists(12*(3*k+3)+7);unfold sh_carry;replace(6*k+7)with(2*(3*k+3)+1)by lia;apply sh_odd_prepare.
Qed.
Lemma sh_carry_six_odd : forall k r,
 sh_reach(sh_carry 6(6*k+3)r)(sh_AF(6*k+7)2 r).
Proof.
 intros;eapply sh_reach_trans with(b:=sh_H(3*k+1)(S3::S3::S3::r)).
 - exists(12*(3*k+1)+7);unfold sh_carry;replace(6*k+3)with(2*(3*k+1)+1)by lia;apply sh_odd_prepare.
 - eapply sh_reach_trans;[apply sh_bad_first|].
   exists(12*(3*k+3)+6);replace(6*k+6)with(2*(3*k+3))by lia.
   replace(6*k+7)with(2*(3*k+3)+1)by lia;apply sh_two_even.
Qed.
Lemma sh_seven_one_odd : forall k r,
 sh_reach(sh_AF 7(6*k+3)(S3::r))(sh_AF(6*k+9)2 r).
Proof.
 intros;eapply sh_reach_trans with(b:=sh_H(3*k+1)(S3::S3::S3::S2::S2::r)).
 - exists(12*(3*k+1)+15);replace(6*k+3)with(2*(3*k+1)+1)by lia;apply sh_seven_odd_bridge.
 - eapply sh_reach_trans;[apply sh_bad_first|].
   eapply sh_reach_trans with(b:=sh_AF(6*k+7)2(S2::S2::r)).
   + exists(12*(3*k+3)+6);replace(6*k+6)with(2*(3*k+3))by lia.
     replace(6*k+7)with(2*(3*k+3)+1)by lia;apply sh_two_even.
   + replace(6*k+9)with(2+(6*k+7))by lia;exact(sh_right_twos_reach(6*k+7)2 2 r).
Qed.
Lemma sh_carry_eight_odd : forall k r,
 sh_reach(sh_carry 8(6*k+3)r)(sh_AF(6*k+9)2 r).
Proof.
 intros;eapply sh_reach_trans with(b:=sh_H(3*k+1)(S3::S3::S3::S3::S3::r)).
 - exists(12*(3*k+1)+7);unfold sh_carry;replace(6*k+3)with(2*(3*k+1)+1)by lia;apply sh_odd_prepare.
 - eapply sh_reach_trans;[apply sh_bad_first|].
   eapply sh_reach_trans with(b:=sh_H(3*k+3)(S3::r)).
   + exists(12*(3*k+3)+6);replace(6*k+6)with(2*(3*k+3))by lia.
     unfold sh_H;exact(sh_two_even(3*k+3)(S3::S3::r)).
   + eapply sh_reach_trans;[apply HH3|apply sh_seven_one_odd].
Qed.
Lemma sh_five_odd_finish : forall k r,
 sh_reach(sh_AF 5(6*k+3)(S3::r))(sh_AF 3(6*k+6)r).
Proof.
 intros;eapply sh_reach_trans;[|apply sh_bad_guard].
 exists(12*(3*k+1)+13);replace(6*k+3)with(2*(3*k+1)+1)by lia;apply sh_five_odd_bridge.
Qed.
Lemma sh_carry_big_seven : forall k r,
 sh_reach(sh_carry(6*k+7)2 r)(sh_AF 3(6*k+6)r).
Proof.
 intros;eapply sh_reach_trans with(b:=sh_AF 5 2(repeat S3(6*k+2)++r)).
 - exists 50;replace(6*k+7)with((6*k+2)+5)by lia;apply sh_big_even_prepare.
 - eapply sh_reach_trans with(b:=sh_AF 5 3(repeat S3(6*k+1)++r)).
   + replace(6*k+2)with(S(6*k+1))by lia;apply sh_before_even_five.
   + eapply sh_reach_trans;[|apply sh_five_odd_finish].
     replace(6*k+1)with(6*k+1)by lia;rewrite sh_repeat_split;apply HHT.
Qed.
Lemma sh_carry_big_nine : forall k r,
 sh_reach(sh_carry(6*k+9)2 r)(sh_AF 1(6*k+10)r).
Proof.
 intros;eapply sh_reach_trans with(b:=sh_AF 5 2(repeat S3(6*k+4)++r)).
 - exists 50;replace(6*k+9)with((6*k+4)+5)by lia;apply sh_big_even_prepare.
 - eapply sh_reach_trans with(b:=sh_AF 5 3(repeat S3(6*k+3)++r)).
   + replace(6*k+4)with(S(6*k+3))by lia;apply sh_before_even_five.
   + eapply sh_reach_trans with(b:=sh_AF 5(6*k+3)(S3::S3::S3::r)).
     * rewrite sh_repeat_split;apply HHT.
     * eapply sh_reach_trans;[apply sh_five_odd_finish|].
       exists(12*(3*k+2)+26);replace(6*k+6)with(2*(3*k+2)+2)by lia.
       replace(6*k+10)with(2*(3*k+2)+6)by lia;apply sh_three_two.
Qed.
End ConditionalOdd.
Lemma sh_main_two_even : forall n,
 csteps sh_tm(12*n+17)(sh_main 2(2*n))=Some(sh_main 3(2*n)).
Proof.
 intro n;replace(12*n+17)with(3+((12*n+13)+1))by lia.
 change(csteps sh_tm(3+((12*n+13)+1))(StA,(sh_word 2(2*n),S0,[]))=Some(sh_main 3(2*n))).
 pose proof(sh_start_zero 2(2*n)[])as E;cbn[Nat.add]in E;rewrite csteps_add,E,csteps_add,sh_carry_two.
 apply sh_finish_two.
Qed.
Lemma sh_main_three_even : forall n,
 sh_reach(sh_main 3(2*n))(sh_main 4(2*n)).
Proof.
 intro n;eapply sh_reach_trans with(b:=sh_carry 3(2*n)[S1]).
 - exists 4;exact(sh_start_zero 3(2*n)[]).
 - eapply sh_reach_trans with(b:=sh_AF 1(2*n+2)[S1]).
   + exists(12*n+8);apply sh_carry_three_even.
   + eapply sh_reach_trans with(b:=sh_carry 1(2*n+2)[S2]).
     * exists 2;exact(sh_start_one 1(2*n+2)[]).
     * eapply sh_reach_trans with(b:=sh_AF 3(2*n)[S2]).
       -- exists 6;apply sh_carry_one.
       -- exists 1;apply sh_finish_two.
Qed.

Section ConditionalMain.
Variable HH2 : forall k r,sh_reach(sh_H(3*k+2)r)(sh_AF 5(6*k+3)r).
Variable HH3 : forall k r,sh_reach(sh_H(3*k+3)r)(sh_AF 7(6*k+3)r).
Variable HHP : forall k r,sh_reach(sh_H(3*k+1)r)
 (sh_AF 1 0(S3::(repeat S2(6*k+4)++r))).
Variable HHT : forall k r,sh_reach(sh_AF 5 3(repeat S3(6*k)++r))(sh_AF 5(6*k+3)r).
Lemma sh_main_four_two : forall k,
 sh_reach(sh_main 4(6*k+4))(sh_main 6(6*k+3)).
Proof.
 intro k;eapply sh_reach_trans with(b:=sh_carry 4(6*k+4)[S1]).
 - exists 5;exact(sh_start_zero 4(6*k+4)[]).
 - eapply sh_reach_trans with(b:=sh_AF 3(6*k+5)[S1]).
   + exists(12*(3*k+2)+13);replace(6*k+4)with(2*(3*k+2))by lia;
     replace(6*k+5)with(2*(3*k+2)+1)by lia;apply sh_carry_four_even.
   + eapply sh_reach_trans with(b:=sh_carry 3(6*k+5)[S2]).
     * exists 4;exact(sh_start_one 3(6*k+5)[]).
     * eapply sh_reach_trans with(b:=sh_AF 5(6*k+3)[S2]).
       -- apply sh_carry_three_odd_two;exact HH2.
       -- exists 1;apply sh_finish_two.
Qed.
Lemma sh_main_six : forall k,
 sh_reach(sh_main 6(6*k+3))(sh_main 4(6*k+6)).
Proof.
 intro k;eapply sh_reach_trans with(b:=sh_carry 6(6*k+3)[S1]).
 - exists 7;exact(sh_start_zero 6(6*k+3)[]).
 - eapply sh_reach_trans with(b:=sh_AF(6*k+7)2[S1]).
   + apply sh_carry_six_odd;exact HHP.
   + eapply sh_reach_trans with(b:=sh_carry(6*k+7)2[S2]).
     * exists(6*k+7+1);apply sh_start_one.
     * eapply sh_reach_trans with(b:=sh_AF 3(6*k+6)[S2]).
       -- apply sh_carry_big_seven;assumption.
       -- exists 1;apply sh_finish_two.
Qed.
Lemma sh_main_four_zero : forall k,
 sh_reach(sh_main 4(6*k+6))(sh_main 8(6*k+3)).
Proof.
 intro k;eapply sh_reach_trans with(b:=sh_carry 4(6*k+6)[S1]).
 - exists 5;exact(sh_start_zero 4(6*k+6)[]).
 - eapply sh_reach_trans with(b:=sh_AF 3(6*k+7)[S1]).
   + exists(12*(3*k+3)+13);replace(6*k+6)with(2*(3*k+3))by lia;
     replace(6*k+7)with(2*(3*k+3)+1)by lia;apply sh_carry_four_even.
   + eapply sh_reach_trans with(b:=sh_carry 3(6*k+7)[S2]).
     * exists 4;exact(sh_start_one 3(6*k+7)[]).
     * eapply sh_reach_trans with(b:=sh_AF 7(6*k+3)[S2]).
       -- apply sh_carry_three_odd_zero;exact HH3.
       -- exists 1;apply sh_finish_two.
Qed.
Lemma sh_main_eight : forall k,
 sh_reach(sh_main 8(6*k+3))(sh_main 2(6*k+10)).
Proof.
 intro k;eapply sh_reach_trans with(b:=sh_carry 8(6*k+3)[S1]).
 - exists 9;exact(sh_start_zero 8(6*k+3)[]).
 - eapply sh_reach_trans with(b:=sh_AF(6*k+9)2[S1]).
   + apply sh_carry_eight_odd;assumption.
   + eapply sh_reach_trans with(b:=sh_carry(6*k+9)2[S2]).
     * exists(6*k+9+1);apply sh_start_one.
     * eapply sh_reach_trans with(b:=sh_AF 1(6*k+10)[S2]).
       -- apply sh_carry_big_nine;assumption.
       -- exists 1;apply sh_finish_two.
Qed.
Lemma sh_six_tail : forall k,
 sh_reach(sh_main 3(6*k+4))(sh_main 2(6*k+10)).
Proof.
 intro k;eapply sh_reach_trans with(b:=sh_main 4(6*k+4)).
 - replace(6*k+4)with(2*(3*k+2))by lia;apply sh_main_three_even.
 - eapply sh_reach_trans;[apply sh_main_four_two|].
   eapply sh_reach_trans;[apply sh_main_six|].
   eapply sh_reach_trans;[apply sh_main_four_zero|apply sh_main_eight].
Qed.
Theorem sh_main_next_conditional : forall k,exists t,0<t /\
 csteps sh_tm t(sh_main 2(6*k+4))=Some(sh_main 2(6*(S k)+4)).
Proof.
 intro k;destruct(sh_six_tail k)as(t&E).
 exists((12*(3*k+2)+17)+t);split;[lia|].
 replace(6*S k+4)with(6*k+10)by lia;rewrite csteps_add.
 replace(6*k+4)with(2*(3*k+2))at 1 by lia;rewrite sh_main_two_even;replace(2*(3*k+2))with(6*k+4)by lia;exact E.
Qed.
Lemma sh_returns_conditional : forall N,exists t k,N<=t /\
 csteps sh_tm t c0=Some(sh_main 2(6*k+4)).
Proof.
 intro N;induction N as[|N IH].
 - exists 142,0;split;[lia|exact sh_entry].
 - destruct IH as(t&k&Ht&E);destruct(sh_main_next_conditional k)as(n&Hn&E').
   exists(t+n),(S k);split;[lia|];rewrite csteps_add,E;exact E'.
Qed.
Theorem sh_A_recurrent_conditional : forall N,exists t,N<=t /\VisitsAt sh_tm StA t.
Proof.
 intro N;destruct(sh_returns_conditional N)as(t&k&Ht&E);exists t;split;[exact Ht|].
 exists(lift(sh_main 2(6*k+4)));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem sh_B_recurrent_conditional : forall N,exists t,N<=t /\VisitsAt sh_tm StB t.
Proof.
 intro N;destruct(sh_returns_conditional N)as(t&k&Ht&E);exists(t+1);split;[lia|].
 exists(lift(sh_back StB(sh_word 2(6*k+4))[S1]));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;reflexivity.
Qed.
Theorem sh_sound_conditional : NonHalt sh_tm /\QHBound 0 sh_tm.
Proof.
 split.
 - intros n Hnone;destruct(sh_returns_conditional n)as(t&k&Ht&E).
   pose proof(csteps_lift sh_tm t c0(sh_main 2(6*k+4))E)as Er;rewrite lift_c0 in Er.
   destruct(stepn_prefix sh_tm n t InitES(lift(sh_main 2(6*k+4)))Ht Er)as(c&Ec&_);congruence.
 - intros q s[_ Hquiet];destruct q.
   + destruct(sh_A_recurrent_conditional(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
   + destruct(sh_B_recurrent_conditional(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
Qed.
End ConditionalMain.
