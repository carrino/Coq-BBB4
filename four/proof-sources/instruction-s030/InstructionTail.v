(** S030: the exposed binary suffix reaches permanent B0 after two bounces. *)
From Coq Require Import List Arith Lia NArith.
From BBB24 Require Import Statement StatementTr Spec CTape Census Bounds.
From BBB24Burn25S030Finite Require Import Counter BinaryBridge Trace Final.
From BBB24InstructionTails Require Import SingleInstruction.
Import ListNotations.

Lemma s30_instruction_escape : forall a,
 csteps s30_tm (5*a+10) (s30_back StB (repeat S2 a) [S2;S2])=
 Some(StB,([],S0,repeat S0(a+4))).
Proof.
 intro a;replace(5*a+10)with(a+((2*a+3)+(2*(a+2)+3)))by lia.
 rewrite csteps_add.
 rewrite <-(app_nil_r(repeat S2 a))at 1.
 rewrite s30_B_twos,csteps_add;unfold s30_back;cbn[chd ctl].
 rewrite s30_B_bounce;unfold s30_back;cbn[chd ctl].
 rewrite s30_B_bounce;unfold s30_back;cbn[chd ctl].
 rewrite app_nil_r;replace(a+2+2)with(a+4)by lia;reflexivity.
Qed.

Lemma s30_instruction_bounce_before : forall n l r,
 csteps s30_tm(2*n+2)(StB,(l,S0,repeat S0 n++S2::r))=
 Some(StB,(l,S2,repeat S0(n+1)++r)).
Proof.
 intros n l r;replace(2*n+2)with(1+(n+(1+n)))by lia.
 rewrite csteps_add.
 change(csteps s30_tm(n+(1+n))(s30_front StB(S2::l)(repeat S0 n++S2::r))=
 Some(StB,(l,S2,repeat S0(n+1)++r))).
 rewrite csteps_add,s30_B_zeros,csteps_add.
 change(csteps s30_tm n(s30_back StB(repeat S2 n++S2::l)(S0::r))=
 Some(StB,(l,S2,repeat S0(n+1)++r))).
 rewrite s30_B_twos;unfold s30_back;cbn[chd ctl].
 rewrite s30_repeat_more;reflexivity.
Qed.

Lemma s30_instruction_before : forall a,
 csteps s30_tm(5*a+9)(s30_back StB(repeat S2 a)[S2;S2])=
 Some(StB,([],S2,repeat S0(a+3))).
Proof.
 intro a;replace(5*a+9)with(a+((2*a+3)+(2*(a+2)+2)))by lia.
 rewrite csteps_add.
 rewrite <-(app_nil_r(repeat S2 a))at 1.
 rewrite s30_B_twos,csteps_add;unfold s30_back;cbn[chd ctl].
 rewrite s30_B_bounce;unfold s30_back;cbn[chd ctl].
 rewrite s30_instruction_bounce_before,app_nil_r.
 replace(a+2+1)with(a+3)by lia;reflexivity.
Qed.

Lemma s30_instruction_before_N : forall a,
 csteps s30_tm(sf_count(5*a+9))(s30_back StB(repeat S2(sf_count a))[S2;S2])=
 Some(StB,([],S2,repeat S0(sf_count(a+3)))).
Proof. intro a;sf_binary;apply s30_instruction_before. Qed.

Lemma s30_instruction_before_prefix :
 csteps s30_tm(sf_count 1367361263048%N)c0=
 Some(StB,([],S2,repeat S0(sf_count 1383585%N))).
Proof.
 exact(sf_comp 1367354345129%N 6917919%N c0
 (s30_back StB(repeat S2(sf_count 1383582%N))[S2;S2])
 (StB,([],S2,repeat S0(sf_count 1383585%N)))
 sf_after(s30_instruction_before_N 1383582%N)).
Qed.

Lemma s30_instruction_escape_N : forall a,
 csteps s30_tm (sf_count(5*a+10)) (s30_back StB (repeat S2(sf_count a)) [S2;S2])=
 Some(StB,([],S0,repeat S0(sf_count(a+4)))).
Proof. intro a;sf_binary;apply s30_instruction_escape. Qed.

Lemma s30_instruction_escape_prefix :
 csteps s30_tm(sf_count 1367361263049%N)c0=
 Some(StB,([],S0,repeat S0(sf_count 1383586%N))).
Proof.
 exact(sf_comp 1367354345129%N 6917920%N c0
 (s30_back StB(repeat S2(sf_count 1383582%N))[S2;S2])
 (StB,([],S0,repeat S0(sf_count 1383586%N)))
 sf_after(s30_instruction_escape_N 1383582%N)).
Qed.

Lemma s30_instruction_B0_drift : forall n l r,all_blank r=true->
 exists l' r',csteps s30_tm n(StB,(l,S0,r))=Some(StB,(l',S0,r'))/\all_blank r'=true.
Proof.
 induction n;intros l r Hr.
 - exists l,r;auto.
 - destruct r as[|h r].
   + cbn[csteps cstep s30_tm ctape_move chd ctl];apply IHn;reflexivity.
   + cbn[all_blank]in Hr;apply andb_prop in Hr as[Hh Hr].
     apply sym_eqb_spec in Hh;subst h.
     cbn[csteps cstep s30_tm ctape_move chd ctl];apply IHn;exact Hr.
Qed.
Lemma s30_repeat_zero_blank : forall n,all_blank(repeat S0 n)=true.
Proof. induction n;cbn;auto. Qed.

Lemma s30_instruction_B0_forever : forall k,sf_count 1367361263049%N<=k ->
 FiresAt s30_tm(StB,S0)k.
Proof.
 intros k Hk.
 destruct(s30_instruction_B0_drift(k-sf_count 1367361263049%N)[]
 (repeat S0(sf_count 1383586%N))(s30_repeat_zero_blank _))as(l'&r'&Et&_).
 exists(lift(StB,(l',S0,r')));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift.
 replace k with(sf_count 1367361263049%N+(k-sf_count 1367361263049%N))by lia.
 rewrite csteps_add,s30_instruction_escape_prefix;exact Et.
Qed.
Theorem s30_instruction_bound : QHBoundTr(sf_count 1367361263049%N)s30_tm.
Proof. eapply single_instruction_tail_bound;exact s30_instruction_B0_forever. Qed.

Lemma s30_instruction_score_successor :
 sf_count 1367361263049%N=S(sf_count 1367361263048%N).
Proof.
 unfold sf_count;change(N.to_nat(N.succ 1367361263048%N)=S(N.to_nat 1367361263048%N)).
 apply N2Nat.inj_succ.
Qed.
Theorem s30_last_instruction_B2 : QuietAfterTr s30_tm(StB,S2)(sf_count 1367361263048%N).
Proof.
 split.
 - exists(lift(StB,([],S2,repeat S0(sf_count 1383585%N))));split;[|reflexivity].
   rewrite <-lift_c0;apply csteps_lift;exact s30_instruction_before_prefix.
 - intros n Hn(c&Ec&Hc).
   assert(Hafter:sf_count 1367361263049%N<=n)by(rewrite s30_instruction_score_successor;lia).
   destruct(s30_instruction_B0_forever n Hafter)as(d&Ed&Hd).
   rewrite Ec in Ed;injection Ed as <-.
   assert(E:(StB,S2)=(StB,S0))by congruence;discriminate.
Qed.
Theorem s30_instruction_attains : AttainsTr s30_tm(sf_count 1367361263049%N).
Proof.
 exists(StB,S2),(sf_count 1367361263048%N);split.
 - exact s30_last_instruction_B2.
 - symmetry;exact s30_instruction_score_successor.
Qed.
Theorem s30_instruction_exact :
 AttainsTr s30_tm(sf_count 1367361263049%N)/\QHBoundTr(sf_count 1367361263049%N)s30_tm.
Proof. split;[exact s30_instruction_attains|exact s30_instruction_bound]. Qed.

Theorem s30_instruction_below_champion : QHBoundTr score s30_tm.
Proof.
 intros tg s H;pose proof(s30_instruction_bound tg s H)as Hb.
 eapply Nat.le_trans;[exact Hb|rewrite sf_score_count;apply sf_count_le;unfold scoreN;vm_compute;discriminate].
Qed.
Print Assumptions s30_instruction_bound.
Print Assumptions s30_instruction_below_champion.

Print Assumptions s30_instruction_exact.
