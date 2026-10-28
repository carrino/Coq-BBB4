(** Exact frozen S010. The supported crossing gate preserves P^n33,
    where P=3311331; a nine-phase cycle adds eight P words. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census TotalCompletion OneStateReach.
Import ListNotations.
Definition s10_tm:TM:=fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S0 DL StB
 |StA,S2=>mkTrans S1 DR StB |StA,S3=>mkTrans S2 DL StA
 |StB,S0=>mkTrans S3 DR StB |StB,S1=>mkTrans S3 DR StA
 |StB,S2=>mkTrans S1 DR StA |StB,S3=>mkTrans S0 DL StA end).
Definition s10_front q l r:cconf:=(q,(l,chd r,ctl r)).
Definition s10_back q l r:cconf:=(q,(ctl l,chd l,r)).
Fixpoint s10_word n:list Sym:=match n with 0=>[]|S n=>S3::S3::S1::S1::S3::S3::S1::s10_word n end.
Fixpoint s10_E n:list Sym:=match n with 0=>[]|S n=>S0::S2::S2::S0::S1::S2::S0::s10_E n end.
Fixpoint s10_V n:list Sym:=match n with 0=>[]|S n=>S1::S3::S3::S1::S1::S3::S3::s10_V n end.
Definition s10_tail n:=s10_word n++[S3;S3].
Definition s10_prefix i:list Sym:=match i with
 |0=>[]|1=>[S3;S3;S1]|2=>[S3]|3=>[S3;S3;S3;S3;S3;S1]
 |4=>[S3;S3;S1;S1;S1;S1;S3;S3;S1]|5=>[S3;S3;S3;S1;S1;S1]
 |6=>[S1;S1;S3;S3;S3;S3;S1]|7=>[S1;S1;S1;S3;S3;S1]
 |_=>[S3;S3;S3;S1]end.
Definition s10_pad i:=match i with 0=>5|1=>4|2=>3|3=>2|4=>1|5=>0|6=>1|7=>4|_=>6 end.
Definition s10_phase i n r:cconf:=(StA,(s10_prefix i++s10_tail n,S0,repeat S0(s10_pad i)++r)).
Definition s10_main n:=s10_phase 0 n[].
Definition s10_cost n:=448*n+2076.
Lemma s10_word_app : forall d n,s10_word(d+n)=s10_word d++s10_word n.
Proof. induction d;intro n;cbn;[reflexivity|now rewrite IHd]. Qed.
Lemma s10_tail_add : forall d n,s10_tail(d+n)=s10_word d++s10_tail n.
Proof. intros d n;unfold s10_tail;rewrite s10_word_app,app_assoc;reflexivity. Qed.
Lemma s10_E_shift : forall n r,
 s10_E n++S0::S2::S2::S0::S1::S2::S0::r=
 S0::S2::S2::S0::S1::S2::S0::(s10_E n++r).
Proof. induction n;intro r;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma s10_V_shift : forall n r,
 s10_V n++S1::S3::S3::S1::S1::S3::S3::r=
 S1::S3::S3::S1::S1::S3::S3::(s10_V n++r).
Proof. induction n;intro r;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma s10_V_rotate : forall n r,s10_V n++S1::r=S1::(s10_word n++r).
Proof. induction n;intro r;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma s10_L9 : forall l r,
 csteps s10_tm 9(s10_back StB(S3::S3::S1::S1::S3::S3::S1::l)r)=
 Some(s10_back StB l(S0::S2::S2::S0::S1::S2::S0::r)).
Proof. reflexivity. Qed.
Lemma s10_R7 : forall l r,
 csteps s10_tm 7(StB,(l,S0,S0::S2::S2::S0::S1::S2::S0::r))=
 Some(StB,(S1::S3::S3::S1::S1::S3::S3::l,S0,r)).
Proof. reflexivity. Qed.
Lemma s10_L_scan : forall n l r,
 csteps s10_tm(9*n)(s10_back StB(s10_word n++l)r)=
 Some(s10_back StB l(s10_E n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(9*S n)with(9+9*n)by lia;rewrite csteps_add.
 change(match csteps s10_tm 9(s10_back StB(S3::S3::S1::S1::S3::S3::S1::(s10_word n++l))r)with
 |Some cc=>csteps s10_tm(9*n)cc|None=>None end=
 Some(s10_back StB l(S0::S2::S2::S0::S1::S2::S0::(s10_E n++r)))).
 rewrite s10_L9,IHn,s10_E_shift;reflexivity.
Qed.
Lemma s10_R_scan : forall n l r,
 csteps s10_tm(7*n)(StB,(l,S0,s10_E n++r))=
 Some(StB,(s10_V n++l,S0,r)).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(7*S n)with(7+7*n)by lia;rewrite csteps_add.
 change(match csteps s10_tm 7(StB,(l,S0,S0::S2::S2::S0::S1::S2::S0::(s10_E n++r)))with
 |Some cc=>csteps s10_tm(7*n)cc|None=>None end=
 Some(StB,(S1::S3::S3::S1::S1::S3::S3::(s10_V n++l),S0,r))).
 rewrite s10_R7,IHn,s10_V_shift;reflexivity.
Qed.
Lemma s10_turn6 : forall r,
 csteps s10_tm 6(s10_back StB[S3;S3]r)=Some(StB,([S1;S3;S3],S0,r)).
Proof. reflexivity. Qed.
Theorem s10_B_gate : forall n r,
 csteps s10_tm(16*n+6)(s10_back StB(s10_tail n)r)=
 Some(StB,(S1::s10_tail n,S0,r)).
Proof.
 intros n r;replace(16*n+6)with(9*n+(6+7*n))by lia;unfold s10_tail.
 rewrite csteps_add,s10_L_scan,csteps_add,s10_turn6,s10_R_scan,s10_V_rotate;reflexivity.
Qed.
Lemma s10_A9 : forall l r,
 csteps s10_tm 9(s10_back StA(S3::S3::S1::S1::S3::S3::S1::l)r)=
 Some(s10_back StB l(S0::S2::S2::S0::S1::S2::S2::r)).
Proof. reflexivity. Qed.
Lemma s10_A8 : forall l r,
 csteps s10_tm 8(StB,(S1::l,S0,S0::S2::S2::S0::S1::S2::S2::r))=
 Some(s10_front StA(S1::S1::S3::S3::S1::S1::S3::S3::S1::l)r).
Proof. reflexivity. Qed.
Theorem s10_A_gate : forall n r,
 csteps s10_tm(16*n+7)(s10_back StA(s10_tail n)r)=
 Some(s10_front StA(S1::S1::s10_tail n)r).
Proof.
 intros[|n]r;[reflexivity|].
 replace(16*S n+7)with(9+((16*n+6)+8))by lia;rewrite csteps_add.
 change(match csteps s10_tm 9
 (s10_back StA(S3::S3::S1::S1::S3::S3::S1::s10_tail n)r)with
 |Some cc=>csteps s10_tm((16*n+6)+8)cc|None=>None end=
 Some(s10_front StA(S1::S1::S3::S3::S1::S1::S3::S3::S1::s10_tail n)r)).
 rewrite s10_A9,csteps_add,s10_B_gate,s10_A8;reflexivity.
Qed.
Lemma s10_chunk_0_0 : forall l r,
 csteps s10_tm 1(StA,(l,S0,S0::S0::S0::S0::S0::r))=Some(s10_back StB l(S1::S0::S0::S0::S0::S0::r)).
Proof. reflexivity. Qed.

Lemma s10_chunk_0_1 : forall l r,
 csteps s10_tm 2(StB,(S1::l,S0,S1::S0::S0::S0::S0::S0::r))=Some((StA,(S3::S3::S1::l,S0,S0::S0::S0::S0::r))).
Proof. reflexivity. Qed.

Theorem s10_phase_0 : forall n r,
 csteps s10_tm(16*n+9)(s10_phase 0 n r)=Some(s10_phase 1(n+0)r).
Proof.
 intros n r;replace(16*n+9)with(1+((16*n+6)+(2)))by lia.
 unfold s10_phase.
 replace(n+0)with(0+n)by lia;rewrite s10_tail_add.
 cbn[s10_prefix s10_pad s10_word repeat app].

 rewrite csteps_add,s10_chunk_0_0,csteps_add,s10_B_gate.

 apply s10_chunk_0_1.
Qed.

Lemma s10_chunk_1_0 : forall l r,
 csteps s10_tm 4(StA,(S3::S3::S1::l,S0,S0::S0::S0::S0::r))=Some(s10_back StB l(S0::S2::S0::S1::S0::S0::S0::S0::r)).
Proof. reflexivity. Qed.

Lemma s10_chunk_1_1 : forall l r,
 csteps s10_tm 10(StB,(S1::l,S0,S0::S2::S0::S1::S0::S0::S0::S0::r))=Some(s10_back StB l(S0::S2::S2::S0::S0::S1::S0::S0::S0::S0::r)).
Proof. reflexivity. Qed.

Lemma s10_chunk_1_2 : forall l r,
 csteps s10_tm 7(StB,(S1::l,S0,S0::S2::S2::S0::S0::S1::S0::S0::S0::S0::r))=Some((StA,(S3::S3::S3::S1::S1::S3::S3::S1::l,S0,S0::S0::S0::r))).
Proof. reflexivity. Qed.

Theorem s10_phase_1 : forall n r,
 csteps s10_tm(32*n+33)(s10_phase 1 n r)=Some(s10_phase 2(n+1)r).
Proof.
 intros n r;replace(32*n+33)with(4+((16*n+6)+(10+((16*n+6)+(7)))))by lia.
 unfold s10_phase.
 replace(n+1)with(1+n)by lia;rewrite s10_tail_add.
 cbn[s10_prefix s10_pad s10_word repeat app].

 rewrite csteps_add,s10_chunk_1_0,csteps_add,s10_B_gate.

 rewrite csteps_add,s10_chunk_1_1,csteps_add,s10_B_gate.

 apply s10_chunk_1_2.
Qed.

Lemma s10_chunk_2_0 : forall l r,
 csteps s10_tm 2(StA,(S3::l,S0,S0::S0::S0::r))=Some(s10_back StA l(S0::S1::S0::S0::S0::r)).
Proof. reflexivity. Qed.

Lemma s10_chunk_2_1 : forall l r,
 csteps s10_tm 5(StA,(S1::S1::l,S0,S1::S0::S0::S0::r))=Some(s10_back StB l(S0::S0::S0::S1::S0::S0::S0::r)).
Proof. reflexivity. Qed.

Lemma s10_chunk_2_2 : forall l r,
 csteps s10_tm 5(StB,(S1::l,S0,S0::S0::S0::S1::S0::S0::S0::r))=Some((StA,(S3::S3::S3::S3::S3::S1::l,S0,S0::S0::r))).
Proof. reflexivity. Qed.

Theorem s10_phase_2 : forall n r,
 csteps s10_tm(32*n+25)(s10_phase 2 n r)=Some(s10_phase 3(n+0)r).
Proof.
 intros n r;replace(32*n+25)with(2+((16*n+7)+(5+((16*n+6)+(5)))))by lia.
 unfold s10_phase.
 replace(n+0)with(0+n)by lia;rewrite s10_tail_add.
 cbn[s10_prefix s10_pad s10_word repeat app].

 rewrite csteps_add,s10_chunk_2_0,csteps_add,s10_A_gate;unfold s10_front;cbn[chd ctl].

 rewrite csteps_add,s10_chunk_2_1,csteps_add,s10_B_gate.

 apply s10_chunk_2_2.
Qed.

Lemma s10_chunk_3_0 : forall l r,
 csteps s10_tm 7(StA,(S3::S3::S3::S3::S3::S1::l,S0,S0::S0::r))=Some(s10_back StB l(S0::S2::S2::S2::S2::S0::S1::S0::S0::r)).
Proof. reflexivity. Qed.

Lemma s10_chunk_3_1 : forall l r,
 csteps s10_tm 8(StB,(S1::l,S0,S0::S2::S2::S2::S2::S0::S1::S0::S0::r))=Some((StA,(S3::S3::S1::S1::S1::S1::S3::S3::S1::l,S0,S0::r))).
Proof. reflexivity. Qed.

Theorem s10_phase_3 : forall n r,
 csteps s10_tm(16*n+21)(s10_phase 3 n r)=Some(s10_phase 4(n+0)r).
Proof.
 intros n r;replace(16*n+21)with(7+((16*n+6)+(8)))by lia.
 unfold s10_phase.
 replace(n+0)with(0+n)by lia;rewrite s10_tail_add.
 cbn[s10_prefix s10_pad s10_word repeat app].

 rewrite csteps_add,s10_chunk_3_0,csteps_add,s10_B_gate.

 apply s10_chunk_3_1.
Qed.

Lemma s10_chunk_4_0 : forall l r,
 csteps s10_tm 14(StA,(S3::S3::S1::S1::S1::S1::S3::S3::S1::l,S0,S0::r))=Some(s10_back StB l(S0::S2::S2::S0::S1::S0::S1::S2::S0::S1::S0::r)).
Proof. reflexivity. Qed.

Lemma s10_chunk_4_1 : forall l r,
 csteps s10_tm 16(StB,(S1::l,S0,S0::S2::S2::S0::S1::S0::S1::S2::S0::S1::S0::r))=Some(s10_back StB l(S0::S2::S2::S0::S1::S2::S0::S1::S1::S2::S0::S1::S0::r)).
Proof. reflexivity. Qed.

Lemma s10_chunk_4_2 : forall l r,
 csteps s10_tm 22(StB,(S1::l,S0,S0::S2::S2::S0::S1::S2::S0::S1::S1::S2::S0::S1::S0::r))=Some(s10_back StB l(S0::S2::S2::S0::S1::S2::S0::S0::S2::S0::S0::S2::S0::S1::S0::r)).
Proof. reflexivity. Qed.

Lemma s10_chunk_4_3 : forall l r,
 csteps s10_tm 26(StB,(S1::l,S0,S0::S2::S2::S0::S1::S2::S0::S0::S2::S0::S0::S2::S0::S1::S0::r))=Some(s10_back StB l(S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S0::S0::S2::S0::S1::S0::r)).
Proof. reflexivity. Qed.

Lemma s10_chunk_4_4 : forall l r,
 csteps s10_tm 38(StB,(S1::l,S0,S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S0::S0::S2::S0::S1::S0::r))=Some(s10_back StB l(S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S1::S2::S2::S2::S0::S0::S1::S0::r)).
Proof. reflexivity. Qed.

Lemma s10_chunk_4_5 : forall l r,
 csteps s10_tm 19(StB,(S1::l,S0,S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S1::S2::S2::S2::S0::S0::S1::S0::r))=Some((StA,(S3::S3::S3::S1::S1::S1::S3::S3::S1::S1::S3::S3::S1::S3::S3::S1::S1::S3::S3::S1::l,S0,r))).
Proof. reflexivity. Qed.

Theorem s10_phase_4 : forall n r,
 csteps s10_tm(80*n+165)(s10_phase 4 n r)=Some(s10_phase 5(n+2)r).
Proof.
 intros n r;replace(80*n+165)with(14+((16*n+6)+(16+((16*n+6)+(22+((16*n+6)+(26+((16*n+6)+(38+((16*n+6)+(19)))))))))))by lia.
 unfold s10_phase.
 replace(n+2)with(2+n)by lia;rewrite s10_tail_add.
 cbn[s10_prefix s10_pad s10_word repeat app].

 rewrite csteps_add,s10_chunk_4_0,csteps_add,s10_B_gate.

 rewrite csteps_add,s10_chunk_4_1,csteps_add,s10_B_gate.

 rewrite csteps_add,s10_chunk_4_2,csteps_add,s10_B_gate.

 rewrite csteps_add,s10_chunk_4_3,csteps_add,s10_B_gate.

 rewrite csteps_add,s10_chunk_4_4,csteps_add,s10_B_gate.

 apply s10_chunk_4_5.
Qed.

Lemma s10_chunk_5_0 : forall l r,
 csteps s10_tm 9(StA,(S3::S3::S3::S1::S1::S1::l,S0,r))=Some(s10_back StB l(S0::S0::S1::S2::S2::S0::S1::r)).
Proof. reflexivity. Qed.

Lemma s10_chunk_5_1 : forall l r,
 csteps s10_tm 16(StB,(S1::l,S0,S0::S0::S1::S2::S2::S0::S1::r))=Some(s10_back StB l(S0::S2::S2::S2::S0::S0::S0::S0::S1::r)).
Proof. reflexivity. Qed.

Lemma s10_chunk_5_2 : forall l r,
 csteps s10_tm 16(StB,(S1::l,S0,S0::S2::S2::S2::S0::S0::S0::S0::S1::r))=Some(s10_back StB l(S0::S2::S2::S0::S1::S0::S0::S0::S0::S0::S1::r)).
Proof. reflexivity. Qed.

Lemma s10_chunk_5_3 : forall l r,
 csteps s10_tm 16(StB,(S1::l,S0,S0::S2::S2::S0::S1::S0::S0::S0::S0::S0::S1::r))=Some(s10_back StB l(S0::S2::S2::S0::S1::S2::S0::S1::S0::S0::S0::S0::S1::r)).
Proof. reflexivity. Qed.

Lemma s10_chunk_5_4 : forall l r,
 csteps s10_tm 22(StB,(S1::l,S0,S0::S2::S2::S0::S1::S2::S0::S1::S0::S0::S0::S0::S1::r))=Some(s10_back StB l(S0::S2::S2::S0::S1::S2::S0::S0::S2::S0::S1::S0::S0::S0::S1::r)).
Proof. reflexivity. Qed.

Lemma s10_chunk_5_5 : forall l r,
 csteps s10_tm 26(StB,(S1::l,S0,S0::S2::S2::S0::S1::S2::S0::S0::S2::S0::S1::S0::S0::S0::S1::r))=Some(s10_back StB l(S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S0::S1::S0::S0::S0::S1::r)).
Proof. reflexivity. Qed.

Lemma s10_chunk_5_6 : forall l r,
 csteps s10_tm 34(StB,(S1::l,S0,S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S0::S1::S0::S0::S0::S1::r))=Some(s10_back StB l(S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S1::S2::S2::S0::S1::S0::S0::S1::r)).
Proof. reflexivity. Qed.

Lemma s10_chunk_5_7 : forall l r,
 csteps s10_tm 38(StB,(S1::l,S0,S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S1::S2::S2::S0::S1::S0::S0::S1::r))=Some(s10_back StB l(S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S1::S2::S0::S0::S0::S0::S1::S0::S0::S1::r)).
Proof. reflexivity. Qed.

Lemma s10_chunk_5_8 : forall l r,
 csteps s10_tm 44(StB,(S1::l,S0,S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S1::S2::S0::S0::S0::S0::S1::S0::S0::S1::r))=Some(s10_back StB l(S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S2::S2::S0::S1::S0::S1::r)).
Proof. reflexivity. Qed.

Lemma s10_chunk_5_9 : forall l r,
 csteps s10_tm 54(StB,(S1::l,S0,S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S2::S2::S0::S1::S0::S1::r))=Some(s10_back StB l(S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S1::S0::S1::S2::S0::S1::S1::r)).
Proof. reflexivity. Qed.

Lemma s10_chunk_5_10 : forall l r,
 csteps s10_tm 48(StB,(S1::l,S0,S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S1::S0::S1::S2::S0::S1::S1::r))=Some(s10_back StB l(S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S1::S2::S0::S1::S1::S2::S0::S1::S1::r)).
Proof. reflexivity. Qed.

Lemma s10_chunk_5_11 : forall l r,
 csteps s10_tm 54(StB,(S1::l,S0,S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S1::S2::S0::S1::S1::S2::S0::S1::S1::r))=Some(s10_back StB l(S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S1::S2::S0::S0::S2::S0::S0::S2::S0::S1::S1::r)).
Proof. reflexivity. Qed.

Lemma s10_chunk_5_12 : forall l r,
 csteps s10_tm 58(StB,(S1::l,S0,S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S1::S2::S0::S0::S2::S0::S0::S2::S0::S1::S1::r))=Some(s10_back StB l(S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S0::S0::S2::S0::S1::S1::r)).
Proof. reflexivity. Qed.

Lemma s10_chunk_5_13 : forall l r,
 csteps s10_tm 70(StB,(S1::l,S0,S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S0::S0::S2::S0::S1::S1::r))=Some(s10_back StB l(S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S1::S2::S2::S2::S0::S0::S1::S1::r)).
Proof. reflexivity. Qed.

Lemma s10_chunk_5_14 : forall l r,
 csteps s10_tm 78(StB,(S1::l,S0,S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S1::S2::S2::S2::S0::S0::S1::S1::r))=Some(s10_back StB l(S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S1::S2::S0::S0::S0::S1::S2::S2::S0::S0::r)).
Proof. reflexivity. Qed.

Lemma s10_chunk_5_15 : forall l r,
 csteps s10_tm 34(StB,(S1::l,S0,S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S1::S2::S0::S0::S2::S2::S0::S1::S2::S0::S0::S0::S1::S2::S2::S0::S0::r))=Some((StA,(S1::S1::S3::S3::S3::S3::S1::S3::S3::S1::S1::S3::S3::S1::S3::S3::S1::S1::S3::S3::S1::S3::S3::S1::S1::S3::S3::S1::S3::S3::S1::S1::S3::S3::S1::l,S0,S0::r))).
Proof. reflexivity. Qed.

Theorem s10_phase_5 : forall n r,
 csteps s10_tm(240*n+707)(s10_phase 5 n r)=Some(s10_phase 6(n+4)r).
Proof.
 intros n r;replace(240*n+707)with(9+((16*n+6)+(16+((16*n+6)+(16+((16*n+6)+(16+((16*n+6)+(22+((16*n+6)+(26+((16*n+6)+(34+((16*n+6)+(38+((16*n+6)+(44+((16*n+6)+(54+((16*n+6)+(48+((16*n+6)+(54+((16*n+6)+(58+((16*n+6)+(70+((16*n+6)+(78+((16*n+6)+(34)))))))))))))))))))))))))))))))by lia.
 unfold s10_phase.
 replace(n+4)with(4+n)by lia;rewrite s10_tail_add.
 cbn[s10_prefix s10_pad s10_word repeat app].

 rewrite csteps_add,s10_chunk_5_0,csteps_add,s10_B_gate.

 rewrite csteps_add,s10_chunk_5_1,csteps_add,s10_B_gate.

 rewrite csteps_add,s10_chunk_5_2,csteps_add,s10_B_gate.

 rewrite csteps_add,s10_chunk_5_3,csteps_add,s10_B_gate.

 rewrite csteps_add,s10_chunk_5_4,csteps_add,s10_B_gate.

 rewrite csteps_add,s10_chunk_5_5,csteps_add,s10_B_gate.

 rewrite csteps_add,s10_chunk_5_6,csteps_add,s10_B_gate.

 rewrite csteps_add,s10_chunk_5_7,csteps_add,s10_B_gate.

 rewrite csteps_add,s10_chunk_5_8,csteps_add,s10_B_gate.

 rewrite csteps_add,s10_chunk_5_9,csteps_add,s10_B_gate.

 rewrite csteps_add,s10_chunk_5_10,csteps_add,s10_B_gate.

 rewrite csteps_add,s10_chunk_5_11,csteps_add,s10_B_gate.

 rewrite csteps_add,s10_chunk_5_12,csteps_add,s10_B_gate.

 rewrite csteps_add,s10_chunk_5_13,csteps_add,s10_B_gate.

 rewrite csteps_add,s10_chunk_5_14,csteps_add,s10_B_gate.

 apply s10_chunk_5_15.
Qed.

Lemma s10_chunk_6_0 : forall l r,
 csteps s10_tm 10(StA,(S1::S1::S3::S3::S3::S3::S1::l,S0,S0::r))=Some(s10_back StB l(S0::S2::S2::S2::S0::S0::S0::S0::S0::r)).
Proof. reflexivity. Qed.

Lemma s10_chunk_6_1 : forall l r,
 csteps s10_tm 5(StB,(S1::l,S0,S0::S2::S2::S2::S0::S0::S0::S0::S0::r))=Some((StA,(S1::S1::S1::S3::S3::S1::l,S0,S0::S0::S0::S0::r))).
Proof. reflexivity. Qed.

Theorem s10_phase_6 : forall n r,
 csteps s10_tm(16*n+21)(s10_phase 6 n r)=Some(s10_phase 7(n+0)r).
Proof.
 intros n r;replace(16*n+21)with(10+((16*n+6)+(5)))by lia.
 unfold s10_phase.
 replace(n+0)with(0+n)by lia;rewrite s10_tail_add.
 cbn[s10_prefix s10_pad s10_word repeat app].

 rewrite csteps_add,s10_chunk_6_0,csteps_add,s10_B_gate.

 apply s10_chunk_6_1.
Qed.

Lemma s10_chunk_7_0 : forall l r,
 csteps s10_tm 6(StA,(S1::S1::S1::S3::S3::S1::l,S0,S0::S0::S0::S0::r))=Some((StA,(S3::S3::S3::S1::l,S0,S0::S0::S0::S0::S0::S0::r))).
Proof. reflexivity. Qed.

Theorem s10_phase_7 : forall n r,
 csteps s10_tm(0*n+6)(s10_phase 7 n r)=Some(s10_phase 8(n+0)r).
Proof.
 intros n r;replace(0*n+6)with(6)by lia.
 unfold s10_phase.
 replace(n+0)with(0+n)by lia;rewrite s10_tail_add.
 cbn[s10_prefix s10_pad s10_word repeat app].

 apply s10_chunk_7_0.
Qed.

Lemma s10_chunk_8_0 : forall l r,
 csteps s10_tm 5(StA,(S3::S3::S3::S1::l,S0,S0::S0::S0::S0::S0::S0::r))=Some(s10_back StB l(S0::S2::S2::S0::S1::S0::S0::S0::S0::S0::S0::r)).
Proof. reflexivity. Qed.

Lemma s10_chunk_8_1 : forall l r,
 csteps s10_tm 6(StB,(S1::l,S0,S0::S2::S2::S0::S1::S0::S0::S0::S0::S0::S0::r))=Some((StA,(S3::S3::S1::S1::S3::S3::S1::l,S0,S0::S0::S0::S0::S0::r))).
Proof. reflexivity. Qed.

Theorem s10_phase_8 : forall n r,
 csteps s10_tm(16*n+17)(s10_phase 8 n r)=Some(s10_phase 0(n+1)r).
Proof.
 intros n r;replace(16*n+17)with(5+((16*n+6)+(6)))by lia.
 unfold s10_phase.
 replace(n+1)with(1+n)by lia;rewrite s10_tail_add.
 cbn[s10_prefix s10_pad s10_word repeat app].

 rewrite csteps_add,s10_chunk_8_0,csteps_add,s10_B_gate.

 apply s10_chunk_8_1.
Qed.
Theorem s10_cycle : forall n r,
 csteps s10_tm(s10_cost n)(s10_phase 0 n r)=Some(s10_phase 0(n+8)r).
Proof.
 intros n r;replace(s10_cost n)with
 ((16*n+9)+((32*n+33)+((32*(n+1)+25)+((16*(n+1)+21)+
 ((80*(n+1)+165)+((240*(n+3)+707)+((16*(n+7)+21)+(6+(16*(n+7)+17)))))))))
 by(unfold s10_cost;lia).
 rewrite csteps_add,s10_phase_0,Nat.add_0_r.
 rewrite csteps_add,s10_phase_1.
 rewrite csteps_add,s10_phase_2,Nat.add_0_r.
 rewrite csteps_add,s10_phase_3,Nat.add_0_r.
 rewrite csteps_add,s10_phase_4;replace(n+1+2)with(n+3)by lia.
 rewrite csteps_add,s10_phase_5;replace(n+3+4)with(n+7)by lia.
 rewrite csteps_add,s10_phase_6,Nat.add_0_r.
 pose proof(s10_phase_7(n+7)r)as E7;rewrite Nat.mul_0_l,Nat.add_0_l,Nat.add_0_r in E7.
 rewrite csteps_add,E7.
 rewrite s10_phase_8;replace(n+7+1)with(n+8)by lia;reflexivity.
Qed.
Theorem s10_main_next : forall n,
 csteps s10_tm(s10_cost n)(s10_main n)=Some(s10_main(n+8)).
Proof. intro n;apply s10_cycle. Qed.
Example s10_entry : csteps s10_tm 2079 c0=Some(s10_main 8).
Proof. vm_compute;reflexivity. Qed.
Lemma s10_returns : forall N,exists t n,N<=t /\csteps s10_tm t c0=Some(s10_main n).
Proof.
 induction N as[|N IH].
 - exists 2079,8;split;[lia|exact s10_entry].
 - destruct IH as(t&n&Ht&E);exists(t+s10_cost n),(n+8);split.
   + unfold s10_cost;lia.
   + rewrite csteps_add,E;apply s10_main_next.
Qed.
Theorem s10_nonhalt : NonHalt s10_tm.
Proof. apply ore_total_nonhalt;intros q h;destruct q,h;eexists;reflexivity. Qed.
Theorem s10_A_recurrent : forall N,exists t,N<=t /\VisitsAt s10_tm StA t.
Proof.
 intro N;destruct(s10_returns N)as(t&n&Ht&E).
 exists t;split;[exact Ht|];exists(lift(s10_main n));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem s10_B_recurrent : forall N,exists t,N<=t /\VisitsAt s10_tm StB t.
Proof.
 intro N;destruct(s10_returns N)as(t&n&Ht&E).
 exists(t+1);split;[lia|];exists(lift(StB,(ctl(s10_tail n),chd(s10_tail n),S1::repeat S0 5)));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;reflexivity.
Qed.
Theorem s10_state_zero : QHBound 0 s10_tm.
Proof.
 intros q s[_ Hquiet];destruct q.
 - destruct(s10_A_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
 - destruct(s10_B_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
Qed.
Theorem s10_sound : NonHalt s10_tm /\QHBound 0 s10_tm.
Proof. split;[exact s10_nonhalt|exact s10_state_zero]. Qed.
Print Assumptions s10_sound.
