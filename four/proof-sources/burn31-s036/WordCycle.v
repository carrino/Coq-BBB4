(** Exact frozen S036: supported crossing gates and a thirteen-cut cycle.
    The arbitrary right suffix is preserved; each cycle prepends W. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census TotalCompletion OneStateReach.
Import ListNotations.
Definition s36_tm:TM:=fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DL StA
 |StA,S2=>mkTrans S2 DR StB |StA,S3=>mkTrans S1 DR StA
 |StB,S0=>mkTrans S3 DR StB |StB,S1=>mkTrans S3 DL StA
 |StB,S2=>mkTrans S0 DL StB |StB,S3=>mkTrans S0 DR StB end).
Definition s36_front q l r:cconf:=(q,(l,chd r,ctl r)).
Definition s36_back q l r:cconf:=(q,(ctl l,chd l,r)).
Fixpoint s36_P n:list Sym:=match n with 0=>[]|S n=>S2::S3::S0::S1::s36_P n end.
Fixpoint s36_Q n:list Sym:=match n with 0=>[]|S n=>S1::S1::S0::S2::s36_Q n end.
Fixpoint s36_E n:list Sym:=match n with 0=>[]|S n=>S0::S1::S2::S3::s36_E n end.
Lemma s36_P_shift : forall n r,s36_P n++S2::S3::S0::S1::r=S2::S3::S0::S1::(s36_P n++r).
Proof. induction n;intro r;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma s36_Q_shift : forall n r,s36_Q n++S1::S1::S0::S2::r=S1::S1::S0::S2::(s36_Q n++r).
Proof. induction n;intro r;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma s36_E_shift : forall n r,s36_E n++S0::S1::S2::S3::r=S0::S1::S2::S3::(s36_E n++r).
Proof. induction n;intro r;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma s36_rotate : forall n r,S2::S3::(s36_E n++r)=s36_P n++S2::S3::r.
Proof. induction n;intro r;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma s36_R6 : forall l r,
 csteps s36_tm 6(s36_front StA l(S2::S3::S0::S1::r))=
 Some(s36_front StA(S1::S1::S0::S2::l)r).
Proof. reflexivity. Qed.
Lemma s36_L4 : forall l r,
 csteps s36_tm 4(s36_back StB(S1::S1::S0::S2::l)r)=
 Some(s36_back StB l(S0::S1::S2::S3::r)).
Proof. reflexivity. Qed.
Lemma s36_L4A : forall l r,
 csteps s36_tm 4(s36_back StA(S1::S1::S0::S2::l)r)=
 Some(s36_back StB l(S0::S1::S2::S2::r)).
Proof. reflexivity. Qed.
Lemma s36_R_scan : forall n l r,
 csteps s36_tm(6*n)(s36_front StA l(s36_P n++r))=
 Some(s36_front StA(s36_Q n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(6*S n)with(6+6*n)by lia;rewrite csteps_add.
 change(match csteps s36_tm 6(s36_front StA l(S2::S3::S0::S1::(s36_P n++r)))with
 |Some cc=>csteps s36_tm(6*n)cc|None=>None end=
 Some(s36_front StA(S1::S1::S0::S2::(s36_Q n++l))r)).
 rewrite s36_R6,IHn,s36_Q_shift;reflexivity.
Qed.
Lemma s36_L_scan : forall n l r,
 csteps s36_tm(4*n)(s36_back StB(s36_Q n++l)r)=
 Some(s36_back StB l(s36_E n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(4*S n)with(4+4*n)by lia;rewrite csteps_add.
 change(match csteps s36_tm 4(s36_back StB(S1::S1::S0::S2::(s36_Q n++l))r)with
 |Some cc=>csteps s36_tm(4*n)cc|None=>None end=
 Some(s36_back StB l(S0::S1::S2::S3::(s36_E n++r)))).
 rewrite s36_L4,IHn,s36_E_shift;reflexivity.
Qed.
Definition s36_support n:=s36_Q n++[S1;S1].
Definition s36_boundary n r:cconf:=(StA,([],S0,s36_P n++r)).
Theorem s36_B_gate : forall n r,
 csteps s36_tm(4*n+2)(s36_back StB(s36_support n)r)=
 Some(s36_boundary n(S2::S3::r)).
Proof.
 intros n r;unfold s36_support;rewrite csteps_add,s36_L_scan.
 change(Some(StA,([],S0,S2::S3::(s36_E n++r)))=Some(s36_boundary n(S2::S3::r))).
 rewrite s36_rotate;reflexivity.
Qed.
Theorem s36_A_gate : forall n r,
 csteps s36_tm(4*n+2)(s36_back StA(s36_support n)r)=
 Some(s36_boundary n(S2::S2::r)).
Proof.
 intros[|n]r;[reflexivity|].
 replace(4*S n+2)with(4+(4*n+2))by lia;rewrite csteps_add.
 change(match csteps s36_tm 4(s36_back StA(S1::S1::S0::S2::s36_support n)r)with
 |Some cc=>csteps s36_tm(4*n+2)cc|None=>None end=
 Some(s36_boundary(S n)(S2::S2::r))).
 rewrite s36_L4A,s36_B_gate;unfold s36_boundary;cbn[s36_P app].
 rewrite s36_P_shift;reflexivity.
Qed.
Lemma s36_launch5 : forall r,
 csteps s36_tm 5(StA,([],S0,r))=Some(s36_front StA[S1;S1]r).
Proof. reflexivity. Qed.
Theorem s36_read_gate : forall n r,
 csteps s36_tm(6*n+5)(s36_boundary n r)=Some(s36_front StA(s36_support n)r).
Proof.
 intros n r;replace(6*n+5)with(5+6*n)by lia;unfold s36_boundary.
 rewrite csteps_add,s36_launch5,s36_R_scan;reflexivity.
Qed.
Definition s36_tag q:=match q with StA=>[S2;S2]|StB=>[S2;S3]end.
Theorem s36_rule : forall q c u v,
 (forall l r,csteps s36_tm c(s36_front StA l(u++r))=Some(s36_back q l(v++r))) ->
 forall n r,csteps s36_tm(10*n+c+7)(s36_boundary n(u++r))=
 Some(s36_boundary n(s36_tag q++v++r)).
Proof.
 intros q c u v H n r;replace(10*n+c+7)with((6*n+5)+(c+(4*n+2)))by lia.
 rewrite csteps_add,s36_read_gate,csteps_add,H.
 destruct q;[rewrite s36_A_gate|rewrite s36_B_gate];reflexivity.
Qed.
Lemma s36_finite_0 : forall l r,
 csteps s36_tm 3(s36_front StA l([S3;S0]++r))=
 Some(s36_back StA l([S3;S1]++r)).
Proof. reflexivity. Qed.
Lemma s36_row_0 : forall n r,
 csteps s36_tm(10*n+10)(s36_boundary n([S3;S0]++r))=
 Some(s36_boundary n([S2;S2;S3;S1]++r)).
Proof. intros n r;replace(10*n+10)with(10*n+3+7)by lia;apply(s36_rule _ _ _ _ s36_finite_0). Qed.
Lemma s36_finite_1 : forall l r,
 csteps s36_tm 3(s36_front StA l([S2;S2]++r))=
 Some(s36_back StB l([S0;S0]++r)).
Proof. reflexivity. Qed.
Lemma s36_row_1 : forall n r,
 csteps s36_tm(10*n+10)(s36_boundary n([S2;S2]++r))=
 Some(s36_boundary n([S2;S3;S0;S0]++r)).
Proof. intros n r;replace(10*n+10)with(10*n+3+7)by lia;apply(s36_rule _ _ _ _ s36_finite_1). Qed.
Lemma s36_finite_2 : forall l r,
 csteps s36_tm 29(s36_front StA l([S2;S3;S0;S0;S3;S1;S1]++r))=
 Some(s36_back StB l([S0;S0;S2;S2;S2;S2;S2]++r)).
Proof. reflexivity. Qed.
Lemma s36_row_2 : forall n r,
 csteps s36_tm(10*n+36)(s36_boundary n([S2;S3;S0;S0;S3;S1;S1]++r))=
 Some(s36_boundary n([S2;S3;S0;S0;S2;S2;S2;S2;S2]++r)).
Proof. intros n r;replace(10*n+36)with(10*n+29+7)by lia;apply(s36_rule _ _ _ _ s36_finite_2). Qed.
Lemma s36_finite_3 : forall l r,
 csteps s36_tm 113(s36_front StA l([S2;S3;S0;S0;S2;S2;S2;S2;S2;S3;S0;S0;S3;S1;S0]++r))=
 Some(s36_back StB l([S0;S0;S2;S3;S0;S0;S2;S2;S2;S3;S1;S2;S2;S3;S1]++r)).
Proof. reflexivity. Qed.
Lemma s36_row_3 : forall n r,
 csteps s36_tm(10*n+120)(s36_boundary n([S2;S3;S0;S0;S2;S2;S2;S2;S2;S3;S0;S0;S3;S1;S0]++r))=
 Some(s36_boundary n([S2;S3;S0;S0;S2;S3;S0;S0;S2;S2;S2;S3;S1;S2;S2;S3;S1]++r)).
Proof. intros n r;replace(10*n+120)with(10*n+113+7)by lia;apply(s36_rule _ _ _ _ s36_finite_3). Qed.
Lemma s36_finite_4 : forall l r,
 csteps s36_tm 129(s36_front StA l([S2;S3;S0;S0;S2;S3;S0;S0;S2;S2;S2;S3;S1;S2;S2;S3;S1;S2;S2]++r))=
 Some(s36_back StB l([S0;S1;S3;S0;S0;S2;S3;S1;S0;S2;S2;S3;S1;S0;S2;S2;S3;S0;S0]++r)).
Proof. reflexivity. Qed.
Lemma s36_row_4 : forall n r,
 csteps s36_tm(10*n+136)(s36_boundary n([S2;S3;S0;S0;S2;S3;S0;S0;S2;S2;S2;S3;S1;S2;S2;S3;S1;S2;S2]++r))=
 Some(s36_boundary n([S2;S3;S0;S1;S3;S0;S0;S2;S3;S1;S0;S2;S2;S3;S1;S0;S2;S2;S3;S0;S0]++r)).
Proof. intros n r;replace(10*n+136)with(10*n+129+7)by lia;apply(s36_rule _ _ _ _ s36_finite_4). Qed.
Lemma s36_finite_5 : forall l r,
 csteps s36_tm 29(s36_front StA l([S2;S3;S0;S0;S3;S1;S0]++r))=
 Some(s36_back StB l([S0;S0;S2;S2;S2;S3;S1]++r)).
Proof. reflexivity. Qed.
Lemma s36_row_5 : forall n r,
 csteps s36_tm(10*n+36)(s36_boundary n([S2;S3;S0;S0;S3;S1;S0]++r))=
 Some(s36_boundary n([S2;S3;S0;S0;S2;S2;S2;S3;S1]++r)).
Proof. intros n r;replace(10*n+36)with(10*n+29+7)by lia;apply(s36_rule _ _ _ _ s36_finite_5). Qed.
Lemma s36_finite_6 : forall l r,
 csteps s36_tm 87(s36_front StA l([S2;S3;S0;S0;S2;S2;S2;S3;S1;S2;S3;S1;S0]++r))=
 Some(s36_back StB l([S0;S1;S3;S0;S1;S3;S0;S0;S3;S0;S0;S3;S1]++r)).
Proof. reflexivity. Qed.
Lemma s36_row_6 : forall n r,
 csteps s36_tm(10*n+94)(s36_boundary n([S2;S3;S0;S0;S2;S2;S2;S3;S1;S2;S3;S1;S0]++r))=
 Some(s36_boundary n([S2;S3;S0;S1;S3;S0;S1;S3;S0;S0;S3;S0;S0;S3;S1]++r)).
Proof. intros n r;replace(10*n+94)with(10*n+87+7)by lia;apply(s36_rule _ _ _ _ s36_finite_6). Qed.
Lemma s36_finite_7 : forall l r,
 csteps s36_tm 193(s36_front StA l([S2;S3;S0;S0;S2;S2;S2;S2;S2;S3;S0;S0;S3;S0;S0;S3;S1;S2;S2]++r))=
 Some(s36_back StB l([S0;S1;S3;S0;S1;S3;S0;S0;S3;S1;S0;S2;S2;S3;S0;S0;S3;S0;S0]++r)).
Proof. reflexivity. Qed.
Lemma s36_row_7 : forall n r,
 csteps s36_tm(10*n+200)(s36_boundary n([S2;S3;S0;S0;S2;S2;S2;S2;S2;S3;S0;S0;S3;S0;S0;S3;S1;S2;S2]++r))=
 Some(s36_boundary n([S2;S3;S0;S1;S3;S0;S1;S3;S0;S0;S3;S1;S0;S2;S2;S3;S0;S0;S3;S0;S0]++r)).
Proof. intros n r;replace(10*n+200)with(10*n+193+7)by lia;apply(s36_rule _ _ _ _ s36_finite_7). Qed.
Definition s36_W:list Sym:=[S3;S0;S0;S3;S0;S0;S3;S1;S0;S2;S2;S3;S0;S0].
Definition s36_wall i:list Sym:=match i with
|0=>[S3;S0;S1;S3;S0;S0;S3;S1;S0;S2;S2]
|1=>[S2;S2;S3;S1;S1;S3;S0;S0;S3;S1;S0;S2;S2]
|2=>[S2;S3;S0;S0;S3;S1;S1;S3;S0;S0;S3;S1;S0;S2;S2]
|3=>[S2;S3;S0;S0;S2;S2;S2;S2;S2;S3;S0;S0;S3;S1;S0;S2;S2]
|4=>[S2;S3;S0;S0;S2;S3;S0;S0;S2;S2;S2;S3;S1;S2;S2;S3;S1;S2;S2]
|5=>[S3;S0;S0;S2;S3;S1;S0;S2;S2;S3;S1;S0;S2;S2;S3;S0;S0]
|6=>[S2;S2;S3;S1;S0;S2;S3;S1;S0;S2;S2;S3;S1;S0;S2;S2;S3;S0;S0]
|7=>[S2;S3;S0;S0;S3;S1;S0;S2;S3;S1;S0;S2;S2;S3;S1;S0;S2;S2;S3;S0;S0]
|8=>[S2;S3;S0;S0;S2;S2;S2;S3;S1;S2;S3;S1;S0;S2;S2;S3;S1;S0;S2;S2;S3;S0;S0]
|9=>[S3;S0;S1;S3;S0;S0;S3;S0;S0;S3;S1;S2;S2;S3;S1;S0;S2;S2;S3;S0;S0]
|10=>[S2;S2;S3;S1;S1;S3;S0;S0;S3;S0;S0;S3;S1;S2;S2;S3;S1;S0;S2;S2;S3;S0;S0]
|11=>[S2;S3;S0;S0;S3;S1;S1;S3;S0;S0;S3;S0;S0;S3;S1;S2;S2;S3;S1;S0;S2;S2;S3;S0;S0]
|12=>[S2;S3;S0;S0;S2;S2;S2;S2;S2;S3;S0;S0;S3;S0;S0;S3;S1;S2;S2;S3;S1;S0;S2;S2;S3;S0;S0]
|_=>[S3;S0;S1;S3;S0;S0;S3;S1;S0;S2;S2] end.
Definition s36_offset i:=match i with |0=>0|1=>0|2=>0|3=>0|4=>0|5=>1|6=>1|7=>1|8=>1|9=>2|10=>2|11=>2|12=>2|_=>0 end.
Definition s36_phase i n r:=s36_boundary(n+s36_offset i)(s36_wall i++r).
Definition s36_main n r:=s36_phase 0 n r.
Lemma s36_phase_0 : forall n r,
 csteps s36_tm(10*n+10)(s36_phase 0 n r)=Some(s36_phase 1 n r).
Proof.
 intros n r;replace(10*n+10)with(10*(n+0)+10)by lia.
 change(csteps s36_tm(10*(n+0)+10)(s36_boundary(n+0)([S3;S0]++([S1;S3;S0;S0;S3;S1;S0;S2;S2]++r)))=Some(s36_phase 1 n r)).
 rewrite s36_row_0.
 reflexivity.
Qed.
Lemma s36_phase_1 : forall n r,
 csteps s36_tm(10*n+10)(s36_phase 1 n r)=Some(s36_phase 2 n r).
Proof.
 intros n r;replace(10*n+10)with(10*(n+0)+10)by lia.
 change(csteps s36_tm(10*(n+0)+10)(s36_boundary(n+0)([S2;S2]++([S3;S1;S1;S3;S0;S0;S3;S1;S0;S2;S2]++r)))=Some(s36_phase 2 n r)).
 rewrite s36_row_1.
 reflexivity.
Qed.
Lemma s36_phase_2 : forall n r,
 csteps s36_tm(10*n+36)(s36_phase 2 n r)=Some(s36_phase 3 n r).
Proof.
 intros n r;replace(10*n+36)with(10*(n+0)+36)by lia.
 change(csteps s36_tm(10*(n+0)+36)(s36_boundary(n+0)([S2;S3;S0;S0;S3;S1;S1]++([S3;S0;S0;S3;S1;S0;S2;S2]++r)))=Some(s36_phase 3 n r)).
 rewrite s36_row_2.
 reflexivity.
Qed.
Lemma s36_phase_3 : forall n r,
 csteps s36_tm(10*n+120)(s36_phase 3 n r)=Some(s36_phase 4 n r).
Proof.
 intros n r;replace(10*n+120)with(10*(n+0)+120)by lia.
 change(csteps s36_tm(10*(n+0)+120)(s36_boundary(n+0)([S2;S3;S0;S0;S2;S2;S2;S2;S2;S3;S0;S0;S3;S1;S0]++([S2;S2]++r)))=Some(s36_phase 4 n r)).
 rewrite s36_row_3.
 reflexivity.
Qed.
Lemma s36_phase_4 : forall n r,
 csteps s36_tm(10*n+136)(s36_phase 4 n r)=Some(s36_phase 5 n r).
Proof.
 intros n r;replace(10*n+136)with(10*(n+0)+136)by lia.
 change(csteps s36_tm(10*(n+0)+136)(s36_boundary(n+0)([S2;S3;S0;S0;S2;S3;S0;S0;S2;S2;S2;S3;S1;S2;S2;S3;S1;S2;S2]++([]++r)))=Some(s36_phase 5 n r)).
 rewrite s36_row_4.
 unfold s36_main,s36_phase,s36_boundary;cbn[s36_offset s36_wall s36_W].
 replace(n+1)with(S(n+0))by lia;cbn[s36_P app].
 rewrite s36_P_shift;repeat rewrite Nat.add_0_r;unfold s36_W;reflexivity.
Qed.
Lemma s36_phase_5 : forall n r,
 csteps s36_tm(10*n+20)(s36_phase 5 n r)=Some(s36_phase 6 n r).
Proof.
 intros n r;replace(10*n+20)with(10*(n+1)+10)by lia.
 change(csteps s36_tm(10*(n+1)+10)(s36_boundary(n+1)([S3;S0]++([S0;S2;S3;S1;S0;S2;S2;S3;S1;S0;S2;S2;S3;S0;S0]++r)))=Some(s36_phase 6 n r)).
 rewrite s36_row_0.
 reflexivity.
Qed.
Lemma s36_phase_6 : forall n r,
 csteps s36_tm(10*n+20)(s36_phase 6 n r)=Some(s36_phase 7 n r).
Proof.
 intros n r;replace(10*n+20)with(10*(n+1)+10)by lia.
 change(csteps s36_tm(10*(n+1)+10)(s36_boundary(n+1)([S2;S2]++([S3;S1;S0;S2;S3;S1;S0;S2;S2;S3;S1;S0;S2;S2;S3;S0;S0]++r)))=Some(s36_phase 7 n r)).
 rewrite s36_row_1.
 reflexivity.
Qed.
Lemma s36_phase_7 : forall n r,
 csteps s36_tm(10*n+46)(s36_phase 7 n r)=Some(s36_phase 8 n r).
Proof.
 intros n r;replace(10*n+46)with(10*(n+1)+36)by lia.
 change(csteps s36_tm(10*(n+1)+36)(s36_boundary(n+1)([S2;S3;S0;S0;S3;S1;S0]++([S2;S3;S1;S0;S2;S2;S3;S1;S0;S2;S2;S3;S0;S0]++r)))=Some(s36_phase 8 n r)).
 rewrite s36_row_5.
 reflexivity.
Qed.
Lemma s36_phase_8 : forall n r,
 csteps s36_tm(10*n+104)(s36_phase 8 n r)=Some(s36_phase 9 n r).
Proof.
 intros n r;replace(10*n+104)with(10*(n+1)+94)by lia.
 change(csteps s36_tm(10*(n+1)+94)(s36_boundary(n+1)([S2;S3;S0;S0;S2;S2;S2;S3;S1;S2;S3;S1;S0]++([S2;S2;S3;S1;S0;S2;S2;S3;S0;S0]++r)))=Some(s36_phase 9 n r)).
 rewrite s36_row_6.
 unfold s36_main,s36_phase,s36_boundary;cbn[s36_offset s36_wall s36_W].
 replace(n+2)with(S(n+1))by lia;cbn[s36_P app].
 rewrite s36_P_shift;repeat rewrite Nat.add_0_r;unfold s36_W;reflexivity.
Qed.
Lemma s36_phase_9 : forall n r,
 csteps s36_tm(10*n+30)(s36_phase 9 n r)=Some(s36_phase 10 n r).
Proof.
 intros n r;replace(10*n+30)with(10*(n+2)+10)by lia.
 change(csteps s36_tm(10*(n+2)+10)(s36_boundary(n+2)([S3;S0]++([S1;S3;S0;S0;S3;S0;S0;S3;S1;S2;S2;S3;S1;S0;S2;S2;S3;S0;S0]++r)))=Some(s36_phase 10 n r)).
 rewrite s36_row_0.
 reflexivity.
Qed.
Lemma s36_phase_10 : forall n r,
 csteps s36_tm(10*n+30)(s36_phase 10 n r)=Some(s36_phase 11 n r).
Proof.
 intros n r;replace(10*n+30)with(10*(n+2)+10)by lia.
 change(csteps s36_tm(10*(n+2)+10)(s36_boundary(n+2)([S2;S2]++([S3;S1;S1;S3;S0;S0;S3;S0;S0;S3;S1;S2;S2;S3;S1;S0;S2;S2;S3;S0;S0]++r)))=Some(s36_phase 11 n r)).
 rewrite s36_row_1.
 reflexivity.
Qed.
Lemma s36_phase_11 : forall n r,
 csteps s36_tm(10*n+56)(s36_phase 11 n r)=Some(s36_phase 12 n r).
Proof.
 intros n r;replace(10*n+56)with(10*(n+2)+36)by lia.
 change(csteps s36_tm(10*(n+2)+36)(s36_boundary(n+2)([S2;S3;S0;S0;S3;S1;S1]++([S3;S0;S0;S3;S0;S0;S3;S1;S2;S2;S3;S1;S0;S2;S2;S3;S0;S0]++r)))=Some(s36_phase 12 n r)).
 rewrite s36_row_2.
 reflexivity.
Qed.
Lemma s36_phase_12 : forall n r,
 csteps s36_tm(10*n+220)(s36_phase 12 n r)=Some(s36_main(n+3)(s36_W++r)).
Proof.
 intros n r;replace(10*n+220)with(10*(n+2)+200)by lia.
 change(csteps s36_tm(10*(n+2)+200)(s36_boundary(n+2)([S2;S3;S0;S0;S2;S2;S2;S2;S2;S3;S0;S0;S3;S0;S0;S3;S1;S2;S2]++([S3;S1;S0;S2;S2;S3;S0;S0]++r)))=Some(s36_main(n+3)(s36_W++r))).
 rewrite s36_row_7.
 unfold s36_main,s36_phase,s36_boundary;cbn[s36_offset s36_wall s36_W].
 replace(n+3)with(S(n+2))by lia;cbn[s36_P app].
 rewrite s36_P_shift;repeat rewrite Nat.add_0_r;unfold s36_W;reflexivity.
Qed.
Definition s36_cost n:=130*n+838.
Theorem s36_return : forall n r,
 csteps s36_tm(s36_cost n)(s36_main n r)=Some(s36_main(n+3)(s36_W++r)).
Proof.
 intros n r;unfold s36_cost.
 replace(130*n+838)with((10*n+10)+((10*n+10)+((10*n+36)+((10*n+120)+((10*n+136)+((10*n+20)+((10*n+20)+((10*n+46)+((10*n+104)+((10*n+30)+((10*n+30)+((10*n+56)+(10*n+220)))))))))))))by lia.
 rewrite csteps_add,s36_phase_0.
 rewrite csteps_add,s36_phase_1.
 rewrite csteps_add,s36_phase_2.
 rewrite csteps_add,s36_phase_3.
 rewrite csteps_add,s36_phase_4.
 rewrite csteps_add,s36_phase_5.
 rewrite csteps_add,s36_phase_6.
 rewrite csteps_add,s36_phase_7.
 rewrite csteps_add,s36_phase_8.
 rewrite csteps_add,s36_phase_9.
 rewrite csteps_add,s36_phase_10.
 rewrite csteps_add,s36_phase_11.
 exact(s36_phase_12 n r).
Qed.
Definition s36_entry_suffix:list Sym:=[S3;S0;S0;S3;S0;S1;S3;S0;S0;S2;S3;S0;S1;S3;S2;S2;S3;S0;S1;S2;S2;S3;S0;S1;S3].
Example s36_entry : csteps s36_tm 2758 c0=Some(s36_main 8 s36_entry_suffix).
Proof. vm_compute;reflexivity. Qed.
Lemma s36_returns : forall N,exists t n r,N<=t /\csteps s36_tm t c0=Some(s36_main n r).
Proof.
 induction N as[|N IH].
 - exists 2758,8,s36_entry_suffix;split;[lia|exact s36_entry].
 - destruct IH as(t&n&r&Ht&E);exists(t+s36_cost n),(n+3),(s36_W++r);split.
   + unfold s36_cost;lia.
   + rewrite csteps_add,E;apply s36_return.
Qed.
Theorem s36_nonhalt : NonHalt s36_tm.
Proof. apply ore_total_nonhalt;intros q h;destruct q,h;eexists;reflexivity. Qed.
Theorem s36_A_recurrent : forall N,exists t,N<=t /\VisitsAt s36_tm StA t.
Proof.
 intro N;destruct(s36_returns N)as(t&n&r&Ht&E).
 exists t;split;[exact Ht|];exists(lift(s36_main n r));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem s36_B_recurrent : forall N,exists t,N<=t /\VisitsAt s36_tm StB t.
Proof.
 intro N;destruct(s36_returns N)as(t&n&r&Ht&E).
 exists(t+1);split;[lia|];exists(lift(StB,([],S0,S1::(s36_P(n+0)++s36_wall 0++r))));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;reflexivity.
Qed.
Theorem s36_state_zero : QHBound 0 s36_tm.
Proof.
 intros q s[_ Hquiet];destruct q.
 - destruct(s36_A_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
 - destruct(s36_B_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
Qed.
Theorem s36_sound : NonHalt s36_tm /\QHBound 0 s36_tm.
Proof. split;[exact s36_nonhalt|exact s36_state_zero]. Qed.
Print Assumptions s36_return.
Print Assumptions s36_sound.
