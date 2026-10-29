(** A context-parametric normalizer shared by the three cut siblings. *)
From Coq Require Import List Arith Lia.
From BBB24 Require Import Statement Spec CTape Census OneStateReach TotalCompletion.
Import ListNotations.
Inductive bn_variant:=bn_LeftZero|bn_RightZero|bn_RightOne.
Definition bn_tm(v:bn_variant):TM:=fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB|StA,S1=>mkTrans S0 DR StA
 |StA,S2=>mkTrans S0 DL StB|StA,S3=>mkTrans S2 DR StB
 |StB,S0=>mkTrans S3 DR StB|StB,S1=>mkTrans S3 DL StA
 |StB,S2=>match v with bn_LeftZero=>mkTrans S0 DL StB
  |bn_RightZero=>mkTrans S0 DR StA|bn_RightOne=>mkTrans S1 DR StA end
 |StB,S3=>mkTrans S1 DR StA end).
Definition bn_at q l h r:cconf:=(q,(l,h,r)).
Definition bn_back q l r:cconf:=(q,(ctl l,chd l,r)).
Definition bn_cut l:=bn_at StA l S0[].
Inductive bn_token:=ba|bb|bc|bd.
Definition bn_code t:=match t with
 |ba=>[S1;S3;S3;S1;S2]|bb=>[S0;S1;S2]
 |bc=>[S3;S1;S2]|bd=>[S1;S3;S3;S1;S3;S3;S1;S2]end.
Fixpoint bn_enc ts:=match ts with []=>[]|t::ts=>bn_code t++bn_enc ts end.
Definition bn_Fword:=[S3;S1;S3;S1;S3].
Definition bn_Jword:=[S3;S1;S3].
Fixpoint bn_F ts:=match ts with
 |[]=>[ba;bb]|ba::ts=>ba::bn_F ts|bb::ts=>bd::ts
 |bc::ts=>bb::bn_F ts|bd::ts=>ba::ba::bc::ts end.
Fixpoint bn_cost ts:=match ts with
 |[]=>30|ba::ts=>38+bn_cost ts|bb::ts=>10
 |bc::ts=>26+bn_cost ts|bd::ts=>46 end.
Lemma bn_left_a : forall v l r,csteps(bn_tm v)29
 (bn_back StB(bn_code ba++l)(S0::r))=
 Some(bn_back StB l(S0::bn_Fword++r)).
Proof. destruct v;intros l r;destruct l;reflexivity. Qed.
Lemma bn_left_c : forall v l r,csteps(bn_tm v)23
 (bn_back StB(bn_code bc++l)([S0;S3;S1]++r))=
 Some(bn_back StB l(S0::bn_Fword++r)).
Proof. destruct v;intros l r;destruct l;reflexivity. Qed.
Lemma bn_right_a : forall v l r,csteps(bn_tm v)9
 (bn_at StA l S3(bn_Fword++r))=
 Some(bn_at StA(bn_code ba++l)S3 r).
Proof. destruct v;intros l r;reflexivity. Qed.
Lemma bn_right_b : forall v l r,csteps(bn_tm v)3
 (bn_at StA l S3(bn_Jword++r))=
 Some(bn_at StA(bn_code bb++l)S3 r).
Proof. destruct v;intros l r;reflexivity. Qed.
Lemma bn_stop_b : forall v l r,csteps(bn_tm v)10
 (bn_back StB(bn_code bb++l)(S0::bn_Fword++r))=
 Some(bn_at StA(bn_code bd++l)S3 r).
Proof. destruct v;intros l r;reflexivity. Qed.
Lemma bn_stop_d : forall v l r,csteps(bn_tm v)46
 (bn_back StB(bn_code bd++l)(S0::bn_Fword++r))=
 Some(bn_at StA(bn_enc[ba;ba;bc]++l)S3 r).
Proof. destruct v;intros l r;reflexivity. Qed.
Lemma bn_stop_end : forall v r,csteps(bn_tm v)30
 (bn_back StB[S3](S0::bn_Fword++r))=
 Some(bn_at StA(bn_enc[ba;bb]++[S3])S3 r).
Proof. destruct v;intro r;reflexivity. Qed.
Theorem bn_normalize : forall ts v r,csteps(bn_tm v)(bn_cost ts)
 (bn_back StB(bn_enc ts++[S3])(S0::bn_Fword++r))=
 Some(bn_at StA(bn_enc(bn_F ts)++[S3])S3 r).
Proof.
 intro ts;induction ts as[|t ts IH];intros v r;[apply bn_stop_end|].
 destruct t.
 - change(csteps(bn_tm v)(38+bn_cost ts)
   (bn_back StB(bn_code ba++(bn_enc ts++[S3]))(S0::bn_Fword++r))=
   Some(bn_at StA(bn_code ba++(bn_enc(bn_F ts)++[S3]))S3 r)).
   replace(38+bn_cost ts)with(29+(bn_cost ts+9))by lia.
   rewrite csteps_add,bn_left_a,csteps_add,IH,bn_right_a;reflexivity.
 - change(csteps(bn_tm v)10(bn_back StB(bn_code bb++(bn_enc ts++[S3]))(S0::bn_Fword++r))=
   Some(bn_at StA(bn_code bd++(bn_enc ts++[S3]))S3 r));apply bn_stop_b.
 - change(csteps(bn_tm v)(26+bn_cost ts)
   (bn_back StB(bn_code bc++(bn_enc ts++[S3]))([S0;S3;S1]++bn_Jword++r))=
   Some(bn_at StA(bn_code bb++(bn_enc(bn_F ts)++[S3]))S3 r)).
   replace(26+bn_cost ts)with(23+(bn_cost ts+3))by lia.
   rewrite csteps_add,bn_left_c,csteps_add,IH,bn_right_b;reflexivity.
 - change(csteps(bn_tm v)46(bn_back StB(bn_code bd++(bn_enc ts++[S3]))(S0::bn_Fword++r))=
   Some(bn_at StA(bn_enc[ba;ba;bc]++(bn_enc ts++[S3]))S3 r));apply bn_stop_d.
Qed.
Lemma bn_right_bb : forall v l r,csteps(bn_tm v)6
 (bn_at StA l S3(bn_Jword++bn_Jword++r))=
 Some(bn_at StA(bn_code bb++bn_code bb++l)S3 r).
Proof. destruct v;intros l r;reflexivity. Qed.
Print Assumptions bn_normalize.
