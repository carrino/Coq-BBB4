(** S042 exact finite scan programs.  Counts are arbitrary naturals. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement CTape.
Import ListNotations.
Definition s42_tm:TM := fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DL StA
 |StA,S2=>mkTrans S3 DR StB |StA,S3=>mkTrans S2 DL StA
 |StB,S0=>mkTrans S0 DR StB |StB,S1=>mkTrans S2 DR StA
 |StB,S2=>mkTrans S3 DR StA |StB,S3=>mkTrans S0 DL StA end).
Definition s42_front q l r:cconf := (q,(l,chd r,ctl r)).
Definition s42_back q l r:cconf := (q,(ctl l,chd l,r)).
Definition s42_flip q:=match q with StA=>StB|StB=>StA end.
Lemma s42_shift : forall(x:Sym)n l,repeat x n++x::l=x::(repeat x n++l).
Proof. intros x n;induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma s42_A_odd : forall h,h=S1\/h=S3->forall n l r,
 csteps s42_tm n(s42_back StA(repeat h n++l)r)=
 Some(s42_back StA l(repeat S2 n++r)).
Proof.
 intros h Hh n;induction n;intros l r;[reflexivity|].
 destruct Hh as [-> | ->];cbn[repeat app s42_back csteps cstep s42_tm ctape_move chd ctl];
 first [change(csteps s42_tm n(s42_back StA(repeat S1 n++l)(S2::r))=
 Some(s42_back StA l(S2::(repeat S2 n++r)))) |
 change(csteps s42_tm n(s42_back StA(repeat S3 n++l)(S2::r))=
 Some(s42_back StA l(S2::(repeat S2 n++r))))];
 rewrite IHn,s42_shift;reflexivity.
Qed.
Lemma s42_B_zeros : forall n l r,csteps s42_tm n
 (s42_front StB l(repeat S0 n++r))=
 Some(s42_front StB(repeat S0 n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app s42_front csteps cstep s42_tm ctape_move chd ctl].
 change(csteps s42_tm n(s42_front StB(S0::l)(repeat S0 n++r))=
 Some(s42_front StB(S0::(repeat S0 n++l))r)).
 rewrite IHn,s42_shift;reflexivity.
Qed.
Lemma s42_twos_pair : forall n q l r,csteps s42_tm(2*n)
 (s42_front q l(repeat S2(2*n)++r))=
 Some(s42_front q(repeat S3(2*n)++l)r).
Proof.
 induction n;intros q l r;[reflexivity|].
 replace(2*S n)with(S(S(2*n)))by lia.
 cbn[repeat app s42_front csteps cstep s42_tm ctape_move chd ctl].
 destruct q;first [change(csteps s42_tm(2*n)(s42_front StA (S3::S3::l)(repeat S2(2*n)++r))=
 Some(s42_front StA (S3::S3::(repeat S3(2*n)++l))r)) |
 change(csteps s42_tm(2*n)(s42_front StB (S3::S3::l)(repeat S2(2*n)++r))=
 Some(s42_front StB (S3::S3::(repeat S3(2*n)++l))r))];
 rewrite IHn,!s42_shift;reflexivity.
Qed.
Lemma s42_twos : forall n q l r,csteps s42_tm n
 (s42_front q l(repeat S2 n++r))=
 Some(s42_front(if Nat.even n then q else s42_flip q)(repeat S3 n++l)r).
Proof.
 intros n q l r;destruct(Nat.Even_or_Odd n)as[[k H]|[k H]];subst n.
 - rewrite Nat.even_mul;cbn;apply s42_twos_pair.
 - replace(2*k+1)with(S(2*k))by lia.
   rewrite Nat.even_succ,<-Nat.negb_even,Nat.even_mul;cbn.
   cbn[repeat app s42_front csteps cstep s42_tm ctape_move chd ctl].
   destruct q;first [change(csteps s42_tm(2*k)(s42_front StB (S3::l)(repeat S2(2*k)++r))=
    Some(s42_front StB (S3::(repeat S3(2*k)++l))r)) |
    change(csteps s42_tm(2*k)(s42_front StA (S3::l)(repeat S2(2*k)++r))=
    Some(s42_front StA (S3::(repeat S3(2*k)++l))r))];
   rewrite s42_twos_pair,s42_shift;reflexivity.
Qed.
