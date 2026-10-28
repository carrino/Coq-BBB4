(** Concrete ternary counter: each A0 return extends the 2-block by one cell. *)
From Coq Require Import Arith Lia List.
From BBB24 Require Import Statement StatementTr CTape.
Import ListNotations.
Definition tc_tm:TM:=fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DL StB
 |StA,S2=>mkTrans S3 DL StB |StA,S3=>mkTrans S2 DR StA
 |StB,S0=>mkTrans S3 DR StA |StB,S1=>mkTrans S1 DR StA
 |StB,S2=>mkTrans S1 DL StB |StB,S3=>mkTrans S1 DR StB end).
Definition tc_front q l r:cconf:=(q,(l,chd r,ctl r)).
Definition tc_back q l r:cconf:=(q,(ctl l,chd l,r)).
Definition tc_first n l r:=tc_front StA(S1::l)(repeat S1 n++r).
Definition tc_after n l r:=tc_front StA(repeat S2 n++S1::l)r.
Lemma tc_repeat:forall (x:Sym) n r,repeat x n++x::r=x::(repeat x n++r).
Proof. intros x n;induction n;intro r;cbn;[reflexivity|now rewrite IHn]. Qed.

Lemma tc_carry:forall n l r,
 csteps tc_tm(S n)(tc_back StB(repeat S2 n++S1::l)r)=Some(tc_front StA(S1::l)(repeat S1 n++r)).
Proof.
 induction n;intros l r.
 - reflexivity.
 - cbn[repeat app tc_back csteps cstep tc_tm ctape_move chd ctl].
   change(csteps tc_tm(S n)(tc_back StB(repeat S2 n++S1::l)(S1::r))=
    Some(tc_front StA(S1::l)(S1::(repeat S1 n++r)))).
   rewrite IHn,tc_repeat;reflexivity.
Qed.
Lemma tc_bump:forall n l r h w,
 tc_tm StA h=Some(mkTrans w DL StB)->
 csteps tc_tm(n+2)(tc_after n l(h::r))=Some(tc_first n l(w::r)).
Proof.
 intros n l r h w H.
 replace(n+2)with(S(S n))by lia.
 cbn[csteps tc_after tc_front cstep chd ctl];rewrite H.
 change(csteps tc_tm(S n)(tc_back StB(repeat S2 n++S1::l)(w::r))=
   Some(tc_first n l(w::r))).
 apply tc_carry.
Qed.
Fixpoint tc_work n:=match n with 0=>0|S k=>3*tc_work k+2*k+5 end.
Lemma tc_block:forall n l r,
 csteps tc_tm(tc_work n)(tc_first n l r)=Some(tc_after n l r).
Proof.
 induction n;intros l r;[reflexivity|].
 assert(H1:csteps tc_tm(n+2+tc_work n)(tc_after n l(S1::r))=Some(tc_after n l(S2::r))).
 {rewrite csteps_add,(tc_bump n l r S1 S2 eq_refl);apply IHn. }
 assert(H2:csteps tc_tm(n+2+tc_work n)(tc_after n l(S2::r))=Some(tc_after n l(S3::r))).
 {rewrite csteps_add,(tc_bump n l r S2 S3 eq_refl);apply IHn. }
 replace(tc_first(S n)l r)with(tc_first n l(S1::r)).
 2:{unfold tc_first;rewrite tc_repeat;reflexivity. }
 replace(tc_work(S n))with(tc_work n+((n+2+tc_work n)+((n+2+tc_work n)+1)))by(cbn[tc_work];lia).
 rewrite csteps_add,IHn,csteps_add,H1,csteps_add,H2.
 reflexivity.
Qed.
Lemma tc_work_formula:forall n,tc_work n+n+3=3^(n+1).
Proof.
 induction n;[reflexivity|].
 replace(S n+1)with(S(n+1))by lia.
 rewrite Nat.pow_succ_r';cbn[tc_work];nia.
Qed.
Definition tc_gap n:=n+2+tc_work(S n).
Lemma tc_gap_positive:forall n,0<tc_gap n.
Proof. intro n;unfold tc_gap;lia. Qed.
Lemma tc_gap_formula:forall n,tc_gap n=3^(n+2)-2.
Proof.
 intro n;pose proof(tc_work_formula(S n))as H.
 replace(S n+1)with(n+2)in H by lia;unfold tc_gap;lia.
Qed.
Definition tc_return n:=tc_after n[][].
Lemma tc_next_return:forall n,
 csteps tc_tm(tc_gap n)(tc_return n)=Some(tc_return(S n)).
Proof.
 intro n;unfold tc_gap,tc_return.
 change(csteps tc_tm(n+2+tc_work(S n))(tc_after n[][S0])=Some(tc_after(S n)[][])).
 rewrite csteps_add,(tc_bump n[][]S0 S1 eq_refl).
 replace(tc_first n[][S1])with(tc_first(S n)[][]).
 - apply tc_block.
 - unfold tc_first;rewrite tc_repeat;reflexivity.
Qed.
Example tc_entry:csteps tc_tm 11 c0=Some(tc_return 1).
Proof. reflexivity. Qed.
Fixpoint tc_time n:=match n with 0=>11|S k=>tc_time k+tc_gap(S k)end.
Lemma tc_time_grows:forall n,n<=tc_time n.
Proof. induction n;cbn[tc_time];[lia|pose proof(tc_gap_positive(S n));lia]. Qed.
Lemma tc_returns:forall n,csteps tc_tm(tc_time n)c0=Some(tc_return(S n)).
Proof.
 induction n;[exact tc_entry|].
 cbn[tc_time];rewrite csteps_add,IHn;apply tc_next_return.
Qed.
Theorem tc_A0_recurrent:forall N,exists k,N<=k /\ FiresAt tc_tm(StA,S0)k.
Proof.
 intro N;exists(tc_time N);split;[apply tc_time_grows|].
 exists(lift(tc_return(S N)));split.
 - rewrite<-lift_c0;apply csteps_lift;apply tc_returns.
 - reflexivity.
Qed.
Print Assumptions tc_A0_recurrent.
