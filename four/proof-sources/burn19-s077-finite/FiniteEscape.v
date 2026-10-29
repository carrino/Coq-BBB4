(** A finite checked prefix followed by a universal B0 blank-right drift.
    Only the prefix predicates are evaluated; no generated tape is trusted. *)
From Coq Require Import List Arith Lia Bool NArith.
From BBB24 Require Import Statement Spec CTape Census TotalCompletion OneStateReach.
Import ListNotations.
Definition s77_tm:TM := fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DR StB
 |StA,S2=>mkTrans S3 DL StA |StA,S3=>mkTrans S2 DR StA
 |StB,S0=>mkTrans S3 DR StB |StB,S1=>mkTrans S3 DL StA
 |StB,S2=>mkTrans S0 DL StB |StB,S3=>mkTrans S1 DL StB end).
Definition s77_count(n:N):nat := N.to_nat n.
Definition s77_blank h := match h with S0=>true|_=>false end.
Definition s77_zeros := Forall(fun h=>h=S0).
Definition s77_endcheck(n:N) := match csteps s77_tm(s77_count n)c0 with
 |Some(StB,(_,S0,r))=>forallb s77_blank r|_=>false end.
Definition s77_visit_Acheck(n:N) := match csteps s77_tm(s77_count n)c0 with
 |Some(StA,_)=>true|_=>false end.
Lemma s77_count_le : forall a b,(a<=b)%N ->s77_count a<=s77_count b.
Proof. intros a b H;unfold s77_count;apply Nat.compare_le_iff;rewrite <-N2Nat.inj_compare;exact H. Qed.
Lemma s77_score_count : score=s77_count scoreN.
Proof. unfold score,s77_count;reflexivity. Qed.
Lemma s77_bound_count : s77_count 4194304%N=N.to_nat 4194304%N.
Proof. reflexivity. Qed.
Lemma s77_escape_successor : s77_count 2501552%N=S(s77_count 2501551%N).
Proof. unfold s77_count;change(N.to_nat(N.succ 2501551%N)=S(N.to_nat 2501551%N));apply N2Nat.inj_succ. Qed.
Lemma s77_total : Total s77_tm.
Proof. intros q h;unfold s77_tm;eexists;reflexivity. Qed.
Theorem s77_nonhalt : NonHalt s77_tm.
Proof. apply ore_total_nonhalt;exact s77_total. Qed.
Lemma s77_endcheck_sound : forall n,s77_endcheck n=true ->
 exists l r,csteps s77_tm(s77_count n)c0=Some(StB,(l,S0,r)) /\s77_zeros r.
Proof.
 intros n H;unfold s77_endcheck in H.
 destruct(csteps s77_tm(s77_count n)c0)as[[q[[l h]r]]|]eqn:E;[|discriminate].
 destruct q,h;try discriminate.
 exists l,r;split;[reflexivity|].
 apply Forall_forall;intros x Hin;apply forallb_forall with(x:=x)in H;[|exact Hin].
 destruct x;cbn[s77_blank]in H;try discriminate;reflexivity.
Qed.
Lemma s77_visit_Acheck_sound : forall n,s77_visit_Acheck n=true ->VisitsAt s77_tm StA(s77_count n).
Proof.
 intros n H;unfold s77_visit_Acheck in H.
 destruct(csteps s77_tm(s77_count n)c0)as[[q ct]|]eqn:E;try discriminate.
 destruct q;[|discriminate].
 exists(lift(StA,ct));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem s77_B_drift : forall t l r,s77_zeros r ->
 exists l' r',csteps s77_tm t(StB,(l,S0,r))=Some(StB,(l',S0,r')) /\s77_zeros r'.
Proof.
 induction t;intros l r Hz.
 - exists l,r;auto.
 - destruct r as[|h r].
   + cbn[csteps cstep s77_tm ctape_move chd ctl];apply IHt;constructor.
   + inversion Hz as[|h' r' Hh Htail];subst.
     cbn[csteps cstep s77_tm ctape_move chd ctl];apply IHt;exact Htail.
Qed.
Theorem s77_B_forever_from_check : forall n,s77_endcheck n=true ->
 forall k,s77_count n<=k ->VisitsAt s77_tm StB k.
Proof.
 intros n H k Hk;destruct(s77_endcheck_sound n H)as(l&r&E&Hz).
 destruct(s77_B_drift(k-s77_count n)l r Hz)as(l'&r'&Et&_).
 exists(lift(StB,(l',S0,r')));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift.
 replace k with(s77_count n+(k-s77_count n))by lia;rewrite csteps_add,E;exact Et.
Qed.
Theorem s77_A_quiet_from_check : forall n,s77_endcheck n=true ->QuietFrom s77_tm StA(s77_count n).
Proof.
 intros n H k Hk(c&Ec&Hs);destruct(s77_B_forever_from_check n H k Hk)as(c'&Ec'&Hs').
 rewrite Ec in Ec';injection Ec' as <-;congruence.
Qed.
Theorem s77_bound_from_check : forall n,s77_endcheck n=true ->QHBound(s77_count n)s77_tm.
Proof.
 intros n H q s[Hv Hquiet];destruct(le_lt_dec(s77_count n)s);[|lia].
 destruct q.
 - destruct Hv as(c&Ec&Hs);destruct(s77_B_forever_from_check n H s l)as(c'&Ec'&Hs').
   rewrite Ec in Ec';injection Ec' as <-;congruence.
 - exfalso;apply(Hquiet(S s));[lia|apply(s77_B_forever_from_check n H);lia].
Qed.
Print Assumptions s77_bound_from_check.
