(** A finite checked entry followed by a universal sliding frontier return.
    The unobserved left tail remains arbitrary and is never supplied as data. *)
From Coq Require Import List Arith Lia Bool NArith.
From BBB24 Require Import Statement Spec CTape Census TotalCompletion OneStateReach.
Import ListNotations.
Definition s66_tm:TM := fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DR StA
 |StA,S2=>mkTrans S0 DL StB |StA,S3=>mkTrans S1 DR StB
 |StB,S0=>mkTrans S3 DR StB |StB,S1=>mkTrans S3 DL StA
 |StB,S2=>mkTrans S1 DL StA |StB,S3=>mkTrans S2 DR StA end).
Definition s66_front q l r:cconf := (q,(l,chd r,ctl r)).
Definition s66_prefix := [S2;S2;S1;S1].
Definition s66_main l:cconf := (StA,(s66_prefix++l,S0,[])).
Definition s66_Bmain l:cconf := (StB,(S2::S1::S1::l,S2,[S1])).
Theorem s66_slide : forall l r,csteps s66_tm 11(StA,(s66_prefix++l,S0,r))=
 Some(s66_front StA(s66_prefix++S2::l)r).
Proof. intros l r;reflexivity. Qed.
Theorem s66_return : forall l,csteps s66_tm 11(s66_main l)=Some(s66_main(S2::l)).
Proof. intro l;exact(s66_slide l[]). Qed.
Theorem s66_B_after_one : forall l,csteps s66_tm 1(s66_main l)=Some(s66_Bmain l).
Proof. intro l;reflexivity. Qed.
Lemma s66_repeat_shift : forall n l,repeat S2 n++S2::l=S2::(repeat S2 n++l).
Proof. induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.
Theorem s66_returns : forall n l,csteps s66_tm(11*n)(s66_main l)=Some(s66_main(repeat S2 n++l)).
Proof.
 induction n;intro l;[reflexivity|].
 replace(11*S n)with(11+11*n)by lia;rewrite csteps_add,s66_return,IHn,s66_repeat_shift;reflexivity.
Qed.
Definition s66_count(n:N):nat := N.to_nat n.
Definition s66_cutcheck(c:cconf):bool := match c with
 |(StA,(l,S0,[]))=>match l with S2::S2::S1::S1::l=>true|_=>false end|_=>false end.
Definition s66_entrycheck := match csteps s66_tm(s66_count 1922128%N)c0 with
 |Some c=>s66_cutcheck c|None=>false end.
Lemma s66_cutcheck_sound : forall c,s66_cutcheck c=true ->exists l,c=s66_main l.
Proof.
 intros[q[[l h]r]];unfold s66_cutcheck;destruct q,h,r;try discriminate.
 destruct l as[|x l];[discriminate|];destruct x;try discriminate.
 destruct l as[|x l];[discriminate|];destruct x;try discriminate.
 destruct l as[|x l];[discriminate|];destruct x;try discriminate.
 destruct l as[|x l];[discriminate|];destruct x;try discriminate.
 intro H;exists l;reflexivity.
Qed.
Lemma s66_entry_sound : s66_entrycheck=true ->
 exists l,csteps s66_tm(s66_count 1922128%N)c0=Some(s66_main l).
Proof.
 unfold s66_entrycheck;destruct(csteps s66_tm(s66_count 1922128%N)c0)as[c|]eqn:E;[|discriminate].
 intro H;destruct(s66_cutcheck_sound c H)as(l&->);exists l;reflexivity.
Qed.
Lemma s66_entry_checked : s66_entrycheck=true.
Proof. vm_compute;reflexivity. Qed.
Opaque s66_count.
Theorem s66_A_late : forall N,exists k,N<=k /\VisitsAt s66_tm StA k.
Proof.
 intro N;destruct(s66_entry_sound s66_entry_checked)as(l&E).
 exists(s66_count 1922128%N+11*N);split;[lia|].
 exists(lift(s66_main(repeat S2 N++l)));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;apply s66_returns.
Qed.
Theorem s66_B_late : forall N,exists k,N<=k /\VisitsAt s66_tm StB k.
Proof.
 intro N;destruct(s66_entry_sound s66_entry_checked)as(l&E).
 exists(s66_count 1922128%N+(11*N+1));split;[lia|].
 exists(lift(s66_Bmain(repeat S2 N++l)));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E,csteps_add,s66_returns;apply s66_B_after_one.
Qed.
Theorem s66_state_zero : QHBound 0 s66_tm.
Proof.
 intros q s[Hv Hquiet];exfalso;destruct q.
 - destruct(s66_A_late(S s))as(k&Hk&Hv');apply(Hquiet k);[lia|exact Hv'].
 - destruct(s66_B_late(S s))as(k&Hk&Hv');apply(Hquiet k);[lia|exact Hv'].
Qed.
Lemma s66_total : Total s66_tm.
Proof. intros q h;unfold s66_tm;eexists;reflexivity. Qed.
Theorem s66_nonhalt : NonHalt s66_tm.
Proof. apply ore_total_nonhalt;exact s66_total. Qed.
Theorem s66_sound : NonHalt s66_tm /\QHBound 0 s66_tm.
Proof. split;[exact s66_nonhalt|exact s66_state_zero]. Qed.
Theorem s66_below_champion : QHBound score s66_tm.
Proof. intros q s H;pose proof(s66_state_zero q s H);lia. Qed.
Print Assumptions s66_slide.
Print Assumptions s66_entry_checked.
Print Assumptions s66_sound.
