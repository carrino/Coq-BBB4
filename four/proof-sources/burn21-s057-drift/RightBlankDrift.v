(** S057: Coq recomputes two finite cuts, then a universal blank-right
    B0 drift proves permanent state B and the exact last A visit.
    The census inventory uses the conservative bound 2^22. *)
From Coq Require Import List Arith Lia Bool NArith.
From BBB24 Require Import Statement Spec CTape Census OneStateReach.
Import ListNotations.
Definition sd_tm:TM:=fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DL StB
 |StA,S2=>mkTrans S1 DR StB |StA,S3=>mkTrans S1 DR StA
 |StB,S0=>mkTrans S1 DR StB |StB,S1=>mkTrans S3 DL StA
 |StB,S2=>mkTrans S3 DR StA |StB,S3=>mkTrans S2 DL StB end).
Definition sd_count(n:N):nat:=N.to_nat n.
Definition sd_stepsN:N:=2333909%N.
Definition sd_lastN:N:=2333908%N.
Definition sd_boundN:N:=4194304%N.
Definition sd_escaped(result:option cconf):bool:=match result with
 |Some(StB,(_,S0,r))=>all_blank r|_=>false end.
Lemma sd_finite_certificate : sd_escaped(csteps sd_tm(sd_count sd_stepsN)c0)=true.
Proof. vm_compute;reflexivity. Qed.
Definition sd_is_A(result:option cconf):bool:=match result with
 |Some(StA,_)=>true|_=>false end.
Lemma sd_lastA_certificate : sd_is_A(csteps sd_tm(sd_count sd_lastN)c0)=true.
Proof. vm_compute;reflexivity. Qed.
Lemma sd_score_count : score=sd_count scoreN.
Proof. unfold score,sd_count;reflexivity. Qed.
Lemma sd_bound_count : sd_count sd_boundN=N.to_nat 4194304%N.
Proof. unfold sd_count,sd_boundN;reflexivity. Qed.
Lemma sd_next_count : sd_count sd_stepsN=S(sd_count sd_lastN).
Proof.
 unfold sd_count;replace sd_stepsN with(N.succ sd_lastN)by reflexivity.
 rewrite N2Nat.inj_succ;reflexivity.
Qed.
Lemma sd_count_le : forall a b,(a<=b)%N->sd_count a<=sd_count b.
Proof. intros a b H;unfold sd_count;apply Nat.compare_le_iff;rewrite <-N2Nat.inj_compare;exact H. Qed.
Opaque sd_count.
Lemma sd_prefix_result : exists l r,
 csteps sd_tm(sd_count sd_stepsN)c0=Some(StB,(l,S0,r))/\all_blank r=true.
Proof.
 pose proof sd_finite_certificate as H;unfold sd_escaped in H.
 destruct(csteps sd_tm(sd_count sd_stepsN)c0)as[[q[[l h]r]]|]eqn:E;[|discriminate H].
 destruct q,h;cbn in H;try discriminate H.
 exists l,r;split;[reflexivity|exact H].
Qed.
Lemma sd_blank_head : forall r,all_blank r=true->chd r=S0.
Proof.
 intros[|h r]H;[reflexivity|];cbn[all_blank]in H.
 apply andb_prop in H as[H _];apply sym_eqb_spec;exact H.
Qed.
Lemma sd_blank_tail : forall r,all_blank r=true->all_blank(ctl r)=true.
Proof. intros[|h r]H;[reflexivity|];cbn[all_blank]in H;apply andb_prop in H;tauto. Qed.
Theorem sd_B_drift : forall t l r,all_blank r=true->exists l' r',
 csteps sd_tm t(StB,(l,S0,r))=Some(StB,(l',S0,r'))/\all_blank r'=true.
Proof.
 induction t;intros l r Hr.
 - exists l,r;split;[reflexivity|exact Hr].
 - change(exists l' r',csteps sd_tm t(StB,(S1::l,chd r,ctl r))=
   Some(StB,(l',S0,r'))/\all_blank r'=true).
   rewrite(sd_blank_head r Hr);apply IHt;apply sd_blank_tail;exact Hr.
Qed.
Theorem sd_B_forever : forall n,sd_count sd_stepsN<=n->VisitsAt sd_tm StB n.
Proof.
 intros n Hn;destruct sd_prefix_result as(l&r&E&Hr).
 destruct(sd_B_drift(n-sd_count sd_stepsN)l r Hr)as(l'&r'&Et&_).
 exists(lift(StB,(l',S0,r')));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift.
 replace n with(sd_count sd_stepsN+(n-sd_count sd_stepsN))by lia.
 rewrite csteps_add,E;exact Et.
Qed.
Theorem sd_A_quiet : QuietFrom sd_tm StA(sd_count sd_stepsN).
Proof.
 intros n Hn(c&Ec&Hs);destruct(sd_B_forever n Hn)as(c'&Ec'&Hs').
 rewrite Ec in Ec';injection Ec' as <-;congruence.
Qed.
Lemma sd_lastA_visit : VisitsAt sd_tm StA(sd_count sd_lastN).
Proof.
 pose proof sd_lastA_certificate as H;unfold sd_is_A in H.
 destruct(csteps sd_tm(sd_count sd_lastN)c0)as[[q tp]|]eqn:E;[|discriminate H].
 destruct q;[|discriminate H].
 exists(lift(StA,tp));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem sd_attains : AttainsSt sd_tm(sd_count sd_stepsN).
Proof.
 exists StA,(sd_count sd_lastN);split.
 - split;[exact sd_lastA_visit|].
   intros n Hn;apply sd_A_quiet;rewrite sd_next_count;lia.
 - symmetry;exact sd_next_count.
Qed.
Theorem sd_nonhalt : NonHalt sd_tm.
Proof. apply ore_total_nonhalt;intros q h;destruct q,h;eexists;reflexivity. Qed.
Theorem sd_prefix_bound : QHBound(sd_count sd_stepsN)sd_tm.
Proof.
 intros q s[Hv Hquiet];destruct(le_lt_dec(sd_count sd_stepsN)s);[|lia].
 destruct q.
 - exfalso;exact(sd_A_quiet s l Hv).
 - exfalso;apply(Hquiet(S s));[lia|apply sd_B_forever;lia].
Qed.
Theorem sd_sound : NonHalt sd_tm/\QHBound(sd_count sd_boundN)sd_tm.
Proof.
 split;[exact sd_nonhalt|].
 intros q s Hq;eapply Nat.le_trans;[exact(sd_prefix_bound q s Hq)|].
 apply sd_count_le;unfold sd_stepsN,sd_boundN;vm_compute;discriminate.
Qed.
Theorem sd_quasihalts : QuasiHaltsSt sd_tm.
Proof.
 exists StA;split.
 - exists 0;exists InitES;split;reflexivity.
 - exists(sd_count sd_stepsN);exact sd_A_quiet.
Qed.
Theorem sd_below_champion : QHBound score sd_tm.
Proof.
 rewrite sd_score_count;intros q s Hq.
 eapply Nat.le_trans;[exact(proj2 sd_sound q s Hq)|].
 apply sd_count_le;unfold sd_boundN,scoreN;vm_compute;discriminate.
Qed.
Print Assumptions sd_sound.
Print Assumptions sd_quasihalts.
Print Assumptions sd_attains.
