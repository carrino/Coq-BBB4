(** Symbolic counter investigation for tr24-2699702328. *)
From Coq Require Import List Arith Lia NArith.
From BBB24 Require Import Statement StatementTr Spec CTape Instructions Bounds Census.
Import ListNotations.
Section GenericCounter.
Variable b0:option Trans.
Definition tc_tm:TM:=fun q h=>match q,h with
 |StA,S0=>Some(mkTrans S1 DL StB) |StA,S1=>Some(mkTrans S2 DL StB)
 |StA,S2=>Some(mkTrans S3 DL StB) |StA,S3=>Some(mkTrans S2 DR StA)
 |StB,S0=>b0 |StB,S1=>Some(mkTrans S3 DR StA)
 |StB,S2=>Some(mkTrans S2 DL StB) |StB,S3=>Some(mkTrans S1 DR StA) end.
Definition twos:=repeat S2.
Definition front l r:cconf:=(StA,(l,chd r,ctl r)).
Definition back l r:cconf:=(StB,(ctl l,chd l,r)).
Definition at_two l r:cconf:=(StA,(l,S2,r)).
Fixpoint work n:=match n with 0=>3|S n=>2*work n+1 end.
Fixpoint walk n k:=match n with 0=>0|S n=>work k+walk n(S k)end.
Lemma two_shift:forall n l,twos n++S2::l=S2::(twos n++l).
Proof. induction n;intro l;cbn[twos repeat app];[reflexivity|now rewrite IHn]. Qed.
Lemma walk_snoc:forall n k,walk(S n)k=walk n k+work(k+n).
Proof.
 induction n;intro k.
 - cbn[walk];rewrite !Nat.add_0_r;reflexivity.
 - change(work k+walk(S n)(S k)=work k+walk n(S k)+work(k+S n)).
   rewrite IHn;replace(S k+n)with(k+S n)by lia;lia.
Qed.
Lemma work_walk:forall n,work n=n+3+walk n 0.
Proof. induction n;[reflexivity|];rewrite walk_snoc;cbn[work];rewrite Nat.add_0_l;lia. Qed.
Lemma work_formula:forall n,work n+1=4*2^n.
Proof. induction n;cbn[work Nat.pow];nia. Qed.

Lemma left_twos:forall n l r,
 csteps tc_tm n(back(twos n++l)r)=Some(back l(twos n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 change(csteps tc_tm n(back(twos n++l)(S2::r))=Some(back l(S2::(twos n++r)))).
 rewrite IHn,two_shift;reflexivity.
Qed.

Theorem one_block:forall n,1<=n->forall l r,
 csteps tc_tm(work n)(at_two(twos n++S1::l)r)=
 Some(front(twos(S n)++S1::l)r).
Proof.
 intro n;induction n using lt_wf_ind;intros Hpos l r.
 assert(Htail:forall p k,1<=k->k+p<=n->forall l r,
  csteps tc_tm(walk p k)(front(twos k++S1::l)(twos p++r))=
  Some(front(twos(k+p)++S1::l)r)).
 { induction p;intros k Hk Hkn l0 r0.
   - cbn[walk twos repeat app];now rewrite Nat.add_0_r.
   - cbn[walk];rewrite csteps_add.
     change(match csteps tc_tm(work k)(at_two(twos k++S1::l0)(twos p++r0))with
       Some d=>csteps tc_tm(walk p(S k))d|None=>None end=
       Some(front(twos(k+S p)++S1::l0)r0)).
     rewrite(H k ltac:(lia)Hk l0(twos p++r0)).
     replace(k+S p)with(S k+p)by lia;apply IHp;lia. }
 assert(Hscan:forall l r,
  csteps tc_tm(walk n 0)(front(S3::l)(twos n++r))=
  Some(front(twos n++S1::l)r)).
 { intros l0 r0;destruct n as[|p];[lia|].
   change(csteps tc_tm(3+walk p 1)(front(S3::l0)(S2::(twos p++r0)))=
    Some(front(S2::(twos p++S1::l0))r0)).
   rewrite csteps_add.
   change(csteps tc_tm(walk p 1)(front(twos 1++S1::l0)(twos p++r0))=
    Some(front(twos(S p)++S1::l0)r0)).
   replace(S p)with(1+p)by lia;apply Htail;lia. }
 replace(work n)with(1+(n+(1+(walk n 0+1))))by(rewrite work_walk;lia).
 rewrite csteps_add.
 change(csteps tc_tm(n+(1+(walk n 0+1)))(back(twos n++S1::l)(S3::r))=
  Some(front(twos(S n)++S1::l)r)).
 rewrite csteps_add,left_twos,csteps_add.
 change(csteps tc_tm(walk n 0+1)(front(S3::l)(twos n++S3::r))=
  Some(front(twos(S n)++S1::l)r)).
 rewrite csteps_add,Hscan;reflexivity.
Qed.

Lemma sweep_tail:forall p k,1<=k->forall l r,
 csteps tc_tm(walk p k)(front(twos k++S1::l)(twos p++r))=
 Some(front(twos(k+p)++S1::l)r).
Proof.
 induction p;intros k Hk l r.
 - cbn[walk twos repeat app];now rewrite Nat.add_0_r.
 - cbn[walk];rewrite csteps_add.
   change(match csteps tc_tm(work k)(at_two(twos k++S1::l)(twos p++r))with
       Some d=>csteps tc_tm(walk p(S k))d|None=>None end=
       Some(front(twos(k+S p)++S1::l)r)).
   rewrite(one_block k Hk l(twos p++r)).
   replace(k+S p)with(S k+p)by lia;apply IHp;lia.
Qed.
Theorem scan_twos:forall n,1<=n->forall l r,
 csteps tc_tm(walk n 0)(front(S3::l)(twos n++r))=
 Some(front(twos n++S1::l)r).
Proof.
 intros[|p]Hpos l r;[lia|].
 change(csteps tc_tm(3+walk p 1)(front(S3::l)(S2::(twos p++r)))=
    Some(front(S2::(twos p++S1::l))r)).
 rewrite csteps_add.
 change(csteps tc_tm(walk p 1)(front(twos 1++S1::l)(twos p++r))=
    Some(front(twos(S p)++S1::l)r)).
 replace(S p)with(1+p)by lia;apply sweep_tail;lia.
Qed.

Definition main n h:cconf:=(StA,(twos n++[S1],h,[])).
Lemma start_one:forall n,
 csteps tc_tm(n+2)(main n S1)=Some(front[S3](twos n++[S2])).
Proof.
 intro n;replace(n+2)with(1+(n+1))by lia;rewrite csteps_add.
 change(csteps tc_tm(n+1)(back(twos n++[S1])[S2])=Some(front[S3](twos n++[S2]))).
 rewrite csteps_add,left_twos;reflexivity.
Qed.
Lemma start_zero:forall n,
 csteps tc_tm(n+2)(main n S0)=Some(front[S3](twos n++[S1])).
Proof.
 intro n;replace(n+2)with(1+(n+1))by lia;rewrite csteps_add.
 change(csteps tc_tm(n+1)(back(twos n++[S1])[S1])=Some(front[S3](twos n++[S1]))).
 rewrite csteps_add,left_twos;reflexivity.
Qed.
Definition phase_one n:=n+2+walk(S n)0.
Definition phase_zero n:=n+2+walk n 0.
Theorem one_phase:forall n,
 csteps tc_tm(phase_one n)(main n S1)=Some(main(S n)S0).
Proof.
 intro n;unfold phase_one;rewrite csteps_add,start_one,two_shift.
 change(csteps tc_tm(walk(S n)0)(front[S3](twos(S n)++[]))=Some(main(S n)S0)).
 rewrite scan_twos by lia;reflexivity.
Qed.
Theorem zero_phase:forall n,
 csteps tc_tm(phase_zero(S n))(main(S n)S0)=Some(main(S n)S1).
Proof.
 intro n;unfold phase_zero;rewrite csteps_add,start_zero.
 rewrite scan_twos by lia;reflexivity.
Qed.
Definition gap n:=phase_one n+phase_zero(S n).
Lemma gap_formula:forall n,gap n+5=16*2^n.
Proof.
 intro n;pose proof(work_walk n);pose proof(work_walk(S n));pose proof(work_formula n).
 unfold gap,phase_one,phase_zero;rewrite walk_snoc;cbn[work Nat.add]in *;lia.
Qed.
Theorem main_next:forall n,
 csteps tc_tm(gap n)(main n S1)=Some(main(S n)S1).
Proof. intro n;unfold gap;rewrite csteps_add,one_phase;apply zero_phase. Qed.
End GenericCounter.
Definition actual_b0:option Trans:=Some(mkTrans S1 DR StA).
Definition actual:=tc_tm actual_b0.
Definition erased:=tc_tm None.
Example entry_two:csteps actual 2 c0=Some(main 0 S1).
Proof. reflexivity. Qed.
Example entry:csteps actual 13 c0=Some(main 1 S1).
Proof. change(csteps actual(2+11)c0=Some(main 1 S1));rewrite csteps_add,entry_two;exact(main_next actual_b0 0). Qed.

Lemma returns_from:forall b0 N,exists k n,1<=n/\N<=k/\
 csteps(tc_tm b0)k(main 0 S1)=Some(main n S1).
Proof.
 intros b0 N;induction N as[|N IH].
 - exists(gap 0),1;repeat split;try lia;apply main_next.
 - destruct IH as(k&n&Hn&Hk&E);exists(k+gap n),(S n);repeat split;try lia.
   + unfold gap,phase_one,phase_zero;lia.
   + rewrite csteps_add,E;apply main_next.
Qed.
Lemma every_from:forall b0 n,exists d,csteps(tc_tm b0)n(main 0 S1)=Some d.
Proof.
 intros b0 n;destruct(returns_from b0 n)as(k&j&Hj&Hk&E).
 destruct(csteps_prefix(tc_tm b0)n k(main 0 S1)(main j S1)Hk E)as(d&Ed&_).
 exists d;exact Ed.
Qed.
Lemma returns:forall N,exists k n,1<=n/\N<=k/\csteps actual k c0=Some(main n S1).
Proof.
 intro N;destruct(returns_from actual_b0 N)as(k&n&Hn&Hk&E).
 exists(2+k),n;repeat split;try lia;rewrite csteps_add,entry_two;exact E.
Qed.
Lemma erased_extends:TM_le erased actual.
Proof. intros q h;destruct q,h;try(right;reflexivity);left;reflexivity. Qed.
Lemma B0_quiet:forall n,2<=n->~FiresAt actual(StB,S0)n.
Proof.
 intros n Hn(c&Eroot&Htarget);set(k:=n-2).
 assert(Eentry:stepn actual 2 InitES=Some(lift(main 0 S1))).
 {rewrite <-lift_c0;apply csteps_lift;exact entry_two. }
 destruct(every_from None k)as(d&Ed).
 pose proof(extend_steps erased actual k(lift(main 0 S1))(lift d)
   erased_extends(csteps_lift erased k(main 0 S1)d Ed))as Ea.
 replace n with(2+k)in Eroot by(unfold k;lia).
 rewrite stepn_add,Eentry,Ea in Eroot;injection Eroot as <-.
 rewrite cinstr_lift in Htarget.
 destruct(every_from None(S k))as(e&Ee).
 replace(S k)with(k+1)in Ee by lia;rewrite csteps_add,Ed in Ee.
 destruct d as[q[[l h]r]];destruct q,h;try discriminate Htarget.
 cbn[csteps cstep erased tc_tm]in Ee;discriminate.
Qed.

Lemma prefix_hits:forall b0 n,1<=n->forall tg,tg<>(StB,S0)->exists j d,
 csteps(tc_tm b0)j(main n S1)=Some d/\cinstr d=tg.
Proof.
 intros b0 n Hn[q h]Hnot;destruct q,h.
 - exists(phase_one n),(main(S n)S0);split;[apply one_phase|reflexivity].
 - exists 0;eexists;split;reflexivity.
 - exists(n+2);rewrite start_one;destruct n;[lia|];eexists;split;reflexivity.
 - exists(n+2+2);rewrite csteps_add,start_one;destruct n;[lia|];eexists;split;reflexivity.
 - contradiction.
 - exists(1+n);rewrite csteps_add.
   change(exists d,csteps(tc_tm b0)n(back(twos n++[S1])[S2])=Some d/\cinstr d=(StB,S1)).
   rewrite left_twos;eexists;split;reflexivity.
 - exists 1;destruct n;[lia|];eexists;split;reflexivity.
 - exists(n+2+1);rewrite csteps_add,start_one;destruct n;[lia|];eexists;split;reflexivity.
Qed.
Theorem seven_recurrent:forall tg,tg<>(StB,S0)->forall N,exists k,N<=k/\FiresAt actual tg k.
Proof.
 intros tg Hnot N;destruct(returns N)as(k&n&Hn&Hk&E).
 destruct(prefix_hits actual_b0 n Hn tg Hnot)as(j&d&Ehit&Htarget).
 exists(k+j);split;[lia|];exists(lift d);split.
 - rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;exact Ehit.
 - rewrite cinstr_lift;exact Htarget.
Qed.
Lemma actual_nonhalt:NonHalt actual.
Proof.
 intros n Hnone;destruct(returns n)as(k&d&Hd&Hk&E).
 pose proof(csteps_lift actual k c0(main d S1)E)as Er;rewrite lift_c0 in Er.
 destruct(stepn_prefix actual n k InitES(lift(main d S1))Hk Er)as(c&Ec&_);congruence.
Qed.
Theorem state_zero:QHBound 0 actual.
Proof.
 intros q s[_ Hquiet];destruct q.
 - destruct(seven_recurrent(StA,S1)ltac:(discriminate)(S s))as(k&Hk&Hfire).
   exfalso;apply(Hquiet k);[lia|eapply fires_visits;exact Hfire].
 - destruct(seven_recurrent(StB,S1)ltac:(discriminate)(S s))as(k&Hk&Hfire).
   exfalso;apply(Hquiet k);[lia|eapply fires_visits;exact Hfire].
Qed.
Theorem instruction_bound:QHBoundTr 2 actual.
Proof.
 intros tg s[Hfire Hquiet];destruct(instr_eqb tg(StB,S0))eqn:Et.
 - apply instr_eqb_spec in Et;subst tg.
   destruct(lt_dec s 2);[lia|exfalso;exact(B0_quiet s ltac:(lia)Hfire)].
 - assert(Hnot:tg<>(StB,S0)).
   { intro E;subst tg;discriminate Et. }
   destruct(seven_recurrent tg Hnot(S s))as(k&Hk&Hf).
   exfalso;exact(Hquiet k ltac:(lia)Hf).
Qed.
Theorem instruction_attains:AttainsTr actual 2.
Proof.
 exists(StB,S0),1;split;[split|reflexivity].
 - eexists;split;reflexivity.
 - intros n Hn;apply B0_quiet;lia.
Qed.
Theorem family_run:NonHalt actual/\Bounds 0%N 2%N actual.
Proof. split;[exact actual_nonhalt|split;[exact state_zero|exact instruction_bound]]. Qed.
Print Assumptions main_next.
Print Assumptions family_run.
Print Assumptions instruction_attains.
