(** Generic boundary counter: the B2 slot is absent from the recurrent suffix. *)
From Coq Require Import List Arith Lia NArith.
From BBB24 Require Import Statement StatementTr Spec CTape Instructions Bounds Census.
Import ListNotations.
Section GenericCounter.
Variable b2:option Trans.
Definition bc_tm:TM:=fun q h=>match q,h with
 |StA,S0=>Some(mkTrans S1 DL StB) |StA,S1=>Some(mkTrans S2 DL StB)
 |StA,S2=>Some(mkTrans S3 DR StA) |StA,S3=>Some(mkTrans S3 DL StB)
 |StB,S0=>Some(mkTrans S2 DR StB) |StB,S1=>Some(mkTrans S1 DL StA)
 |StB,S2=>b2 |StB,S3=>Some(mkTrans S1 DR StA) end.
Definition front l r:cconf:=(StA,(l,chd r,ctl r)).
Definition at_one l r:cconf:=(StA,(l,S1,r)).
Fixpoint w12 n:=match n with 0=>[]|S n=>S1::S2::w12 n end.
Fixpoint w31 n:=match n with 0=>[]|S n=>S3::S1::w31 n end.
Fixpoint work n:=match n with 0=>12|S n=>2*work n+4 end.
Fixpoint walk n k:=match n with 0=>0|S n=>work k+walk n(S k)end.

Lemma w31_shift:forall n l,w31 n++S3::S1::l=S3::S1::(w31 n++l).
Proof. induction n;intro l;cbn[w31 app];[reflexivity|now rewrite IHn]. Qed.
Lemma w12_shift:forall n l,w12 n++S1::S2::l=S1::S2::(w12 n++l).
Proof. induction n;intro l;cbn[w12 app];[reflexivity|now rewrite IHn]. Qed.
Lemma walk_snoc:forall n k,walk(S n)k=walk n k+work(k+n).
Proof.
 induction n;intro k.
 - cbn[walk];rewrite !Nat.add_0_r;reflexivity.
 - change(work k+walk(S n)(S k)=work k+walk n(S k)+work(k+S n)).
   rewrite IHn;replace(S k+n)with(k+S n)by lia;lia.
Qed.
Lemma work_walk:forall n,work n=4*n+12+walk n 0.
Proof.
 induction n;[reflexivity|]. rewrite walk_snoc;cbn[work].
 rewrite Nat.add_0_l;lia.
Qed.
Lemma work_positive:forall n,0<work n.
Proof. induction n;cbn[work];lia. Qed.
Lemma work_formula:forall n,work n+4=16*2^n.
Proof. induction n;cbn[work Nat.pow];nia. Qed.

Lemma scan12:forall n l r,
 csteps bc_tm(4*n)(front(S3::l)(w12 n++r))=
 Some(front(S3::(w31 n++l))r).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(4*S n)with(4+4*n)by lia.
 rewrite csteps_add.
 change(csteps bc_tm(4*n)(front(S3::S3::S1::l)(w12 n++r))=
 Some(front(S3::S3::S1::(w31 n++l))r)).
 rewrite IHn,w31_shift;reflexivity.
Qed.
Lemma bounce13:forall l r,
 csteps bc_tm 7(front(S3::l)(S1::S3::r))=Some(at_one l(S1::S3::r)).
Proof. intros;reflexivity. Qed.
Lemma scan_return:forall n l r,
 csteps bc_tm(4*n+7)(front(S3::l)(w12 n++S1::S3::r))=
 Some(at_one(w31 n++l)(S1::S3::r)).
Proof. intros;rewrite csteps_add,scan12;apply bounce13. Qed.

Theorem one_block:forall m l r,
 csteps bc_tm(work m)(at_one(S3::S1::l)(w12 m++S1::S3::r))=
 Some(at_one l(w12(S m)++S1::S3::r)).
Proof.
 intro m;induction m using lt_wf_ind;intros l r.
 assert(Hconsume:forall n k,k+n<=m->forall l r,
   csteps bc_tm(walk n k)(at_one(w31 n++l)(w12 k++S1::S3::r))=
   Some(at_one l(w12(k+n)++S1::S3::r))).
 { induction n;intros k Hkn l0 r0.
   - cbn[walk w31 app];now rewrite Nat.add_0_r.
   - cbn[walk w31 app];rewrite csteps_add.
     rewrite(H k ltac:(lia)(w31 n++l0)r0).
     replace(k+S n)with(S k+n)by lia.
     apply IHn;lia. }
 replace(work m)with(3+(4*m+7+(walk m 0+2)))by(rewrite work_walk;lia).
 rewrite csteps_add.
 change(csteps bc_tm(4*m+7+(walk m 0+2))
   (front(S3::S1::S1::l)(w12 m++S1::S3::r))=
   Some(at_one l(w12(S m)++S1::S3::r))).
 rewrite csteps_add,scan_return,csteps_add.
 pose proof(Hconsume m 0 ltac:(lia)(S1::S1::l)r)as HC.
 cbn[w12 app Nat.add]in HC;rewrite HC.
 cbn[Nat.add w12];reflexivity.
Qed.

Theorem consume_blocks:forall n k l r,
 csteps bc_tm(walk n k)(at_one(w31 n++l)(w12 k++S1::S3::r))=
 Some(at_one l(w12(k+n)++S1::S3::r)).
Proof.
 induction n;intros k l r.
 - cbn[walk w31 app];now rewrite Nat.add_0_r.
 - cbn[walk w31 app];rewrite csteps_add,one_block.
   replace(k+S n)with(S k+n)by lia;apply IHn.
Qed.


Definition tail_word m:=w12 m++[S1;S3;S1;S2].
Definition main m:cconf:=(StA,([],S0,tail_word m)).
Lemma start_zero:forall m,
 csteps bc_tm 7(main m)=Some(front[S3;S1](tail_word m)).
Proof. intros;reflexivity. Qed.
Theorem main_next:forall m,
 csteps bc_tm(work m+4)(main m)=Some(main(S m)).
Proof.
 intro m;replace(work m+4)with(7+(4*m+7+(walk m 0+2)))by(rewrite work_walk;lia).
 rewrite csteps_add,start_zero,csteps_add.
 unfold tail_word;rewrite scan_return,csteps_add.
 pose proof(consume_blocks m 0 [S1] [S1;S2])as HC.
 cbn[w12 app Nat.add]in HC;rewrite HC.
 cbn[Nat.add w12];reflexivity.
Qed.
Lemma returns_from:forall m N,exists k n,N<=k/\csteps bc_tm k(main m)=Some(main n).
Proof.
 intros m N;induction N as[|N IH].
 - exists 0,m;split;[lia|reflexivity].
 - destruct IH as(k&n&Hk&E);exists(k+(work n+4)),(S n);split;[lia|].
   rewrite csteps_add,E;apply main_next.
Qed.
Lemma every_from:forall m n,exists d,csteps bc_tm n(main m)=Some d.
Proof.
 intros m n;destruct(returns_from m n)as(k&j&Hk&E).
 destruct(csteps_prefix bc_tm n k(main m)(main j)Hk E)as(d&Ed&_).
 exists d;exact Ed.
Qed.
Lemma prefix_hits:forall m tg,tg<>(StB,S2)->exists j d,
 csteps bc_tm j(main m)=Some d/\cinstr d=tg.
Proof.
 intros m[q h]Hnot;destruct q,h.
 - exists 0;eexists;split;reflexivity.
 - exists 4;eexists;split;reflexivity.
 - exists 3;eexists;split;reflexivity.
 - exists(7+(4*m+3));rewrite csteps_add,start_zero,csteps_add.
   unfold tail_word;rewrite scan12;eexists;split;reflexivity.
 - exists 1;eexists;split;reflexivity.
 - exists 2;eexists;split;reflexivity.
 - contradiction.
 - exists 5;eexists;split;reflexivity.
Qed.
End GenericCounter.

Lemma erased_extends:forall b2,TM_le(bc_tm None)(bc_tm b2).
Proof. intros b2 q h;destruct q,h;try(right;reflexivity);left;reflexivity. Qed.
Lemma B2_quiet:forall b2 p m,csteps(bc_tm b2)p c0=Some(main m)->
 forall n,p<=n->~FiresAt(bc_tm b2)(StB,S2)n.
Proof.
 intros b2 p m Eprefix n Hn(c&Eroot&Htarget);set(k:=n-p).
 assert(Eentry:stepn(bc_tm b2)p InitES=Some(lift(main m))).
 {rewrite <-lift_c0;apply csteps_lift;exact Eprefix. }
 destruct(every_from None m k)as(d&Ed).
 pose proof(extend_steps(bc_tm None)(bc_tm b2)k(lift(main m))(lift d)
   (erased_extends b2)(csteps_lift(bc_tm None)k(main m)d Ed))as Ea.
 replace n with(p+k)in Eroot by(unfold k;lia).
 rewrite stepn_add,Eentry,Ea in Eroot;injection Eroot as <-.
 rewrite cinstr_lift in Htarget.
 destruct(every_from None m(S k))as(e&Ee).
 replace(S k)with(k+1)in Ee by lia;rewrite csteps_add,Ed in Ee.
 destruct d as[q[[l h]r]];destruct q,h;try discriminate Htarget.
 cbn[csteps cstep bc_tm]in Ee;discriminate.
Qed.
Lemma returns:forall b2 p m,csteps(bc_tm b2)p c0=Some(main m)->
 forall N,exists k n,N<=k/\csteps(bc_tm b2)k c0=Some(main n).
Proof.
 intros b2 p m Eprefix N;destruct(returns_from b2 m N)as(k&n&Hk&E).
 exists(p+k),n;split;[lia|];rewrite csteps_add,Eprefix;exact E.
Qed.
Theorem seven_recurrent:forall b2 p m,csteps(bc_tm b2)p c0=Some(main m)->
 forall tg,tg<>(StB,S2)->forall N,exists k,N<=k/\FiresAt(bc_tm b2)tg k.
Proof.
 intros b2 p m Eprefix tg Hnot N;destruct(returns b2 p m Eprefix N)as(k&n&Hk&E).
 destruct(prefix_hits b2 n tg Hnot)as(j&d&Ehit&Htarget).
 exists(k+j);split;[lia|];exists(lift d);split.
 - rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;exact Ehit.
 - rewrite cinstr_lift;exact Htarget.
Qed.
Theorem entry_nonhalt:forall b2 p m,csteps(bc_tm b2)p c0=Some(main m)->NonHalt(bc_tm b2).
Proof.
 intros b2 p m Eprefix n Hnone;destruct(returns b2 p m Eprefix n)as(k&d&Hk&E).
 pose proof(csteps_lift(bc_tm b2)k c0(main d)E)as Er;rewrite lift_c0 in Er.
 destruct(stepn_prefix(bc_tm b2)n k InitES(lift(main d))Hk Er)as(c&Ec&_);congruence.
Qed.
Theorem entry_state_zero:forall b2 p m,csteps(bc_tm b2)p c0=Some(main m)->QHBound 0(bc_tm b2).
Proof.
 intros b2 p m Eprefix q s[_ Hquiet];destruct q.
 - destruct(seven_recurrent b2 p m Eprefix (StA,S1)ltac:(discriminate)(S s))as(k&Hk&Hfire).
   exfalso;apply(Hquiet k);[lia|eapply fires_visits;exact Hfire].
 - destruct(seven_recurrent b2 p m Eprefix (StB,S1)ltac:(discriminate)(S s))as(k&Hk&Hfire).
   exfalso;apply(Hquiet k);[lia|eapply fires_visits;exact Hfire].
Qed.
Theorem entry_instruction_bound:forall b2 p m,csteps(bc_tm b2)p c0=Some(main m)->QHBoundTr p(bc_tm b2).
Proof.
 intros b2 p m Eprefix tg s[Hfire Hquiet];destruct(instr_eqb tg(StB,S2))eqn:Et.
 - apply instr_eqb_spec in Et;subst tg.
   destruct(lt_dec s p);[lia|exfalso;exact(B2_quiet b2 p m Eprefix s ltac:(lia)Hfire)].
 - assert(Hnot:tg<>(StB,S2)). {intro E;subst tg;discriminate Et. }
   destruct(seven_recurrent b2 p m Eprefix tg Hnot(S s))as(k&Hk&Hf).
   exfalso;exact(Hquiet k ltac:(lia)Hf).
Qed.
Print Assumptions main_next.
Print Assumptions entry_instruction_bound.
