(** Universal boundary macros for tr24-2806290152.
    Small finite traces select the invariant; the lemmas quantify over all words. *)
From Coq Require Import List Arith Lia NArith.
From BBB24 Require Import Statement StatementTr Spec CTape Instructions Bounds InstructionPortfolio.
Import ListNotations.

Definition sp_tm:TM:=fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DL StB
 |StA,S2=>mkTrans S3 DR StA |StA,S3=>mkTrans S3 DL StB
 |StB,S0=>mkTrans S1 DR StB |StB,S1=>mkTrans S1 DL StA
 |StB,S2=>mkTrans S3 DR StA |StB,S3=>mkTrans S1 DR StA end).
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
 csteps sp_tm(4*n)(front(S3::l)(w12 n++r))=
 Some(front(S3::(w31 n++l))r).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(4*S n)with(4+4*n)by lia.
 rewrite csteps_add.
 change(csteps sp_tm(4*n)(front(S3::S3::S1::l)(w12 n++r))=
 Some(front(S3::S3::S1::(w31 n++l))r)).
 rewrite IHn,w31_shift;reflexivity.
Qed.
Lemma bounce13:forall l r,
 csteps sp_tm 7(front(S3::l)(S1::S3::r))=Some(at_one l(S1::S3::r)).
Proof. intros;reflexivity. Qed.
Lemma scan_return:forall n l r,
 csteps sp_tm(4*n+7)(front(S3::l)(w12 n++S1::S3::r))=
 Some(at_one(w31 n++l)(S1::S3::r)).
Proof. intros;rewrite csteps_add,scan12;apply bounce13. Qed.

Theorem one_block:forall m l r,
 csteps sp_tm(work m)(at_one(S3::S1::l)(w12 m++S1::S3::r))=
 Some(at_one l(w12(S m)++S1::S3::r)).
Proof.
 intro m;induction m using lt_wf_ind;intros l r.
 assert(Hconsume:forall n k,k+n<=m->forall l r,
   csteps sp_tm(walk n k)(at_one(w31 n++l)(w12 k++S1::S3::r))=
   Some(at_one l(w12(k+n)++S1::S3::r))).
 { induction n;intros k Hkn l0 r0.
   - cbn[walk w31 app];now rewrite Nat.add_0_r.
   - cbn[walk w31 app];rewrite csteps_add.
     rewrite(H k ltac:(lia)(w31 n++l0)r0).
     replace(k+S n)with(S k+n)by lia.
     apply IHn;lia. }
 replace(work m)with(3+(4*m+7+(walk m 0+2)))by(rewrite work_walk;lia).
 rewrite csteps_add.
 change(csteps sp_tm(4*m+7+(walk m 0+2))
   (front(S3::S1::S1::l)(w12 m++S1::S3::r))=
   Some(at_one l(w12(S m)++S1::S3::r))).
 rewrite csteps_add,scan_return,csteps_add.
 pose proof(Hconsume m 0 ltac:(lia)(S1::S1::l)r)as HC.
 cbn[w12 app Nat.add]in HC;rewrite HC.
 cbn[Nat.add w12];reflexivity.
Qed.

Theorem consume_blocks:forall n k l r,
 csteps sp_tm(walk n k)(at_one(w31 n++l)(w12 k++S1::S3::r))=
 Some(at_one l(w12(k+n)++S1::S3::r)).
Proof.
 induction n;intros k l r.
 - cbn[walk w31 app];now rewrite Nat.add_0_r.
 - cbn[walk w31 app];rewrite csteps_add,one_block.
   replace(k+S n)with(S k+n)by lia;apply IHn.
Qed.

Definition tail_word m:=w12 m++[S1;S3;S1;S3;S1;S2].
Definition main m h:cconf:=(StA,([],h,tail_word m)).
Lemma start_zero:forall m,
 csteps sp_tm 9(main m S0)=Some(front[S3;S1;S1](tail_word m)).
Proof. intros;reflexivity. Qed.
Lemma start_one:forall m,
 csteps sp_tm 3(main m S1)=Some(front[S3;S1](tail_word m)).
Proof. intros;reflexivity. Qed.

Theorem zero_phase:forall m,
 csteps sp_tm(work m+6)(main m S0)=Some(main(S m)S1).
Proof.
 intro m;replace(work m+6)with(9+(4*m+7+(walk m 0+2)))by(rewrite work_walk;lia).
 rewrite csteps_add,start_zero,csteps_add.
 unfold tail_word;rewrite scan_return,csteps_add.
 pose proof(consume_blocks m 0 [S1;S1] [S1;S3;S1;S2])as HC.
 cbn[w12 app Nat.add]in HC;rewrite HC.
 cbn[Nat.add w12];reflexivity.
Qed.
Theorem one_phase:forall m,
 csteps sp_tm(work m)(main m S1)=Some(main(S m)S0).
Proof.
 intro m;replace(work m)with(3+(4*m+7+(walk m 0+2)))by(rewrite work_walk;lia).
 rewrite csteps_add,start_one,csteps_add.
 unfold tail_word;rewrite scan_return,csteps_add.
 pose proof(consume_blocks m 0 [S1] [S1;S3;S1;S2])as HC.
 cbn[w12 app Nat.add]in HC;rewrite HC.
 cbn[Nat.add w12];reflexivity.
Qed.
Definition gap m:=work m+6+work(S m).
Lemma gap_formula:forall m,gap m+2=48*2^m.
Proof. intro m;pose proof(work_formula m);unfold gap;cbn[work];lia. Qed.
Theorem main_next:forall m,
 csteps sp_tm(gap m)(main m S0)=Some(main(S(S m))S0).
Proof. intro m;unfold gap;rewrite csteps_add,zero_phase;apply one_phase. Qed.
Example main_entry:csteps sp_tm 42 c0=Some(main 1 S0).
Proof. vm_compute;reflexivity. Qed.

Lemma returns:forall N,exists k m,N<=k/\csteps sp_tm k c0=Some(main m S0).
Proof.
 induction N as[|N IH].
 - exists 42,1;split;[lia|exact main_entry].
 - destruct IH as(k&m&Hk&E).
   exists(k+gap m),(S(S m));split;[unfold gap;lia|].
   rewrite csteps_add,E;apply main_next.
Qed.

Lemma prefix_hits:forall m tg,exists j d,
 csteps sp_tm j(main m S0)=Some d/\cinstr d=tg.
Proof.
 intros m[q h];destruct q,h.
 - exists 0; eexists;split;reflexivity.
 - exists 3; eexists;split;reflexivity.
 - exists 8; eexists;split;reflexivity.
 - exists(9+(4*m+3)).
   rewrite csteps_add,start_zero,csteps_add.
   unfold tail_word;rewrite scan12.
   eexists;split;reflexivity.
 - exists 1; eexists;split;reflexivity.
 - exists 2; eexists;split;reflexivity.
 - exists 5; eexists;split;reflexivity.
 - exists 7; eexists;split;reflexivity.
Qed.

Theorem all_instructions_recurrent:forall tg N,exists k,N<=k/\FiresAt sp_tm tg k.
Proof.
 intros tg N;destruct(returns N)as(k&m&Hk&E).
 destruct(prefix_hits m tg)as(j&d&Ehit&Htarget).
 exists(k+j);split;[lia|].
 exists(lift d);split.
 - rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;exact Ehit.
 - rewrite cinstr_lift;exact Htarget.
Qed.
Theorem family_zero:NonHalt sp_tm/\Bounds 0%N 0%N sp_tm.
Proof. apply wp_all_recur_sound;exact all_instructions_recurrent. Qed.

Print Assumptions one_block.
Print Assumptions main_next.
Print Assumptions family_zero.
