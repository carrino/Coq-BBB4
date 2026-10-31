From Coq Require Import Arith Lia List.
From BBB24 Require Import Statement StatementTr CTape.
Import ListNotations.

Definition ti_tm (q:St)(h:Sym) : option Trans := Some
 (match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DL StA
 |StA,S2=>mkTrans S1 DR StB |StA,S3=>mkTrans S3 DR StB
 |StB,S0=>mkTrans S3 DR StA |StB,S1=>mkTrans S1 DR StB
 |StB,S2=>mkTrans S3 DL StA |StB,S3=>mkTrans S1 DR StA end).

Definition ti_good (d:Sym) := d=S2 \/ d=S3.
Fixpoint ti_word (ds:list Sym) : list Sym :=
 match ds with []=>[] |d::rest=>d::S2::ti_word rest end.
Definition ti_left n := repeat S1 n ++ [S3].

Lemma ti_word_app : forall xs ys,
 ti_word(xs++ys)=ti_word xs++ti_word ys.
Proof. induction xs;intros;cbn;[reflexivity|now rewrite IHxs]. Qed.
Lemma ti_word_twos : forall k,ti_word(repeat S2 k)=repeat S2(2*k).
Proof.
 induction k;[reflexivity|]. cbn[ti_word repeat]. rewrite IHk.
 replace(2*S k)with(S(S(2*k)))by lia;reflexivity.
Qed.
Lemma ti_word_prefix : forall k ds,
 repeat S2(2*k)++ti_word ds=ti_word(repeat S2 k++ds).
Proof. intros;rewrite ti_word_app,ti_word_twos;reflexivity. Qed.
Lemma ti_good_twos : forall k,Forall ti_good(repeat S2 k).
Proof. induction k;constructor;auto;left;reflexivity. Qed.

(** The only B configurations have head 0,2,3. The reset phase tracks
    parity of the processed prefix, preserving the digit-pair language. *)
Inductive ti_inv : cconf -> Prop :=
| ti_marker ds : Forall ti_good ds ->
 ti_inv(StA,([],S3,ti_word ds))
| ti_digit k d ds : ti_good d -> Forall ti_good ds ->
 ti_inv(StB,(ti_left(2*k),d,S2::ti_word ds))
| ti_separator k ds : Forall ti_good ds ->
 ti_inv(StA,(ti_left(2*k+1),S2,ti_word ds))
| ti_front_B k : ti_inv(StB,(ti_left(2*k),S0,[]))
| ti_front_A k : ti_inv(StA,(S3::ti_left(2*k),S0,[]))
| ti_turn k : ti_inv(StB,(ti_left(2*k),S3,[S1]))
| ti_reset l j k ds : l+j+1=2*k -> Forall ti_good ds ->
 ti_inv(StA,(ti_left l,S1,repeat S2 j++ti_word ds)).

Lemma ti_inv_step : forall c c',ti_inv c ->
 cstep ti_tm c=Some c' -> ti_inv c'.
Proof.
 intros c c' H E;destruct H as[ds Hds|k d ds Hd Hds|k ds Hds|k|k|k|l j k ds Hpar Hds].
 - destruct ds as[|d ds].
   + cbn[cstep ti_tm ctape_move ti_word chd ctl]in E;inversion E;subst.
     change(ti_inv(StB,(ti_left(2*0),S0,[])));constructor.
   + inversion Hds;subst. cbn[cstep ti_tm ctape_move ti_word chd ctl]in E;inversion E;subst.
     change(ti_inv(StB,(ti_left(2*0),d,S2::ti_word ds)));constructor;assumption.
 - destruct Hd as[-> | ->].
   + destruct k as[|k].
     * cbn[cstep ti_tm ctape_move ti_left repeat chd ctl]in E;inversion E;subst.
       change(ti_inv(StA,([],S3,ti_word(S3::ds))));constructor;constructor;auto;right;reflexivity.
     * replace(2*S k)with(S(S(2*k)))in E by lia.
       cbn[cstep ti_tm ctape_move ti_left repeat chd ctl]in E;inversion E;subst.
       change(ti_inv(StA,(ti_left(S(2*k)),S1,repeat S2 0++ti_word(S3::ds)))).
       eapply ti_reset with(k:=S k);[lia|constructor;auto;right;reflexivity].
   + cbn[cstep ti_tm ctape_move chd ctl]in E;inversion E;subst.
     change(ti_inv(StA,(ti_left(S(2*k)),S2,ti_word ds))).
     replace(S(2*k))with(2*k+1)by lia;constructor;exact Hds.
 - cbn[cstep ti_tm ctape_move]in E.
   destruct ds as[|d ds].
   + cbn[ti_word chd ctl]in E;inversion E;subst.
     change(ti_inv(StB,(ti_left(S(2*k+1)),S0,[]))).
     replace(S(2*k+1))with(2*S k)by lia;constructor.
   + inversion Hds;subst;cbn[ti_word chd ctl]in E;inversion E;subst.
     change(ti_inv(StB,(ti_left(S(2*k+1)),d,S2::ti_word ds))).
     replace(S(2*k+1))with(2*S k)by lia;constructor;assumption.
 - cbn[cstep ti_tm ctape_move chd ctl]in E;inversion E;subst;constructor.
 - cbn[cstep ti_tm ctape_move chd ctl]in E;inversion E;subst;constructor.
 - cbn[cstep ti_tm ctape_move chd ctl]in E;inversion E;subst.
   change(ti_inv(StA,(ti_left(S(2*k)),S1,repeat S2 0++ti_word []))).
   eapply ti_reset with(k:=S k);[lia|constructor].
 - destruct l as[|l].
   + cbn[cstep ti_tm ctape_move ti_left repeat chd ctl]in E;inversion E;subst.
     change(ti_inv(StA,([],S3,repeat S2(S j)++ti_word ds))).
     replace(S j)with(2*k)by lia;rewrite ti_word_prefix.
     constructor;apply Forall_app;split;[apply ti_good_twos|exact Hds].
   + cbn[cstep ti_tm ctape_move ti_left repeat chd ctl]in E;inversion E;subst.
     change(ti_inv(StA,(ti_left l,S1,repeat S2(S j)++ti_word ds))).
     eapply ti_reset with(k:=k);[lia|exact Hds].
Qed.

Lemma ti_inv_steps : forall n c c',ti_inv c ->
 csteps ti_tm n c=Some c' -> ti_inv c'.
Proof.
 induction n;intros c c' H E;cbn[csteps]in E.
 - inversion E;subst;exact H.
 - destruct(cstep ti_tm c)as[d|]eqn:Ed;[|discriminate].
   eapply IHn;[eapply ti_inv_step;eauto|exact E].
Qed.
Lemma ti_inv_excludes_B1 : forall c,ti_inv c ->
 (fst c,let '(_,h,_) := snd c in h)<>(StB,S1).
Proof.
 intros c H;destruct H;cbn;try discriminate.
 destruct H as[-> | ->];discriminate.
Qed.

Example ti_prefix : csteps ti_tm 10 c0=Some(StB,(ti_left 2,S0,[])).
Proof. reflexivity. Qed.
Lemma ti_total : forall n c,exists c',csteps ti_tm n c=Some c'.
Proof.
 induction n;intro c;[eexists;reflexivity|].
 destruct c as[q[[l h]r]];destruct q,h;cbn[csteps cstep ti_tm];apply IHn.
Qed.
Theorem ti_B1_quiet : QuietFromTr ti_tm(StB,S1)10.
Proof.
 intros n Hn(e&He&Hfire).
 destruct(ti_total (n-10)(StB,(ti_left 2,S0,[])))as(d&Hd).
 assert(Hinv:ti_inv d).
 {eapply (ti_inv_steps (n-10)(StB,(ti_left 2,S0,[])) d);[change(ti_inv(StB,(ti_left(2*1),S0,[])));constructor|exact Hd ]. }
 replace n with(10+(n-10))in He by lia.
 rewrite stepn_add,<-lift_c0,(csteps_lift _ _ _ _ ti_prefix),(csteps_lift _ _ _ _ Hd)in He.
 injection He as <-;apply(ti_inv_excludes_B1 d Hinv).
 destruct d as[q[[l h]r]];exact Hfire.
Qed.
Theorem ti_B1_exact_last : QuietAfterTr ti_tm(StB,S1)9.
Proof.
 split.
 - eexists;split;[rewrite<-lift_c0;apply csteps_lift;reflexivity|reflexivity].
 - intros n Hn;apply ti_B1_quiet;lia.
Qed.
Print Assumptions ti_B1_quiet.
Print Assumptions ti_B1_exact_last.
