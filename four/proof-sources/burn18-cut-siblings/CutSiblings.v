(** A regular tape cut shared by two rotor siblings.  At B returns the left
    alphabet is {0,3}, the right alphabet is {1,2}, and the right side has
    strictly more 1s than the left side has 3s.  All macros are universal. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census OneStateReach.
Import ListNotations.

Definition cs_tm (bit:bool) : TM := fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DL StA
 |StA,S2=>mkTrans(if bit then S1 else S0)DR StA
 |StA,S3=>mkTrans S2 DL StB
 |StB,S0=>mkTrans S3 DR StB |StB,S1=>mkTrans S1 DL StA
 |StB,S2=>mkTrans S0 DR StB |StB,S3=>mkTrans S3 DR StA end).
Definition cs_front q l r:cconf := (q,(l,chd r,ctl r)).
Definition cs_back q l r:cconf := (q,(ctl l,chd l,r)).
Definition cs_left h := h=S0 \/ h=S3.
Definition cs_right h := h=S1 \/ h=S2.
Fixpoint cs_ones(l:list Sym):nat := match l with
 |[]=>0|S1::l=>S(cs_ones l)|_::l=>cs_ones l end.
Fixpoint cs_threes(l:list Sym):nat := match l with
 |[]=>0|S3::l=>S(cs_threes l)|_::l=>cs_threes l end.
Definition cs_valid l r := Forall cs_left l /\ Forall cs_right r /\ cs_threes l<cs_ones r.

Lemma cs_repeat_shift : forall (x:Sym)n l,repeat x n++x::l=x::(repeat x n++l).
Proof. intros x n;induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma cs_ones_twos : forall n r,cs_ones(repeat S2 n++r)=cs_ones r.
Proof. induction n;intro r;cbn;[reflexivity|apply IHn]. Qed.
Lemma cs_threes_zeros : forall n l,cs_threes(repeat S0 n++l)=cs_threes l.
Proof. induction n;intro l;cbn;[reflexivity|apply IHn]. Qed.
Lemma cs_left_zeros : forall n l,Forall cs_left l -> Forall cs_left(repeat S0 n++l).
Proof. induction n;intros l H;cbn;[exact H|constructor;[left;reflexivity|now apply IHn]]. Qed.
Lemma cs_right_twos : forall n r,Forall cs_right r -> Forall cs_right(repeat S2 n++r).
Proof. induction n;intros r H;cbn;[exact H|constructor;[right;reflexivity|now apply IHn]]. Qed.
Lemma cs_normal : forall l r,cs_valid l r -> cs_valid(chd l::ctl l)r.
Proof. intros[|h l]r H;[unfold cs_valid in *;cbn in *;intuition;constructor;[left;reflexivity|constructor]|exact H]. Qed.
Lemma cs_first_one : forall r,Forall cs_right r -> 0<cs_ones r ->
 exists n tail,r=repeat S2 n++S1::tail /\ Forall cs_right tail.
Proof.
 induction r as[|h r IH];intros Hr Hn;[cbn in Hn;lia|].
 inversion Hr as[|? ? Hh Ht];subst;destruct Hh as [Hh | Hh]; subst h.
 - exists 0,r;auto.
 - cbn[cs_ones]in Hn;destruct(IH Ht Hn)as(n&tail&E&Htail).
   exists(S n),tail;cbn;rewrite E;auto.
Qed.

Lemma cs_B_twos : forall bit n l r,
 csteps(cs_tm bit)n(cs_front StB l(repeat S2 n++r))=
 Some(cs_front StB(repeat S0 n++l)r).
Proof.
 intros bit n;induction n;intros l r;[reflexivity|].
 cbn[repeat app cs_front csteps cstep cs_tm ctape_move chd ctl].
 change(csteps(cs_tm bit)n(cs_front StB(S0::l)(repeat S2 n++r))=
 Some(cs_front StB(S0::(repeat S0 n++l))r)).
 rewrite IHn,cs_repeat_shift;reflexivity.
Qed.
Lemma cs_A_twos : forall bit n l r,
 csteps(cs_tm bit)n(cs_front StA l(repeat S2 n++r))=
 Some(cs_front StA(repeat(if bit then S1 else S0)n++l)r).
Proof.
 intros bit n;induction n;intros l r;[reflexivity|].
 cbn[repeat app cs_front csteps cstep cs_tm ctape_move chd ctl].
 change(csteps(cs_tm bit)n(cs_front StA((if bit then S1 else S0)::l)(repeat S2 n++r))=
 Some(cs_front StA((if bit then S1 else S0)::(repeat(if bit then S1 else S0)n++l))r)).
 rewrite IHn,cs_repeat_shift;reflexivity.
Qed.
Lemma cs_A_ones : forall bit n l r,
 csteps(cs_tm bit)n(cs_back StA(repeat S1 n++l)r)=
 Some(cs_back StA l(repeat S2 n++r)).
Proof.
 intros bit n;induction n;intros l r;[reflexivity|].
 cbn[repeat app cs_back csteps cstep cs_tm ctape_move chd ctl].
 change(csteps(cs_tm bit)n(cs_back StA(repeat S1 n++l)(S2::r))=
 Some(cs_back StA l(S2::(repeat S2 n++r)))).
 rewrite IHn,cs_repeat_shift;reflexivity.
Qed.

Lemma cs_zero_direct : forall bit l r,
 csteps(cs_tm bit)3(cs_back StB(S0::l)(S1::r))=
 Some(cs_back StB l(S2::S1::r)).
Proof. reflexivity. Qed.
Lemma cs_zero_sweep : forall bit n l r,
 csteps(cs_tm bit)(S n+3)(cs_back StB(S0::l)(repeat S2(S n)++S1::r))=
 Some(cs_back StB(repeat S0 n++S3::l)(S1::S1::r)).
Proof.
 intros bit n l r;replace(S n+3)with(1+(S n+2))by lia.
 rewrite csteps_add.
 change(csteps(cs_tm bit)(S n+2)(cs_front StB(S3::l)(repeat S2(S n)++S1::r))=
 Some(cs_back StB(repeat S0 n++S3::l)(S1::S1::r))).
 rewrite csteps_add,cs_B_twos.
 cbn[repeat app cs_front cs_back csteps cstep cs_tm ctape_move chd ctl].
 reflexivity.
Qed.
Lemma cs_three_direct : forall bit l r,
 csteps(cs_tm bit)3(cs_back StB(S3::l)(S1::r))=
 Some(cs_back StB l(S2::S2::r)).
Proof. reflexivity. Qed.
Lemma cs_three_zero_sweep : forall n l r,
 csteps(cs_tm false)(S n+3)(cs_back StB(S3::l)(repeat S2(S n)++S1::r))=
 Some(cs_back StB(repeat S0 n++S3::l)(S1::S2::r)).
Proof.
 intros n l r;replace(S n+3)with(1+(S n+2))by lia.
 rewrite csteps_add.
 change(csteps(cs_tm false)(S n+2)(cs_front StA(S3::l)(repeat S2(S n)++S1::r))=
 Some(cs_back StB(repeat S0 n++S3::l)(S1::S2::r))).
 rewrite csteps_add,cs_A_twos.
 cbn[repeat app cs_front cs_back csteps cstep cs_tm ctape_move chd ctl].
 reflexivity.
Qed.
Lemma cs_three_one_sweep : forall n l r,
 csteps(cs_tm true)(2*n+3)(cs_back StB(S3::l)(repeat S2 n++S1::r))=
 Some(cs_back StB l(S2::(repeat S2 n++S2::r))).
Proof.
 intros n l r;replace(2*n+3)with(1+(n+(1+(n+1))))by lia.
 rewrite csteps_add.
 change(csteps(cs_tm true)(n+(1+(n+1)))(cs_front StA(S3::l)(repeat S2 n++S1::r))=
 Some(cs_back StB l(S2::(repeat S2 n++S2::r)))).
 rewrite csteps_add,cs_A_twos,csteps_add.
 change(csteps(cs_tm true)(n+1)(cs_back StA(repeat S1 n++S3::l)(S2::r))=
 Some(cs_back StB l(S2::(repeat S2 n++S2::r)))).
 rewrite csteps_add,cs_A_ones;reflexivity.
Qed.

Lemma cs_next_normal : forall bit h l r,
 cs_left h -> cs_valid(h::l)r ->
 exists t l' r',0<t /\ csteps(cs_tm bit)t(cs_back StB(h::l)r)=Some(cs_back StB l' r') /\
 cs_valid l' r'.
Proof.
 intros bit h l r Hh[Hl[Hr Hcount]].
 inversion Hl as[|? ? Hhead Hleft];subst.
 assert(Hpos:0<cs_ones r)by lia.
 destruct(cs_first_one r Hr Hpos)as(n&tail&E&Htail);subst r.
 rewrite cs_ones_twos in Hcount;cbn[cs_ones]in Hcount.
 destruct Hh as[Hh|Hh];subst h.
 - destruct n as[|n].
   + exists 3,l,(S2::S1::tail);split;[lia|];split;[apply cs_zero_direct|].
     unfold cs_valid;split;[exact Hleft|];split.
     * constructor;[right;reflexivity|constructor;[left;reflexivity|exact Htail]].
     * cbn[cs_threes cs_ones]in *;lia.
   + exists(S n+3),(repeat S0 n++S3::l),(S1::S1::tail).
     split;[lia|];split;[apply cs_zero_sweep|].
     unfold cs_valid;split.
     * apply cs_left_zeros;constructor;[right;reflexivity|exact Hleft].
     * split.
       -- constructor;[left;reflexivity|constructor;[left;reflexivity|exact Htail]].
       -- rewrite cs_threes_zeros;cbn[cs_threes cs_ones]in *;lia.
 - destruct bit.
   + exists(2*n+3),l,(S2::(repeat S2 n++S2::tail)).
     split;[lia|];split;[apply cs_three_one_sweep|].
     unfold cs_valid;split;[exact Hleft|];split.
     * constructor;[right;reflexivity|apply cs_right_twos;constructor;[right;reflexivity|exact Htail]].
     * cbn[cs_ones];rewrite cs_ones_twos;cbn[cs_threes cs_ones]in *;lia.
   + destruct n as[|n].
     * exists 3,l,(S2::S2::tail);split;[lia|];split;[apply cs_three_direct|].
       unfold cs_valid;split;[exact Hleft|];split.
       -- constructor;[right;reflexivity|constructor;[right;reflexivity|exact Htail]].
       -- cbn[cs_threes cs_ones]in *;lia.
     * exists(S n+3),(repeat S0 n++S3::l),(S1::S2::tail).
       split;[lia|];split;[apply cs_three_zero_sweep|].
       unfold cs_valid;split.
       -- apply cs_left_zeros;constructor;[right;reflexivity|exact Hleft].
       -- split.
          ++ constructor;[left;reflexivity|constructor;[right;reflexivity|exact Htail]].
          ++ rewrite cs_threes_zeros;cbn[cs_threes cs_ones]in *;lia.
Qed.

Definition cs_inv(cc:cconf) := exists l r,cc=cs_back StB l r /\ cs_valid l r.
Lemma cs_next : forall bit cc,cs_inv cc ->
 exists t cc',0<t /\ csteps(cs_tm bit)t cc=Some cc' /\ cs_inv cc'.
Proof.
 intros bit cc(l&r&->&Hv).
 pose proof(cs_normal l r Hv)as Hnormal.
 assert(He:cs_left(chd l)). {destruct Hnormal as[H _];inversion H;assumption. }
 destruct(cs_next_normal bit(chd l)(ctl l)r He Hnormal)as(t&l'&r'&Ht&E&Hv').
 exists t,(cs_back StB l' r');split;[exact Ht|];split.
 - unfold cs_back in E;cbn[chd ctl]in E;exact E.
 - exists l',r';auto.
Qed.
Lemma cs_B0_A : forall bit n l r,
 csteps(cs_tm bit)(n+2)(cs_back StB(S0::l)(repeat S2 n++S1::r))=
 Some(cs_back StA(repeat S0 n++S3::l)(S1::r)).
Proof.
 intros bit n l r;replace(n+2)with(1+(n+1))by lia;rewrite csteps_add.
 change(csteps(cs_tm bit)(n+1)(cs_front StB(S3::l)(repeat S2 n++S1::r))=
 Some(cs_back StA(repeat S0 n++S3::l)(S1::r))).
 rewrite csteps_add,cs_B_twos;reflexivity.
Qed.
Lemma cs_reaches_A : forall bit cc,cs_inv cc -> ore_reaches(cs_tm bit)StA cc.
Proof.
 intros bit cc(l&r&->&Hv).
 pose proof(cs_normal l r Hv)as[Hleft[Hright Hcount]].
 inversion Hleft as[|? ? Hh Htail];subst.
 destruct Hh as[Hh|Hh].
 - assert(Hpos:0<cs_ones r)by lia.
   destruct(cs_first_one r Hright Hpos)as(n&tail&E&Htail');subst r.
   exists(n+2),(cs_back StA(repeat S0 n++S3::ctl l)(S1::tail));split;[|reflexivity].
   pose proof(cs_B0_A bit n(ctl l)tail)as E.
   unfold cs_back in *;cbn[chd ctl]in E;rewrite Hh;exact E.
 - exists 1,(cs_front StA(S3::ctl l)r);split;[|reflexivity].
   unfold cs_back;rewrite Hh;reflexivity.
Qed.
Example cs_entry : forall bit,csteps(cs_tm bit)1 c0=Some(cs_back StB[][S1]).
Proof. reflexivity. Qed.
Lemma cs_initial_inv : cs_inv(cs_back StB[][S1]).
Proof.
 exists[],[S1];split;[reflexivity|].
 unfold cs_valid;repeat split;repeat constructor;unfold cs_right;auto.
Qed.
Lemma cs_returns : forall bit N,exists t cc,N<=t /\ csteps(cs_tm bit)t c0=Some cc /\ cs_inv cc.
Proof.
 intros bit N;induction N as[|N IH].
 - exists 1,(cs_back StB[][S1]);split;[lia|];split;[apply cs_entry|apply cs_initial_inv].
 - destruct IH as(t&cc&Ht&E&Hi);destruct(cs_next bit cc Hi)as(j&cc'&Hj&E'&Hi').
   exists(t+j),cc';split;[lia|];split;[rewrite csteps_add,E;exact E'|exact Hi'].
Qed.
Theorem cs_nonhalt : forall bit,NonHalt(cs_tm bit).
Proof.
 intro bit;apply ore_total_nonhalt;intros q h;destruct q,h;eexists;reflexivity.
Qed.
Theorem cs_B_recurrent : forall bit N,exists t,N<=t /\ VisitsAt(cs_tm bit)StB t.
Proof.
 intros bit N;destruct(cs_returns bit N)as(t&cc&Ht&E&l&r&->&Hv).
 exists t;split;[exact Ht|];exists(lift(cs_back StB l r));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem cs_A_recurrent : forall bit N,exists t,N<=t /\ VisitsAt(cs_tm bit)StA t.
Proof.
 intros bit N;destruct(cs_returns bit N)as(t&cc&Ht&E&Hi).
 destruct(cs_reaches_A bit cc Hi)as(j&cc'&E'&Hq).
 exists(t+j);split;[lia|];exists(lift cc');split;[|exact Hq].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;exact E'.
Qed.
Theorem cs_state_zero : forall bit,QHBound 0(cs_tm bit).
Proof.
 intros bit q s[_ Hquiet];destruct q.
 - destruct(cs_A_recurrent bit(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
 - destruct(cs_B_recurrent bit(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
Qed.
Theorem cs_sound : forall bit,NonHalt(cs_tm bit) /\ QHBound 0(cs_tm bit).
Proof. intro bit;split;[apply cs_nonhalt|apply cs_state_zero]. Qed.
Print Assumptions cs_sound.
