(** * A fixed binary window forces the recurrence of A1.

    Between successive A configurations, B scans a run of ones and C
    chooses one of two macros. The rightward macro replaces 0 1^m by
    1 0^m. The leftward macro changes a following zero to one, or grows
    an external unary tail without changing the window. A left marker
    prevents the window from being crossed before A1 is reached.

    Thus the zero-value of the fixed binary window decreases, or stays
    unchanged while the head moves left. [DyadicRankTr] supplies this
    finite lexicographic rank. No canonical tape language is required:
    every finite A0 configuration eventually reaches A1 with a zero on
    its right. A positive erase-left macro for A1 then gives recurrence.
    The A1 macro may take several steps, allowing stuttering variants. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import DyadicRankTr DyadicRecurTr WTape.
Import ListNotations.
Lemma dw_repeat_tail : forall (x:Sym) m L,
 repeat x m ++ x::L = x::repeat x m ++ L.
Proof. intros x m;induction m;intro L;cbn [repeat app];[reflexivity|now rewrite IHm]. Qed.
Lemma dw_ones_split : forall v:list Sym, exists m t,
 v=repeat S1 m++t /\ (t=[] \/ exists x,t=S0::x).
Proof.
 induction v as [|[] v IH].
 - exists 0,[]. split;[reflexivity|now left].
 - exists 0,(S0::v). split;[reflexivity|right;eexists;reflexivity].
 - destruct IH as(m&t&H&Ht). exists(S m),t. split;[cbn[repeat app];now rewrite H|exact Ht].
Qed.
Section Machine.
Variable tm:TM.
Hypothesis HA0:tm StA S0=Some(mkTrans S1 DR StB).
Hypothesis HB0:tm StB S0=Some(mkTrans S0 DR StC).
Hypothesis HB1:tm StB S1=Some(mkTrans S0 DR StB).
Hypothesis HC0:tm StC S0=Some(mkTrans S0 DL StD).
Hypothesis HC1:tm StC S1=Some(mkTrans S1 DL StA).
Hypothesis HD0:tm StD S0=Some(mkTrans S1 DL StD).
Hypothesis HD1:tm StD S1=Some(mkTrans S0 DL StA).
Local Ltac dw_compute :=
 cbn [Nat.add csteps cstep ctape_move chd ctl t_next t_dir t_write];
 repeat(first[rewrite HA0|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[Nat.add csteps cstep ctape_move chd ctl t_next t_dir t_write]);reflexivity.
Lemma dw_bscan : forall m L R,
 csteps tm m (StB,(L,chd(repeat S1 m++R),ctl(repeat S1 m++R)))=
 Some(StB,(repeat S0 m++L,chd R,ctl R)).
Proof.
 induction m as[|m IH];intros L R;[reflexivity|].
 cbn[repeat app chd ctl csteps].
 assert(H:cstep tm(StB,(L,S1,repeat S1 m++R))=
 Some(StB,(S0::L,chd(repeat S1 m++R),ctl(repeat S1 m++R)))) by dw_compute.
 rewrite H,IH. rewrite dw_repeat_tail. reflexivity.
Qed.
Lemma dw_dscan : forall m L R,
 csteps tm m (StD,(ctl(repeat S0 m++L),chd(repeat S0 m++L),R))=
 Some(StD,(ctl L,chd L,repeat S1 m++R)).
Proof.
 induction m as[|m IH];intros L R;[reflexivity|].
 cbn[repeat app chd ctl csteps].
 assert(H:cstep tm(StD,(repeat S0 m++L,S0,R))=
 Some(StD,(ctl(repeat S0 m++L),chd(repeat S0 m++L),S1::R))) by dw_compute.
 rewrite H,IH,dw_repeat_tail. reflexivity.
Qed.
Lemma dw_start : forall m L R,
 csteps tm (1+m) (StA,(L,S0,repeat S1 m++R))=
 Some(StB,(repeat S0 m++S1::L,chd R,ctl R)).
Proof.
 intros. rewrite csteps_add.
 assert(H:csteps tm 1(StA,(L,S0,repeat S1 m++R))=
 Some(StB,(S1::L,chd(repeat S1 m++R),ctl(repeat S1 m++R)))) by dw_compute.
 rewrite H. apply dw_bscan.
Qed.
Lemma dw_right : forall m L X,
 csteps tm (m+3)(StA,(L,S0,repeat S1 m++S0::S1::X))=
 Some(StA,(repeat S0 m++S1::L,S0,S1::X)).
Proof.
 intros. replace(m+3)with((1+m)+2)by lia. rewrite csteps_add,dw_start.
 cbn[chd ctl]. dw_compute.
Qed.
Lemma dw_left : forall m L X,
 csteps tm (2*m+5)(StA,(L,S0,repeat S1 m++S0::S0::X))=
 Some(StA,(ctl L,chd L,S0::repeat S1(S m)++S0::X)).
Proof.
 intros. replace(2*m+5)with((1+m)+(2+(S m+1)))by lia.
 rewrite csteps_add,dw_start. cbn[chd ctl]. rewrite csteps_add.
 assert(H:csteps tm 2(StB,(repeat S0 m++S1::L,S0,S0::X))=
 Some(StD,(repeat S0 m++S1::L,S0,S0::X)))by dw_compute.
 rewrite H,csteps_add.
 change(csteps tm (S m)(StD,(repeat S0 m++S1::L,S0,S0::X)))with
 (csteps tm(S m)(StD,(ctl(repeat S0(S m)++S1::L),chd(repeat S0(S m)++S1::L),S0::X))).
 rewrite dw_dscan. cbn[chd ctl]. dw_compute.
Qed.
Lemma dw_end : forall m L,
 csteps tm (2*m+5)(StA,(L,S0,repeat S1 m++[S0]))=
 Some(StA,(ctl L,chd L,S0::repeat S1(S m)++[S0])).
Proof.
 intros. replace(2*m+5)with((1+m)+(2+(S m+1)))by lia.
 rewrite csteps_add,dw_start. cbn[chd ctl]. rewrite csteps_add.
 assert(H:csteps tm 2(StB,(repeat S0 m++S1::L,S0,[]))=
 Some(StD,(repeat S0 m++S1::L,S0,[S0])))by dw_compute.
 rewrite H,csteps_add.
 change(csteps tm (S m)(StD,(repeat S0 m++S1::L,S0,[S0])))with
 (csteps tm(S m)(StD,(ctl(repeat S0(S m)++S1::L),chd(repeat S0(S m)++S1::L),[S0]))).
 rewrite dw_dscan. cbn[chd ctl]. dw_compute.
Qed.
Lemma dw_marker_assoc : forall (v u X:list Sym),
 v++S1::(u++S1::X)=(v++S1::u)++S1::X.
Proof. intros;rewrite <-app_assoc;reflexivity. Qed.
Definition dw_hit (c:cconf) : Prop := exists k L R,
 csteps tm k c=Some(StA,(L,S1,S0::R)).
Lemma dw_hit_back : forall k c d, csteps tm k c=Some d -> dw_hit d -> dw_hit c.
Proof.
 intros k c d H(j&L&R&Hj). exists(k+j),L,R. now rewrite csteps_add,H.
Qed.
Lemma dw_hit_left : forall u X R,
 (forall u',u=S0::u' -> dw_hit(StA,(u'++S1::X,S0,S0::R))) ->
 dw_hit(StA,(ctl(u++S1::X),chd(u++S1::X),S0::R)).
Proof.
 intros [|[] u] X R H;[exists 0,X,R;reflexivity|apply H;reflexivity|exists 0,(u++S1::X),R;reflexivity].
Qed.

Lemma dw_window_hit : forall N u v b X,
 length u+1+length v=N ->
 dw_hit(StA,(u++S1::X,S0,v++repeat S1 b++[S0])).
Proof.
 intro N.
 assert(H : forall fuel u v b X, dw_rank N u v=fuel ->
   length u+1+length v=N -> dw_hit(StA,(u++S1::X,S0,v++repeat S1 b++[S0]))).
 { intro fuel. induction fuel as[fuel IH]using(well_founded_induction lt_wf).
   intros u v b X Er En.
   destruct(dw_ones_split v)as(m&t&Ev&[Et|(w&Et)]);subst t;subst v.
   - rewrite app_nil_r. rewrite app_nil_r in En,Er.
     rewrite app_assoc,<-repeat_app.
     eapply dw_hit_back;[apply dw_end|].
     apply dw_hit_left. intros u' Eu. subst u.
     replace(S(m+b))with(m+S b)by lia. rewrite repeat_app,<-app_assoc.
     change(dw_hit(StA,(u'++S1::X,S0,(S0::repeat S1 m)++repeat S1(S b)++[S0]))).
     eapply(IH (dw_rank N u'(S0::repeat S1 m))).
     + rewrite <-Er. apply dw_rank_tail.
     + reflexivity.
     + cbn[length]in En|-*. lia.
   - destruct w as[|h w].
     + destruct b as[|b].
       * cbn[repeat app]. rewrite <-app_assoc. cbn[app].
         eapply dw_hit_back;[apply dw_left|].
         apply dw_hit_left. intros u' Eu. subst u.
         change(dw_hit(StA,(u'++S1::X,S0,(S0::repeat S1(S m))++repeat S1 0++[S0]))).
         eapply(IH(dw_rank N u'(S0::repeat S1(S m)))).
         -- rewrite <-Er. replace (S0::repeat S1(S m))with(S0::repeat S1(S m)++[])by now rewrite app_nil_r.
            apply dw_rank_left.
         -- reflexivity.
         -- rewrite app_length,repeat_length in En. cbn[length]in En|-*.
            rewrite repeat_length. lia.
       * cbn[repeat]. rewrite <-app_assoc. cbn[app].
         eapply dw_hit_back;[apply dw_right|].
         rewrite dw_marker_assoc.
         change(dw_hit(StA,((repeat S0 m++S1::u)++S1::X,S0,[]++repeat S1(S b)++[S0]))).
         eapply(IH(dw_rank N (repeat S0 m++S1::u)[])).
         -- rewrite <-Er. apply dw_rank_right.
            rewrite app_length,repeat_length in En. cbn[length]in En|-*. lia.
         -- reflexivity.
         -- rewrite app_length,repeat_length. cbn[length].
            rewrite app_length,repeat_length in En. cbn[length]in En. lia.
     + destruct h.
       * rewrite <-app_assoc. cbn[app].
         eapply dw_hit_back;[apply dw_left|].
         apply dw_hit_left. intros u' Eu. subst u.
         rewrite app_assoc.
         assert(E : (S0::repeat S1(S m)++S0::w)++repeat S1 b++[S0] =
            S0::repeat S1(S m)++S0::(w++repeat S1 b)++[S0]).
         { cbn[app]. repeat rewrite <-app_assoc. reflexivity. }
         rewrite <-E.
         eapply(IH(dw_rank N u'(S0::repeat S1(S m)++S0::w))).
         -- rewrite <-Er. apply dw_rank_left.
         -- reflexivity.
         -- rewrite dw_left_length. exact En.
       * rewrite <-app_assoc. cbn[app].
         eapply dw_hit_back;[apply dw_right|].
         rewrite dw_marker_assoc.
         change(dw_hit(StA,((repeat S0 m++S1::u)++S1::X,S0,(S1::w)++repeat S1 b++[S0]))).
         eapply(IH(dw_rank N (repeat S0 m++S1::u)(S1::w))).
         -- rewrite <-Er. apply dw_rank_right.
            rewrite app_length,repeat_length in En. cbn[length]in En|-*. lia.
         -- reflexivity.
         -- rewrite app_length,repeat_length. cbn[length].
            rewrite app_length,repeat_length in En. cbn[length]in En. lia.
 }
 intros u v b X En. apply(H(dw_rank N u v)u v b X eq_refl En).
Qed.
Lemma dw_zero_one_hit : forall L w,
 dw_hit(StA,(L,S0,S0::S1::w++[S0])).
Proof.
 intros. eapply dw_hit_back with(k:=3).
 - exact(dw_right 0 L(w++[S0])).
 - change(dw_hit(StA,([]++S1::L,S0,(S1::w)++repeat S1 0++[S0]))).
   apply(dw_window_hit (1+length(S1::w))). cbn[length]. lia.
Qed.
Lemma dw_after_left : forall L w,
 dw_hit(StA,(ctl L,chd L,S0::S1::w++[S0])).
Proof.
 intros [|[] L] w;cbn[chd ctl].
 - apply dw_zero_one_hit.
 - apply dw_zero_one_hit.
 - exists 0,L,(S1::w++[S0]). reflexivity.
Qed.
Lemma dw_a0_hit_pad : forall L R,
 dw_hit(StA,(L,S0,R++[S0])).
Proof.
 intros L R. destruct(dw_ones_split R)as(m&t&ER&[ET|(w&ET)]);subst t;subst R.
 - rewrite app_nil_r. eapply dw_hit_back;[apply dw_end|].
   cbn[repeat app]. apply dw_after_left.
 - destruct w as[|[] w].
   + rewrite <-app_assoc. cbn[app].
     eapply dw_hit_back;[apply dw_left|]. cbn[repeat app]. apply dw_after_left.
   + rewrite <-app_assoc. cbn[app].
     eapply dw_hit_back;[apply dw_left|]. cbn[repeat app].
     replace (S0::S1::repeat S1 m++S0::w++[S0]) with
       (S0::S1::(repeat S1 m++S0::w)++[S0]).
     2:{ cbn[app]. rewrite <-app_assoc. reflexivity. }
     apply dw_after_left.
   + rewrite <-app_assoc. cbn[app].
     eapply dw_hit_back;[apply dw_right|].
     change(dw_hit(StA,(repeat S0 m++S1::L,S0,(S1::w)++repeat S1 0++[S0]))).
     apply(dw_window_hit (length(repeat S0 m)+1+length(S1::w))). reflexivity.
Qed.
Lemma dw_a0_hit : forall L R, exists k L' R',
 stepn tm k(lift(StA,(L,S0,R)))=Some(lift(StA,(L',S1,S0::R'))).
Proof.
 intros L R. destruct(dw_a0_hit_pad L R)as(k&L'&R'&H).
 exists k,L',R'. rewrite <- (lift_app_blank StA L S0 R).
 apply csteps_lift. exact H.
Qed.
Lemma dw_blank_boot : csteps tm 15 c0=Some(StA,([],S1,[S0;S1;S1;S0])).
Proof. unfold c0. dw_compute. Qed.
Theorem dw_blank_A1_recurrent : forall ka, 0<ka ->
 (forall L R,csteps tm ka(StA,(L,S1,S0::R))=Some(StA,(ctl L,chd L,S0::S0::R))) ->
 forall N,exists j e,N<=j /\ stepn tm j InitES=Some e /\ instr_of e=(StA,S1).
Proof.
 intros ka Hpos Hka.
 apply(dyadic_A1_recurrent tm ka Hpos Hka dw_a0_hit).
 exists 15,[],[S1;S1;S0]. rewrite <-lift_c0. apply csteps_lift,dw_blank_boot.
Qed.

End Machine.
