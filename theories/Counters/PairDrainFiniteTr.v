(** * Pair-draining finite-tape termination.

    Seven transition equations force a visit to A1 from every finite
    configuration; the instruction at A1 is unconstrained. The C scan
    consumes 01 pairs. Even and odd left-pair prefixes reduce to one of
    two frontier configurations. A 01001 marker closes the zero branch,
    and induction on the untouched right suffix closes the one branch.
    Induction on the finite left word then handles arbitrary tapes. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape DyadicWindowTr.
Import ListNotations.
Fixpoint pd_pairs(n:nat):list Sym := match n with 0=>[]|S n=>S0::S1::pd_pairs n end.
Lemma pd_app:forall n m,pd_pairs(n+m)=pd_pairs n++pd_pairs m.
Proof. induction n;intros;cbn[pd_pairs app Nat.add];[reflexivity|now rewrite IHn]. Qed.
Lemma pd_push:forall n L,pd_pairs n++S0::S1::L=pd_pairs(S n)++L.
Proof. induction n;intros;cbn[pd_pairs app];[reflexivity|now rewrite IHn]. Qed.
Definition pd_C(L R:list Sym):cconf := (StC,(L,chd R,ctl R)).
Definition pd_A(L R:list Sym):cconf := (StA,(ctl L,chd L,R)).
Section Core.
Variable tm:TM.
Hypotheses
 (HA0:tm StA S0=Some(mkTrans S1 DL StB))
 (HB0:tm StB S0=Some(mkTrans S1 DL StC))
 (HB1:tm StB S1=Some(mkTrans S0 DL StB))
 (HC0:tm StC S0=Some(mkTrans S1 DR StD))
 (HC1:tm StC S1=Some(mkTrans S0 DL StA))
 (HD0:tm StD S0=Some(mkTrans S1 DR StA))
 (HD1:tm StD S1=Some(mkTrans S0 DR StC)).
Local Ltac run :=
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app pd_C pd_A pd_pairs repeat];
 repeat(first[rewrite HA0|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app pd_C pd_A pd_pairs repeat]);reflexivity.
Definition pd_hit(c:cconf):Prop:=exists k e,stepn tm k(lift c)=Some e /\ instr_of e=(StA,S1).
Lemma pd_now:forall L R,pd_hit(StA,(L,S1,R)).
Proof. intros;exists 0,(lift(StA,(L,S1,R)));split;reflexivity. Qed.
Lemma pd_back:forall k c d,csteps tm k c=Some d->pd_hit d->pd_hit c.
Proof. intros k c d E(j&e&Hj&Hi). exists(k+j),e;split;[rewrite stepn_add,(csteps_lift _ _ _ _ E);exact Hj|exact Hi]. Qed.
Lemma pd_lift_eq:forall c d,lift c=lift d->pd_hit d->pd_hit c.
Proof. intros c d E H;unfold pd_hit in*;now rewrite E. Qed.
Lemma pd_short:forall U R,csteps tm 4(StA,(S1::S0::S1::U,S0,R))=Some(pd_A U(S0::S1::S0::S1::R)).
Proof. intros;run. Qed.
Lemma pd_long:forall U R,csteps tm 5(StA,(S1::S1::S0::S1::U,S0,R))=Some(pd_A U(S0::S1::S0::S0::S1::R)).
Proof. intros;run. Qed.
Lemma pd_even:forall n U R,
 csteps tm(4*n)(StA,(S1::pd_pairs(2*n)++U,S0,R))=
 Some(StA,(S1::U,S0,pd_pairs(2*n)++R)).
Proof.
 induction n as[|n IH];intros U R;[reflexivity|].
 replace(2*S n)with(S(S(2*n)))by lia.
 replace(4*S n)with(4+4*n)by lia.
 rewrite csteps_add. cbn[pd_pairs app]. rewrite pd_short.
 unfold pd_A;cbn[chd ctl].
 rewrite IH. repeat rewrite pd_push. reflexivity.
Qed.
Lemma pd_odd:forall n U R,
 csteps tm(4*n+4)(StA,(S1::pd_pairs(S(2*n))++U,S0,R))=
 Some(pd_A U(pd_pairs(2*n+2)++R)).
Proof.
 intros n U R. replace(S(2*n))with(2*n+1)by lia. rewrite pd_app,<-app_assoc.
 rewrite csteps_add,pd_even. cbn[pd_pairs app]. rewrite pd_short.
 rewrite pd_app. cbn[pd_pairs app]. repeat rewrite <-app_assoc.
 cbn[app]. repeat rewrite pd_push. reflexivity.
Qed.
Lemma pd_parity:forall k,exists n,k=2*n \/ k=S(2*n).
Proof. induction k as[|k(n&[E|E])];[exists 0;left;reflexivity|exists n;right;lia|exists(S n);left;lia]. Qed.
Lemma pd_reduce:forall U,
 (forall R,pd_hit(StA,(S1::U,S0,R))) ->
 (forall R,pd_hit(pd_A U R)) ->
 forall k R,pd_hit(StA,(S1::pd_pairs k++U,S0,R)).
Proof.
 intros U H1 HU k R. destruct(pd_parity k)as(n&[E|E]);subst k.
 - eapply pd_back;[apply pd_even|apply H1].
 - eapply pd_back;[apply pd_odd|apply HU].
Qed.
Lemma pd_scan:forall k L R,
 csteps tm(2*k)(pd_C L(pd_pairs k++R))=Some(pd_C(pd_pairs k++L)R).
Proof.
 induction k as[|k IH];intros L R;[reflexivity|].
 replace(2*S k)with(2+2*k)by lia. rewrite csteps_add.
 assert(E:csteps tm 2(pd_C L(pd_pairs(S k)++R))=Some(pd_C(S0::S1::L)(pd_pairs k++R)))by run.
 rewrite E,IH,pd_push. reflexivity.
Qed.
Lemma pd_one:forall R,csteps tm 7(StA,([S1],S0,R))=Some(pd_C(pd_pairs 2)R).
Proof. intros;run. Qed.
Lemma pd_empty:forall R,csteps tm 5(StA,([],S0,R))=Some(StA,([S1],S0,S0::R)).
Proof. intros;run. Qed.
Lemma pd_mark_one:forall k R,pd_hit(StA,([S1],S0,pd_pairs k++S0::S0::S1::R)).
Proof.
 intros. eapply pd_back;[apply pd_one|]. eapply pd_back;[apply pd_scan|].
 eapply pd_back with(k:=2)(d:=(StA,(S1::S1::pd_pairs k++pd_pairs 2,S1,R)));[run|apply pd_now].
Qed.
Lemma pd_mark_empty:forall k R,pd_hit(StA,([],S0,pd_pairs(S k)++R)).
Proof.
 intros. eapply pd_back;[apply pd_empty|].
 change(pd_hit(StA,([S1],S0,S0::S0::S1::pd_pairs k++R))).
 apply(pd_mark_one 0).
Qed.
Lemma pd_clean:forall k R,pd_hit(StA,(S1::pd_pairs k,S0,S0::S1::S0::S0::S1::R)).
Proof.
 intros. rewrite <-(app_nil_r(pd_pairs k)). destruct(pd_parity k)as(n&[E|E]);subst k.
 - eapply pd_back;[apply pd_even|]. cbn[app].
   change(pd_hit(StA,([S1],S0,pd_pairs(2*n)++pd_pairs 1++S0::S0::S1::R))).
   rewrite app_assoc,<-pd_app. apply pd_mark_one.
 - eapply pd_back;[apply pd_odd|].
   unfold pd_A;cbn[chd ctl]. replace(2*n+2)with(S(2*n+1))by lia. apply pd_mark_empty.
Qed.
Lemma pd_C00:forall k R,pd_hit(pd_C(pd_pairs(S(S k)))(S0::S0::R)).
Proof.
 intros. eapply pd_back with(k:=2)(d:=(StA,(S1::S1::pd_pairs(S(S k)),chd R,ctl R)));[run|].
 destruct R as[|[] R];try apply pd_now.
 all: eapply pd_back;[apply pd_long|unfold pd_A;cbn[chd ctl pd_pairs app];apply pd_clean].
Qed.
Lemma pd_pad_right:forall q L h R,lift(q,(L,h,R++[S0]))=lift(q,(L,h,R)).
Proof. intros;unfold lift,lift_tape;cbn;rewrite lift_side_app_blank;reflexivity. Qed.
Lemma pd_blank_C:forall L,pd_hit(pd_C L[S0;S0])->pd_hit(pd_C L[]).
Proof. intros. eapply pd_lift_eq;[symmetry;apply(pd_pad_right StC L S0 [])|exact H]. Qed.
(** Termination of the finite right frontier, including implicit blanks. *)
Lemma pd_frontier:forall R k,pd_hit(pd_C(pd_pairs(k+2))R).
Proof.
 intro R. remember(length R)as z eqn:Ez. revert R Ez.
 induction z using lt_wf_ind;intros R Ez k.
 replace(k+2)with(S(S k))by lia.
 destruct R as[|a R].
 - apply pd_blank_C,pd_C00.
 - destruct a.
   + destruct R as[|a R].
     * change(pd_hit(pd_C(pd_pairs(S(S k)))[])). apply pd_blank_C,pd_C00.
     * destruct a.
       -- apply pd_C00.
       -- eapply pd_back with(k:=2)(d:=pd_C(pd_pairs(S(S(S k))))R);[run|].
          replace(S(S(S k)))with(S k+2)by lia. apply(H(length R));[cbn in Ez;lia|reflexivity].
   + eapply pd_back with(k:=1)(d:=(StA,(S1::pd_pairs(S k),S0,S0::R)));[run|].
     destruct(pd_parity(S k))as(n&[E|E]);rewrite E.
     * rewrite <-(app_nil_r(pd_pairs(2*n))). eapply pd_back;[apply pd_even|].
       eapply pd_back;[apply pd_one|]. eapply pd_back;[apply pd_scan|].
       rewrite <-pd_app. replace(2*n+2)with(S(S(2*n)))by lia.
       destruct R as[|a R].
       -- change(pd_hit(pd_C(pd_pairs(S(S(2*n))))[])). apply pd_blank_C,pd_C00.
       -- destruct a.
          ++ apply pd_C00.
          ++ eapply pd_back with(k:=2)(d:=pd_C(pd_pairs(S(S(S(2*n)))))R);[run|].
             replace(S(S(S(2*n))))with(S(2*n)+2)by lia.
             apply(H(length R));[cbn in Ez;lia|reflexivity].
     * rewrite <-(app_nil_r(pd_pairs(S(2*n)))). eapply pd_back;[apply pd_odd|].
       unfold pd_A;cbn[chd ctl]. replace(2*n+2)with(S(2*n+1))by lia. apply pd_mark_empty.
Qed.
Lemma pd_one_hit:forall R,pd_hit(StA,([S1],S0,R)).
Proof. intro R;eapply pd_back;[apply pd_one|apply(pd_frontier R 0)]. Qed.
Lemma pd_empty_hit:forall R,pd_hit(StA,([],S0,R)).
Proof. intro R;eapply pd_back;[apply pd_empty|apply pd_one_hit]. Qed.
Lemma pd_C00_suffix:forall U,
 (forall R,pd_hit(StA,(S1::U,S0,R))) ->
 (forall R,pd_hit(pd_A U R)) ->
 forall k R,pd_hit(pd_C(pd_pairs(S(S k))++U)(S0::S0::R)).
Proof.
 intros U H1 HU k R.
 eapply pd_back with(k:=2)(d:=(StA,(S1::S1::pd_pairs(S(S k))++U,chd R,ctl R)));[run|].
 destruct R as[|[] R];try apply pd_now.
 all:eapply pd_back;[apply pd_long|unfold pd_A;cbn[chd ctl pd_pairs app];apply pd_reduce;assumption].
Qed.
Lemma pd_C_suffix:forall U,
 (forall R,pd_hit(StA,(S1::U,S0,R))) ->
 (forall R,pd_hit(pd_A U R)) ->
 forall R k,pd_hit(pd_C(pd_pairs(k+2)++U)R).
Proof.
 intros U H1 HU. fix IH 1. intros R k.
 replace(k+2)with(S(S k))by lia.
 destruct R as[|[] R].
 - apply pd_blank_C,pd_C00_suffix;assumption.
 - destruct R as[|[] R].
   + change(pd_hit(pd_C(pd_pairs(S(S k))++U)[])). apply pd_blank_C,pd_C00_suffix;assumption.
   + apply pd_C00_suffix;assumption.
   + eapply pd_back with(k:=2)(d:=pd_C(pd_pairs(S(S(S k)))++U)R);[run|].
     replace(S(S(S k)))with(S k+2)by lia. apply IH.
 - eapply pd_back with(k:=1)(d:=(StA,(S1::pd_pairs(S k)++U,S0,S0::R)));[run|].
   apply pd_reduce;assumption.
Qed.
Lemma pd_Bscan:forall n L R,
 csteps tm n(StB,(ctl(repeat S1 n++S0::L),chd(repeat S1 n++S0::L),R))=
 Some(StB,(L,S0,repeat S0 n++R)).
Proof.
 induction n as[|n IH];intros L R;[reflexivity|].
 replace(S n)with(1+n)at 1 by lia. rewrite csteps_add.
 assert(E:csteps tm 1(StB,(ctl(repeat S1(S n)++S0::L),chd(repeat S1(S n)++S0::L),R))=
 Some(StB,(ctl(repeat S1 n++S0::L),chd(repeat S1 n++S0::L),S0::R)))by run.
 rewrite E,IH,dw_repeat_tail. reflexivity.
Qed.
Lemma pd_enter:forall n U R,
 csteps tm(1+(n+3))(StA,(repeat S1 n++S0::S0::U,S0,R))=
 Some(pd_C(pd_pairs 1++U)(repeat S0 n++S1::R)).
Proof.
 intros. rewrite csteps_add.
 assert(E:csteps tm 1(StA,(repeat S1 n++S0::S0::U,S0,R))=
 Some(StB,(ctl(repeat S1 n++S0::S0::U),chd(repeat S1 n++S0::S0::U),S1::R)))by run.
 rewrite E,csteps_add,pd_Bscan. run.
Qed.
Lemma pd_enter_one:forall n U R,
 csteps tm(1+(n+2))(StA,(repeat S1 n++S0::S1::U,S0,R))=
 Some(pd_A U(S0::S1::repeat S0 n++S1::R)).
Proof.
 intros. rewrite csteps_add.
 assert(E:csteps tm 1(StA,(repeat S1 n++S0::S1::U,S0,R))=
 Some(StB,(ctl(repeat S1 n++S0::S1::U),chd(repeat S1 n++S0::S1::U),S1::R)))by run.
 rewrite E,csteps_add,pd_Bscan. run.
Qed.
Lemma pd_zeros:forall U,
 (forall R,pd_hit(StA,(S1::U,S0,R))) ->
 (forall R,pd_hit(pd_A U R)) ->
 forall n R,pd_hit(StA,(repeat S1 n++S0::S0::U,S0,R)).
Proof.
 intros U H1 HU n R. eapply pd_back;[apply pd_enter|].
 destruct n as[|[|n]].
 - eapply pd_back with(k:=1)(d:=(StA,(S1::U,S0,S0::R)));[run|apply H1].
 - eapply pd_back with(k:=2)(d:=pd_C(pd_pairs 2++U)R);[run|apply(pd_C_suffix U H1 HU R 0)].
 - eapply pd_back with(k:=2)(d:=(StA,(S1::S1::S0::S1::U,chd(repeat S0 n++S1::R),ctl(repeat S0 n++S1::R))));[run|].
   destruct n as[|n];[apply pd_now|].
   eapply pd_back;[apply pd_long|apply HU].
Qed.
Lemma pd_pad_left:forall q L h R,lift(q,(L++[S0],h,R))=lift(q,(L,h,R)).
Proof. intros;unfold lift,lift_tape;cbn;rewrite lift_side_app_blank;reflexivity. Qed.
(** Remove the leading one run and two following cells from the left word. *)
Lemma pd_A_finite:forall L h R,pd_hit(StA,(L,h,R)).
Proof.
 intro L. remember(length L)as z eqn:Ez. revert L Ez.
 induction z using lt_wf_ind;intros L Ez h R.
 destruct h;[|apply pd_now].
 destruct(dw_ones_split L)as(n&T&ET&[ET0|(U&ET0)]);subst T.
 - rewrite app_nil_r in ET;subst L.
   eapply pd_lift_eq with(d:=(StA,(repeat S1 n++S0::S0::[],S0,R))).
   + symmetry. change(lift(StA,(repeat S1 n++([S0]++[S0]),S0,R))=lift(StA,(repeat S1 n,S0,R))).
     rewrite app_assoc,!pd_pad_left;reflexivity.
   + apply pd_zeros;[apply pd_one_hit|intro V;apply pd_empty_hit].
 - subst L. destruct U as[|b U].
   + eapply pd_lift_eq with(d:=(StA,(repeat S1 n++S0::S0::[],S0,R))).
     * symmetry. change(lift(StA,(repeat S1 n++([S0]++[S0]),S0,R))=lift(StA,(repeat S1 n++[S0],S0,R))). rewrite app_assoc. apply pd_pad_left.
     * apply pd_zeros;[apply pd_one_hit|intro V;apply pd_empty_hit].
   + assert(HU:forall V,pd_hit(pd_A U V)).
     { intro V. destruct U as[|a U];[apply pd_empty_hit|].
       unfold pd_A;cbn[chd ctl]. apply(H(length U));[rewrite app_length in Ez;cbn[length]in Ez;lia|reflexivity]. }
     destruct b.
     * apply pd_zeros;[|exact HU].
       intro V. apply(H(length(S1::U)));[rewrite app_length in Ez;cbn[length]in*;lia|reflexivity].
     * eapply pd_back;[apply pd_enter_one|apply HU].
Qed.
Lemma pd_C_finite:forall R L,pd_hit(pd_C L R).
Proof.
 fix IH 1. intros R L. destruct R as[|[] R].
 - eapply pd_back with(k:=2)(d:=(StA,(S1::S1::L,S0,[])));[run|apply pd_A_finite].
 - destruct R as[|[] R].
   + eapply pd_back with(k:=2)(d:=(StA,(S1::S1::L,S0,[])));[run|apply pd_A_finite].
   + eapply pd_back with(k:=2)(d:=(StA,(S1::S1::L,chd R,ctl R)));[run|apply pd_A_finite].
   + eapply pd_back with(k:=2)(d:=pd_C(S0::S1::L)R);[run|apply IH].
 - eapply pd_back with(k:=1)(d:=pd_A L(S0::R));[run|apply pd_A_finite].
Qed.
Lemma pd_B_finite:forall L h R,pd_hit(StB,(L,h,R)).
Proof.
 induction L as[|a L IH];intros h R;destruct h.
 - eapply pd_back with(k:=1)(d:=pd_C[](S0::S1::R));[run|apply pd_C_finite].
 - eapply pd_back with(k:=1)(d:=(StB,([],S0,S0::R)));[run|].
   eapply pd_back with(k:=1)(d:=pd_C[](S0::S1::S0::R));[run|apply pd_C_finite].
 - eapply pd_back with(k:=1)(d:=pd_C L(a::S1::R));[run|apply pd_C_finite].
 - eapply pd_back with(k:=1)(d:=(StB,(L,a,S0::R)));[run|apply IH].
Qed.
Theorem pd_finite:forall c,pd_hit c.
Proof.
 intros[q[[L h]R]]. destruct q.
 - apply pd_A_finite.
 - apply pd_B_finite.
 - change(pd_hit(pd_C L(h::R))). apply pd_C_finite.
 - destruct h.
   + eapply pd_back with(k:=1)(d:=(StA,(S1::L,chd R,ctl R)));[run|apply pd_A_finite].
   + eapply pd_back with(k:=1)(d:=pd_C(S0::L)R);[run|apply pd_C_finite].
Qed.
End Core.
