(** * A finite right scan forces a return to A1.

    A normalized right word is empty or ends in one. A D scan either
    returns to the saved A head, or returns to A0 with a strictly shorter
    right word. Strong induction on that length gives a universal A0 to
    A1 return. Erasing the finite left run of ones supplies positive
    A1 returns and hence recurrence. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape.
Import ListNotations.
Fixpoint ars_normal (R:list Sym):Prop:=match R with
 |[]=>True|S1::R=>ars_normal R|S0::R=>R<>[] /\ ars_normal R end.
Lemma ars_normal_ones:forall k R,ars_normal R->ars_normal(repeat S1 k++R).
Proof. induction k;intros;cbn[repeat app ars_normal];auto. Qed.
Lemma ars_normalize:forall R,exists U,ars_normal U /\ lift_side R=lift_side U.
Proof.
 induction R as[|s R IH].
 - exists[]. split;[exact I|reflexivity].
 - destruct IH as(U&HU&EU). destruct s.
   + destruct U as[|u U].
     * exists[]. split;[exact I|]. rewrite lift_side_cons,EU.
       change(lift_side([]++[S0])=lift_side[]). apply lift_side_app_blank.
     * exists(S0::u::U). split;[cbn[ars_normal];split;[discriminate|exact HU]|].
       rewrite !lift_side_cons. now rewrite EU.
   + exists(S1::U). split;[exact HU|]. rewrite !lift_side_cons. now rewrite EU.
Qed.
Lemma ars_lift_right:forall q L h R U,lift_side R=lift_side U->
 lift(q,(L,h,R))=lift(q,(L,h,U)).
Proof. intros;unfold lift,lift_tape;cbn;now rewrite H. Qed.
Section RightScanReturn.
Variable tm:TM.
Hypothesis HA0:tm StA S0=Some(mkTrans S1 DR StB).
Hypothesis HA1:tm StA S1=Some(mkTrans S0 DL StA).
Hypothesis HB0:tm StB S0=Some(mkTrans S0 DL StC).
Hypothesis HB1:tm StB S1=Some(mkTrans S1 DR StD).
Hypothesis HC0:tm StC S0=Some(mkTrans S1 DL StC).
Hypothesis HC1:tm StC S1=Some(mkTrans S1 DL StA).
Hypothesis HD0:tm StD S0=Some(mkTrans S0 DR StB).
Hypothesis HD1:tm StD S1=Some(mkTrans S0 DR StD).
Local Ltac ars_compute:=
 cbn[Nat.add csteps cstep ctape_move chd ctl t_next t_dir t_write];
 repeat(first[rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[Nat.add csteps cstep ctape_move chd ctl t_next t_dir t_write]);reflexivity.
Definition ars_reaches(c d:cconf):Prop:=exists k,stepn tm k(lift c)=Some(lift d).
Lemma ars_reaches_refl:forall c,ars_reaches c c.
Proof. intro c;exists 0;reflexivity. Qed.
Lemma ars_reaches_trans:forall c d e,ars_reaches c d->ars_reaches d e->ars_reaches c e.
Proof. intros c d e(n&En)(m&Em);exists(n+m);now rewrite stepn_add,En. Qed.
Lemma ars_reaches_steps:forall k c d,csteps tm k c=Some d->ars_reaches c d.
Proof. intros;exists k;now apply csteps_lift. Qed.
Lemma ars_cturn:forall k s L R,
 csteps tm(k+2)(StC,(repeat S0 k++S1::s::L,S0,R))=
 Some(StA,(L,s,repeat S1(k+2)++R)).
Proof.
 induction k as[|k IH];intros s L R.
 - cbn[repeat app];ars_compute.
 - replace(S k+2)with(1+(k+2))by lia. rewrite csteps_add.
   assert(E:csteps tm 1(StC,(repeat S0(S k)++S1::s::L,S0,R))=
   Some(StC,(repeat S0 k++S1::s::L,S0,S1::R)))by(cbn[repeat app];ars_compute).
   rewrite E,IH.
   assert(T:forall n R,repeat S1 n++S1::R=S1::repeat S1 n++R).
   { induction n;intros;cbn[repeat app];[reflexivity|now rewrite IHn]. }
   rewrite T. replace(S k+2)with(S(k+2))by lia. reflexivity.
Qed.
Lemma ars_dscan:forall R,ars_normal R->forall k s L,
 exists L' s' U,ars_reaches
  (StD,(repeat S0 k++S1::s::L,chd R,ctl R))
  (StA,(L',s',S1::U)) /\
 ars_normal U /\ length U<=k+length R+1 /\
 ((s'=s /\ L'=L) \/ (s'=S0 /\ length U<length R)).
Proof.
 intro R. remember(length R)as z eqn:Ez. revert R Ez.
 induction z using lt_wf_ind;intros R Ez HN k s L.
 destruct R as[|r R].
 - exists L,s,(repeat S1(k+1)). repeat split.
   + exists(2+(k+2)). rewrite <-(lift_app_blank StA L s (S1::repeat S1(k+1))).
     apply csteps_lift. rewrite csteps_add.
     assert(E:csteps tm 2(StD,(repeat S0 k++S1::s::L,chd[],ctl[]))=
      Some(StC,(repeat S0 k++S1::s::L,S0,[S0])))by ars_compute.
     rewrite E,ars_cturn. replace(k+2)with(S(k+1))by lia. reflexivity.
   + replace(repeat S1(k+1))with(repeat S1(k+1)++[])by apply app_nil_r.
     apply ars_normal_ones;exact I.
   + rewrite repeat_length;cbn;lia.
   + left;auto.
 - destruct r.
   + destruct R as[|r R];[destruct HN as(HN&_);contradiction|].
     destruct r.
     * destruct HN as(_&HN). exists L,s,(repeat S1(k+1)++S0::R). repeat split.
       -- exists(2+(k+2)). apply csteps_lift. rewrite csteps_add.
          assert(E:csteps tm 2(StD,(repeat S0 k++S1::s::L,chd(S0::S0::R),ctl(S0::S0::R)))=
          Some(StC,(repeat S0 k++S1::s::L,S0,S0::R)))by ars_compute.
          rewrite E,ars_cturn. replace(k+2)with(S(k+1))by lia. reflexivity.
       -- apply ars_normal_ones;exact HN.
       -- rewrite app_length,repeat_length;cbn in Ez|-*;lia.
       -- left;auto.
     * destruct HN as(_&HN). cbn[ars_normal]in HN.
       assert(Hlt:length R<z)by(cbn in Ez;lia).
       destruct(H(length R)Hlt R eq_refl HN 0 S0(repeat S0 k++S1::s::L))as(L'&s'&U&ER&NU&BU&DU).
       exists L',s',U. repeat split.
       -- eapply ars_reaches_trans;[apply ars_reaches_steps with(k:=2)|exact ER].
          cbn[repeat app chd ctl];ars_compute.
       -- exact NU.
       -- cbn in BU,Ez|-*;lia.
       -- right. split;[destruct DU as[[E _]|[E _]];exact E|cbn in BU,Ez|-*;lia].
   + assert(Hlt:length R<z)by(cbn in Ez;lia).
     destruct(H(length R)Hlt R eq_refl HN(S k)s L)as(L'&s'&U&ER&NU&BU&DU).
     exists L',s',U. repeat split.
     * eapply ars_reaches_trans;[apply ars_reaches_steps with(k:=1)|exact ER].
       cbn[repeat app chd ctl];ars_compute.
     * exact NU.
     * cbn in BU,Ez|-*;lia.
     * destruct DU as[D|[D HD]];[now left|right;split;[exact D|cbn in Ez|-*;lia]].
Qed.


Lemma ars_a01:forall R,ars_normal R->forall L,
 exists L' R',ars_reaches(StA,(L,S0,S1::R))(StA,(L',S1,R')).
Proof.
 intro R. remember(length R)as z eqn:Ez. revert R Ez.
 induction z using lt_wf_ind;intros R Ez HN L.
 destruct(ars_dscan R HN 0 S1 L)as(V&s&U&ER&NU&BU&DU).
 assert(E:ars_reaches(StA,(L,S0,S1::R))(StA,(V,s,S1::U))).
 { eapply ars_reaches_trans;[apply ars_reaches_steps with(k:=2)|exact ER].
   cbn[repeat app];ars_compute. }
 destruct DU as[[Es EV]|[Es HU]];subst s.
 - exists V,(S1::U). exact E.
 - assert(Hlt:length U<z)by lia.
   destruct(H(length U)Hlt U eq_refl NU V)as(V'&R'&EU).
   exists V',R'. eapply ars_reaches_trans;eauto.
Qed.
Lemma ars_a01_any:forall L R,
 exists L' R',ars_reaches(StA,(L,S0,S1::R))(StA,(L',S1,R')).
Proof.
 intros L R. destruct(ars_normalize R)as(U&NU&EU).
 destruct(ars_a01 U NU L)as(L'&R'&ER). exists L',R'.
 unfold ars_reaches in *. destruct ER as(k&EK). exists k.
 assert(E:lift(StA,(L,S0,S1::R))=lift(StA,(L,S0,S1::U))).
 { apply ars_lift_right. now rewrite !lift_side_cons,EU. }
 now rewrite E.
Qed.
Lemma ars_a00:forall L R,
 exists L' R',ars_reaches(StA,(L,S0,S0::R))(StA,(L',S1,R')).
Proof.
 intros L R.
 assert(E:ars_reaches(StA,(L,S0,S0::R))(StA,(ctl L,chd L,S1::S0::R))).
 { apply ars_reaches_steps with(k:=3). ars_compute. }
 destruct(chd L)eqn:EL.
 - destruct(ars_a01_any(ctl L)(S0::R))as(L'&R'&ER).
   exists L',R'. eapply ars_reaches_trans;[exact E|exact ER].
 - exists(ctl L),(S1::S0::R). exact E.
Qed.
Lemma ars_a0nil:forall L,
 exists L' R',ars_reaches(StA,(L,S0,[]))(StA,(L',S1,R')).
Proof.
 intro L.
 assert(E:ars_reaches(StA,(L,S0,[]))(StA,(ctl L,chd L,[S1;S0]))).
 { apply ars_reaches_steps with(k:=3). ars_compute. }
 destruct(chd L)eqn:EL.
 - destruct(ars_a01_any(ctl L)[S0])as(L'&R'&ER).
   exists L',R'. eapply ars_reaches_trans;[exact E|exact ER].
 - exists(ctl L),[S1;S0]. exact E.
Qed.
Theorem ars_A0_return:forall L R,exists k L' R',
 stepn tm k(lift(StA,(L,S0,R)))=Some(lift(StA,(L',S1,R'))).
Proof.
 intros L [|[] R].
 - destruct(ars_a0nil L)as(L'&R'&k&E). exists k,L',R'. exact E.
 - destruct(ars_a00 L R)as(L'&R'&k&E). exists k,L',R'. exact E.
 - destruct(ars_a01_any L R)as(L'&R'&k&E). exists k,L',R'. exact E.
Qed.
Lemma ars_A1_drain:forall L R,exists k L' R',0<k /\
 csteps tm k(StA,(L,S1,R))=Some(StA,(L',S0,R')).
Proof.
 induction L as[|[] L IH];intro R.
 - exists 1,[],(S0::R). split;[lia|ars_compute].
 - exists 1,L,(S0::R). split;[lia|ars_compute].
 - destruct(IH(S0::R))as(k&L'&R'&Hk&EK).
   exists(1+k),L',R'. split;[lia|]. rewrite csteps_add.
   assert(E:csteps tm 1(StA,(S1::L,S1,R))=Some(StA,(L,S1,S0::R)))by ars_compute.
   now rewrite E.
Qed.
Lemma ars_A1_positive_return:forall L R,exists k L' R',0<k /\
 stepn tm k(lift(StA,(L,S1,R)))=Some(lift(StA,(L',S1,R'))).
Proof.
 intros L R. destruct(ars_A1_drain L R)as(n&U&V&Hn&EN).
 destruct(ars_A0_return U V)as(m&L'&R'&EM).
 exists(n+m),L',R'. split;[lia|].
 now rewrite stepn_add,(csteps_lift _ _ _ _ EN).
Qed.
Theorem right_scan_A1_recurrent:forall N,exists j e,N<=j /\
 stepn tm j InitES=Some e /\instr_of e=(StA,S1).
Proof.
 assert(Reach:forall N,exists t L R,N<=t /\
 stepn tm t InitES=Some(lift(StA,(L,S1,R)))).
 { induction N as[|N IH].
   - destruct(ars_A0_return[][])as(t&L&R&ET).
     exists t,L,R. split;[lia|]. rewrite <-lift_c0. exact ET.
   - destruct IH as(t&L&R&Ht&ET).
     destruct(ars_A1_positive_return L R)as(k&L'&R'&Hk&EK).
     exists(t+k),L',R'. split;[lia|]. now rewrite stepn_add,ET. }
 intro N. destruct(Reach N)as(t&L&R&Ht&ET).
 exists t,(lift(StA,(L,S1,R))). repeat split;assumption || reflexivity.
Qed.
End RightScanReturn.
