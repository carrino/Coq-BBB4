(** The common period-three core with the rightward B0=1RC reset. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import Period3MacroTr ValueFrontierTransducer
 Period3WordTermination ValueFrontierD0.
Import ListNotations.
Section Frontier.
Variable tm:TM.
Hypotheses
 (HA0:tm StA S0=Some(mkTrans S1 DR StB))
 (HA1:tm StA S1=Some(mkTrans S0 DL StC))
 (HB0:tm StB S0=Some(mkTrans S1 DR StC))
 (HB1:tm StB S1=Some(mkTrans S1 DR StD))
 (HC0:tm StC S0=Some(mkTrans S1 DL StA))
 (HC1:tm StC S1=Some(mkTrans S1 DL StC))
 (HD0:tm StD S0=Some(mkTrans S1 DR StB))
 (HD1:tm StD S1=Some(mkTrans S0 DR StA)).
Local Ltac pr_compute:=
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app];
 repeat(first[rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app]);reflexivity.
Lemma pr_turn:forall L a R,
 csteps tm 6(StA,(S0::L,S0,S0::a::R))=
 Some(StA,(ctl L,chd L,S1::S1::a::S1::R)).
Proof. intros L[]R;pr_compute. Qed.
Lemma pr_reset:forall ms a R,
 exists k,stepn tm k(lift(StA,([],S0,vft_Ps ms++S0::a::R)))=
 Some(lift(StA,([],S0,vft_Us ms++S1::S1::a::S1::R))).
Proof.
 intros ms a R. destruct(vft_push tm HA0 HB1 HD0 HD1 ms [] [] (S0::a::R))as[k Hk].
 rewrite app_nil_r in Hk. cbn[vft_stack]in Hk.
 destruct(vft_pop tm HA1 HC0 HC1(rev ms)[](S1::S1::a::S1::R))as[j Hj].
 rewrite rev_involutive in Hj.
 exists(k+(6+j)). rewrite vfd_pad_left. apply csteps_lift.
 rewrite csteps_add,Hk,csteps_add,pr_turn. exact Hj.
Qed.
Lemma pr_zeros:forall k R,vfd_hit tm(vft_Ps(repeat 0 k)++S0::S0::S0::R).
Proof.
 intros k R. destruct(pr_reset(repeat 0 k)S0(S0::R))as[j Hj].
 eapply vfd_back;[exact Hj|]. rewrite vfd_Us0.
 change(vfd_hit tm(vft_Ps(repeat 0 k)++vft_P 0++S1::S0::R)).
 rewrite app_assoc,vfd_Ps_snoc. apply vfd_direct;assumption.
Qed.
Lemma pr_padded:forall R k,vfd_hit tm(vft_Ps(repeat 0 k)++R++[S0;S0;S0;S0]).
Proof.
 intro R. remember(length R)as z eqn:Ez. revert R Ez.
 induction z using lt_wf_ind;intros R Ez k.
 destruct R as[|a R].
 - change(vfd_hit tm(vft_Ps(repeat 0 k)++S0::S0::S0::[S0])). apply pr_zeros.
 - destruct a.
   + destruct R as[|a R].
     * change(vfd_hit tm(vft_Ps(repeat 0 k)++S0::S0::S0::[S0;S0])). apply pr_zeros.
     * destruct(pr_reset(repeat 0 k)a(R++[S0;S0;S0;S0]))as[j Hj].
       cbn[app]. eapply vfd_back;[exact Hj|]. rewrite vfd_Us0.
       destruct a.
       -- change(vfd_hit tm(vft_Ps(repeat 0 k)++vft_P 0++(S1::R)++[S0;S0;S0;S0])).
          rewrite app_assoc,vfd_Ps_snoc. apply(H(length(S1::R)));[cbn in Ez|-*;lia|reflexivity].
       -- apply vfd_three;assumption.
   + destruct R as[|a R].
     * change(vfd_hit tm(vft_Ps(repeat 0 k)++S1::S0::[S0;S0;S0])). apply vfd_direct;assumption.
     * destruct a.
       -- change(vfd_hit tm(vft_Ps(repeat 0 k)++S1::S0::(R++[S0;S0;S0;S0]))). apply vfd_direct;assumption.
       -- destruct R as[|a R].
          ++ change(vfd_hit tm(vft_Ps(repeat 0 k)++vft_P 0++[S0;S0;S0])).
             rewrite app_assoc,vfd_Ps_snoc. apply pr_zeros.
          ++ destruct a.
             ** change(vfd_hit tm(vft_Ps(repeat 0 k)++vft_P 0++R++[S0;S0;S0;S0])).
                rewrite app_assoc,vfd_Ps_snoc. apply(H(length R));[cbn in Ez;lia|reflexivity].
             ** change(vfd_hit tm(vft_Ps(repeat 0 k)++S1::S1::S1::(R++[S0;S0;S0;S0]))).
                apply vfd_three;assumption.
Qed.
Lemma pr_frontier:forall R,vfd_hit tm R.
Proof.
 intro R. unfold vfd_hit.
 replace(lift(StA,([],S0,R)))with(lift(StA,([],S0,R++[S0;S0;S0;S0]))).
 - exact(pr_padded R 0).
 - symmetry. rewrite pwt_pad. rewrite(pwt_pad(R++[S0;S0])). rewrite <-app_assoc. reflexivity.
Qed.
End Frontier.

Section Finite.
Variable tm:TM.
Hypotheses
 (HA0:tm StA S0=Some(mkTrans S1 DR StB))
 (HA1:tm StA S1=Some(mkTrans S0 DL StC))
 (HB0:tm StB S0=Some(mkTrans S1 DR StC))
 (HB1:tm StB S1=Some(mkTrans S1 DR StD))
 (HC0:tm StC S0=Some(mkTrans S1 DL StA))
 (HC1:tm StC S1=Some(mkTrans S1 DL StC))
 (HD0:tm StD S0=Some(mkTrans S1 DR StB))
 (HD1:tm StD S1=Some(mkTrans S0 DR StA)).
Local Ltac prf_compute :=
 cbn [p3_R p3_L p3_raw p3_written p3_shifted
 csteps cstep ctape_move t_dir t_write t_next chd ctl length app];
 repeat(first[rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[csteps cstep ctape_move t_dir t_write t_next chd ctl length app]);reflexivity.
Definition prf_hit(c:cconf):Prop := exists k e,
 stepn tm k (lift c)=Some e /\ instr_of e=(StD,S0).
Lemma prf_now:forall L R,prf_hit(StD,(L,S0,R)).
Proof. intros;exists 0,(lift(StD,(L,S0,R)));split;reflexivity. Qed.
Lemma prf_back:forall k c d,csteps tm k c=Some d ->prf_hit d ->prf_hit c.
Proof. intros k c d H(j&e&Ej&Hq). exists(k+j),e;split;[|exact Hq].
 rewrite stepn_add,(csteps_lift _ _ _ _ H);exact Ej. Qed.
Definition prf_state(b:bool):St:=if b then StA else StC.
Lemma prf_rollback:forall b L R,
 csteps tm 3(p3_L(prf_state b)(p3_written true++L)R)=
 Some(p3_L StC L((if b then[S0;S1;S0]else[S0;S1;S1])++R)).
Proof. intros[]L R;unfold prf_state;prf_compute. Qed.
Lemma prf_scanner:forall R L,
 prf_hit(p3_R StB L R) \/
 exists k b R',csteps tm k(p3_R StB L R)=Some(p3_L(prf_state b)L R').
Proof.
 fix IH 1. intros R L. destruct R as[|[] R].
 - right. exists 3,false,[S0;S1]. unfold prf_state. prf_compute.
 - right. exists 3,false,(chd R::S1::ctl R). unfold prf_state.
   destruct R as[|[]R];prf_compute.
 - destruct R as[|[] R].
   + left. eapply prf_back with(k:=1)(d:=(StD,(S1::L,S0,[])));[prf_compute|apply prf_now].
   + left. eapply prf_back with(k:=1)(d:=(StD,(S1::L,S0,R)));[prf_compute|apply prf_now].
   + destruct R as[|[] R].
     * right. exists 9,false,[S0;S1;S1;S0;S1]. unfold prf_state. prf_compute.
     * destruct(IH R(p3_written true++L))as[Hhit|(k&b&R'&Ek)].
       -- left. eapply prf_back;[apply(p3_right_token tm HA0 HB1 HD0 HD1 true)|exact Hhit].
       -- right. exists(length(p3_raw true)+k+3),false,((if b then[S0;S1;S0]else[S0;S1;S1])++R').
          change(p3_R StB L(S1::S1::S0::R))with(p3_R StB L(p3_raw true++R)).
          pose proof(p3_right_token tm HA0 HB1 HD0 HD1 true L R)as E.
          rewrite <-Nat.add_assoc,csteps_add,E,csteps_add,Ek. apply prf_rollback.
     * right. exists 5,false,(S0::S1::S0::R). apply p3_turn;assumption.
Qed.
Hypothesis Hblank:forall R,prf_hit(StA,([],S0,R)).
Lemma prf_C:forall L R,prf_hit(p3_L StC L R).
Proof.
 fix IH 1. intros L R. destruct L as[|[] L].
 - eapply prf_back with(k:=1)(d:=(StA,([],S0,S1::R)));[prf_compute|apply Hblank].
 - destruct L as[|[] L].
   + eapply prf_back with(k:=1)(d:=(StA,([],S0,S1::R)));[prf_compute|apply Hblank].
   + destruct(prf_scanner(S1::R)(S1::L))as[Hhit|(k&b&R'&Ek)].
     * eapply prf_back with(k:=2)(d:=p3_R StB(S1::L)(S1::R));[prf_compute|exact Hhit].
     * eapply prf_back with(k:=2+k)(d:=p3_L(prf_state b)(S1::L)R').
       -- rewrite csteps_add. assert(E:csteps tm 2(p3_L StC(S0::S0::L)R)=Some(p3_R StB(S1::L)(S1::R)))by prf_compute.
          rewrite E. exact Ek.
       -- destruct b;unfold prf_state.
          ++ eapply prf_back with(k:=1)(d:=p3_L StC L(S0::R'));[prf_compute|apply IH].
          ++ eapply prf_back with(k:=1)(d:=p3_L StC L(S1::R'));[prf_compute|apply IH].
   + eapply prf_back with(k:=2)(d:=p3_L StC L(S0::S1::R));[prf_compute|apply IH].
 - eapply prf_back with(k:=1)(d:=p3_L StC L(S1::R));[prf_compute|apply IH].
Qed.
Lemma prf_A:forall L s R,prf_hit(StA,(L,s,R)).
Proof.
 intros L[]R.
 - destruct(prf_scanner R(S1::L))as[Hhit|(k&b&R'&Ek)].
   + eapply prf_back with(k:=1)(d:=p3_R StB(S1::L)R);[prf_compute|exact Hhit].
   + eapply prf_back with(k:=1+k)(d:=p3_L(prf_state b)(S1::L)R').
     * rewrite csteps_add. cbn[csteps cstep]. rewrite HA0. exact Ek.
     * destruct b;unfold prf_state.
       -- eapply prf_back with(k:=1)(d:=p3_L StC L(S0::R'));[prf_compute|apply prf_C].
       -- eapply prf_back with(k:=1)(d:=p3_L StC L(S1::R'));[prf_compute|apply prf_C].
 - eapply prf_back with(k:=1)(d:=p3_L StC L(S0::R));[prf_compute|apply prf_C].
Qed.
Theorem prf_finite:forall c:cconf,prf_hit c.
Proof.
 intros[q[[L s]R]]. destruct q.
 - apply prf_A.
 - destruct(prf_scanner(s::R)L)as[Hhit|(k&b&R'&Ek)];[exact Hhit|].
   eapply prf_back;[exact Ek|]. destruct b;unfold prf_state;[apply prf_A|apply prf_C].
 - change(prf_hit(p3_L StC(s::L)R)). apply prf_C.
 - destruct s;[apply prf_now|].
   eapply prf_back with(k:=1)(d:=(StA,(S0::L,chd R,ctl R)));[prf_compute|apply prf_A].
Qed.
End Finite.
Theorem pr_D0_finite tm
 (HA0:tm StA S0=Some(mkTrans S1 DR StB))
 (HA1:tm StA S1=Some(mkTrans S0 DL StC))
 (HB0:tm StB S0=Some(mkTrans S1 DR StC))
 (HB1:tm StB S1=Some(mkTrans S1 DR StD))
 (HC0:tm StC S0=Some(mkTrans S1 DL StA))
 (HC1:tm StC S1=Some(mkTrans S1 DL StC))
 (HD0:tm StD S0=Some(mkTrans S1 DR StB))
 (HD1:tm StD S1=Some(mkTrans S0 DR StA)) c : prf_hit tm c.
Proof.
 apply(prf_finite tm HA0 HA1 HB0 HB1 HC0 HC1 HD0 HD1).
 intro R. destruct(pr_frontier tm HA0 HA1 HB0 HB1 HC0 HC1 HD0 HD1 R)as(k&L&R'&E).
 exists k,(lift(StD,(L,S0,R')));split;[exact E|reflexivity].
Qed.
