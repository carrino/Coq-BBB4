(** * Period3FiniteTr: visits from every finite tape in two period-three cores.

    The right scanner either visits the requested instruction or returns
    to the left scanner. Each left-scanner recurrence consumes cells of
    the original finite left tape. At the blank boundary, the checked
    finite-word frontier theorems supply the visit. B0 needs only the seven
    shared transitions; D0 additionally permits either B0=1LA or B0=1LC. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import Period3MacroTr Period3WordTermination ValueFrontierD0.
Import ListNotations.

Section Core.
Variable tm:TM.
Hypotheses
 (HA0:tm StA S0=Some(mkTrans S1 DR StB))
 (HA1:tm StA S1=Some(mkTrans S0 DL StC))
 (HB1:tm StB S1=Some(mkTrans S1 DR StD))
 (HC0:tm StC S0=Some(mkTrans S1 DL StA))
 (HC1:tm StC S1=Some(mkTrans S1 DL StC))
 (HD0:tm StD S0=Some(mkTrans S1 DR StB))
 (HD1:tm StD S1=Some(mkTrans S0 DR StA)).
Local Ltac p3f_compute :=
 cbn [p3_R p3_L p3_raw p3_written p3_shifted
 csteps cstep ctape_move t_dir t_write t_next chd ctl length app];
 repeat(first[rewrite HA0|rewrite HA1|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[csteps cstep ctape_move t_dir t_write t_next chd ctl length app]);reflexivity.
Definition p3f_hit(c:cconf):Prop := exists k e,
 stepn tm k (lift c)=Some e /\ instr_of e=(StB,S0).
Lemma p3f_now:forall L R,p3f_hit(StB,(L,S0,R)).
Proof. intros;exists 0,(lift(StB,(L,S0,R)));split;reflexivity. Qed.
Lemma p3f_back:forall k c d,csteps tm k c=Some d ->p3f_hit d ->p3f_hit c.
Proof. intros k c d H(j&e&Ej&Hq). exists(k+j),e;split;[|exact Hq].
 rewrite stepn_add,(csteps_lift _ _ _ _ H);exact Ej. Qed.
Lemma p3f_scanner:forall R L,
 p3f_hit(p3_R StB L R) \/
 exists k R',csteps tm k(p3_R StB L R)=Some(p3_L StC L R').
Proof.
 fix IH 1. intros R L. destruct R as[|[] R].
 - left;apply p3f_now.
 - left;apply p3f_now.
 - destruct R as[|[] R].
   + left. eapply p3f_back with(k:=2)(d:=(StB,(S1::S1::L,S0,[]))).
     * p3f_compute.
     * apply p3f_now.
   + destruct(IH R(p3_written false++L))as[Hhit|(k&R'&Ek)].
     * left. eapply p3f_back;[apply(p3_right_token tm HA0 HB1 HD0 HD1 false)|exact Hhit].
     * right. exists(length(p3_raw false)+k+length(p3_written false)),(p3_shifted false++R').
       change(p3_R StB L(S1::S0::R))with(p3_R StB L(p3_raw false++R)).
       pose proof(p3_right_token tm HA0 HB1 HD0 HD1 false L R)as E.
       rewrite <-Nat.add_assoc,csteps_add.
       rewrite E,csteps_add,Ek.
       apply p3_left_token;assumption.
   + destruct R as[|[] R].
     * left. eapply p3f_back with(k:=3)(d:=(StB,(S1::S0::S1::L,S0,[]))).
       -- p3f_compute.
       -- apply p3f_now.
     * destruct(IH R(p3_written true++L))as[Hhit|(k&R'&Ek)].
       -- left. eapply p3f_back;[apply(p3_right_token tm HA0 HB1 HD0 HD1 true)|exact Hhit].
       -- right. exists(length(p3_raw true)+k+length(p3_written true)),(p3_shifted true++R').
          change(p3_R StB L(S1::S1::S0::R))with(p3_R StB L(p3_raw true++R)).
          pose proof(p3_right_token tm HA0 HB1 HD0 HD1 true L R)as E.
          rewrite <-Nat.add_assoc,csteps_add,E,csteps_add,Ek.
          apply p3_left_token;assumption.
     * right. exists 5,(S0::S1::S0::R). apply p3_turn;assumption.
Qed.
Hypothesis Hblank:forall R,p3f_hit(StA,([],S0,R)).
Lemma p3f_C:forall L R,p3f_hit(p3_L StC L R).
Proof.
 fix IH 1. intros L R. destruct L as[|[] L].
 - eapply p3f_back with(k:=1)(d:=(StA,([],S0,S1::R))).
   + p3f_compute.
   + apply Hblank.
 - destruct L as[|[] L].
   + eapply p3f_back with(k:=1)(d:=(StA,([],S0,S1::R))).
     * p3f_compute.
     * apply Hblank.
   + destruct(p3f_scanner(S1::R)(S1::L))as[Hhit|(k&R'&Ek)].
     * eapply p3f_back with(k:=2)(d:=p3_R StB(S1::L)(S1::R));[p3f_compute|exact Hhit].
     * eapply p3f_back with(k:=2+k+1)(d:=p3_L StC L(S1::R')).
       -- rewrite <-Nat.add_assoc,csteps_add.
          assert(E:csteps tm 2(p3_L StC(S0::S0::L)R)=Some(p3_R StB(S1::L)(S1::R)))by p3f_compute.
          rewrite E,csteps_add,Ek. p3f_compute.
       -- apply IH.
   + eapply p3f_back with(k:=2)(d:=p3_L StC L(S0::S1::R));[p3f_compute|apply IH].
 - eapply p3f_back with(k:=1)(d:=p3_L StC L(S1::R));[p3f_compute|apply IH].
Qed.
Theorem p3f_finite:forall c:cconf,p3f_hit c.
Proof.
 intros[q[[L s]R]]. destruct q,s.
 - destruct(p3f_scanner R(S1::L))as[Hhit|(k&R'&Ek)].
   + eapply p3f_back with(k:=1)(d:=p3_R StB(S1::L)R);[p3f_compute|exact Hhit].
   + eapply p3f_back with(k:=1+k)(d:=p3_L StC(S1::L)R').
     * rewrite csteps_add. cbn[csteps cstep]. rewrite HA0. exact Ek.
     * apply p3f_C.
 - eapply p3f_back with(k:=1)(d:=p3_L StC L(S0::R));[p3f_compute|apply p3f_C].
 - apply p3f_now.
 - destruct(p3f_scanner(S1::R)L)as[Hhit|(k&R'&Ek)];[exact Hhit|].
   eapply p3f_back;[exact Ek|apply p3f_C].
 - change(p3f_hit(p3_L StC(S0::L)R)). apply p3f_C.
 - change(p3f_hit(p3_L StC(S1::L)R)). apply p3f_C.
 - destruct(p3f_scanner R(S1::L))as[Hhit|(k&R'&Ek)].
   + eapply p3f_back with(k:=1)(d:=p3_R StB(S1::L)R);[p3f_compute|exact Hhit].
   + eapply p3f_back with(k:=1+k)(d:=p3_L StC(S1::L)R').
     * rewrite csteps_add. cbn[csteps cstep]. rewrite HD0. exact Ek.
     * apply p3f_C.
 - destruct R as[|[] R].
   + eapply p3f_back with(k:=2)(d:=(StB,(S1::S0::L,S0,[])));[p3f_compute|apply p3f_now].
   + destruct(p3f_scanner R(S1::S0::L))as[Hhit|(k&R'&Ek)].
     * eapply p3f_back with(k:=2)(d:=p3_R StB(S1::S0::L)R);[p3f_compute|exact Hhit].
     * eapply p3f_back with(k:=2+k)(d:=p3_L StC(S1::S0::L)R').
       -- rewrite csteps_add. cbn[csteps cstep ctape_move t_next t_write t_dir chd ctl]. rewrite HD1.
          cbn[cstep ctape_move t_next t_write t_dir chd ctl]. rewrite HA0. exact Ek.
       -- apply p3f_C.
   + eapply p3f_back with(k:=2)(d:=p3_L StC(S0::L)(S0::R));[p3f_compute|apply p3f_C].
Qed.
End Core.

Section DZero.
Variable tm:TM.
Hypotheses
 (HA0:tm StA S0=Some(mkTrans S1 DR StB))
 (HA1:tm StA S1=Some(mkTrans S0 DL StC))
 (HB0:tm StB S0=Some(mkTrans S1 DL StA) \/ tm StB S0=Some(mkTrans S1 DL StC))
 (HB1:tm StB S1=Some(mkTrans S1 DR StD))
 (HC0:tm StC S0=Some(mkTrans S1 DL StA))
 (HC1:tm StC S1=Some(mkTrans S1 DL StC))
 (HD0:tm StD S0=Some(mkTrans S1 DR StB))
 (HD1:tm StD S1=Some(mkTrans S0 DR StA)).
Local Ltac p3d_compute :=
 cbn [p3_R p3_L p3_raw p3_written p3_shifted
 csteps cstep ctape_move t_dir t_write t_next chd ctl length app];
 repeat(first[rewrite HA0|rewrite HA1|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[csteps cstep ctape_move t_dir t_write t_next chd ctl length app]);reflexivity.
Definition p3d_hit(c:cconf):Prop := exists k e,
 stepn tm k (lift c)=Some e /\ instr_of e=(StD,S0).
Lemma p3d_now:forall L R,p3d_hit(StD,(L,S0,R)).
Proof. intros;exists 0,(lift(StD,(L,S0,R)));split;reflexivity. Qed.
Lemma p3d_back:forall k c d,csteps tm k c=Some d ->p3d_hit d ->p3d_hit c.
Proof. intros k c d H(j&e&Ej&Hq). exists(k+j),e;split;[|exact Hq].
 rewrite stepn_add,(csteps_lift _ _ _ _ H);exact Ej. Qed.
Definition p3d_state(b:bool):St:=if b then StA else StC.
Lemma p3d_rollback:forall b L R,
 csteps tm 3(p3_L(p3d_state b)(p3_written true++L)R)=
 Some(p3_L StC L((if b then[S0;S1;S0]else[S0;S1;S1])++R)).
Proof. intros[]L R;unfold p3d_state;p3d_compute. Qed.
Lemma p3d_scanner:forall R L,
 p3d_hit(p3_R StB L R) \/
 exists k b R',csteps tm k(p3_R StB L R)=Some(p3_L(p3d_state b)L R').
Proof.
 fix IH 1. intros R L. destruct R as[|[] R].
 - right. destruct HB0 as[Htrans|Htrans].
   + exists 1,true,[S1]. unfold p3d_state. cbn[p3_R p3_L csteps cstep chd ctl]. rewrite Htrans. reflexivity.
   + exists 1,false,[S1]. unfold p3d_state. cbn[p3_R p3_L csteps cstep chd ctl]. rewrite Htrans. reflexivity.
 - right. destruct HB0 as[Htrans|Htrans].
   + exists 1,true,(S1::R). unfold p3d_state. cbn[p3_R p3_L csteps cstep chd ctl]. rewrite Htrans. reflexivity.
   + exists 1,false,(S1::R). unfold p3d_state. cbn[p3_R p3_L csteps cstep chd ctl]. rewrite Htrans. reflexivity.
 - destruct R as[|[] R].
   + left. eapply p3d_back with(k:=1)(d:=(StD,(S1::L,S0,[])));[p3d_compute|apply p3d_now].
   + left. eapply p3d_back with(k:=1)(d:=(StD,(S1::L,S0,R)));[p3d_compute|apply p3d_now].
   + destruct R as[|[] R].
     * right. destruct HB0 as[Htrans|Htrans].
       -- exists 7,false,[S0;S1;S0;S1]. unfold p3d_state.
          cbn[p3_R p3_L csteps cstep chd ctl]. rewrite HB1. cbn[cstep ctape_move t_write t_dir t_next chd ctl].
          rewrite HD1. cbn[cstep ctape_move t_write t_dir t_next chd ctl].
          rewrite HA0. cbn[cstep ctape_move t_write t_dir t_next chd ctl].
          rewrite Htrans. p3d_compute.
       -- exists 7,false,[S0;S1;S1;S1]. unfold p3d_state.
          cbn[p3_R p3_L csteps cstep chd ctl]. rewrite HB1. cbn[cstep ctape_move t_write t_dir t_next chd ctl].
          rewrite HD1. cbn[cstep ctape_move t_write t_dir t_next chd ctl].
          rewrite HA0. cbn[cstep ctape_move t_write t_dir t_next chd ctl].
          rewrite Htrans. p3d_compute.
     * destruct(IH R(p3_written true++L))as[Hhit|(k&b&R'&Ek)].
       -- left. eapply p3d_back;[apply(p3_right_token tm HA0 HB1 HD0 HD1 true)|exact Hhit].
       -- right. exists(length(p3_raw true)+k+3),false,((if b then[S0;S1;S0]else[S0;S1;S1])++R').
          change(p3_R StB L(S1::S1::S0::R))with(p3_R StB L(p3_raw true++R)).
          pose proof(p3_right_token tm HA0 HB1 HD0 HD1 true L R)as E.
          rewrite <-Nat.add_assoc,csteps_add,E,csteps_add,Ek. apply p3d_rollback.
     * right. exists 5,false,(S0::S1::S0::R). apply p3_turn;assumption.
Qed.
Hypothesis Hblank:forall R,p3d_hit(StA,([],S0,R)).
Lemma p3d_C:forall L R,p3d_hit(p3_L StC L R).
Proof.
 fix IH 1. intros L R. destruct L as[|[] L].
 - eapply p3d_back with(k:=1)(d:=(StA,([],S0,S1::R)));[p3d_compute|apply Hblank].
 - destruct L as[|[] L].
   + eapply p3d_back with(k:=1)(d:=(StA,([],S0,S1::R)));[p3d_compute|apply Hblank].
   + destruct(p3d_scanner(S1::R)(S1::L))as[Hhit|(k&b&R'&Ek)].
     * eapply p3d_back with(k:=2)(d:=p3_R StB(S1::L)(S1::R));[p3d_compute|exact Hhit].
     * eapply p3d_back with(k:=2+k)(d:=p3_L(p3d_state b)(S1::L)R').
       -- rewrite csteps_add. assert(E:csteps tm 2(p3_L StC(S0::S0::L)R)=Some(p3_R StB(S1::L)(S1::R)))by p3d_compute.
          rewrite E. exact Ek.
       -- destruct b;unfold p3d_state.
          ++ eapply p3d_back with(k:=1)(d:=p3_L StC L(S0::R'));[p3d_compute|apply IH].
          ++ eapply p3d_back with(k:=1)(d:=p3_L StC L(S1::R'));[p3d_compute|apply IH].
   + eapply p3d_back with(k:=2)(d:=p3_L StC L(S0::S1::R));[p3d_compute|apply IH].
 - eapply p3d_back with(k:=1)(d:=p3_L StC L(S1::R));[p3d_compute|apply IH].
Qed.
Lemma p3d_A:forall L s R,p3d_hit(StA,(L,s,R)).
Proof.
 intros L[]R.
 - destruct(p3d_scanner R(S1::L))as[Hhit|(k&b&R'&Ek)].
   + eapply p3d_back with(k:=1)(d:=p3_R StB(S1::L)R);[p3d_compute|exact Hhit].
   + eapply p3d_back with(k:=1+k)(d:=p3_L(p3d_state b)(S1::L)R').
     * rewrite csteps_add. cbn[csteps cstep]. rewrite HA0. exact Ek.
     * destruct b;unfold p3d_state.
       -- eapply p3d_back with(k:=1)(d:=p3_L StC L(S0::R'));[p3d_compute|apply p3d_C].
       -- eapply p3d_back with(k:=1)(d:=p3_L StC L(S1::R'));[p3d_compute|apply p3d_C].
 - eapply p3d_back with(k:=1)(d:=p3_L StC L(S0::R));[p3d_compute|apply p3d_C].
Qed.
Theorem p3d_finite:forall c:cconf,p3d_hit c.
Proof.
 intros[q[[L s]R]]. destruct q.
 - apply p3d_A.
 - destruct(p3d_scanner(s::R)L)as[Hhit|(k&b&R'&Ek)];[exact Hhit|].
   eapply p3d_back;[exact Ek|]. destruct b;unfold p3d_state;[apply p3d_A|apply p3d_C].
 - change(p3d_hit(p3_L StC(s::L)R)). apply p3d_C.
 - destruct s;[apply p3d_now|].
   eapply p3d_back with(k:=1)(d:=(StA,(S0::L,chd R,ctl R)));[p3d_compute|apply p3d_A].
Qed.
End DZero.

Theorem p3_B0_finite tm
 (HA0:tm StA S0=Some(mkTrans S1 DR StB))
 (HA1:tm StA S1=Some(mkTrans S0 DL StC))
 (HB1:tm StB S1=Some(mkTrans S1 DR StD))
 (HC0:tm StC S0=Some(mkTrans S1 DL StA))
 (HC1:tm StC S1=Some(mkTrans S1 DL StC))
 (HD0:tm StD S0=Some(mkTrans S1 DR StB))
 (HD1:tm StD S1=Some(mkTrans S0 DR StA)):
 forall c:cconf,p3f_hit tm c.
Proof.
 apply(p3f_finite tm HA0 HA1 HB1 HC0 HC1 HD0 HD1).
 intro R. destruct(pwt_frontier tm HA0 HA1 HB1 HC0 HC1 HD0 HD1 R)
 as(k&L&R'&Hpos&Ek).
 exists k,(lift(StB,(L,S0,R')));split;[exact Ek|reflexivity].
Qed.
Theorem p3_D0_finite tm s
 (HA0:tm StA S0=Some(mkTrans S1 DR StB))
 (HA1:tm StA S1=Some(mkTrans S0 DL StC))
 (HB0:tm StB S0=Some(mkTrans S1 DL(match s with S0=>StA|S1=>StC end)))
 (HB1:tm StB S1=Some(mkTrans S1 DR StD))
 (HC0:tm StC S0=Some(mkTrans S1 DL StA))
 (HC1:tm StC S1=Some(mkTrans S1 DL StC))
 (HD0:tm StD S0=Some(mkTrans S1 DR StB))
 (HD1:tm StD S1=Some(mkTrans S0 DR StA)):
 forall c:cconf,p3d_hit tm c.
Proof.
 apply(p3d_finite tm HA0 HA1).
 - destruct s;[left|right];exact HB0.
 - exact HB1.
 - exact HC0.
 - exact HC1.
 - exact HD0.
 - exact HD1.
 - intro R. destruct(vfd_D0_frontier tm s HA0 HA1 HB0 HB1 HC0 HC1 HD0 HD1 R)
   as(k&L&R'&Ek).
   exists k,(lift(StD,(L,S0,R')));split;[exact Ek|reflexivity].
Qed.
