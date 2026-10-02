(** * Every finite frontier word reaches B0.

    The induction follows the length of the unprocessed original suffix;
    it permits an arbitrary prefix of P blocks and an arbitrary zigzag.
    A U block normalizes modulo three.  A pending zigzag of length two
    either meets three ones and reaches B0, or makes the universally
    terminating prefix P2.  Thus each surviving frontier round consumes
    three symbols of the original suffix.  Explicit zero padding is
    removed only in the final tape-semantics theorem. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import ValueFrontierTransducer ValueWordNormalization.
Import ListNotations.

Lemma pwt_zig_succ n : vft_zig (S n) = vft_zig n ++ [S1;S0].
Proof. induction n; cbn [vft_zig app]; [reflexivity|]. f_equal. f_equal. exact IHn. Qed.
Lemma pwt_zig_cons n R : vft_zig n++S1::S0::R = vft_zig(S n)++R.
Proof. rewrite pwt_zig_succ,<-app_assoc. reflexivity. Qed.
Lemma pwt_P_cons n R : vft_zig n++S1::S1::S0::R = vft_P n++R.
Proof. unfold vft_P;rewrite <-app_assoc;reflexivity. Qed.
Lemma pwt_Q_cons n R : vft_zig n++S1::S1::S1::R = vft_Q n++R.
Proof. unfold vft_Q;rewrite <-app_assoc;reflexivity. Qed.
Lemma pwt_Ps_app ns ms : vft_Ps(ns++ms)=vft_Ps ns++vft_Ps ms.
Proof. induction ns; cbn [vft_Ps app]; [reflexivity|now rewrite IHns,app_assoc]. Qed.
Lemma pwt_mod3 n : exists k, n=3*k \/ n=3*k+1 \/ n=3*k+2.
Proof.
 exists(n/3). pose proof(Nat.div_mod n 3 ltac:(lia)).
 pose proof(Nat.mod_upper_bound n 3 ltac:(lia)). lia.
Qed.

Lemma pwt_bad_prefix : forall R ms n,
 vwn_Halt(vft_Ps(2::ms)++vft_zig n++R++[S0;S0]).
Proof.
 intro R. remember(length R)as z eqn:Ez. revert R Ez.
 induction z using lt_wf_ind; intros R Ez ms n.
 destruct R as[|a R].
 - change(vwn_Halt(vft_Ps(2::ms)++vft_zig n++S0::[S0])). apply vwn_terminal.
 - destruct a.
   + change(vwn_Halt(vft_Ps(2::ms)++vft_zig n++S0::(R++[S0;S0]))).
     apply vwn_terminal.
   + destruct R as[|a R].
     * cbn[app]. rewrite pwt_zig_cons. change(vwn_Halt(vft_Ps(2::ms)++vft_zig(S n)++S0::[])).
       apply vwn_terminal.
     * destruct a.
       -- cbn[app]. rewrite pwt_zig_cons. apply(H(length R)); [cbn in Ez;lia|reflexivity].
       -- destruct R as[|a R].
          ++ cbn[app]. rewrite pwt_P_cons.
             replace(vft_Ps(2::ms)++vft_P n++[S0])with
              (vft_Ps((2::ms)++[n])++vft_zig 0++S0::[])by
              (rewrite pwt_Ps_app;cbn[vft_Ps vft_zig];rewrite app_nil_r,<-app_assoc;reflexivity).
             apply vwn_terminal.
          ++ destruct a.
             ** cbn[app]. rewrite pwt_P_cons.
                replace(vft_Ps(2::ms)++vft_P n++R++[S0;S0])with
                 (vft_Ps(2::(ms++[n]))++vft_zig 0++R++[S0;S0])by
                 (cbn[vft_Ps vft_zig];rewrite pwt_Ps_app;cbn[vft_Ps];rewrite app_nil_r;repeat rewrite <-app_assoc;reflexivity).
                apply(H(length R)); [cbn in Ez;lia|reflexivity].
             ** cbn[app]. rewrite pwt_Q_cons.
                apply vwn_round.
                cbn[vft_Us]. rewrite <-app_assoc.
                apply(vwn_Us2 0).
Qed.

Lemma pwt_zig2_three R : vwn_Halt(vft_zig 2++S1::S1::S1::R).
Proof.
 change(vwn_Halt(vft_Ps []++vft_Q 2++R)). apply vwn_round.
 change(vwn_Halt(vft_U(3*0+2)++S1::S0::R)). apply vwn_Us2.
Qed.

Lemma pwt_Us_all : forall ns R,
 (forall n,vwn_Halt(vft_zig n++R++[S0;S0])) ->
 vwn_Halt(vft_Us ns++R++[S0;S0]).
Proof.
 induction ns as[|n ns IH];intros R H.
 - apply(H 0).
 - cbn[vft_Us]. destruct(pwt_mod3 n)as[k[En|[En|En]]];subst n.
   + rewrite <-app_assoc. apply vwn_Us0. apply IH,H.
   + rewrite <-app_assoc. apply vwn_Us1.
     destruct ns as[|j ns].
     * cbn[vft_Us app]. apply H.
     * destruct j.
       -- pose proof(pwt_bad_prefix(vft_Us ns++R)[]0)as E.
          cbn[vft_Ps vft_P vft_zig vft_Us vft_U Nat.mul Nat.add repeat app]in E|-*.
          rewrite <-app_assoc in E. exact E.
       -- cbn[vft_Us]. unfold vft_U at 1.
          replace(2*S j+2)with(S(S(S(2*j+1))))by lia.
          cbn[repeat app]. apply pwt_zig2_three.
   + rewrite <-app_assoc. apply vwn_Us2.
Qed.

Theorem pwt_all_padded : forall R ms n,
 vwn_Halt(vft_Ps ms++vft_zig n++R++[S0;S0]).
Proof.
 intro R. remember(length R)as z eqn:Ez. revert R Ez.
 induction z using lt_wf_ind;intros R Ez ms n.
 destruct R as[|a R].
 - change(vwn_Halt(vft_Ps ms++vft_zig n++S0::[S0])). apply vwn_terminal.
 - destruct a.
   + change(vwn_Halt(vft_Ps ms++vft_zig n++S0::(R++[S0;S0]))). apply vwn_terminal.
   + destruct R as[|a R].
     * cbn[app]. rewrite pwt_zig_cons. change(vwn_Halt(vft_Ps ms++vft_zig(S n)++S0::[])). apply vwn_terminal.
     * destruct a.
       -- cbn[app]. rewrite pwt_zig_cons. apply(H(length R));[cbn in Ez;lia|reflexivity].
       -- destruct R as[|a R].
          ++ cbn[app]. rewrite pwt_P_cons.
             replace(vft_Ps ms++vft_P n++[S0])with
              (vft_Ps(ms++[n])++vft_zig 0++S0::[])by
              (rewrite pwt_Ps_app;cbn[vft_Ps vft_zig];rewrite app_nil_r,<-app_assoc;reflexivity).
             apply vwn_terminal.
          ++ destruct a.
             ** cbn[app]. rewrite pwt_P_cons.
                replace(vft_Ps ms++vft_P n++R++[S0;S0])with
                 (vft_Ps(ms++[n])++vft_zig 0++R++[S0;S0])by
                 (rewrite pwt_Ps_app;cbn[vft_Ps vft_zig];rewrite app_nil_r;repeat rewrite <-app_assoc;reflexivity).
                apply(H(length R));[cbn in Ez;lia|reflexivity].
             ** cbn[app]. rewrite pwt_Q_cons.
                apply vwn_round.
                replace(vft_Us ms++vft_U n++S1::S0::(R++[S0;S0]))with
                 (vft_Us(ms++[n])++(S1::S0::R)++[S0;S0])by
                 (rewrite vft_Us_app;cbn[vft_Us];rewrite app_nil_r;repeat rewrite <-app_assoc;reflexivity).
                apply pwt_Us_all. intro b.
                change(vwn_Halt(vft_zig b++[S1;S0]++R++[S0;S0])).
                rewrite app_assoc,<-pwt_zig_succ.
                change(vwn_Halt(vft_Ps []++vft_zig(S b)++R++[S0;S0])).
                apply(H(length R));[cbn in Ez;lia|reflexivity].
Qed.
Corollary pwt_all R : vwn_Halt(R++[S0;S0]).
Proof. exact(pwt_all_padded R [] 0). Qed.

Lemma pwt_pad R : lift(StA,([],S0,R))=lift(StA,([],S0,R++[S0;S0])).
Proof.
 apply ceqb_lift. cbn[ceqb st_eqb sym_eqb lpad_eqb].
 induction R as[|a R IH];[reflexivity|].
 cbn[app lpad_eqb]. destruct a;cbn[sym_eqb];exact IH.
Qed.
Theorem pwt_frontier tm
 (HA0:tm StA S0=Some(mkTrans S1 DR StB))
 (HA1:tm StA S1=Some(mkTrans S0 DL StC))
 (HB1:tm StB S1=Some(mkTrans S1 DR StD))
 (HC0:tm StC S0=Some(mkTrans S1 DL StA))
 (HC1:tm StC S1=Some(mkTrans S1 DL StC))
 (HD0:tm StD S0=Some(mkTrans S1 DR StB))
 (HD1:tm StD S1=Some(mkTrans S0 DR StA)) R :
 exists k L R',0<k /\
 stepn tm k(lift(StA,([],S0,R)))=Some(lift(StB,(L,S0,R'))).
Proof.
 rewrite pwt_pad. apply(vwn_Halt_sound tm HA0 HA1 HB1 HC0 HC1 HD0 HD1),pwt_all.
Qed.
