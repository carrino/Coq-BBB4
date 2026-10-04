(** * Instruction witnesses for the signed binary counter

    A finite A sweep reaches the left blank boundary. Its initial fragment
    and boundary turn witness seven instructions; D scans the finite right
    word up to its terminal one to witness D1. Every marked anchor thus
    reaches all eight instructions, independently of the lap duration. *)
From Coq Require Import Arith Lia List ZArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import BlockCoreKValueTr.
Import ListNotations.
Section Machine.
Variable tm:TM.
Hypotheses
 (HA0:tm StA S0=Some(mkTrans S1 DR StB))
 (HA1:tm StA S1=Some(mkTrans S0 DL StC))
 (HB0:tm StB S0=Some(mkTrans S1 DR StC))
 (HB1:tm StB S1=Some(mkTrans S0 DR StD))
 (HC0:tm StC S0=Some(mkTrans S1 DL StA))
 (HC1:tm StC S1=Some(mkTrans S0 DL StC))
 (HD0:tm StD S0=Some(mkTrans S1 DR StD))
 (HD1:tm StD S1=Some(mkTrans S0 DR StA)).
Local Ltac run:=cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR bk_anchor bk_encode rep];
 repeat(first[rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR bk_anchor bk_encode rep]);reflexivity.
Local Ltac go n:=eapply(r0_run _ n);[run|].
Lemma bk_fire_A_scan:forall k L R,
 Reach0 tm(cL StA(rep[S1;S0]k++L)R)(cL StA L(rep[S1;S0]k++R)).
Proof. apply sweepL. intros;go 2;r0. Qed.
Lemma bk_fire_boundary:forall k R,
 Reach0 tm(cL StA(rep[S1;S0]k++[S1])R)
 (StA,([],S0,S1::S0::(rep[S1;S0]k++R))).
Proof. intros;eapply reach0_trans;[apply bk_fire_A_scan|];go 2;r0. Qed.
Lemma bk_anchor_boundary:forall n d w,exists R,
 Reach0 tm(bk_anchor(S n)(d::w))(StA,([],S0,S1::S0::R)).
Proof.
 intros n d w. replace(2*S n)with(S(S(2*n)))by lia.
 unfold bk_anchor. replace(2*S n)with(S(S(2*n)))by lia.
 destruct d;eexists;eapply reach0_trans.
 - go 5;r0.
 - apply (bk_fire_boundary(S(2*n))).
 - go 5;r0.
 - apply (bk_fire_boundary(S(2*n))).
Qed.
Lemma bk_anchor_simple_fires:forall n d w q,
 q<>(StD,S1)->Fires tm(bk_anchor(S n)(d::w))q.
Proof.
 intros n d w[q h]H. destruct q,h.
 - destruct(bk_anchor_boundary n d w)as(R&HR);eapply fire_back;[exact HR|apply fires_here;reflexivity].
 - destruct d;unfold bk_anchor;replace(2*S n)with(S(S(2*n)))by lia.
   + exists 2;eexists;split;[run|reflexivity].
   + exists 5;eexists;split;[run|reflexivity].
 - apply fires_here;reflexivity.
 - destruct(bk_anchor_boundary n d w)as(R&HR);eapply fire_back;[exact HR|].
   exists 1;eexists;split;[run|reflexivity].
 - destruct d;unfold bk_anchor;replace(2*S n)with(S(S(2*n)))by lia.
   + exists 1;eexists;split;[run|reflexivity].
   + exists 4;eexists;split;[run|reflexivity].
 - destruct d;unfold bk_anchor;replace(2*S n)with(S(S(2*n)))by lia.
   + exists 3;eexists;split;[run|reflexivity].
   + exists 1;eexists;split;[run|reflexivity].
 - destruct(bk_anchor_boundary n d w)as(R&HR);eapply fire_back;[exact HR|].
   exists 2;eexists;split;[run|reflexivity].
 - contradiction.
Qed.
Lemma bk_D_one_fires:forall U L R,
 Fires tm(cR StD L(U++S1::R))(StD,S1).
Proof.
 induction U as[|[]U IH];intros L R.
 - apply fires_here;reflexivity.
 - eapply fire_back;[go 1;r0|apply IH].
 - apply fires_here;reflexivity.
Qed.
Lemma bk_encode_last:forall w,exists U,bk_encode w=U++[S1].
Proof. induction w as[|d w(U&IH)].
 - exists[];reflexivity.
 - exists(d::S0::S0::U);cbn[bk_encode app];rewrite IH;reflexivity.
Qed.
Lemma bk_A_scan_D1:forall k U,
 Fires tm(cL StA(rep[S1;S0]k++[S1])(U++[S1]))(StD,S1).
Proof.
 intros k U;eapply fire_back;[apply bk_fire_boundary|].
 eapply fire_back;[go 3;r0|].
 rewrite app_assoc. apply(bk_D_one_fires (rep[S1;S0]k++U) _ []).
Qed.
Lemma bk_anchor_D1:forall n d w,Fires tm(bk_anchor(S n)(d::w))(StD,S1).
Proof.
 intros n d w. destruct(bk_encode_last w)as(U&EU).
 unfold bk_anchor;replace(2*S n)with(S(S(2*n)))by lia.
 destruct d;eapply fire_back.
 - go 5;r0.
 - change(Fires tm(cL StA(rep[S1;S0](S(2*n))++[S1])([S1;S0;S0;S1;S0;S0]++bk_encode w))(StD,S1)).
   rewrite EU,app_assoc;apply bk_A_scan_D1.
 - go 5;r0.
 - change(Fires tm(cL StA(rep[S1;S0](S(2*n))++[S1])([S1;S0;S0;S0;S0;S0]++bk_encode w))(StD,S1)).
   rewrite EU,app_assoc;apply bk_A_scan_D1.
Qed.
Theorem bk_anchor_fires:forall n w,1<=n->w<>[]->forall q,Fires tm(bk_anchor n w)q.
Proof.
 intros[|n][|d w]HN HW q;try lia;try contradiction.
 destruct(instr_eqb q(StD,S1))eqn:E.
 - apply instr_eqb_spec in E;subst;apply bk_anchor_D1.
 - apply bk_anchor_simple_fires;intro H;subst;discriminate.
Qed.
Theorem bk_mark_fires:forall c,bk_mark c->forall q,Fires tm c q.
Proof.
 intros c H q;destruct H as[n w Hn Hw].
 apply bk_anchor_fires;[exact Hn|apply bk_positive_nonempty;exact Hw].
Qed.
End Machine.
