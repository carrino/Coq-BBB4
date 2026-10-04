(** A short marked return for the nested-overflow counter.  At A1 the
    nearest and third-nearest cells on the left are both one.  This local
    marker suffices even when the rest of the finite tape is arbitrary. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr.
Import ListNotations.
Section Core.
Variable tm:TM.
Hypotheses
 (HA0:tm StA S0=Some(mkTrans S1 DR StB))
 (HA1:tm StA S1=Some(mkTrans S0 DR StB))
 (HB0:tm StB S0=Some(mkTrans S1 DL StC))
 (HB1:tm StB S1=Some(mkTrans S1 DR StA))
 (HC0:tm StC S0=Some(mkTrans S0 DL StD))
 (HC1:tm StC S1=Some(mkTrans S0 DL StC))
 (HD0:tm StD S0=Some(mkTrans S1 DR StD))
 (HD1:tm StD S1=Some(mkTrans S0 DR StB)).
Local Ltac run :=
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR rep];
 repeat(first[rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR rep]);reflexivity.
Local Ltac go n := first
 [eapply(r1_run _ n);[lia|run|]
 |eapply(r0_run _ n);[run|]].
Definition on_anchor (b:Sym)(L R:list Sym):cconf := (StA,(S1::b::S1::L,S1,R)).
Definition on_hit(c:cconf):Prop := exists b L R, Reach0 tm c(on_anchor b L R).
Lemma on_back c d:Reach0 tm c d -> on_hit d -> on_hit c.
Proof. intros H(b&L&R&E). exists b,L,R. exact(reach0_trans tm c d _ H E). Qed.
Lemma on_here b L R:on_hit(on_anchor b L R).
Proof. exists b,L,R;apply reach0_refl. Qed.
Lemma on_drain:forall n L R,
 Reach0 tm(cL StC(rep [S1;S1] n++L)R)
          (cL StC L(rep [S0;S0] n++R)).
Proof. apply sweepL. intros;go 2;r0. Qed.
Lemma on_d_stop:forall L h R,
 on_hit(StD,(L,h,S0::S1::S1::S1::R)).
Proof.
 induction L as[|a L IH];intros h R;destruct h.
 - eapply on_back;[go 4;r0|apply on_here].
 - eapply on_back;[go 7;r0|apply on_here].
 - eapply on_back;[go 4;r0|apply on_here].
 - eapply on_back;[go 3;r0|apply IH].
Qed.
Lemma on_strong_zero:forall n L R,
 on_hit(cR StB(rep [S1;S1] n++S0::S1::S1::S1::L)(S0::R)).
Proof.
 intros. eapply on_back.
 - go 1. change(StC,(ctl(rep [S1;S1] n++S0::S1::S1::S1::L),chd(rep [S1;S1] n++S0::S1::S1::S1::L),S1::R))
   with(cL StC(rep [S1;S1] n++S0::S1::S1::S1::L)(S1::R)).
   rt on_drain. go 10;r0.
 - apply on_d_stop.
Qed.
Lemma on_strong:forall R n L,
 on_hit(cR StB(rep [S1;S1] n++S0::S1::S1::S1::L)R).
Proof.
 fix IH 1. intros[|[]R]n L.
 - change(on_hit(cR StB(rep [S1;S1] n++S0::S1::S1::S1::L)[S0])). apply on_strong_zero.
 - apply on_strong_zero.
 - destruct R as[|[]R].
   + eapply on_back;[go 2;r0|].
     change(on_hit(cR StB(rep [S1;S1](S n)++S0::S1::S1::S1::L)[])).
     change(on_hit(cR StB(rep [S1;S1](S n)++S0::S1::S1::S1::L)[S0])). apply on_strong_zero.
   + eapply on_back;[go 2;r0|].
     change(on_hit(cR StB(rep [S1;S1](S n)++S0::S1::S1::S1::L)R)). apply IH.
   + destruct n as[|n];eapply on_back;[go 1;r0|apply on_here|go 1;r0|apply on_here].
Qed.
Lemma on_weak_zero:forall n L R,
 on_hit(cR StB(rep [S1;S1] n++S0::S1::S0::S1::L)(S0::R)).
Proof.
 intros. eapply on_back.
 - go 1. change(StC,(ctl(rep [S1;S1] n++S0::S1::S0::S1::L),chd(rep [S1;S1] n++S0::S1::S0::S1::L),S1::R))
   with(cL StC(rep [S1;S1] n++S0::S1::S0::S1::L)(S1::R)).
   rt on_drain. go 7;r0.
 - exact(on_strong _ 0 L).
Qed.
Lemma on_weak:forall R n L,
 on_hit(cR StB(rep [S1;S1] n++S0::S1::S0::S1::L)R).
Proof.
 fix IH 1. intros[|[]R]n L.
 - change(on_hit(cR StB(rep [S1;S1] n++S0::S1::S0::S1::L)[S0])). apply on_weak_zero.
 - apply on_weak_zero.
 - destruct R as[|[]R].
   + eapply on_back;[go 2;r0|].
     change(on_hit(cR StB(rep [S1;S1](S n)++S0::S1::S0::S1::L)[])).
     change(on_hit(cR StB(rep [S1;S1](S n)++S0::S1::S0::S1::L)[S0])). apply on_weak_zero.
   + eapply on_back;[go 2;r0|].
     change(on_hit(cR StB(rep [S1;S1](S n)++S0::S1::S0::S1::L)R)). apply IH.
   + destruct n as[|n];eapply on_back;[go 1;r0|apply on_here|go 1;r0|apply on_here].
Qed.
Theorem on_return:forall b L R,exists b' L' R',
 Reach1 tm(on_anchor b L R)(on_anchor b' L' R').
Proof.
 intros b L R.
 assert(H:on_hit(cR StB(S0::S1::b::S1::L)R)).
 { destruct b;[exact(on_weak R 0 L)|exact(on_strong R 0 L)]. }
 destruct H as(b'&L'&R'&E). exists b',L',R'. unfold on_anchor at 1.
 go 1;exact E.
Qed.
(** D0 also has a direct witness: every finite B configuration reaches it. *)
Lemma on_d_fire:forall L h R,Fires tm(StD,(L,h,S0::R))(StD,S0).
Proof.
 induction L as[|a L IH];intros h R;destruct h.
 - apply fires_here;reflexivity.
 - eapply fire_back;[go 3;r0|apply fires_here;reflexivity].
 - apply fires_here;reflexivity.
 - eapply fire_back;[go 3;r0|apply IH].
Qed.
Lemma on_c_fire:forall L h R,Fires tm(StC,(L,h,R))(StD,S0).
Proof.
 induction L as[|a L IH];intros h R;destruct h.
 - eapply fire_back;[go 1;r0|apply on_d_fire].
 - eapply fire_back;[go 2;r0|apply on_d_fire].
 - eapply fire_back;[go 1;r0|apply on_d_fire].
 - eapply fire_back;[go 1;r0|apply IH].
Qed.
Lemma on_b_fire:forall R L,Fires tm(cR StB L R)(StD,S0).
Proof.
 fix IH 1. intros[|[]R]L.
 - eapply fire_back;[go 1;r0|apply on_c_fire].
 - eapply fire_back;[go 1;r0|apply on_c_fire].
 - destruct R as[|[]R].
   + eapply fire_back;[go 3;r0|apply on_c_fire].
   + eapply fire_back;[go 2;r0|apply IH].
   + eapply fire_back;[go 2;r0|apply IH].
Qed.
Theorem on_anchor_fire_d:forall b L R,Fires tm(on_anchor b L R)(StD,S0).
Proof. intros. eapply fire_back;[unfold on_anchor;go 1;r0|apply on_b_fire]. Qed.
End Core.
