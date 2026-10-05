(** Finite connecting paths between the shared periodic core-C sweeps.
    Every path is quantified over its untouched right tail.  The initial
    path contributes the positive step needed by the final return theorem;
    the eight middle paths join nine copies of the same guarded round trip. *)
From Coq Require Import Arith Lia List FunctionalExtensionality.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr BlockCoreCOrbitDefsTr.
Import ListNotations.
Definition bco_initial_prefix:list Sym:=[S1;S0;S1;S1;S1;S1;S0;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1].
Definition bco_frame_prefix:list Sym:=[S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1].
Definition bco_finish_prefix:list Sym:=[S1;S0;S1;S1;S1;S1;S0;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0].
Definition bco_AX:list Sym:=[S0;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S0;S1;S0;S1;S0;S1;S1;S0;S1;S1;S1;S0;S1;S0;S1;S0;S1;S1;S0;S1;S1;S1;S0;S1;S0;S1;S0;S1;S1;S0;S1;S1;S1].
Definition bco_frame_0:list Sym:=[S0;S1;S1;S0;S1;S0;S1;S1].
Definition bco_frame_1:list Sym:=[S0;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1].
Definition bco_frame_2:list Sym:=[S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S0;S1;S0;S1;S0;S1;S1;S1;S1].
Definition bco_frame_3:list Sym:=[S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S0;S1;S0;S1;S0;S1;S1;S0;S1;S1;S1;S0;S1;S0;S1].
Definition bco_frame_4:list Sym:=[S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S0;S1;S0;S1;S0;S1;S1;S0;S1;S1;S1;S0;S1;S0;S1;S0;S1;S0;S1;S1;S1;S1].
Definition bco_frame_5:list Sym:=[S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S0;S1;S0;S1;S0;S1;S1;S0;S1;S1;S1;S0;S1;S0;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S0;S1;S1].
Definition bco_frame_6:list Sym:=[S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S0;S1;S0;S1;S0;S1;S1;S0;S1;S1;S1;S0;S1;S0;S1;S0;S1;S1;S0;S1;S1;S1;S0;S1;S0;S1;S0;S1;S0;S1].
Definition bco_frame_7:list Sym:=[S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S0;S1;S0;S1;S0;S1;S1;S0;S1;S1;S1;S0;S1;S0;S1;S0;S1;S1;S0;S1;S1;S1;S0;S1;S0;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1].
Definition bco_frame_8:list Sym:=[S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S0;S1;S0;S1;S0;S1;S1;S0;S1;S1;S1;S0;S1;S0;S1;S0;S1;S1;S0;S1;S1;S1;S0;S1;S0;S1;S0;S1;S1;S0;S1;S1;S1;S0;S1;S0;S1;S0;S1;S1;S0;S1;S1].
Section Machine.
Variable tm:TM.
Hypothesis Htm:forall q h,tm q h=bco_tm q h.
Lemma bco_frames_tm:tm=bco_tm.
Proof. apply functional_extensionality;intro q;apply functional_extensionality;apply Htm. Qed.
Local Ltac run:=rewrite bco_frames_tm;vm_compute;reflexivity.
Lemma bco_frame_init:forall R,
 Reach1 tm(cR StA [](S0::bco_initial_prefix++R))
 (cR StB(bco_AX++bco_frame_0)R).
Proof. intro R;eapply(r1_run _ 305);[lia|run|r0]. Qed.
Lemma bco_frame_step_0:forall R,
 Reach0 tm(cL StC bco_frame_0(bco_frame_prefix++R))
 (cR StB(bco_AX++bco_frame_1)R).
Proof. intro R;eapply(r0_run _ 440);[run|r0]. Qed.
Lemma bco_frame_step_1:forall R,
 Reach0 tm(cL StC bco_frame_1(bco_frame_prefix++R))
 (cR StB(bco_AX++bco_frame_2)R).
Proof. intro R;eapply(r0_run _ 462);[run|r0]. Qed.
Lemma bco_frame_step_2:forall R,
 Reach0 tm(cL StC bco_frame_2(bco_frame_prefix++R))
 (cR StB(bco_AX++bco_frame_3)R).
Proof. intro R;eapply(r0_run _ 544);[run|r0]. Qed.
Lemma bco_frame_step_3:forall R,
 Reach0 tm(cL StC bco_frame_3(bco_frame_prefix++R))
 (cR StB(bco_AX++bco_frame_4)R).
Proof. intro R;eapply(r0_run _ 584);[run|r0]. Qed.
Lemma bco_frame_step_4:forall R,
 Reach0 tm(cL StC bco_frame_4(bco_frame_prefix++R))
 (cR StB(bco_AX++bco_frame_5)R).
Proof. intro R;eapply(r0_run _ 636);[run|r0]. Qed.
Lemma bco_frame_step_5:forall R,
 Reach0 tm(cL StC bco_frame_5(bco_frame_prefix++R))
 (cR StB(bco_AX++bco_frame_6)R).
Proof. intro R;eapply(r0_run _ 668);[run|r0]. Qed.
Lemma bco_frame_step_6:forall R,
 Reach0 tm(cL StC bco_frame_6(bco_frame_prefix++R))
 (cR StB(bco_AX++bco_frame_7)R).
Proof. intro R;eapply(r0_run _ 736);[run|r0]. Qed.
Lemma bco_frame_step_7:forall R,
 Reach0 tm(cL StC bco_frame_7(bco_frame_prefix++R))
 (cR StB(bco_AX++bco_frame_8)R).
Proof. intro R;eapply(r0_run _ 792);[run|r0]. Qed.
Lemma bco_frame_finish:forall R,
 Reach0 tm(cL StC bco_frame_8([S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0]++R))
 (StA,([],S0,bco_finish_prefix++R)).
Proof. intro R;eapply(r0_run _ 251);[run|r0]. Qed.
End Machine.
