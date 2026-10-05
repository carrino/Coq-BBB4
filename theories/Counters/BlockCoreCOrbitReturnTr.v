(** The shared 16-anchor orbit, with nine uniform round trips.
    The two blank-start orbits differ only in their terminal words.  Three
    word identities rotate the repeated block into the sweep orientation,
    restore that orientation between round trips, and collect one extra
    block at the end.  Counts zero and one use finite checked paths; the
    shared parametric proof covers every count at least two. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr BlockCoreCOrbitDefsTr BlockCoreCOrbitSweepTr.
From BBB4.Counters Require Import BlockCoreCOrbitFramesTr.
Import ListNotations.
Definition bco_tail_b(second:bool):list Sym:=if second then bco_tail2 else bco_tail.
Definition bco_cfg(second:bool)(n:nat):cconf:=(StA,([],S0,rep bco_Q n++bco_tail_b second)).
Lemma bco_word_commute:forall (P Q I:list Sym),P++I=I++Q->forall n,
 rep P n++I=I++rep Q n.
Proof.
 intros P Q I H n;induction n as[|n IH].
 - cbn[rep];rewrite app_nil_r;reflexivity.
 - cbn[rep];rewrite <-app_assoc,IH,app_assoc,H.
   repeat rewrite <-app_assoc;reflexivity.
Qed.
Lemma bco_word_transfer:forall(P Q I A B:list Sym),P++I=I++Q->A=I++B->forall n,
 rep P n++A=I++rep Q n++B.
Proof.
 intros P Q I A B H -> n;rewrite app_assoc,(bco_word_commute _ _ _ H).
 rewrite <-app_assoc;reflexivity.
Qed.
Lemma bco_word_initial:forall second n,
 rep bco_Q(n+2)++bco_tail_b second=
 bco_initial_prefix++rep bco_Qr n++bco_T second.
Proof.
 intros second n;rewrite rep_add,<-app_assoc.
 apply bco_word_transfer;destruct second;reflexivity.
Qed.
Definition bco_frame_turn:list Sym:=skipn 14 bco_frame_prefix.
Lemma bco_word_reset:forall second n,
 bco_G++rep bco_Wl n++bco_S second=
 bco_frame_prefix++rep bco_Qr n++bco_T second++[S0].
Proof.
 intros second n.
 change(bco_G++rep bco_Wl n++bco_S second=
 bco_G++bco_frame_turn++rep bco_Qr n++(bco_T second++[S0])).
 f_equal;apply bco_word_transfer;destruct second;reflexivity.
Qed.
Lemma bco_word_finish:forall second n,
 bco_finish_prefix++rep bco_Wl n++bco_S second=
 (rep bco_Q(n+3)++bco_tail_b second)++[S0].
Proof.
 intros second n;rewrite rep_add;repeat rewrite <-app_assoc.
 assert(H:bco_Q++bco_finish_prefix=bco_finish_prefix++bco_Wl)by reflexivity.
 rewrite app_assoc,<-(bco_word_commute _ _ _ H),<-app_assoc.
 f_equal;destruct second;reflexivity.
Qed.

Section Machine.
Variable tm:TM.
Hypothesis Htm:forall q h,tm q h=bco_tm q h.
Theorem bco_return_large:forall second n,
 Reach1 tm(bco_cfg second(n+2))(bco_cfg second(n+3)).
Proof.
 intros second n;unfold bco_cfg;rewrite bco_word_initial.
 change(Reach1 tm(cR StA [](S0::bco_initial_prefix++rep bco_Qr n++bco_T second))
  (StA,([],S0,rep bco_Q(n+3)++bco_tail_b second))).
 eapply reach10;[apply bco_frame_init;exact Htm|].
 change bco_AX with (bco_A++bco_X).
 eapply reach0_trans;[apply bco_roundtrip;exact Htm|].
 rewrite bco_word_reset.
 eapply reach0_trans;[apply bco_frame_step_0;exact Htm|].
 change bco_AX with (bco_A++bco_X).
 eapply reach0_trans;[apply bco_roundtrip_pad;exact Htm|].
 rewrite bco_word_reset.
 eapply reach0_trans;[apply bco_frame_step_1;exact Htm|].
 change bco_AX with (bco_A++bco_X).
 eapply reach0_trans;[apply bco_roundtrip_pad;exact Htm|].
 rewrite bco_word_reset.
 eapply reach0_trans;[apply bco_frame_step_2;exact Htm|].
 change bco_AX with (bco_A++bco_X).
 eapply reach0_trans;[apply bco_roundtrip_pad;exact Htm|].
 rewrite bco_word_reset.
 eapply reach0_trans;[apply bco_frame_step_3;exact Htm|].
 change bco_AX with (bco_A++bco_X).
 eapply reach0_trans;[apply bco_roundtrip_pad;exact Htm|].
 rewrite bco_word_reset.
 eapply reach0_trans;[apply bco_frame_step_4;exact Htm|].
 change bco_AX with (bco_A++bco_X).
 eapply reach0_trans;[apply bco_roundtrip_pad;exact Htm|].
 rewrite bco_word_reset.
 eapply reach0_trans;[apply bco_frame_step_5;exact Htm|].
 change bco_AX with (bco_A++bco_X).
 eapply reach0_trans;[apply bco_roundtrip_pad;exact Htm|].
 rewrite bco_word_reset.
 eapply reach0_trans;[apply bco_frame_step_6;exact Htm|].
 change bco_AX with (bco_A++bco_X).
 eapply reach0_trans;[apply bco_roundtrip_pad;exact Htm|].
 rewrite bco_word_reset.
 eapply reach0_trans;[apply bco_frame_step_7;exact Htm|].
 change bco_AX with (bco_A++bco_X).
 eapply reach0_trans;[apply bco_roundtrip_pad;exact Htm|].
 eapply reach0_trans;[apply bco_frame_finish;exact Htm|].
 rewrite bco_word_finish;apply reach0_lift.
 apply(lift_padR 1).
Qed.
Theorem bco_return:forall n,Reach1 tm(bco_anchor n)(bco_anchor(S n)).
Proof.
 intros [|[|n]].
 - apply bco_base0;exact Htm.
 - apply bco_base1;exact Htm.
 - replace(S(S n))with(n+2)by lia;replace(S(n+2))with(n+3)by lia.
   exact(bco_return_large false n).
Qed.
Theorem bco_return2:forall n,Reach1 tm(bco_anchor2 n)(bco_anchor2(S n)).
Proof.
 intros [|[|n]].
 - apply bco_base20;exact Htm.
 - apply bco_base21;exact Htm.
 - replace(S(S n))with(n+2)by lia;replace(S(n+2))with(n+3)by lia.
   exact(bco_return_large true n).
Qed.
End Machine.
