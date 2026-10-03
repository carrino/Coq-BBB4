(** A marked binary carry forces a return to A1. The marker is recreated
    by leaving A1, so recurrence needs no invariant for the whole run. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
Section Core.
Variable tm:TM.
Hypotheses
 (HA0:tm StA S0=Some(mkTrans S0 DR StB))
 (HA1:tm StA S1=Some(mkTrans S0 DL StA))
 (HB0:tm StB S0=Some(mkTrans S1 DR StC))
 (HB1:tm StB S1=Some(mkTrans S0 DR StC))
 (HC0:tm StC S0=Some(mkTrans S1 DL StD))
 (HC1:tm StC S1=Some(mkTrans S1 DR StB))
 (HD0:tm StD S0=Some(mkTrans S1 DL StA))
 (HD1:tm StD S1=Some(mkTrans S0 DL StD)).
Local Ltac run :=
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR rep];
 repeat(first[rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR rep]);reflexivity.
Local Ltac go n := first
 [eapply(r1_run _ n);[lia|run|]
 |eapply(r0_run _ n);[run|]].
Definition mc_anchor(L R:list Sym):cconf := cR StC(S0::S0::L)R.
Definition mc_hit(c:cconf):Prop := Fires tm c(StA,S1).
Lemma mc_scan:forall n L R,
 Reach0 tm(cR StC L(rep [S1;S0] n++R))
          (cR StC(rep [S1;S1] n++L)R).
Proof. apply sweepR. intros;go 2;r0. Qed.
Lemma mc_drain:forall n L R,
 Reach0 tm(cL StD(rep [S1;S1] n++L)R)
          (cL StD L(rep [S0;S0] n++R)).
Proof. apply sweepL. intros;go 2;r0. Qed.
Lemma mc_finish:forall n L R,
 mc_hit(cR StC(rep [S1;S1] n++S0::S1::L)(S0::R)).
Proof.
 intros;unfold mc_hit;eapply fire_back.
 - go 1. change(StD,(ctl(rep [S1;S1] n++S0::S1::L),chd(rep [S1;S1] n++S0::S1::L),S1::R))
   with(cL StD(rep [S1;S1] n++S0::S1::L)(S1::R)).
   rt mc_drain. go 1;r0.
 - apply fires_here;reflexivity.
Qed.
Lemma mc_stop:forall R n L,mc_hit(cR StC(rep [S1;S1] n++S0::S1::L)R).
Proof.
 fix IH 1. intros[|[]R]n L.
 - change(mc_hit(cR StC(rep [S1;S1] n++S0::S1::L)[S0])). apply mc_finish.
 - apply mc_finish.
 - destruct R as[|[]R].
   + eapply fire_back;[go 2;r0|].
     change(mc_hit(cR StC(rep [S1;S1](S n)++S0::S1::L)[S0])). apply mc_finish.
   + eapply fire_back;[go 2;r0|].
     change(mc_hit(cR StC(rep [S1;S1](S n)++S0::S1::L)R)). apply IH.
   + eapply fire_back;[go 2;r0|]. exact(IH R 0 (rep [S1;S1] n++S0::S1::L)).
Qed.
Lemma mc_carry:forall k L R,
 Reach1 tm(mc_anchor L(rep [S1;S0] k++S0::R))
          (mc_anchor L(rep [S0;S0] k++S1::R)).
Proof.
 intros. unfold mc_anchor. eapply reach01;[apply mc_scan|]. go 1.
 change(StD,(ctl(rep [S1;S1] k++S0::S0::L),chd(rep [S1;S1] k++S0::S0::L),S1::R))
 with(cL StD(rep [S1;S1] k++S0::S0::L)(S1::R)).
 rt mc_drain. go 3;r0.
Qed.
Lemma mc_fill:forall k L R,
 Reach0 tm(mc_anchor L(rep [S0;S0] k++R))
          (mc_anchor L(rep [S1;S0] k++R)).
Proof.
 intros k L R. apply(count_from_carry_lt tm(mc_anchor L)[S0;S0][S1;S0]k).
 intros j Y _. apply mc_carry.
Qed.
Lemma mc_bad:forall k L R,
 mc_hit(mc_anchor L(rep [S1;S0] k++S1::S1::R)).
Proof.
 intros;unfold mc_hit,mc_anchor;eapply fire_back.
 - rt mc_scan. go 2;r0.
 - exact(mc_stop R 0 (rep [S1;S1] k++S0::S0::L)).
Qed.
Lemma mc_marker:forall k L R,
 mc_hit(mc_anchor L(rep [S0;S0] k++S0::S1::R)).
Proof.
 intros;eapply fire_back;[apply mc_fill|].
 eapply fire_back;[apply reach1_0,mc_carry|].
 eapply fire_back;[apply mc_fill|apply mc_bad].
Qed.
Lemma mc_seed_turn:forall k L R,
 mc_hit(cR StC(rep [S1;S1] k++S1::S0::L)(S0::R)).
Proof.
 intros. unfold mc_hit. eapply fire_back.
 - go 1. change(StD,(ctl(rep [S1;S1] k++S1::S0::L),chd(rep [S1;S1] k++S1::S0::L),S1::R))
   with(cL StD(rep [S1;S1] k++S1::S0::L)(S1::R)).
   rt mc_drain. go 2;r0.
 - destruct L as[|[]L];try(apply fires_here;reflexivity).
   all:eapply fire_back;[go 2;r0|].
   + change(mc_hit(mc_anchor [] (S0::rep [S0;S0] k++S1::R))).
     rewrite(rep_shift S0 S0 k);apply mc_marker.
   + change(mc_hit(mc_anchor L (S0::rep [S0;S0] k++S1::R))).
   rewrite(rep_shift S0 S0 k);apply mc_marker.
Qed.
Lemma mc_seed:forall R k L,
 mc_hit(cR StC(rep [S1;S1] k++S1::S0::L)R).
Proof.
 fix IH 1. intros[|[]R]k L.
 - change(mc_hit(cR StC(rep [S1;S1] k++S1::S0::L)[S0])). apply mc_seed_turn.
 - apply mc_seed_turn.
 - destruct R as[|[]R].
   + eapply fire_back;[go 2;r0|].
     change(mc_hit(cR StC(rep [S1;S1](S k)++S1::S0::L)[S0])). apply mc_seed_turn.
   + eapply fire_back;[go 2;r0|].
     change(mc_hit(cR StC(rep [S1;S1](S k)++S1::S0::L)R)). apply IH.
   + eapply fire_back;[go 2;r0|]. exact(mc_stop R 0 (rep [S1;S1] k++S1::S0::L)).
Qed.
Theorem mc_return:forall L R,exists k L' R',0<k /\
 csteps tm k(StA,(L,S1,R))=Some(StA,(L',S1,R')).
Proof.
 intros L R.
 assert(E:csteps tm 1(StA,(L,S1,R))=Some(cL StA L(S0::R)))by run.
 assert(H:mc_hit(cL StA L(S0::R))).
 { destruct L as[|[]L];try(apply fires_here;reflexivity).
   all:eapply fire_back;[go 2;r0|apply(mc_seed R 0)]. }
 destruct H as(k&[q[[U h]V]]&Hr&Hi).
 unfold cinstr in Hi;cbn in Hi;injection Hi as Hq Hh. subst q h.
 exists(1+k),U,V;split;[lia|]. rewrite csteps_add,E;exact Hr.
Qed.
End Core.
