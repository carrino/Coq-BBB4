(** A marked return combining the periodic sweep and its finite wall. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import BlockCoreEStartTr BlockCoreELeftTr BlockCoreEWallTr.
Import ListNotations.
Inductive ber_mark:cconf->Prop:=
| ber_start:forall n U,ber_mark(bce_start n U)
| ber_wall:forall n L P W,bew_word W->
 ber_mark(StA,(L,S0,P++W++rep bce_unit(S n))).
Lemma ber_mark_instr:forall c,ber_mark c->cinstr c=(StA,S0).
Proof. intros c H;inversion H;reflexivity. Qed.
Section Core.
Variable tm:TM.
Hypotheses
 (HA0:tm StA S0=Some(mkTrans S1 DR StA))
 (HA1:tm StA S1=Some(mkTrans S1 DL StB))
 (HB0:tm StB S0=Some(mkTrans S1 DL StA))
 (HB1:tm StB S1=Some(mkTrans S0 DL StC))
 (HC0:tm StC S0=Some(mkTrans S0 DL StA))
 (HC1:tm StC S1=Some(mkTrans S0 DR StD))
 (HD0:tm StD S0=Some(mkTrans S1 DR StC))
 (HD1:tm StD S1=Some(mkTrans S1 DR StD)).
Lemma ber_exit:forall n V,
 Reach0 tm(cR StD(bew_exit++V)(rep bce_unit(S n)))(bce_start n V).
Proof.
 intros n V.
 change(Reach0 tm(cR StD(S1::S1::(S0::S1::S0::S1::V))(rep bce_unit(S n)))
                 (cL StA(S0::S1::S0::S1::V)(bce_right_prefix++rep bce_unit(S n)))).
 apply bce_shuttle;assumption.
Qed.
Lemma ber_result:forall n c,bew_result tm(rep bce_unit(S n))c->
 exists d,ber_mark d/\Reach0 tm c d.
Proof.
 intros n c[(W&HW&L&P&HR)|(V&HR)].
 - exists(StA,(L,S0,P++W++rep bce_unit(S n)));split;[apply ber_wall;exact HW|exact HR].
 - exists(bce_start n V);split;[apply ber_start|]. eapply reach0_trans;[exact HR|apply ber_exit].
Qed.
Theorem ber_return:forall c,ber_mark c->exists d,ber_mark d/\Reach1 tm c d.
Proof.
 intros c HM;inversion HM;subst.
 - pose proof(bce_start_to_left tm HA0 HA1 HB0 HB1 HC0 HC1 HD0 HD1 n U)as HS.
   change(Reach1 tm(bce_start n U)(cL StA U(bew_P++rep bce_unit(S(S n)))))in HS.
   pose proof(bew_left_finite tm HA1 HB0 HB1 HC0 HC1 HD0 HD1 U bew_P
       (rep bce_unit(S(S n)))StA ltac:(left;reflexivity)ltac:(left;reflexivity))as HR.
   destruct(ber_result(S n)_ HR)as(d&HD&HH).
   exists d;split;[exact HD|eapply reach10;eauto].
 - destruct(bew_A0_prefix tm HA1 HB0 HB1 HC0 HC1 HD0 HD1 HA0
     L P W(rep bce_unit(S n))H)as[(L'&P'&W'&HW&HR)|(V&HR)].
   + exists(StA,(L',S0,P'++W'++rep bce_unit(S n)));split;[apply ber_wall;exact HW|exact HR].
   + exists(bce_start n V);split;[apply ber_start|]. eapply reach10;[exact HR|apply ber_exit].
Qed.
End Core.
