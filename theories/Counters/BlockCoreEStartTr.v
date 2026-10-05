(** The three uniform shuttles in the paired-zero block-list entrance. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
Definition bce_unit:list Sym := [S0;S0;S1;S1;S1;S1;S1].
Definition bce_right_prefix:list Sym := [S1;S1;S1;S1].
Definition bce_work:list Sym := [S1;S1;S0;S1;S0;S1;S0].
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
Local Ltac run :=
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR rep
 bce_unit bce_right_prefix bce_work];
 repeat(first[rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR rep
 bce_unit bce_right_prefix bce_work]);reflexivity.
Local Ltac go n := first
 [eapply(r1_run _ n);[lia|run|]
 |eapply(r0_run _ n);[run|]].
Lemma bce_unit_right:forall L R,
 Reach0 tm(cR StD(S1::S1::L)(bce_unit++R))
          (cR StD(S1::S1::bce_work++L)R).
Proof. intros;go 13;r0. Qed.
Lemma bce_unit_left:forall L R,
 Reach0 tm(cL StA(bce_work++L)(bce_right_prefix++R))
          (cL StA L(bce_right_prefix++bce_unit++R)).
Proof. intros;go 7;r0. Qed.
Lemma bce_shuttle:forall k L,
 Reach0 tm(cR StD(S1::S1::L)(rep bce_unit k))
          (cL StA L(bce_right_prefix++rep bce_unit k)).
Proof.
 induction k as[|k IH];intro L.
 - cbn[rep]. go 13.
   eapply reach0_lift_l with(a':=cL StA L bce_right_prefix).
   + unfold cL,bce_right_prefix.
     change(lift(StA,(ctl L,chd L,[S1;S1;S1;S1]++rep[S0]1))=
            lift(StA,(ctl L,chd L,[S1;S1;S1;S1]))).
     apply lift_padR.
   + r0.
 - cbn[rep]. rt bce_unit_right. rt IH. apply bce_unit_left.
Qed.
Definition bce_start(n:nat)(U:list Sym):cconf :=
 (StA,(S1::S0::S1::U,S0,bce_right_prefix++rep bce_unit(S n))).
Theorem bce_start_to_left:forall n U,
 Reach1 tm(bce_start n U)
   (cL StA U(S1::S1::S0::S0::S1::S1::S1::rep bce_unit(S(S n)))).
Proof.
 intros n U. unfold bce_start. go 9.
 change(Reach0 tm(cR StD(S1::S1::S1::S0::S1::S0::S0::S1::U)
   (rep bce_unit(S n)))
   (cL StA U(S1::S1::S0::S0::S1::S1::S1::rep bce_unit(S(S n))))).
 rt bce_shuttle. go 17.
 change(Reach0 tm(cR StD(S1::S1::S1::S1::S1::S1::S1::S0::S1::S0::U)
   (rep bce_unit(S n)))
   (cL StA U(S1::S1::S0::S0::S1::S1::S1::rep bce_unit(S(S n))))).
 rt bce_shuttle. go 9.
 change(Reach0 tm(cR StD(S1::S1::S1::S1::S0::S1::S0::S1::S1::S0::S1::S0::U)
   (rep bce_unit(S n)))
   (cL StA U(S1::S1::S0::S0::S1::S1::S1::rep bce_unit(S(S n))))).
 rt bce_shuttle. go 10;r0.
Qed.
End Core.
