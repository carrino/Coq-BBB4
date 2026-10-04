(** The three-cell mirror counter only needs a local return invariant:
    a C1 with a 1 immediately to its left. A leftward walk preserves a
    right-hand 01 marker, preceded by an arbitrary run of ones. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
Section Core.
Variable tm:TM.
Hypotheses
 (HA0:tm StA S0=Some(mkTrans S1 DR StB))
 (HA1:tm StA S1=Some(mkTrans S1 DL StD))
 (HB0:tm StB S0=Some(mkTrans S1 DR StC))
 (HB1:tm StB S1=Some(mkTrans S0 DR StB))
 (HC0:tm StC S0=Some(mkTrans S1 DL StA))
 (HC1:tm StC S1=Some(mkTrans S1 DR StC))
 (HD0:tm StD S0=Some(mkTrans S1 DL StC))
 (HD1:tm StD S1=Some(mkTrans S0 DL StA)).
Local Ltac run :=
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR rep];
 repeat(first[rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR rep]);reflexivity.
Local Ltac go n := first
 [eapply(r1_run _ n);[lia|run|]
 |eapply(r0_run _ n);[run|]].
Definition mn_anchor(L R:list Sym):cconf := (StC,(S1::L,S1,R)).
Definition mn_hit(c:cconf):Prop := exists L R,Reach0 tm c(mn_anchor L R).
Lemma mn_back:forall c d,Reach0 tm c d->mn_hit d->mn_hit c.
Proof. intros c d E(L&R&H). exists L,R;eapply reach0_trans;eauto. Qed.
Lemma mn_here:forall L R,mn_hit(mn_anchor L R).
Proof. intros;exists L,R;apply reach0_refl. Qed.
Lemma mn_clear:forall n L R,
 Reach0 tm(cR StB L(rep[S1]n++R))(cR StB(rep[S0]n++L)R).
Proof. apply sweepR. intros;go 1;r0. Qed.
Lemma mn_finish:forall L n R,
 mn_hit(cL StA(S0::L)(rep[S1]n++S0::S1::R)).
Proof.
 intros. eapply mn_back;[go 1;r0|].
 change(mn_hit(cR StB(S1::L)(rep[S1]n++S0::S1::R))).
 eapply mn_back;[apply mn_clear|].
 eapply mn_back;[go 1;r0|apply mn_here].
Qed.
(** Reading left in A, the only continuing blocks are 11 and 100.
    They become respectively 01 and 111 to the right of the new head.
    Thus the 01 marker survives, and induction on the finite left word
    ends at A0 or at C1 followed by 1. *)
Lemma mn_walk:forall L n R,
 mn_hit(cL StA L(rep[S1]n++S0::S1::R)).
Proof.
 fix IH 1. intros[|[]L]n R.
 - change(mn_hit(cL StA[S0](rep[S1]n++S0::S1::R))). apply mn_finish.
 - apply mn_finish.
 - destruct L as[|[]L].
   + eapply mn_back;[go 3;r0|].
     change(mn_hit(cL StA[S0](rep[S1](S(S(S n)))++S0::S1::R))). apply mn_finish.
   + destruct L as[|[]L].
     * eapply mn_back;[go 3;r0|].
       change(mn_hit(cL StA[S0](rep[S1](S(S(S n)))++S0::S1::R))). apply mn_finish.
     * eapply mn_back;[go 3;r0|].
       change(mn_hit(cL StA L(rep[S1](S(S(S n)))++S0::S1::R))). apply IH.
     * eapply mn_back;[go 3;r0|apply mn_here].
   + eapply mn_back;[go 2;r0|].
     change(mn_hit(cL StA L(rep[S1]0++S0::S1::(rep[S1]n++S0::S1::R)))). apply IH.
Qed.
(** A following 1 returns immediately. A following 0 gives the four
    steps C1,C0,A1,D1 and recreates the right marker 011. *)
Theorem mn_return:forall L R,exists L' R',
 Reach1 tm(mn_anchor L R)(mn_anchor L' R').
Proof.
 intros L[|[]R].
 - assert(H:mn_hit(cL StA L[S0;S1;S1]))by apply(mn_walk L 0 [S1]).
   destruct H as(U&V&H). exists U,V. unfold mn_anchor. go 4. exact H.
 - assert(H:mn_hit(cL StA L(S0::S1::S1::R)))by apply(mn_walk L 0(S1::R)).
   destruct H as(U&V&H). exists U,V. unfold mn_anchor. go 4. exact H.
 - exists(S1::L),R. unfold mn_anchor. go 1;r0.
Qed.
(** The finite right run of ones ends at a zero. C0 then A1 reaches D1;
    the protected left neighbor covers the case of an empty run. *)
Theorem mn_D1:forall R L,Fires tm(mn_anchor L R)(StD,S1).
Proof.
 induction R as[|[]R IH];intro L.
 - eapply fire_back;[unfold mn_anchor;go 3;r0|apply fires_here;reflexivity].
 - eapply fire_back;[unfold mn_anchor;go 3;r0|apply fires_here;reflexivity].
 - eapply fire_back;[unfold mn_anchor;go 1;r0|apply IH].
Qed.
End Core.
