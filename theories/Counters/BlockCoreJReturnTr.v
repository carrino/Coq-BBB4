(** * Counters.BlockCoreJReturnTr: paired sweeps with a terminal 1101 guard

    Canonical table: [1LB0LA_1RC0LB_1LA0RD_1RC0RC].  The marked
    family is A1 with arbitrary finite left word and right word ending
    in 1101.  A positive marked return makes A1 recurrent.  Every mark
    also reaches B1 and D0, the other two missing instructions.

    D consumes pairs 01 and 11.  D00 turns to A with right prefix 01;
    A either reaches marked A1 or drains that prefix back to D on the
    shorter right suffix.  D10 turns to B with right prefix 11.  B
    either reaches marked A1 or returns to D on 1 followed by the
    shorter suffix.  Simultaneous induction on D(U++1101) and
    D(1::U++1101) closes both cases.  The terminal passes manufacture
    the same guard, even when they read the implicit blank tail.

    The B1 witness follows the same induction.  The D0 witness needs
    only a finite left word and is proved by mutual A1/B1 induction.
    The only axiom is functional_extensionality_dep, inherited from
    concrete tape lifting. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
Definition bj_guard:list Sym:=[S1;S1;S0;S1].
Definition bj_suffix(R:list Sym):Prop:=exists U,R=U++bj_guard.
Lemma bj_suffix_prefix:forall U R,bj_suffix R->bj_suffix(U++R).
Proof. intros U R(V&E);subst;exists(U++V);apply app_assoc. Qed.
Lemma bj_suffix_guard:bj_suffix bj_guard.
Proof. exists[];reflexivity. Qed.
Inductive bj_mark:cconf->Prop:=
| bj_anchor:forall L R,bj_suffix R->bj_mark(StA,(L,S1,R)).
Section Machine.
Variable tm:TM.
Hypotheses
 (HA0:tm StA S0=Some(mkTrans S1 DL StB))
 (HA1:tm StA S1=Some(mkTrans S0 DL StA))
 (HB0:tm StB S0=Some(mkTrans S1 DR StC))
 (HB1:tm StB S1=Some(mkTrans S0 DL StB))
 (HC0:tm StC S0=Some(mkTrans S1 DL StA))
 (HC1:tm StC S1=Some(mkTrans S0 DR StD))
 (HD0:tm StD S0=Some(mkTrans S1 DR StC))
 (HD1:tm StD S1=Some(mkTrans S0 DR StC)).
Local Ltac run:=
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR rep bj_guard];
 repeat(first[rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR rep bj_guard]);reflexivity.
Local Ltac go n:=first[eapply(r1_run _ n);[lia|run|]|eapply(r0_run _ n);[run|]].
Definition bj_hit(c:cconf):Prop:=exists d,bj_mark d/\Reach0 tm c d.
Lemma bj_back:forall c d,Reach0 tm c d->bj_hit d->bj_hit c.
Proof. intros c d H(e&He&Hr);exists e;split;[exact He|eapply reach0_trans;eauto]. Qed.
Lemma bj_here:forall c,bj_mark c->bj_hit c.
Proof. intros;exists c;split;[assumption|r0]. Qed.
Lemma bj_B_one:forall L R,bj_suffix R->bj_hit(StB,(L,S1,R)).
Proof.
 fix IH 1. intros L R HS. destruct L as[|[]L].
 - eapply bj_back;[go 3;r0|]. apply bj_here,bj_anchor.
   change(bj_suffix([S1]++R));apply bj_suffix_prefix;exact HS.
 - eapply bj_back;[go 3;r0|]. apply bj_here,bj_anchor.
   change(bj_suffix([S1]++R));apply bj_suffix_prefix;exact HS.
 - eapply bj_back;[go 1;r0|]. apply IH.
   change(bj_suffix([S0]++R));apply bj_suffix_prefix;exact HS.
Qed.
Lemma bj_A_drain:forall L R,bj_suffix R->
 (forall L',bj_hit(cR StD L' R))->
 bj_hit(cL StA L(S0::S1::R)).
Proof.
 intros L R HS HD. destruct L as[|[]L].
 - eapply bj_back;[go 5;r0|]. apply HD.
 - destruct L as[|[]L].
   + eapply bj_back;[go 5;r0|]. apply HD.
   + eapply bj_back;[go 5;r0|]. apply HD.
   + eapply bj_back;[go 1;r0|]. apply bj_B_one.
     change(bj_suffix([S1;S0;S1]++R));apply bj_suffix_prefix;exact HS.
 - apply bj_here,bj_anchor.
   change(bj_suffix([S0;S1]++R));apply bj_suffix_prefix;exact HS.
Qed.
Lemma bj_B_drain:forall L R,bj_suffix R->
 (forall L',bj_hit(cR StD L'(S1::R)))->
 bj_hit(cL StB L(S1::S1::R)).
Proof.
 intros L R HS HD. destruct L as[|[]L].
 - eapply bj_back;[go 2;r0|]. apply HD.
 - eapply bj_back;[go 2;r0|]. apply HD.
 - apply bj_B_one.
   change(bj_suffix([S1;S1]++R));apply bj_suffix_prefix;exact HS.
Qed.
Lemma bj_D_guard:forall L,bj_hit(cR StD L bj_guard).
Proof. intros. eapply bj_back;[go 11;r0|]. apply bj_here,bj_anchor,bj_suffix_guard. Qed.
Lemma bj_D_zero_guard:forall L,bj_hit(cR StD L(S0::bj_guard)).
Proof. intros. eapply bj_back;[go 24;r0|]. apply bj_here,bj_anchor,bj_suffix_guard. Qed.
Lemma bj_D_one_guard:forall L,bj_hit(cR StD L(S1::bj_guard)).
Proof. intros. eapply bj_back;[go 24;r0|]. apply bj_here,bj_anchor,bj_suffix_guard. Qed.
Lemma bj_D_finite:forall U,
 (forall L,bj_hit(cR StD L(U++bj_guard)))/\
 (forall L,bj_hit(cR StD L(S1::U++bj_guard))).
Proof.
 fix IH 1. intros U;destruct U as[|[]U];split;intro L;cbn[app].
 - apply bj_D_guard.
 - apply bj_D_one_guard.
 - destruct U as[|[]U];cbn[app].
   + apply bj_D_zero_guard.
   + eapply bj_back;[go 3;r0|]. apply bj_A_drain.
     * exists U;reflexivity.
     * apply(IH U).
   + eapply bj_back;[go 2;r0|]. apply(IH U).
 - eapply bj_back;[go 3;r0|]. apply bj_B_drain.
   + exists U;reflexivity.
   + apply(IH U).
 - apply(IH U).
 - eapply bj_back;[go 2;r0|]. apply(IH U).
Qed.
Lemma bj_D_suffix:forall L R,bj_suffix R->bj_hit(cR StD L R).
Proof. intros L R(U&E);subst;apply(bj_D_finite U). Qed.
Lemma bj_A_suffix:forall L R,bj_suffix R->bj_hit(cL StA L R).
Proof.
 intros L R HS. destruct L as[|[]L].
 - eapply bj_back;[go 3;r0|]. apply bj_D_suffix;exact HS.
 - destruct L as[|[]L].
   + eapply bj_back;[go 3;r0|]. apply bj_D_suffix;exact HS.
   + eapply bj_back;[go 3;r0|]. apply bj_D_suffix;exact HS.
   + eapply bj_back;[go 1;r0|]. apply bj_B_one.
     change(bj_suffix([S1]++R));apply bj_suffix_prefix;exact HS.
 - apply bj_here,bj_anchor;exact HS.
Qed.
Theorem bj_return:forall c,bj_mark c->exists d,bj_mark d/\Reach1 tm c d.
Proof.
 intros c H;inversion H;subst.
 assert(HS:bj_suffix(S0::R)). { change(bj_suffix([S0]++R));apply bj_suffix_prefix;assumption. }
 destruct(bj_A_suffix L(S0::R)HS)as(d&HM&HR).
 exists d;split;[exact HM|go 1;exact HR].
Qed.

Lemma bj_A_one_zero_B:forall L R,Fires tm(StA,(L,S1,S0::R))(StB,S1).
Proof.
 fix IH 1. intros L R;destruct L as[|[]L].
 - eapply fire_back;[go 8;r0|]. apply fires_here;reflexivity.
 - destruct L as[|[]L].
   + eapply fire_back;[go 8;r0|]. apply fires_here;reflexivity.
   + eapply fire_back;[go 8;r0|]. apply fires_here;reflexivity.
   + eapply fire_back;[go 2;r0|]. apply fires_here;reflexivity.
 - eapply fire_back;[go 1;r0|]. apply IH.
Qed.
Lemma bj_fire_A_drain:forall L R,
 (forall L',Fires tm(cR StD L' R)(StB,S1))->
 Fires tm(cL StA L(S0::S1::R))(StB,S1).
Proof.
 intros L R HD. destruct L as[|[]L].
 - eapply fire_back;[go 5;r0|]. apply HD.
 - destruct L as[|[]L].
   + eapply fire_back;[go 5;r0|]. apply HD.
   + eapply fire_back;[go 5;r0|]. apply HD.
   + eapply fire_back;[go 1;r0|]. apply fires_here;reflexivity.
 - apply bj_A_one_zero_B.
Qed.
Lemma bj_fire_B_drain:forall L R,
 (forall L',Fires tm(cR StD L'(S1::R))(StB,S1))->
 Fires tm(cL StB L(S1::S1::R))(StB,S1).
Proof.
 intros L R HD. destruct L as[|[]L].
 - eapply fire_back;[go 2;r0|]. apply HD.
 - eapply fire_back;[go 2;r0|]. apply HD.
 - apply fires_here;reflexivity.
Qed.
Lemma bj_fire_D_finite:forall U,
 (forall L,Fires tm(cR StD L(U++bj_guard))(StB,S1))/\
 (forall L,Fires tm(cR StD L(S1::U++bj_guard))(StB,S1)).
Proof.
 fix IH 1. intros U;destruct U as[|[]U];split;intro L;cbn[app].
 - eapply fire_back;[go 8;r0|]. apply fires_here;reflexivity.
 - eapply fire_back;[go 21;r0|]. apply fires_here;reflexivity.
 - destruct U as[|[]U];cbn[app].
   + eapply fire_back;[go 21;r0|]. apply fires_here;reflexivity.
   + eapply fire_back;[go 3;r0|]. apply bj_fire_A_drain. apply(IH U).
   + eapply fire_back;[go 2;r0|]. apply(IH U).
 - eapply fire_back;[go 3;r0|]. apply bj_fire_B_drain. apply(IH U).
 - apply(IH U).
 - eapply fire_back;[go 2;r0|]. apply(IH U).
Qed.
Lemma bj_fire_D_suffix:forall L R,bj_suffix R->Fires tm(cR StD L R)(StB,S1).
Proof. intros L R(U&E);subst;apply(bj_fire_D_finite U). Qed.
Theorem bj_mark_B:forall c,bj_mark c->Fires tm c(StB,S1).
Proof.
 intros c H;inversion H;subst.
 assert(HS:bj_suffix(S0::R)). { change(bj_suffix([S0]++R));apply bj_suffix_prefix;assumption. }
 destruct L as[|[]L].
 - eapply fire_back;[go 4;r0|]. change(Fires tm(cR StD [S0;S1] (S0::R))(StB,S1));apply bj_fire_D_suffix;exact HS.
 - destruct L as[|[]L].
   + eapply fire_back;[go 4;r0|]. change(Fires tm(cR StD [S0;S1] (S0::R))(StB,S1));apply bj_fire_D_suffix;exact HS.
   + eapply fire_back;[go 4;r0|]. change(Fires tm(cR StD (S0::S1::L) (S0::R))(StB,S1));apply bj_fire_D_suffix;exact HS.
   + eapply fire_back;[go 2;r0|]. apply fires_here;reflexivity.
 - eapply fire_back;[go 1;r0|]. apply bj_A_one_zero_B.
Qed.
Lemma bj_AB_one_D:forall L,
 (forall R,Fires tm(StA,(L,S1,R))(StD,S0))/\
 (forall R,Fires tm(StB,(L,S1,R))(StD,S0)).
Proof.
 fix IH 1. intros L;destruct L as[|[]L];split;intro R.
 - eapply fire_back;[go 4;r0|]. apply fires_here;reflexivity.
 - eapply fire_back;[go 7;r0|]. apply fires_here;reflexivity.
 - destruct L as[|[]L].
   + eapply fire_back;[go 4;r0|]. apply fires_here;reflexivity.
   + eapply fire_back;[go 4;r0|]. apply fires_here;reflexivity.
   + eapply fire_back;[go 2;r0|]. apply(IH L).
 - eapply fire_back;[go 3;r0|]. apply(IH L).
 - eapply fire_back;[go 1;r0|]. apply(IH L).
 - eapply fire_back;[go 1;r0|]. apply(IH L).
Qed.
Theorem bj_mark_D:forall c,bj_mark c->Fires tm c(StD,S0).
Proof. intros c H;inversion H;subst;apply(bj_AB_one_D L). Qed.
Lemma bj_boot_A:csteps tm 10(StA,([],S0,[]))=Some(StA,([],S1,bj_guard)).
Proof. run. Qed.
Lemma bj_boot_B:csteps tm 15(StB,([],S0,[]))=Some(StA,([S1],S1,bj_guard)).
Proof. run. Qed.
Lemma bj_boot_D:csteps tm 15(StD,([],S0,[]))=Some(StA,([S1],S1,bj_guard)).
Proof. run. Qed.
End Machine.
Lemma bj_mark_instr:forall c,bj_mark c->cinstr c=(StA,S1).
Proof. intros c H;inversion H;reflexivity. Qed.
