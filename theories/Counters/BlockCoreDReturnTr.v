(** * Counters.BlockCoreDReturnTr: a terminal guard for block-list core D

    Canonical table: [0LB0LA_0RC1LA_1LB1RD_1RC0RD].  A marked
    configuration is A1 with an arbitrary finite left word and a right
    word ending in 1011.  [bd_return] proves a positive marked return.

    D consumes right 1 and 01.  A right 00 turns to A with a newly
    manufactured right prefix 11.  A strips left pairs 01, placing 10
    on the right; it either encounters a 1 immediately, or turns back to
    D on left 00 (including implicit blanks).  D consumes all of the
    manufactured prefix (10)^k11 and resumes at the old right suffix.
    Thus induction on the finite prefix before 1011 closes every D pass.
    At the boundary, D on 1011 or 01011 returns directly to marked A1.

    The only axiom is functional_extensionality_dep, inherited from
    concrete tape lifting. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
Definition bd_guard:list Sym:=[S1;S0;S1;S1].
Definition bd_suffix(R:list Sym):Prop:=exists U,R=U++bd_guard.
Lemma bd_suffix_prefix:forall U R,bd_suffix R->bd_suffix(U++R).
Proof. intros U R(V&E);subst;exists(U++V);apply app_assoc. Qed.
Lemma bd_suffix_guard:bd_suffix bd_guard.
Proof. exists[];reflexivity. Qed.
Inductive bd_mark:cconf->Prop:=
| bd_anchor:forall L R,bd_suffix R->bd_mark(StA,(L,S1,R)).
Section Machine.
Variable tm:TM.
Hypotheses
 (HA0:tm StA S0=Some(mkTrans S0 DL StB))
 (HA1:tm StA S1=Some(mkTrans S0 DL StA))
 (HB0:tm StB S0=Some(mkTrans S0 DR StC))
 (HB1:tm StB S1=Some(mkTrans S1 DL StA))
 (HC0:tm StC S0=Some(mkTrans S1 DL StB))
 (HC1:tm StC S1=Some(mkTrans S1 DR StD))
 (HD0:tm StD S0=Some(mkTrans S1 DR StC))
 (HD1:tm StD S1=Some(mkTrans S0 DR StD)).
Local Ltac run:=
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR rep bd_guard];
 repeat(first[rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR rep bd_guard]);reflexivity.
Local Ltac go n:=first[eapply(r1_run _ n);[lia|run|]|eapply(r0_run _ n);[run|]].
Definition bd_hit(c:cconf):Prop:=exists d,bd_mark d/\Reach0 tm c d.
Lemma bd_back:forall c d,Reach0 tm c d->bd_hit d->bd_hit c.
Proof. intros c d H(e&He&Hr);exists e;split;[exact He|eapply reach0_trans;eauto]. Qed.
Lemma bd_here:forall c,bd_mark c->bd_hit c.
Proof. intros;exists c;split;[assumption|r0]. Qed.
Lemma bd_D_pairs:forall k L R,
 Reach0 tm(cR StD L(rep[S0;S1]k++R))(cR StD(rep[S1;S1]k++L)R).
Proof. apply sweepR. intros;go 2;r0. Qed.
Lemma bd_D_turnword:forall k L R,
 Reach0 tm(cR StD L(rep[S1;S0]k++S1::S1::R))
 (cR StD(S0::rep[S1;S1]k++S0::L)R).
Proof.
 intros. rewrite rep_rot. go 1.
 eapply reach0_trans;[apply bd_D_pairs|]. go 1;r0.
Qed.
Lemma bd_A_turn:forall L R,
 Reach0 tm(cL StA(S0::S0::L)R)(cR StD(S1::S0::L)R).
Proof. intros;go 5;r0. Qed.
Lemma bd_A_blank:forall R,
 Reach0 tm(cL StA[]R)(cR StD[S1;S0]R).
Proof. intros;go 5;r0. Qed.
Lemma bd_A_pair:forall L R,
 Reach0 tm(cL StA(S0::S1::L)R)(cL StA L(S1::S0::R)).
Proof. intros;go 2;r0. Qed.
(** A turn either visits marked A1 or drains its manufactured right
    prefix back to D.  The continuation quantifies over the new left word. *)
Lemma bd_A_drain:forall L k R,bd_suffix R->
 (forall L',bd_hit(cR StD L' R))->
 bd_hit(cL StA L(rep[S1;S0]k++S1::S1::R)).
Proof.
 fix IH 1. intros L k R HS HD. destruct L as[|[]L].
 - eapply bd_back;[apply bd_A_blank|].
   eapply bd_back;[apply bd_D_turnword|]. apply HD.
 - destruct L as[|[]L].
   + eapply bd_back;[apply bd_A_blank|].
     eapply bd_back;[apply bd_D_turnword|]. apply HD.
   + eapply bd_back;[apply bd_A_turn|].
     eapply bd_back;[apply bd_D_turnword|]. apply HD.
   + eapply bd_back;[apply bd_A_pair|].
     change(bd_hit(cL StA L(rep[S1;S0](S k)++S1::S1::R))).
     apply IH;assumption.
 - apply bd_here,bd_anchor. apply bd_suffix_prefix.
   change(bd_suffix([S1;S1]++R));apply bd_suffix_prefix;exact HS.
Qed.
Lemma bd_D_guard:forall L,bd_hit(cR StD L bd_guard).
Proof. intros. eapply bd_back;[go 9;r0|]. apply bd_here,bd_anchor,bd_suffix_guard. Qed.
Lemma bd_D_zero_guard:forall L,bd_hit(cR StD L(S0::bd_guard)).
Proof. intros. eapply bd_back;[go 10;r0|]. apply bd_here,bd_anchor,bd_suffix_guard. Qed.
(** Every continuing branch consumes at least one symbol of U.  The
    terminal guard cases may read implicit blanks beyond its final 1. *)
Lemma bd_D_finite:forall U L,bd_hit(cR StD L(U++bd_guard)).
Proof.
 fix IH 1. intros U L. destruct U as[|[]U];cbn[app].
 - apply bd_D_guard.
 - destruct U as[|[]U];cbn[app].
   + apply bd_D_zero_guard.
   + eapply bd_back;[go 3;r0|].
     change(bd_hit(cL StA L(rep[S1;S0]0++S1::S1::(U++bd_guard)))).
     apply bd_A_drain.
     * exists U;reflexivity.
     * intros;apply IH.
   + eapply bd_back;[go 2;r0|]. apply IH.
 - eapply bd_back;[go 1;r0|]. apply IH.
Qed.
Lemma bd_D_suffix:forall L R,bd_suffix R->bd_hit(cR StD L R).
Proof. intros L R(U&E);subst;apply bd_D_finite. Qed.
Lemma bd_A_suffix:forall L R,bd_suffix R->bd_hit(cL StA L R).
Proof.
 fix IH 1. intros L R HS. destruct L as[|[]L].
 - eapply bd_back;[apply bd_A_blank|]. apply bd_D_suffix;exact HS.
 - destruct L as[|[]L].
   + eapply bd_back;[apply bd_A_blank|]. apply bd_D_suffix;exact HS.
   + eapply bd_back;[apply bd_A_turn|]. apply bd_D_suffix;exact HS.
   + eapply bd_back;[apply bd_A_pair|]. apply IH.
     change(bd_suffix([S1;S0]++R));apply bd_suffix_prefix;exact HS.
 - apply bd_here,bd_anchor;exact HS.
Qed.
Theorem bd_return:forall c,bd_mark c->exists d,bd_mark d/\Reach1 tm c d.
Proof.
 intros c H;inversion H;subst.
 assert(HS:bd_suffix(S0::R)). { change(bd_suffix([S0]++R));apply bd_suffix_prefix;assumption. }
 destruct(bd_A_suffix L(S0::R)HS)as(d&HM&HR).
 exists d;split;[exact HM|go 1;exact HR].
Qed.
End Machine.
Lemma bd_mark_instr:forall c,bd_mark c->cinstr c=(StA,S1).
Proof. intros c H;inversion H;reflexivity. Qed.
