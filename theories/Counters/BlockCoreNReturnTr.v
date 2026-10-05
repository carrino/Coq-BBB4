(** * Counters.BlockCoreNReturnTr: two implementations of one word map

    The tables are [1RB0RD_1LC1LB_1RA0LB_0RB1RA] and the variant with
    D0=[1LC].  Their anchor is A0 with left word [101].  The right
    word starts in 1 and satisfies both the regular phase invariant
    and [(1|01)*].  A lap sends w to [101]++F(w).

    The transducer pass has the interface A(1::L,w) -> B(L,F(w)),
    where the latter head reads the first cell of L.  Its recursive
    clauses are checked by concrete runs followed by two short left
    drains.  D0 changes the duration of one clause, but both variants
    have the same endpoint.  Every instruction fires during the
    uniform entrance.  The only inherited axiom is dependent
    functional extensionality, used for finite tape lifting. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import BlockCoreNWordTr.
Import ListNotations.
Definition bn_anchor(w:list Sym):cconf:=(StA,([S1;S0;S1],S0,w)).
Inductive bn_mark:cconf->Prop:=
| bn_mark_anchor:forall x,bn_good(S1::x)->bn_word(S1::x)->bn_mark(bn_anchor(S1::x)).
Section Machine.
Variable tm:TM.
Hypotheses
 (HA0:tm StA S0=Some(mkTrans S1 DR StB))
 (HA1:tm StA S1=Some(mkTrans S0 DR StD))
 (HB0:tm StB S0=Some(mkTrans S1 DL StC))
 (HB1:tm StB S1=Some(mkTrans S1 DL StB))
 (HC0:tm StC S0=Some(mkTrans S1 DR StA))
 (HC1:tm StC S1=Some(mkTrans S0 DL StB))
 (HD0:tm StD S0=Some(mkTrans S0 DR StB)\/
       tm StD S0=Some(mkTrans S1 DL StC))
 (HD1:tm StD S1=Some(mkTrans S1 DR StA)).
Local Ltac run:=
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR rep bn_anchor bn_Q];
 repeat(first[rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD1];
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR rep bn_anchor bn_Q]);reflexivity.
Local Ltac runD H:=
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR rep bn_anchor bn_Q];
 repeat(first[rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite H|rewrite HD1];
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR rep bn_anchor bn_Q]);reflexivity.
Local Ltac go n:=first[eapply(r1_run _ n);[lia|run|]|eapply(r0_run _ n);[run|]].
Local Ltac goD n H:=first[eapply(r1_run _ n);[lia|runD H|]|eapply(r0_run _ n);[runD H|]].
Lemma bn_B_01:forall L R,Reach0 tm(cL StB(S0::S1::L)R)(cL StB L(S0::S1::R)).
Proof. intros;go 2;r0. Qed.
Lemma bn_B_011:forall L R,Reach0 tm(cL StB(S0::S1::S1::L)R)(cL StB L(S1::S0::S1::R)).
Proof. intros;go 3;r0. Qed.
Lemma bn_A_Q:forall L R,Reach0 tm(cR StA L(S1::S0::S1::R))(cR StA(S1::S0::S1::L)R).
Proof. intros;destruct HD0 as[HD|HD];[goD 7 HD;r0|goD 5 HD;r0]. Qed.
Lemma bn_A_map:forall x y,bn_map x y->bn_word x->forall L,
 Reach0 tm(cR StA(S1::L)x)(cL StB L y).
Proof.
 intros x y HM;induction HM;intros HW L.
 - go 4;r0.
 - destruct(bn_word_tail0 _ HW)as(u&->&HU). go 4;r0.
 - apply bn_word_tail1,bn_word_tail1 in HW.
   go 2. rt(IHHM HW). apply bn_B_01.
 - apply bn_word_tail1 in HW.
   destruct(bn_word_tail0 _ HW)as(u&E&HU);injection E as <-.
   rt bn_A_Q. rt(IHHM HU). apply bn_B_011.
Qed.
Lemma bn_start:forall x,Reach1 tm(bn_anchor(S1::x))
 (cR StA[S1;S0;S1;S0;S1;S1](S1::x)).
Proof. intros;destruct HD0 as[HD|HD];[goD 17 HD;r0|goD 15 HD;r0]. Qed.
Lemma bn_finish:forall y,Reach0 tm(cL StB[S0;S1;S0;S1;S1]y)(bn_anchor(bn_Q++y)).
Proof. intros;go 9;r0. Qed.
Theorem bn_return:forall c,bn_mark c->exists d,bn_mark d/\Reach1 tm c d.
Proof.
 intros c HM;inversion HM;subst.
 destruct(bn_good_map _ H)as(y&HY&HG).
 exists(bn_anchor(bn_Q++y));split.
 - apply bn_mark_anchor.
   + apply bn_good_Q;exact HG.
   + apply bn_word_q. eapply bn_map_word;eauto.
 - eapply reach10;[apply bn_start|]. rt(bn_A_map _ _ HY H0). apply bn_finish.
Qed.
Theorem bn_mark_fires:forall c,bn_mark c->forall i,Fires tm c i.
Proof.
 intros c HM[q h];inversion HM;subst;destruct q,h.
 - apply fires_here;reflexivity.
 - eapply fire_back;[go 8;r0|apply fires_here;reflexivity].
 - eapply fire_back;[go 4;r0|apply fires_here;reflexivity].
 - eapply fire_back;[go 1;r0|apply fires_here;reflexivity].
 - eapply fire_back;[go 7;r0|apply fires_here;reflexivity].
 - eapply fire_back;[go 5;r0|apply fires_here;reflexivity].
 - eapply fire_back;[go 9;r0|apply fires_here;reflexivity].
 - destruct HD0 as[HD|HD].
   + eapply fire_back;[goD 14 HD;r0|apply fires_here;reflexivity].
   + eapply fire_back;[goD 12 HD;r0|apply fires_here;reflexivity].
Qed.
Lemma bn_boot:exists n,stepn tm n InitES=Some(lift(bn_anchor(bn_A0 0))).
Proof.
 destruct HD0 as[HD|HD].
 - exists 23;apply boot_ok;unfold bn_A0,CTape.c0;runD HD.
 - exists 21;apply boot_ok;unfold bn_A0,CTape.c0;runD HD.
Qed.
End Machine.
Lemma bn_mark_instr:forall c,bn_mark c->cinstr c=(StA,S0).
Proof. intros c H;inversion H;reflexivity. Qed.
Lemma bn_seed_mark:bn_mark(bn_anchor(bn_A0 0)).
Proof.
 apply bn_mark_anchor.
 - apply bn_good_A0.
 - apply bn_one,bn_one,bn_pair,bn_nil.
Qed.
