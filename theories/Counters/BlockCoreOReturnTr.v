(** * Counters.BlockCoreOReturnTr: an odd-count word transducer

    Canonical table: [1RB0RC_0LC1LB_0LD1LC_1RD0RA].  The anchor is A0,
    left [01], with a finite right word starting and ending in 1 and
    containing no adjacent zeros.  Its number of ones is odd.

    The right pass uses a partial transducer:
      F(1)=011, F(10x)=101x,
      F(111x)=11 F(1x), F(1101x)=011 F(1x).
    Odd nonblank count ensures that its undefined terminal case [11]
    cannot occur.  Each pass increases the number of ones by one; the
    complete lap prefixes another three ones, preserving oddness.

    The transducer is a relation so its domain and preservation proofs
    need no artificial default output.  A structural length induction
    proves existence, and induction on its derivation proves the exact
    concrete-tape return.  All eight instructions already fire in the
    initial 20 steps of every lap.  The only inherited axiom is
    functional_extensionality_dep, used for finite tape lifting. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
Fixpoint bo_ones(w:list Sym):nat:=match w with
|[]=>0|S0::w=>bo_ones w|S1::w=>S(bo_ones w) end.
Inductive bo_word:list Sym->Prop:=
| bo_nil:bo_word []
| bo_one:forall w,bo_word w->bo_word(S1::w)
| bo_pair:forall w,bo_word w->bo_word(S0::S1::w).
Inductive bo_map:list Sym->list Sym->Prop:=
| bo_map_last:bo_map[S1][S0;S1;S1]
| bo_map_stop:forall x,bo_map(S1::S0::S1::x)(S1::S0::S1::S1::x)
| bo_map_one:forall x y,bo_map(S1::x)y->bo_map(S1::S1::S1::x)(S1::S1::y)
| bo_map_pair:forall x y,bo_map(S1::x)y->bo_map(S1::S1::S0::S1::x)(S0::S1::S1::y).
Lemma bo_word_tail1:forall w,bo_word(S1::w)->bo_word w.
Proof. intros w H;inversion H;assumption. Qed.
Lemma bo_word_tail0:forall w,bo_word(S0::w)->exists x,w=S1::x/\bo_word x.
Proof. intros w H;inversion H;subst;eauto. Qed.
Lemma bo_map_exists:forall x,bo_word x->Nat.Even(bo_ones x)->exists y,bo_map(S1::x)y.
Proof.
 refine(well_founded_induction_type(well_founded_ltof (list Sym) (@length Sym))
  (fun x=>bo_word x->Nat.Even(bo_ones x)->exists y,bo_map(S1::x)y) _).
 intros x IH HW HE;destruct x as[|[]x].
 - exists[S0;S1;S1];constructor.
 - destruct(bo_word_tail0 x HW)as(u&E&HU);subst.
   eexists;apply bo_map_stop.
 - apply bo_word_tail1 in HW. destruct x as[|[]x].
   + destruct HE as[k Hk];cbn[bo_ones]in Hk;lia.
   + destruct(bo_word_tail0 x HW)as(u&E&HU);subst.
     assert(HUe:Nat.Even(bo_ones u)). { destruct HE as[k Hk];cbn[bo_ones]in Hk.
       destruct k;[lia|exists k;lia]. }
     destruct(IH u ltac:(unfold ltof;cbn;lia) HU HUe)as(y&HY). eexists;apply bo_map_pair;exact HY.
   + apply bo_word_tail1 in HW.
     assert(HXe:Nat.Even(bo_ones x)). { destruct HE as[k Hk];cbn[bo_ones]in Hk.
       destruct k;[lia|exists k;lia]. }
     destruct(IH x ltac:(unfold ltof;cbn;lia) HW HXe)as(y&HY). eexists;apply bo_map_one;exact HY.
Qed.
Lemma bo_map_word:forall x y,bo_map x y->bo_word x->bo_word y.
Proof.
 intros x y H;induction H;intro HW.
 - apply bo_pair,bo_one,bo_nil.
 - repeat apply bo_word_tail1 in HW.
   destruct(bo_word_tail0 _ HW)as(u&E&HU);injection E as <-.
   apply bo_one,bo_pair,bo_one;exact HU.
 - apply bo_one,bo_one,IHbo_map.
   apply bo_word_tail1,bo_word_tail1 in HW;exact HW.
 - apply bo_pair,bo_one,IHbo_map.
   apply bo_word_tail1,bo_word_tail1 in HW.
   destruct(bo_word_tail0 _ HW)as(u&E&HU);injection E as <-;apply bo_one;exact HU.
Qed.
Lemma bo_map_ones:forall x y,bo_map x y->bo_ones y=S(bo_ones x).
Proof. intros x y H;induction H;cbn[bo_ones]in *;lia. Qed.
Definition bo_anchor(w:list Sym):cconf:=(StA,([S0;S1],S0,w)).
Inductive bo_mark:cconf->Prop:=
| bo_mark_anchor:forall x,bo_word x->Nat.Even(bo_ones x)->bo_mark(bo_anchor(S1::x)).
Section Machine.
Variable tm:TM.
Hypotheses
 (HA0:tm StA S0=Some(mkTrans S1 DR StB))
 (HA1:tm StA S1=Some(mkTrans S0 DR StC))
 (HB0:tm StB S0=Some(mkTrans S0 DL StC))
 (HB1:tm StB S1=Some(mkTrans S1 DL StB))
 (HC0:tm StC S0=Some(mkTrans S0 DL StD))
 (HC1:tm StC S1=Some(mkTrans S1 DL StC))
 (HD0:tm StD S0=Some(mkTrans S1 DR StD))
 (HD1:tm StD S1=Some(mkTrans S0 DR StA)).
Local Ltac run:=
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR rep bo_anchor];
 repeat(first[rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR rep bo_anchor]);reflexivity.
Local Ltac go n:=first[eapply(r1_run _ n);[lia|run|]|eapply(r0_run _ n);[run|]].
Lemma bo_C_11:forall L R,Reach0 tm(cL StC(S1::S1::L)R)(cL StC L(S1::S1::R)).
Proof. intros;go 2;r0. Qed.
Lemma bo_C_101:forall L R,Reach0 tm(cL StC(S1::S0::S1::L)R)(cL StC L(S0::S1::S1::R)).
Proof. intros;go 7;r0. Qed.
Lemma bo_D_map:forall x y,bo_map x y->forall L,
 Reach0 tm(cR StD(S1::L)x)(cL StC L y).
Proof.
 intros x y H;induction H;intro L.
 - eapply reach0_lift_r.
   + unfold cL. symmetry. apply(lift_padR 1 StC(ctl L)(chd L)[S0;S1;S1]).
   + go 10;r0.
 - go 6;r0.
 - go 6. rt IHbo_map. apply bo_C_11.
 - go 5. rt IHbo_map. apply bo_C_101.
Qed.
Lemma bo_start:forall x,Reach1 tm(bo_anchor(S1::x))
 (cR StD [S1;S1;S1;S1;S0;S1;S1](S1::x)).
Proof. intros;go 29;r0. Qed.
Lemma bo_finish:forall y,Reach0 tm(cL StC[S1;S1;S1;S0;S1;S1]y)
 (bo_anchor(S1::S1::S1::y)).
Proof. intros;go 5;r0. Qed.
Theorem bo_return:forall c,bo_mark c->exists d,bo_mark d/\Reach1 tm c d.
Proof.
 intros c HM;inversion HM;subst.
 destruct(bo_map_exists x H H0)as(y&HY).
 exists(bo_anchor(S1::S1::S1::y));split.
 - apply bo_mark_anchor.
   + apply bo_one,bo_one. eapply bo_map_word;[exact HY|apply bo_one;exact H].
   + pose proof(bo_map_ones _ _ HY)as HO;cbn[bo_ones]in HO|-*.
     destruct H0 as[k HK]. exists(S(S k));lia.
 - go 29. rt(bo_D_map _ _ HY). apply bo_finish.
Qed.
Theorem bo_mark_fires:forall c,bo_mark c->forall i,Fires tm c i.
Proof.
 intros c HM[q h];inversion HM;subst;destruct q,h.
 - apply fires_here;reflexivity.
 - eapply fire_back;[go 19;r0|apply fires_here;reflexivity].
 - eapply fire_back;[go 3;r0|apply fires_here;reflexivity].
 - eapply fire_back;[go 1;r0|apply fires_here;reflexivity].
 - eapply fire_back;[go 5;r0|apply fires_here;reflexivity].
 - eapply fire_back;[go 4;r0|apply fires_here;reflexivity].
 - eapply fire_back;[go 6;r0|apply fires_here;reflexivity].
 - eapply fire_back;[go 8;r0|apply fires_here;reflexivity].
Qed.
Lemma bo_boot_raw:csteps tm 12(StA,([],S0,[]))=Some(StA,([S0;S1],S0,[S1;S0])).
Proof. run. Qed.
Lemma bo_boot:stepn tm 12 InitES=Some(lift(bo_anchor[S1])).
Proof.
 rewrite <-CTape.lift_c0. unfold CTape.c0. rewrite(csteps_lift tm 12 _ _ bo_boot_raw).
 f_equal. unfold bo_anchor;apply(lift_padR 1 StA [S0;S1] S0 [S1]).
Qed.
End Machine.
Lemma bo_mark_instr:forall c,bo_mark c->cinstr c=(StA,S0).
Proof. intros c H;inversion H;reflexivity. Qed.
