(** Returns of the wandering balanced pair. A protected 01 marker on
    the left is reached by nested induction on (zeros + right ones, zeros).
    The number of leading left ones does not enter this measure. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
Fixpoint wc_ones(R:list Sym):nat := match R with []=>0|S0::R=>wc_ones R|S1::R=>S(wc_ones R)end.
Lemma wc_ones_app:forall R T,wc_ones(R++T)=wc_ones R+wc_ones T.
Proof. induction R as[|[]R IH];intros;cbn;now rewrite ?IH. Qed.
Lemma wc_ones_zero:forall n,wc_ones(rep[S0]n)=0.
Proof. induction n;cbn;auto. Qed.
Section Core.
Variable tm:TM.
Hypotheses
 (HA0:tm StA S0=Some(mkTrans S0 DR StB))
 (HA1:tm StA S1=Some(mkTrans S0 DL StA))
 (HB0:tm StB S0=Some(mkTrans S1 DL StC))
 (HB1:tm StB S1=Some(mkTrans S1 DR StD))
 (HC0:tm StC S0=Some(mkTrans S1 DL StA))
 (HC1:tm StC S1=Some(mkTrans S0 DL StC))
 (HD0:tm StD S0=Some(mkTrans S1 DR StB))
 (HD1:tm StD S1=Some(mkTrans S0 DR StD)).
Local Ltac run :=
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR rep];
 repeat(first[rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR rep]);reflexivity.
Local Ltac go n := first
 [eapply(r1_run _ n);[lia|run|]
 |eapply(r0_run _ n);[run|]].
Definition wc_cfg n k L R := cR StD(rep[S1]k++rep[S0]n++S1::L)R.
Definition wc_hit c := Fires tm c(StA,S1).
Lemma wc_clear:forall k L R,
 Reach0 tm(cL StC(rep[S1]k++L)R)(cL StC L(rep[S0]k++R)).
Proof. apply sweepL. intros;go 1;r0. Qed.
Lemma wc_finish:forall k L R,wc_hit(wc_cfg 1 k L(S0::S0::R)).
Proof.
 intros;unfold wc_cfg,wc_hit;eapply fire_back.
 - go 3. change(StC,(ctl(rep[S1]k++rep[S0]1++S1::L),chd(rep[S1]k++rep[S0]1++S1::L),S0::S1::R))
   with(cL StC(rep[S1]k++rep[S0]1++S1::L)(S0::S1::R)).
   rt wc_clear. go 1;r0.
 - apply fires_here;reflexivity.
Qed.
Lemma wc_turn:forall n k L R,
 Reach0 tm(wc_cfg(S(S n))k L(S0::S0::R))
          (wc_cfg(S n)1 L(rep[S0]k++S0::S1::R)).
Proof.
 intros;unfold wc_cfg. go 3.
 change(StC,(ctl(rep[S1]k++rep[S0](S(S n))++S1::L),chd(rep[S1]k++rep[S0](S(S n))++S1::L),S0::S1::R))
 with(cL StC(rep[S1]k++rep[S0](S(S n))++S1::L)(S0::S1::R)).
 rt wc_clear. go 3;r0.
Qed.
Lemma wc_empty:forall n k L,wc_hit(wc_cfg n k L[S0;S0])->wc_hit(wc_cfg n k L[]).
Proof.
 intros. eapply fire_lift;[|exact H]. symmetry.
 unfold wc_cfg,cR;cbn[chd ctl]. exact(lift_padR 1 StD _ S0 []).
Qed.
Lemma wc_positive:forall M,
 (forall n k L R,0<n->n+wc_ones R<M->wc_hit(wc_cfg n k L R))->
 forall n k L R,0<n->n+wc_ones R<=M->wc_hit(wc_cfg n(S k)L R).
Proof.
 intros M Hlow n. induction n as[|n IH];intros k L R Hn HM;[lia|].
 assert(Z:forall k L R,S n+wc_ones R<=M->wc_hit(wc_cfg(S n)k L(S0::S0::R))).
 { intros k' L' R' HE. destruct n as[|n].
   - apply wc_finish.
   - eapply fire_back;[apply wc_turn|]. apply(IH 0);[lia|].
     rewrite wc_ones_app,wc_ones_zero;cbn[wc_ones];lia. }
 destruct R as[|[]R].
 - apply wc_empty,Z;exact HM.
 - destruct R as[|[]R].
   + change(wc_hit(wc_cfg(S n)(S k)L[])). apply wc_empty,Z;exact HM.
   + apply Z;exact HM.
   + eapply fire_back;[unfold wc_cfg;go 2;r0|].
     change(wc_hit(wc_cfg(S n)(S(S(S k)))L R)).
     apply Hlow;[lia|cbn[wc_ones]in HM;lia].
 - eapply fire_back;[unfold wc_cfg;go 1;r0|].
   change(wc_hit(wc_cfg 1 0(rep[S1]k++rep[S0](S n)++S1::L)R)).
   apply Hlow;[lia|cbn[wc_ones]in HM;lia].
Qed.
Lemma wc_zero:forall M,
 (forall n k L R,0<n->n+wc_ones R<=M->wc_hit(wc_cfg n(S k)L R))->
 forall R n L,0<n->n+wc_ones R<=M->wc_hit(wc_cfg n 0 L R).
Proof.
 intros M HP. fix IH 1. intros R n L Hn HM.
 assert(Z:forall n L R,0<n->n+wc_ones R<=M->wc_hit(wc_cfg n 0 L(S0::S0::R))).
 { intros[|[|n']]L' R' Hpos HE;[lia|apply wc_finish|].
   eapply fire_back;[apply wc_turn|]. apply(HP _ 0);[lia|].
   cbn[rep app wc_ones];lia. }
 destruct R as[|[]R].
 - apply wc_empty,Z;assumption.
 - destruct R as[|[]R].
   + change(wc_hit(wc_cfg n 0 L[])). apply wc_empty,Z;assumption.
   + apply Z;assumption.
   + eapply fire_back;[unfold wc_cfg;go 2;r0|].
     change(wc_hit(wc_cfg n 2 L R)). apply(HP _ 1);[exact Hn|cbn[wc_ones]in HM;lia].
 - eapply fire_back;[unfold wc_cfg;go 1;r0|].
   change(wc_hit(wc_cfg(S n)0 L R)). apply IH;[lia|cbn[wc_ones]in HM;lia].
Qed.
Theorem wc_marked:forall n k L R,0<n->wc_hit(wc_cfg n k L R).
Proof.
 assert(H:forall M n k L R,0<n->n+wc_ones R<=M->wc_hit(wc_cfg n k L R)).
 { intro M;induction M using lt_wf_ind.
   assert(HP:forall n k L R,0<n->n+wc_ones R<=M->wc_hit(wc_cfg n(S k)L R)).
   { apply wc_positive. intros n k L R Hn HM.
     apply(H(n+wc_ones R));[exact HM|exact Hn|lia]. }
   intros n[|k]L R Hn HM;[apply(wc_zero M HP R n L Hn HM)|apply HP;assumption]. }
 intros n k L R Hn;apply(H(n+wc_ones R));[exact Hn|lia].
Qed.
Lemma wc_Amarked:forall L R,wc_hit(StA,(L,S0,S0::R)).
Proof.
 intros. eapply fire_back;[go 3;r0|].
 destruct L as[|[]L];try(apply fires_here;reflexivity).
 - eapply fire_back;[go 3;r0|]. exact(wc_marked 1 0 [S0] R ltac:(lia)).
 - eapply fire_back;[go 3;r0|]. exact(wc_marked 1 0 (S0::L) R ltac:(lia)).
Qed.
Theorem wc_return:forall L R,exists k L' R',0<k /\
 csteps tm k(StA,(L,S1,R))=Some(StA,(L',S1,R')).
Proof.
 intros L R. assert(E:csteps tm 1(StA,(L,S1,R))=Some(cL StA L(S0::R)))by run.
 assert(H:wc_hit(cL StA L(S0::R))).
 { destruct L as[|[]L];try(apply fires_here;reflexivity);apply wc_Amarked. }
 destruct H as(k&[q[[U h]V]]&Hr&Hi).
 unfold cinstr in Hi;cbn in Hi;injection Hi as Hq Hh;subst q h.
 exists(1+k),U,V;split;[lia|]. rewrite csteps_add,E;exact Hr.
Qed.
Theorem wc_cross:forall L R,Fires tm(StA,(L,S1,R))(StD,S1).
Proof.
 fix IH 1. intros[|[]L]R.
 - eapply fire_back;[go 6;r0|apply fires_here;reflexivity].
 - eapply fire_back;[go 4;r0|]. destruct L as[|[]L].
   + eapply fire_back;[go 2;r0|apply fires_here;reflexivity].
   + eapply fire_back;[go 2;r0|apply fires_here;reflexivity].
   + apply IH.
 - eapply fire_back;[go 1;r0|apply IH].
Qed.
End Core.
