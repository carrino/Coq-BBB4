(** Seven transitions force B1 from every finite tape. Before B1, a
    right sweep and alternating left erasure implement carries on pairs
    01/11. A zero in the second position ends this finite carry process. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr FiniteInstrTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
Section Core.
Variable tm:TM.
Hypotheses
 (HA0:tm StA S0=Some(mkTrans S0 DR StB))
 (HA1:tm StA S1=Some(mkTrans S0 DL StD))
 (HB0:tm StB S0=Some(mkTrans S0 DR StC))
 (HC0:tm StC S0=Some(mkTrans S1 DL StD))
 (HC1:tm StC S1=Some(mkTrans S1 DR StC))
 (HD0:tm StD S0=Some(mkTrans S0 DL StA))
 (HD1:tm StD S1=Some(mkTrans S1 DL StA)).
Local Ltac run :=
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR rep];
 repeat(first[rewrite HA0|rewrite HA1|rewrite HB0|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR rep]);reflexivity.
Local Ltac go n := first
 [eapply(r1_run _ n);[lia|run|]
 |eapply(r0_run _ n);[run|]].
Definition ac_anchor(L R:list Sym):cconf := (StA,(L,S0,S0::R)).
Definition ac_hit(c:cconf):Prop := Fires tm c (StB,S1).
Lemma ac_scan:forall n L R,
 Reach0 tm(cR StC L(rep [S1;S1] n++R))
          (cR StC(rep [S1;S1] n++L)R).
Proof. apply sweepR. intros;go 2;r0. Qed.
Lemma ac_drain:forall n L R,
 Reach0 tm(cL StD(rep [S1;S1] n++L)R)
          (cL StD L(rep [S0;S1] n++R)).
Proof. apply sweepL. intros;go 2;r0. Qed.
Lemma ac_drain_odd:forall n L R,
 Reach0 tm(cL StA(rep [S1;S1] n++L)R)
          (cL StA L(rep [S1;S0] n++R)).
Proof. apply sweepL. intros;go 2;r0. Qed.
Lemma ac_carry:forall k L R,
 Reach1 tm(ac_anchor L(rep [S1;S1] k++S0::R))
          (ac_anchor L(rep [S0;S1] k++S1::R)).
Proof.
 intros. unfold ac_anchor. go 2.
 change(StC,(S0::S0::L,chd(rep [S1;S1] k++S0::R),ctl(rep [S1;S1] k++S0::R)))
 with(cR StC(S0::S0::L)(rep [S1;S1] k++S0::R)).
 rt ac_scan. go 1.
 change(StD,(ctl(rep [S1;S1] k++S0::S0::L),chd(rep [S1;S1] k++S0::S0::L),S1::R))
 with(cL StD(rep [S1;S1] k++S0::S0::L)(S1::R)).
 rt ac_drain. go 1. r0.
Qed.
Lemma ac_fill:forall k L R,
 Reach0 tm(ac_anchor L(rep [S0;S1] k++R))
          (ac_anchor L(rep [S1;S1] k++R)).
Proof.
 intros k L R. apply(count_from_carry_lt tm(ac_anchor L)[S0;S1][S1;S1]k).
 intros j Y _. apply ac_carry.
Qed.
Lemma ac_odd:forall k L R,
 ac_hit(ac_anchor L(rep [S1;S1] k++S1::S0::R)).
Proof.
 intros. unfold ac_hit,ac_anchor. eapply fire_back.
 - go 2. change(StC,(S0::S0::L,chd(rep [S1;S1] k++S1::S0::R),ctl(rep [S1;S1] k++S1::S0::R)))
   with(cR StC(S0::S0::L)(rep [S1;S1] k++S1::S0::R)).
   rt ac_scan. go 3.
   change(StA,(ctl(rep [S1;S1] k++S0::S0::L),chd(rep [S1;S1] k++S0::S0::L),S1::S1::R))
   with(cL StA(rep [S1;S1] k++S0::S0::L)(S1::S1::R)).
   rt ac_drain_odd. r0.
 - destruct k;unfold cL;cbn[chd ctl rep app];(eapply fire_back;[go 1;r0|apply fires_here;reflexivity]).
Qed.
Lemma ac_eq:forall c d,lift c=lift d->ac_hit d->ac_hit c.
Proof. intros c d E H;exact(fire_lift tm c d (StB,S1) E H). Qed.
Lemma ac_pad:forall q L h R,
 lift(q,(L,h,R++[S0]))=lift(q,(L,h,R)).
Proof. intros;unfold lift,lift_tape;cbn;rewrite lift_side_app_blank;reflexivity. Qed.
Lemma ac_one_end:forall k L,ac_hit(ac_anchor L(rep [S1;S1] k++[S1])).
Proof.
 intros;eapply ac_eq with(d:=ac_anchor L(rep [S1;S1] k++[S1;S0]));[|apply ac_odd].
 symmetry. unfold ac_anchor.
 pose proof(ac_pad StA L S0 (S0::rep [S1;S1] k++[S1]))as E.
 cbn[app]in E. rewrite <-app_assoc in E. exact E.
Qed.
Lemma ac_empty_end:forall k L,ac_hit(ac_anchor L(rep [S1;S1] k++[])).
Proof.
 intros. eapply ac_eq with(d:=ac_anchor L(rep [S1;S1] k++[S0])).
 - symmetry. unfold ac_anchor. rewrite app_nil_r. change(lift(StA,(L,S0,(S0::rep [S1;S1] k)++[S0]))=lift(StA,(L,S0,S0::rep [S1;S1] k))). apply ac_pad.
 - eapply fire_back;[apply reach1_0,ac_carry|].
   eapply fire_back;[apply ac_fill|apply ac_one_end].
Qed.
Lemma ac_suffix:forall R k L,ac_hit(ac_anchor L(rep [S1;S1] k++R)).
Proof.
 fix IH 1. intros R k L. destruct R as[|[] R].
 - apply ac_empty_end.
 - eapply fire_back;[apply reach1_0,ac_carry|]. eapply fire_back;[apply ac_fill|].
   destruct R as[|[] R].
   + apply ac_one_end.
   + apply ac_odd.
   + change(ac_hit(ac_anchor L(rep [S1;S1] k++[S1;S1]++R))).
     rewrite app_assoc,<-rep_S_r. apply IH.
 - destruct R as[|[] R].
   + apply ac_one_end.
   + apply ac_odd.
   + change(ac_hit(ac_anchor L(rep [S1;S1] k++[S1;S1]++R))).
     rewrite app_assoc,<-rep_S_r. apply IH.
Qed.
Lemma ac_Azero:forall L R,ac_hit(StA,(L,S0,R)).
Proof.
 intros L[|[]R].
 - eapply ac_eq with(d:=ac_anchor L[]).
   + symmetry;exact(ac_pad StA L S0 []).
   + exact(ac_suffix [] 0 L).
 - exact(ac_suffix R 0 L).
 - unfold ac_hit;eapply fire_back;[go 1;r0|apply fires_here;reflexivity].
Qed.
Lemma ac_Afinite:forall L h R,ac_hit(StA,(L,h,R)).
Proof.
 fix IH 1. intros L h R. destruct h;[apply ac_Azero|].
 destruct L as[|a L];[eapply fire_back;[go 2;r0|apply ac_Azero]|].
 destruct a;destruct L as[|b L];eapply fire_back;[go 2;r0|apply ac_Azero|go 2;r0|apply IH|go 2;r0|apply ac_Azero|go 2;r0|apply IH].
Qed.
Lemma ac_Cfinite:forall R L,ac_hit(cR StC L R).
Proof.
 fix IH 1. intros[|[]R]L.
 - eapply fire_back;[go 1;r0|]. destruct L as[|[]L];eapply fire_back;[go 1;r0|apply ac_Afinite|go 1;r0|apply ac_Afinite|go 1;r0|apply ac_Afinite].
 - eapply fire_back;[go 1;r0|]. destruct L as[|[]L];eapply fire_back;[go 1;r0|apply ac_Afinite|go 1;r0|apply ac_Afinite|go 1;r0|apply ac_Afinite].
 - eapply fire_back;[go 1;r0|apply IH].
Qed.
Theorem ac_finite:finite_instr_hit tm(StB,S1).
Proof.
 assert(H:forall c,ac_hit c).
 { intros[q[[L h]R]]. destruct q.
   - apply ac_Afinite.
   - destruct h;[eapply fire_back;[go 1;r0|apply ac_Cfinite]|apply fires_here;reflexivity].
   - exact(ac_Cfinite(h::R)L).
   - destruct h;eapply fire_back;[go 1;r0|apply ac_Afinite|go 1;r0|apply ac_Afinite]. }
 intros c. destruct(H c)as(k&e&Hr&Hi). exists k,(lift e);split;[apply csteps_lift;exact Hr|].
 rewrite cinstr_lift;exact Hi.
Qed.
End Core.
