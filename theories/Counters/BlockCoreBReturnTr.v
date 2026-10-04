(** A finite right frontier builds positive one-runs separated by zeros.
    The return guard 100 drains those runs from the left. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr FiniteInstrTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
Fixpoint bb_word (xs:list nat)(U:list Sym):list Sym :=
 match xs with []=>U|n::xs=>rep[S1](S n)++S0::bb_word xs U end.
Lemma bb_ones_split:forall L,exists n U,L=rep[S1]n++U /\
 (U=[] \/ exists V,U=S0::V).
Proof.
 induction L as[|[]L IH].
 - exists 0,[];auto.
 - exists 0,(S0::L);split;[reflexivity|right;eauto].
 - destruct IH as(n&U&E&H). exists(S n),U;split;[cbn[rep app];now rewrite E|exact H].
Qed.
Lemma bb_len:forall n,length(rep[S1]n)=n.
Proof. induction n;cbn[rep app length];auto. Qed.
Section Core.
Variable tm:TM.
Hypotheses
 (HA1:tm StA S1=Some(mkTrans S0 DL StB))
 (HB0:tm StB S0=Some(mkTrans S1 DR StC))
 (HB1:tm StB S1=Some(mkTrans S1 DL StB))
 (HC0:tm StC S0=Some(mkTrans S1 DL StD))
 (HC1:tm StC S1=Some(mkTrans S0 DR StB))
 (HD0:tm StD S0=Some(mkTrans S1 DL StA))
 (HD1:tm StD S1=Some(mkTrans S0 DL StD)).
Local Ltac run :=
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR rep];
 repeat(first[rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR rep]);reflexivity.
Local Ltac go n := eapply(r0_run _ n);[run|].
Definition bb_hit c := Fires tm c (StA,S0).
Definition bb_front L R := cR StB(S0::L)R.
Lemma bb_here:forall L R,bb_hit(StA,(L,S0,R)).
Proof. intros;apply fires_here;reflexivity. Qed.
Lemma bb_back:forall c d,Reach0 tm c d->bb_hit d->bb_hit c.
Proof. intros;eapply fire_back;eauto. Qed.
Lemma bb_Bsweep:forall n L R,
 Reach0 tm(cL StB(rep[S1]n++L)R)(cL StB L(rep[S1]n++R)).
Proof. apply sweepL. intros;go 1;r0. Qed.
Lemma bb_Dsweep:forall n L R,
 Reach0 tm(cL StD(rep[S1]n++L)R)(cL StD L(rep[S0]n++R)).
Proof. apply sweepL. intros;go 1;r0. Qed.
Lemma bb_Fsweep:forall n L R,
 Reach0 tm(bb_front L(rep[S1]n++R))(bb_front(rep[S1]n++L)R).
Proof. apply(sweepFR tm bb_front [S1][S1]). intros;unfold bb_front;go 3;r0. Qed.
Lemma bb_enter:forall n U R,
 Reach0 tm(StA,(rep[S1](S n)++S0::U,S1,R))
   (bb_front(rep[S1](S n)++U)(S0::R)).
Proof.
 intros. go 1.
 change(Reach0 tm(cL StB(rep[S1](S n)++S0::U)(S0::R))(bb_front(rep[S1](S n)++U)(S0::R))).
 rt bb_Bsweep. go 2.
 change(Reach0 tm(bb_front(S1::U)(rep[S1]n++S0::R))(bb_front(rep[S1](S n)++U)(S0::R))).
 rt bb_Fsweep. rewrite rep1_snoc. r0.
Qed.
Lemma bb_enter11:forall n U R,
 Reach0 tm(cL StA(rep[S1](S(S n))++S0::U)(S1::R))
   (bb_front(S1::S0::rep[S1](S n)++U)R).
Proof.
 intros. change(Reach0 tm(StA,(rep[S1](S n)++S0::U,S1,S1::R))(bb_front(S1::S0::rep[S1](S n)++U)R)).
 rt bb_enter. unfold bb_front. go 2;r0.
Qed.
Lemma bb_turn:forall L R,
 Reach0 tm(bb_front L(S0::S0::R))(cL StA L(S1::S0::S1::R)).
Proof. intros;unfold bb_front;go 4;r0. Qed.
Lemma bb_A10:forall U R,
 Reach0 tm(cL StA(S1::S0::U)R)(cL StD U(S0::S1::R)).
Proof. intros;go 4;r0. Qed.
(** The first two zeros in the right guard survive a drain of every
    positive block. The tail hypotheses are used only after the blocks. *)
Lemma bb_drain:forall U,
 (forall R,bb_hit(cL StA U R))->
 (forall R,bb_hit(cL StD U R))->
 forall xs R,bb_hit(cL StA(bb_word xs U)(S1::S0::S0::R)).
Proof.
 intros U HA HD. fix IH 1. intros [|n xs] R;[apply HA|].
 destruct n as[|n].
 - cbn[bb_word rep app]. eapply bb_back;[apply bb_A10|].
   destruct xs as[|m xs];[apply HD|].
   cbn[bb_word]. eapply bb_back;[apply bb_Dsweep|].
   eapply bb_back;[go 1;r0|].
   destruct m as[|m].
   all:apply IH.
 - change(bb_hit(cL StA(rep[S1](S(S n))++S0::bb_word xs U)(S1::S0::S0::R))).
   eapply bb_back;[apply bb_enter11|].
   eapply bb_back;[apply bb_turn|].
   eapply bb_back;[apply bb_A10|].
   eapply bb_back;[apply bb_Dsweep|].
   destruct xs as[|m xs];[apply HD|]. cbn[bb_word].
   eapply bb_back;[apply bb_Dsweep|].
   eapply bb_back;[go 1;r0|].
   destruct m as[|m];apply IH.
Qed.
Lemma bb_zero_one:forall U,
 (forall R,bb_hit(cL StA U R))->
 (forall R,bb_hit(cL StD U R))->
 forall m xs R,bb_hit(bb_front(bb_word(0::m::xs)U)(S0::S0::R)).
Proof.
 intros U HA HD m xs R. eapply bb_back;[apply bb_turn|].
 change(bb_hit(cL StA(S1::S0::bb_word(m::xs)U)(S1::S0::S1::R))).
 eapply bb_back;[apply bb_A10|]. cbn[bb_word].
 eapply bb_back;[apply bb_Dsweep|]. eapply bb_back;[go 1;r0|].
 destruct m as[|m];apply bb_drain;assumption.
Qed.
Lemma bb_normalize:forall n m xs U R,
 Reach0 tm(bb_front(bb_word(S n::m::xs)U)(S0::S0::R))
 (bb_front(bb_word(0::0::S(n+m)::xs)U)R).
Proof.
 intros. rt bb_turn. cbn[bb_word]. rt bb_enter11.
 unfold bb_front. go 2.
 change(Reach0 tm(bb_front(S1::S0::S1::S0::(rep[S1](S n)++rep[S1](S m)++S0::bb_word xs U))R)
 (bb_front(bb_word(0::0::S(n+m)::xs)U)R)).
 rewrite app_assoc,<-rep_add.
 replace(S n+S m)with(S(S(n+m)))by lia. r0.
Qed.
Lemma bb_blank:forall L,bb_hit(bb_front L[S0;S0])->bb_hit(bb_front L[]).
Proof.
 intros. eapply fire_lift;[|exact H]. symmetry.
 unfold bb_front,cR;cbn[chd ctl]. apply(lift_padR 1 StB _ S0 []).
Qed.
Lemma bb_frontier:forall U,
 (forall R,bb_hit(cL StA U R))->
 (forall R,bb_hit(cL StD U R))->
 forall R n m xs,bb_hit(bb_front(bb_word(n::m::xs)U)R).
Proof.
 intros U HA HD. fix IH 1. intros R n m xs.
 assert(Z:forall n m xs,bb_hit(bb_front(bb_word(n::m::xs)U)[S0;S0])).
 { intros[|n']m' xs';[apply bb_zero_one;assumption|].
   eapply bb_back;[apply bb_normalize|]. apply bb_blank,bb_zero_one;assumption. }
 destruct R as[|[]R].
 - apply bb_blank,Z.
 - destruct R as[|[]R].
   + change(bb_hit(bb_front(bb_word(n::m::xs)U)[])). apply bb_blank,Z.
   + destruct n as[|n].
     * apply bb_zero_one;assumption.
     * eapply bb_back;[apply bb_normalize|apply IH].
   + eapply bb_back;[unfold bb_front;go 2;r0|].
     change(bb_hit(bb_front(bb_word(0::n::m::xs)U)R)). apply IH.
 - eapply bb_back;[unfold bb_front;go 3;r0|].
   change(bb_hit(bb_front(bb_word(S n::m::xs)U)R)). apply IH.
Qed.
Lemma bb_Aempty:forall R,bb_hit(cL StA [] R).
Proof. intros;apply bb_here. Qed.
Lemma bb_Dempty:forall R,bb_hit(cL StD [] R).
Proof. intros;eapply bb_back;[go 1;r0|apply bb_here]. Qed.
Lemma bb_Ablock_empty:forall k R,
 bb_hit(cL StA(rep[S1](S k)++[S0])(S1::R)).
Proof.
 intros[|k]R.
 - eapply bb_back;[apply bb_A10|apply bb_Dempty].
 - eapply bb_back;[apply bb_enter11|].
   eapply fire_lift with(b:=bb_front(bb_word[0;k][])R).
   + symmetry. unfold bb_front,cR;cbn[chd ctl bb_word]. rewrite app_nil_r.
     change(lift(StB,((S0::S1::S0::rep[S1](S k))++[S0],chd R,ctl R))=
       lift(StB,(S0::S1::S0::rep[S1](S k),chd R,ctl R))).
     apply(lift_padL 1).
   + apply bb_frontier;[apply bb_Aempty|apply bb_Dempty].
Qed.
Lemma bb_Apositive:forall n m U,
 (forall R,bb_hit(cL StA U R))->
 (forall R,bb_hit(cL StD U R))->
 (forall R,bb_hit(cL StA(rep[S1](S(n+m))++S0::U)(S1::R)))->
 forall R,bb_hit(StA,(rep[S1](S n)++S0::rep[S1]m++S0::U,S1,R)).
Proof.
 intros n m U HA HD HM R. eapply bb_back;[apply bb_enter|].
 rewrite app_assoc,<-rep_add. replace(S n+m)with(S(n+m))by lia.
 destruct R as[|[]R].
 - apply bb_blank. eapply bb_back;[apply bb_turn|apply HM].
 - eapply bb_back;[apply bb_turn|apply HM].
 - eapply bb_back;[unfold bb_front;go 2;r0|].
   change(bb_hit(bb_front(bb_word[0;n+m]U)R)). apply bb_frontier;assumption.
Qed.
Lemma bb_Aones:forall n R,bb_hit(StA,(rep[S1]n,S1,R)).
Proof.
 intros[|n]R.
 - eapply bb_back;[go 5;r0|apply bb_here].
 - eapply fire_lift with(b:=(StA,(rep[S1](S n)++[S0;S0],S1,R))).
   + symmetry;apply(lift_padL 2).
   + apply(bb_Apositive n 0 []);[apply bb_Aempty|apply bb_Dempty|].
     replace(n+0)with n by lia. apply bb_Ablock_empty.
Qed.
Lemma bb_AD:forall L,
 (forall R,bb_hit(cL StA L R)) /\ (forall R,bb_hit(cL StD L R)).
Proof.
 intro L. remember(length L)as z eqn:Ez. revert L Ez.
 induction z using lt_wf_ind;intros L Ez. split;intro R.
 - destruct L as[|[]L];try apply bb_here.
   destruct(bb_ones_split L)as(n&U&E&[HU|(V&HU)]);subst U.
   + rewrite app_nil_r in E;subst L. apply bb_Aones.
   + subst L. destruct n as[|n].
     * eapply bb_back;[apply bb_A10|].
       apply(proj2(H(length V) ltac:(cbn[length rep app]in Ez;lia) V eq_refl)).
     * destruct(bb_ones_split V)as(m&U&E&[HU|(W&HU)]);subst U.
       -- rewrite app_nil_r in E;subst V.
          eapply fire_lift with(b:=(StA,(rep[S1](S n)++S0::rep[S1]m++[S0],S1,R))).
          ++ symmetry. replace(rep[S1](S n)++S0::rep[S1]m++[S0]) with ((rep[S1](S n)++S0::rep[S1]m)++[S0])
             by (rewrite <-app_assoc;reflexivity). apply(lift_padL 1).
          ++ apply bb_Apositive;[apply bb_Aempty|apply bb_Dempty|apply bb_Ablock_empty].
       -- subst V. apply bb_Apositive.
          ++ apply(proj1(H(length W) ltac:(repeat first[rewrite app_length in Ez|progress cbn[length]in Ez];lia) W eq_refl)).
          ++ apply(proj2(H(length W) ltac:(repeat first[rewrite app_length in Ez|progress cbn[length]in Ez];lia) W eq_refl)).
          ++ intro T. apply(proj1(H(length(rep[S1](S(n+m))++S0::W))
             ltac:(repeat first[rewrite app_length in Ez|progress cbn[length]in Ez];rewrite app_length;cbn[length];rewrite !bb_len in *;cbn[length]in *;lia)
             _ eq_refl)).
 - destruct L as[|[]L].
   + apply bb_Dempty.
   + eapply bb_back;[go 1;r0|]. apply(proj1(H(length L) ltac:(cbn[length]in Ez;lia) L eq_refl)).
   + eapply bb_back;[go 1;r0|]. apply(proj2(H(length L) ltac:(cbn[length]in Ez;lia) L eq_refl)).
Qed.
Lemma bb_Ffinite:forall R L,bb_hit(bb_front L R).
Proof.
 fix IH 1. intros R L. destruct R as[|[]R].
 - apply bb_blank. eapply bb_back;[apply bb_turn|apply(proj1(bb_AD L))].
 - destruct R as[|[]R].
   + change(bb_hit(bb_front L[])). apply bb_blank.
     eapply bb_back;[apply bb_turn|apply(proj1(bb_AD L))].
   + eapply bb_back;[apply bb_turn|apply(proj1(bb_AD L))].
   + eapply bb_back;[unfold bb_front;go 2;r0|apply IH].
 - eapply bb_back;[unfold bb_front;go 3;r0|apply IH].
Qed.
Lemma bb_Bzero:forall L R,bb_hit(StB,(L,S0,R)).
Proof.
 intros L[|[]R].
 - eapply bb_back;[go 3;r0|apply(proj2(bb_AD L))].
 - eapply bb_back;[go 3;r0|apply(proj2(bb_AD L))].
 - eapply bb_back;[go 2;r0|apply bb_Ffinite].
Qed.
Lemma bb_Bfinite:forall L R,bb_hit(cL StB L R).
Proof.
 induction L as[|[]L IH];intro R.
 - apply bb_Bzero.
 - apply bb_Bzero.
 - eapply bb_back;[go 1;r0|apply IH].
Qed.
Theorem bb_finite:finite_instr_hit tm(StA,S0).
Proof.
 intros[q[[L h]R]].
 assert(H:bb_hit(q,(L,h,R))).
 { destruct q.
   - apply(proj1(bb_AD(h::L))).
   - apply(bb_Bfinite(h::L)).
   - destruct h.
     + eapply bb_back;[go 1;r0|apply(proj2(bb_AD L))].
     + eapply bb_back;[go 1;r0|apply(bb_Bfinite(chd R::S0::L))].
   - apply(proj2(bb_AD(h::L))). }
 destruct H as(k&e&Ek&Ei). exists k,(lift e);split.
 - exact(csteps_lift _ _ _ _ Ek).
 - rewrite cinstr_lift;exact Ei.
Qed.
End Core.

