(** * Positive laps for the signed binary two-sweep counter

    For every table satisfying the eight hypotheses, an even left sweep
    flips the first digit and reaches D0. The finite H/F carry transducers
    return over the same left prefix; an odd sweep reaches the next B0
    anchor with two more 10 pairs. The return is positive even when the
    carry makes no recursive call. Signed-value positivity closes the
    marked family. Blank padding is interpreted through CTape.lift. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr.
From BBB4.Counters Require Import BlockCoreKValueTr.
Import ListNotations.
Definition bk_flip(d:Sym):Sym:=match d with S0=>S1|S1=>S0 end.
Section Core.
Variable tm:TM.
Hypotheses
 (HA0:tm StA S0=Some(mkTrans S1 DR StB))
 (HA1:tm StA S1=Some(mkTrans S0 DL StC))
 (HB0:tm StB S0=Some(mkTrans S1 DR StC))
 (HB1:tm StB S1=Some(mkTrans S0 DR StD))
 (HC0:tm StC S0=Some(mkTrans S1 DL StA))
 (HC1:tm StC S1=Some(mkTrans S0 DL StC))
 (HD0:tm StD S0=Some(mkTrans S1 DR StD))
 (HD1:tm StD S1=Some(mkTrans S0 DR StA)).
Local Ltac run:=
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR rep bk_flip bk_encode];
 repeat(first[rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[csteps cstep ctape_move chd ctl t_next t_dir t_write app cL cR rep bk_flip bk_encode]);reflexivity.
Local Ltac go n:=first[eapply(r1_run _ n);[lia|run|]|eapply(r0_run _ n);[run|]].
Lemma bk_left_scan:forall k q R,q=StA\/q=StC->
 Reach0 tm(q,(rep[S0;S1]k,S1,R))
 (cR StD[S1;S0;S1](rep[S1;S0]k++R)).
Proof.
 induction k as[|k IH];intros q R Hq;destruct Hq as[-> | ->].
 - cbn[rep];go 5;r0.
 - cbn[rep];go 5;r0.
 - cbn[rep app];go 2.
   rt (IH StA (S1::S0::R) (or_introl eq_refl)).
   change(Reach0 tm(cR StD[S1;S0;S1](rep[S1;S0]k++[S1;S0]++R))
     (cR StD[S1;S0;S1]([S1;S0]++rep[S1;S0]k++R))).
   rewrite rep_snoc;r0.
 - cbn[rep app];go 2.
   rt (IH StA (S1::S0::R) (or_introl eq_refl)).
   change(Reach0 tm(cR StD[S1;S0;S1](rep[S1;S0]k++[S1;S0]++R))
     (cR StD[S1;S0;S1]([S1;S0]++rep[S1;S0]k++R))).
   rewrite rep_snoc;r0.
Qed.
Lemma bk_pairs_even:forall n q L R,q=StB\/q=StD->
 Reach0 tm(cR q L(rep[S1;S0](2*n)++R))
 (cR q(rep[S1;S0](2*n)++L)R).
Proof.
 induction n as[|n IH];intros q L R Hq.
 - cbn[rep];r0.
 - replace(2*S n)with(S(S(2*n)))by lia.
   destruct Hq as[-> | ->];cbn[rep app];go 4.
   + rt(IH StB (S1::S0::S1::S0::L) R (or_introl eq_refl)).
     change(Reach0 tm(cR StB(rep[S1;S0](2*n)++[S1;S0]++[S1;S0]++L)R)
      (cR StB([S1;S0]++[S1;S0]++rep[S1;S0](2*n)++L)R)).
     repeat rewrite rep_snoc;r0.
   + rt(IH StD (S1::S0::S1::S0::L) R (or_intror eq_refl)).
     change(Reach0 tm(cR StD(rep[S1;S0](2*n)++[S1;S0]++[S1;S0]++L)R)
      (cR StD([S1;S0]++[S1;S0]++rep[S1;S0](2*n)++L)R)).
     repeat rewrite rep_snoc;r0.
Qed.
Lemma bk_even_sweep:forall n d w,
 Reach0 tm(bk_anchor n(d::w))
 (StD,(rep[S1;S0](2*n+1)++[S1],S0,bk_encode(bk_flip d::w))).
Proof.
 intros n d w. unfold bk_anchor.
 rewrite <-(LoopRunTr.rep_shift S1 S0 (2*n)[]).
 rewrite app_nil_r.
 destruct d;cbn[bk_encode bk_flip];go 3.
 - rt(bk_left_scan (2*n) StC (S0::S1::S0::S0::bk_encode w)(or_intror eq_refl)).
   rt(bk_pairs_even n StD[S1;S0;S1](S0::S1::S0::S0::bk_encode w)(or_intror eq_refl)).
   replace(2*n+1)with(S(2*n))by lia.
   rewrite rep_S_r. repeat rewrite <- app_assoc. cbn[app cR chd ctl]. r0.
 - rt(bk_left_scan (2*n) StC (S0::S0::S0::S0::bk_encode w)(or_intror eq_refl)).
   rt(bk_pairs_even n StD[S1;S0;S1](S0::S0::S0::S0::bk_encode w)(or_intror eq_refl)).
   replace(2*n+1)with(S(2*n))by lia.
   rewrite rep_S_r. repeat rewrite <- app_assoc. cbn[app cR chd ctl]. r0.
Qed.
Lemma bk_padR:forall q L R k,
 Reach0 tm(cL q L(R++rep[S0]k))(cL q L R).
Proof.
 intros. eapply reach0_lift_l with(a':=cL q L R).
 - unfold cL;apply lift_padR.
 - r0.
Qed.
Lemma bk_H_phase:forall w L,
 Reach0 tm(cR StD L(bk_encode(S1::w)))(cL StA L(bk_encode(bk_H w))).
Proof.
 intros[|d w]L;[|destruct d];cbn[bk_encode bk_H];go 7.
 - change(Reach0 tm(cL StA L([S1]++rep[S0]3))(cL StA L[S1])).
   apply bk_padR.
 - r0.
 - r0.
Qed.
Lemma bk_F_phase:forall w L,
 exists q,(q=StA\/q=StC)/\
 Reach0 tm(cR StD L(bk_encode w))(cL q L(bk_encode(bk_F w))).
Proof.
 induction w as[|d w IH];intro L.
 - exists StA;split;[left;reflexivity|]. cbn[bk_encode bk_F]. go 7;r0.
 - destruct d.
   + exists StC;split;[right;reflexivity|]. cbn[bk_encode bk_F]. go 3.
     destruct(IH(S1::S1::S1::L))as[q[Hq Hr]]. rt Hr.
     destruct Hq as[-> | ->];go 3;r0.
   + exists StA;split;[left;reflexivity|]. cbn[bk_F]. apply bk_H_phase.
Qed.
Lemma bk_carry_phase:forall d w L,
 exists q,(q=StA\/q=StC)/\
 Reach0 tm(StD,(L,S0,bk_encode(bk_flip d::w)))
          (q,(L,S1,bk_encode(bk_S(d::w)))).
Proof.
 intros d w L;destruct d.
 - exists StA;split;[left;reflexivity|]. cbn[bk_flip bk_S]. go 1.
   apply(bk_H_phase w(S1::L)).
 - destruct(bk_F_phase(S0::w)(S1::L))as[q[Hq Hr]].
   exists q;split;[exact Hq|]. cbn[bk_flip bk_S]. go 1.
   exact Hr.
Qed.
Lemma bk_pairs_odd:forall n L R,
 Reach0 tm(cR StD L(rep[S1;S0](2*n+1)++R))
 (cR StB(rep[S1;S0](2*n+1)++L)R).
Proof.
 intros. replace(2*n+1)with(S(2*n))by lia. cbn[rep app];go 2.
 rt(bk_pairs_even n StB(S1::S0::L)R(or_introl eq_refl)).
 change(Reach0 tm(cR StB(rep[S1;S0](2*n)++[S1;S0]++L)R)
   (cR StB([S1;S0]++rep[S1;S0](2*n)++L)R)).
 rewrite rep_snoc;r0.
Qed.
Lemma bk_odd_return:forall n q R,q=StA\/q=StC->
 Reach1 tm(q,(rep[S1;S0](2*n+1)++[S1],S1,R))
 (StB,(rep[S1;S0](2*(S n))++[S1],S0,R)).
Proof.
 intros n q R Hq.
 rewrite <-(LoopRunTr.rep_shift S1 S0 (2*n+1)[]). rewrite app_nil_r.
 destruct Hq as[-> | ->];go 1.
 - rt(bk_left_scan (2*n+1) StC(S0::R)(or_intror eq_refl)).
   rt(bk_pairs_odd n[S1;S0;S1](S0::R)).
   replace(2*S n)with(S(2*n+1))by lia.
   rewrite rep_S_r. repeat rewrite <- app_assoc. cbn[app cR chd ctl]. r0.
 - rt(bk_left_scan (2*n+1) StC(S0::R)(or_intror eq_refl)).
   rt(bk_pairs_odd n[S1;S0;S1](S0::R)).
   replace(2*S n)with(S(2*n+1))by lia.
   rewrite rep_S_r. repeat rewrite <- app_assoc. cbn[app cR chd ctl]. r0.
Qed.
Theorem bk_lap:forall n w,w<>[]->
 Reach1 tm(bk_anchor n w)(bk_anchor(S n)(bk_S w)).
Proof.
 intros n[|d w]H;[contradiction|]. rt01(bk_even_sweep n d w).
 destruct(bk_carry_phase d w(rep[S1;S0](2*n+1)++[S1]))as[q[Hq Hr]].
 rt01 Hr. apply bk_odd_return;exact Hq.
Qed.
Theorem bk_return:forall c,bk_mark c->exists d,bk_mark d/\Reach1 tm c d.
Proof.
 intros c H;destruct H as[n w Hn Hw].
 exists(bk_anchor(S n)(bk_S w));split.
 - apply bk_marked;[lia|apply bk_S_positive;exact Hw].
 - apply bk_lap,bk_positive_nonempty;exact Hw.
Qed.
End Core.
