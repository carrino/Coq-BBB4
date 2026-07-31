(** * KpWallAlt: the wall bouncer whose RETURN sweep alternates.

    [Counters/KpWallQH.v] closes the [1RB---] wall counter whose carry RIPPLE
    alternates between two states and whose return is one state.  This file is
    its twin: the ripple is one state and the RETURN alternates.

      qD  0 -> 1 L qA     qD  1 -> 0 R qD     (the stop, and the carry ripple)
      qA  0 -> 0 L qB     qA  1 -> 1 R qD     (the return sweep, and the wall)
      qB  0 -> 0 L qA     qB  1 -> 1 R qD

    Read at the anchor

      Cc p = (qD, ([S1], S0, Kp p))

    -- the wall cell [S1] alone on the left, the head on the blank beside it,
    the plain base-2 counter ([KpCounter.Kp], low bit first) to the right.
    One lap is

      STP . WALL . RIP^k . RIP . STP . RET^k . RET . WALL

    ([qD] turns left onto the wall and bounces straight back off it; the
    bounce leaves an [S1] under the head, which is the first cell the ripple
    clears, so the ripple runs [k+1] cells for a carry of length [k]; the
    first clear cell stops it and turns it left; the return sweep crosses the
    [k] cells just cleared, pops the wall and bounces again, and IS the next
    anchor).  Exactly [2k + 6] steps, but the count is never written down:
    [LapGlue]'s lap obligation is existential in it.

    ** Why the alternation is handled existentially

    [qA] and [qB] agree on [S1] and differ only in each other's names on [S0],
    so the return flips between them and its parity is not determined by [k].
    Nothing downstream cares: the wall bounce is the same from either.  So the
    return lemma carries "the state is still one of the two" rather than
    naming it -- which is what lets ONE lap lemma cover both parities.  It is
    also why the chain language of [Checkers/LapDecider.v] cannot express this
    lap: an [SCycL] unit must return to the state it started in, and this one
    does so only every second cell.

    ** Both branches close EXACTLY

    [chd [] = S0], so the blank past the counter's top digit behaves exactly
    like the clear bit that stops an interior carry: the overflow branch is
    [lap_shape] at [k = S j] with [w = []], and its result [rep [S0] (S j) ++
    [S1]] is [Kp (Pos.succ p)] on the nose.  No [lift] slack anywhere.

    ** Why this is a QUASIHALTING closer

    On these rows [StA] fires once, at index 0, and is the target of no
    transition -- so the machine genuinely quasihalts with score 1 and
    [NeverQuasiHaltsSt] is FALSE for it.  The theorem is the census R_QH
    triple, via [LapGlueQuiet.glue_qh_quiet] with [qa = StA] and [s0 = 0].
    Its [AvoidRun] premise -- no lap may touch [StA] -- comes free from
    [Checkers/ReachStI.inv_csteps_all]: [[qD; qA; qB]] is total and closed, so
    no run from the anchor can reach [StA] at all.

    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import ReachStI.
From BBB4.Counters Require Import WTape LapGlue LapGlueQuiet MonoCounter KpCounter.
Import ListNotations.

Section KpWallAlt.

Variable tm : TM.
Variable qD qA qB : St.
Variable t0 : nat.
Variable p0 : positive.

Hypothesis HD0 : tm qD S0 = Some (mkTrans S1 DL qA).
Hypothesis HD1 : tm qD S1 = Some (mkTrans S0 DR qD).
Hypothesis HA0 : tm qA S0 = Some (mkTrans S0 DL qB).
Hypothesis HA1 : tm qA S1 = Some (mkTrans S1 DR qD).
Hypothesis HB0 : tm qB S0 = Some (mkTrans S0 DL qA).
Hypothesis HB1 : tm qB S1 = Some (mkTrans S1 DR qD).

(** The three roles are exactly the non-[StA] states, and [StA] is not one
    of them: that is what makes [StA] the quiet state. *)
Hypothesis Hcover : forall q, q = StA \/ q = qD \/ q = qA \/ q = qB.
Hypothesis HDA : qD <> StA.
Hypothesis HAA : qA <> StA.
Hypothesis HBA : qB <> StA.

(** Totality and closure of the role set -- one [vm_compute] per row. *)
Hypothesis Hinv : inv_ok tm [qD; qA; qB] = true.

(** The bootstrap, and the checked [StA]-free window below it. *)
Hypothesis Hboot : stepn tm t0 InitES = Some (lift (qD, ([S1], S0, Kp p0))).
Hypothesis Hbq : forall n c, 0 < n < t0 -> stepn tm n InitES = Some c -> fst c <> StA.

Definition Cc (p : positive) : cconf := (qD, ([S1], S0, Kp p)).

(** ** Units *)

(** [qD] on a clear cell: set it, turn left, hand over to the return pair. *)
Lemma uSTP : forall L R, csteps tm 1 (qD,(L,S0,R)) = Some (qA,(ctl L,chd L,S1::R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HD0.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

(** The wall bounce, from either member of the return pair. *)
Lemma uWALL : forall q L R, (q = qA \/ q = qB) ->
  csteps tm 1 (q,(L,S1,R)) = Some (qD,(S1::L,chd R,ctl R)).
Proof.
  intros q L R [-> | ->]; cbn [csteps cstep]; [rewrite HA1 | rewrite HB1];
    cbn [t_next t_dir t_write ctape_move]; reflexivity.
Qed.

(** One cell of the carry ripple. *)
Lemma uRIP : forall L R, csteps tm 1 (qD,(L,S1,R)) = Some (qD,(S0::L,chd R,ctl R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HD1.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

(** One cell of the return sweep, from each member of the pair. *)
Lemma uRETA : forall L R, csteps tm 1 (qA,(L,S0,R)) = Some (qB,(ctl L,chd L,S0::R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HA0.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

Lemma uRETB : forall L R, csteps tm 1 (qB,(L,S0,R)) = Some (qA,(ctl L,chd L,S0::R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HB0.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

(** What the sweep carries is "still one of the two"; which one flips. *)
Lemma uRET : forall q L R, (q = qA \/ q = qB) ->
  exists q', (q' = qA \/ q' = qB) /\
  csteps tm 1 (q,(L,S0,R)) = Some (q',(ctl L,chd L,S0::R)).
Proof.
  intros q L R [-> | ->].
  - exists qB. split; [auto | apply uRETA].
  - exists qA. split; [auto | apply uRETB].
Qed.

(** ** Phases *)

Lemma rep_cons : forall (u : list Sym) k L,
  rep u k ++ (u ++ L) = u ++ (rep u k ++ L).
Proof.
  intros u k L. rewrite app_assoc, rep_shift, <- app_assoc. reflexivity.
Qed.

(** The carry ripple: [k] set cells clear and cross the head rightward. *)
Lemma phRIP : forall k L w,
  csteps tm k (qD,(L,S1,rep [S1] k ++ w)) = Some (qD,(rep [S0] k ++ L,S1,w)).
Proof.
  induction k as [|k IH]; intros L w; [reflexivity |].
  assert (Hstep : csteps tm 1 (qD,(L,S1,rep [S1] (S k) ++ w))
                  = Some (qD,(S0::L,S1,rep [S1] k ++ w))).
  { cbn [rep app]. rewrite (uRIP L (S1 :: (rep [S1] k ++ w))). reflexivity. }
  replace (S k) with (1 + k) at 1 by lia.
  rewrite csteps_add, Hstep, IH.
  cbn [rep]. change (S0 :: L) with ([S0] ++ L).
  rewrite (rep_cons [S0] k L). reflexivity.
Qed.

(** The return sweep: [k] clear cells cross the head leftward, and the
    sweeping state flips once per cell. *)
Lemma phRET : forall k q L R, (q = qA \/ q = qB) ->
  exists q', (q' = qA \/ q' = qB) /\
  csteps tm k (q,(rep [S0] k ++ L,S0,R)) = Some (q',(L,S0,rep [S0] k ++ R)).
Proof.
  induction k as [|k IH]; intros q L R Hq.
  - exists q. split; [exact Hq | reflexivity].
  - destruct (uRET q (S0 :: (rep [S0] k ++ L)) R Hq) as (q2 & Hq2 & Hstep).
    cbn [chd ctl] in Hstep.
    destruct (IH q2 L (S0 :: R) Hq2) as (q' & Hq' & Hrun).
    exists q'. split; [exact Hq' |].
    cbn [rep app].
    replace (S k) with (1 + k) at 1 by lia.
    rewrite csteps_add, Hstep, Hrun.
    cbn [rep]. change (S0 :: R) with ([S0] ++ R).
    rewrite (rep_cons [S0] k R). reflexivity.
Qed.

(** ** The lap

    [w] is what lies beyond the carry run: [S0 :: Kp q0] in the interior,
    [[]] at overflow.  [chd [] = S0] makes those the same stop. *)
Lemma lap_shape : forall k w, chd w = S0 ->
  exists n, 0 < n /\
  csteps tm n (qD,([S1],S0,rep [S1] k ++ w))
    = Some (qD,([S1],S0,rep [S0] k ++ S1 :: ctl w)).
Proof.
  intros k w Hw. exists (1 + (1 + (k + (1 + (1 + (k + (1 + 1))))))).
  split; [lia |].
  eapply csteps_chain. { apply (uSTP [S1] (rep [S1] k ++ w)). }
  cbn [chd ctl].
  eapply csteps_chain.
  { apply (uWALL qA [] (S1 :: (rep [S1] k ++ w))). auto. }
  cbn [chd ctl].
  eapply csteps_chain. { apply (phRIP k [S1] w). }
  eapply csteps_chain. { apply (uRIP (rep [S0] k ++ [S1]) w). }
  rewrite Hw.
  eapply csteps_chain.
  { apply (uSTP (S0 :: (rep [S0] k ++ [S1])) (ctl w)). }
  cbn [chd ctl].
  destruct (phRET k qA [S1] (S1 :: ctl w) (or_introl eq_refl))
    as (q' & Hq' & Hret).
  eapply csteps_chain. { exact Hret. }
  destruct (uRET q' [S1] (rep [S0] k ++ S1 :: ctl w) Hq') as (q2 & Hq2 & Hlast).
  eapply csteps_chain. { exact Hlast. }
  cbn [chd ctl].
  rewrite (uWALL q2 [] (S0 :: (rep [S0] k ++ S1 :: ctl w)) Hq2).
  cbn [chd ctl]. reflexivity.
Qed.

Lemma lap_exact : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ c' = Cc (Pos.succ p) /\ 0 < n.
Proof.
  intro p. unfold Cc.
  destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - destruct (cview_some_K p j q0 Ecv) as (HKp & HKs).
    destruct (lap_shape j (S0 :: Kp q0) eq_refl) as (n & Hn & Hrun).
    exists n. eexists. split; [| split; [| exact Hn]].
    + rewrite HKp. exact Hrun.
    + rewrite HKs. cbn [ctl]. reflexivity.
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv;
        [destruct (cview p); discriminate | discriminate | discriminate]. }
    destruct (cview_none_K p j' Ecv) as (HKp & HKs).
    destruct (lap_shape (S j') [] eq_refl) as (n & Hn & Hrun).
    exists n. eexists. split; [| split; [| exact Hn]].
    + rewrite HKp. rewrite <- (app_nil_r (rep [S1] (S j'))). exact Hrun.
    + rewrite HKs. cbn [ctl]. reflexivity.
Qed.

(** ** No lap touches [StA] *)

Lemma avoid_from_anchor : forall p n, AvoidRun tm StA n (Cc p).
Proof.
  intros p n m cm _ Hst.
  assert (Hin : InAllowed [qD; qA; qB] (Cc p)) by (cbn; auto).
  pose proof (inv_csteps_all tm [qD; qA; qB] Hinv m (Cc p) cm Hin Hst) as H.
  unfold InAllowed in H. cbn in H.
  destruct H as [<- | [<- | [<- | []]]]; auto.
Qed.

Lemma lap_Q : forall p, (p0 <= p)%positive ->
  exists n c', csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n
               /\ AvoidRun tm StA n (Cc p).
Proof.
  intros p _. destruct (lap_exact p) as (n & c' & H1 & H2 & H3).
  exists n, c'. repeat split; try assumption.
  - rewrite H2. reflexivity.
  - apply avoid_from_anchor.
Qed.

(** ** Visit witnesses

    [qD] is the anchor and [qA] is one step in.  [qB] needs the return
    sweep, whose length parity is not determined -- so the witness is taken
    at whichever of the last two return states is [qB]. *)
Lemma visB_shape : forall k w, chd w = S0 ->
  exists n c, csteps tm n (qD,([S1],S0,rep [S1] k ++ w)) = Some c /\ fst c = qB.
Proof.
  intros k w Hw.
  assert (Hpre : csteps tm (1 + (1 + (k + (1 + 1))))
                   (qD,([S1],S0,rep [S1] k ++ w))
                 = Some (qA,(rep [S0] k ++ [S1],S0,S1 :: ctl w))).
  { eapply csteps_chain. { apply (uSTP [S1] (rep [S1] k ++ w)). }
    cbn [chd ctl].
    eapply csteps_chain.
    { apply (uWALL qA [] (S1 :: (rep [S1] k ++ w))). auto. }
    cbn [chd ctl].
    eapply csteps_chain. { apply (phRIP k [S1] w). }
    eapply csteps_chain. { apply (uRIP (rep [S0] k ++ [S1]) w). }
    rewrite Hw.
    rewrite (uSTP (S0 :: (rep [S0] k ++ [S1])) (ctl w)).
    cbn [chd ctl]. reflexivity. }
  destruct (phRET k qA [S1] (S1 :: ctl w) (or_introl eq_refl))
    as (q' & [-> | ->] & Hret).
  - (* the return ends on [qA]: one more cell, and it is [qB] *)
    exists (1 + (1 + (k + (1 + 1))) + (k + 1)),
      (qB,(ctl [S1],chd [S1],S0 :: (rep [S0] k ++ S1 :: ctl w))).
    split; [| reflexivity].
    rewrite csteps_add, Hpre, csteps_add, Hret.
    apply (uRETA [S1] (rep [S0] k ++ S1 :: ctl w)).
  - (* the return already ends on [qB] *)
    exists (1 + (1 + (k + (1 + 1))) + k), (qB,([S1],S0,rep [S0] k ++ S1 :: ctl w)).
    split; [rewrite csteps_add, Hpre; exact Hret | reflexivity].
Qed.

Lemma vis_T : forall p q, q <> StA ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q Hq. unfold Cc.
  destruct (Hcover q) as [-> | [-> | [-> | ->]]];
    [contradiction Hq; reflexivity | | |].
  - exists 0, (qD,([S1],S0,Kp p)). split; reflexivity.
  - exists 1, (qA,([],chd [S1],S1 :: Kp p)). split;
      [apply (uSTP [S1] (Kp p)) | reflexivity].
  - destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
    + destruct (cview_some_K p j q0 Ecv) as (HKp & _).
      rewrite HKp. exact (visB_shape j (S0 :: Kp q0) eq_refl).
    + destruct j as [|j'].
      { exfalso. destruct p; simpl in Ecv;
          [destruct (cview p); discriminate | discriminate | discriminate]. }
      destruct (cview_none_K p j' Ecv) as (HKp & _).
      rewrite HKp, <- (app_nil_r (rep [S1] (S j'))).
      exact (visB_shape (S j') [] eq_refl).
Qed.

Lemma vis0_T : VisitsAt tm StA 0.
Proof. exists InitES. split; reflexivity. Qed.

(** ** The closer *)

Definition iqh (m : TM) : Prop :=
  NonHalt m /\ QHBound 2000 m /\ QuasiHaltsSt m.

Theorem kpwallalt_qh : iqh tm.
Proof.
  destruct (glue_qh_quiet tm Cc p0 StA t0 0 Hboot lap_Q
              (fun p q _ Hq => vis_T p q Hq) vis0_T Hbq)
    as (Hnh & Hqb & Hqh).
  split; [exact Hnh | split; [| exact Hqh]].
  apply (qhbound_mono 1 2000); [lia | exact Hqb].
Qed.

End KpWallAlt.
