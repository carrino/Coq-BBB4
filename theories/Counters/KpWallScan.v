(** * KpWallScan: the wall bouncer whose return pair splits at the wall.

    The third [1RB---] wall-counter shape, after [Counters/KpWallQH.v] (the
    RIPPLE alternates) and [Counters/KpWallAlt.v] (the RETURN alternates):

      qR  0 -> 1 L qQ     qR  1 -> 0 R qR     (the stop, and the carry ripple)
      qQ  0 -> 0 L qP     qQ  1 -> 1 R qR     (return, and the wall bounce)
      qP  0 -> 0 L qQ     qP  1 -> 1 R qP     (return, and a SCAN instead)

    Here the return pair does NOT agree at the wall: [qQ] bounces into the
    ripple, [qP] bounces into itself.  That is what
    [tools/closeout/residue_map.tsv] calls "PARITY-AFFINE" -- measured at the
    anchor

      Cc p = (qQ, ([], S1, Kp p))

    the lap is [2j + 2] when the carry length [j] is even and [2j + 4] when
    it is odd, because the return sweep alternates [qQ]/[qP] and an odd
    number of cells lands on [qP], which costs two extra steps to get back
    to [qQ].

    ** Why the parity does not reach the anchor

    A [qP] wall bounce runs right onto the counter's low cell, and after an
    increment that cell is CLEAR (the increment that put the head there had
    [j >= 1], so [Kp (p+1)] starts with [S0]) -- so [qP] turns straight back
    round, one cell out and one cell in, and hands over to [qQ] at the very
    same anchor.  The parity therefore lives entirely inside the lap: the
    anchor state is always [qQ], and the lap obligation is existential in
    the step count, so the two laws need no separate branch in the closer's
    interface.  The return lemma carries "the state is still one of the two"
    rather than naming it, which is what covers both parities at once.

    ** Both branches close EXACTLY

    [chd [] = S0], so the blank past the counter's top digit behaves exactly
    like the clear bit that stops an interior carry: the overflow branch is
    [lap_shape] at [k = S j] with [w = []], and its result
    [rep [S0] (S j) ++ [S1]] is [Kp (Pos.succ p)] on the nose.

    ** Why this is a QUASIHALTING closer

    On these rows [StA] fires once, at index 0, and is the target of no
    transition -- so the machine genuinely quasihalts with score 1 and
    [NeverQuasiHaltsSt] is FALSE for it.  The theorem is the census R_QH
    triple, via [LapGlueQuiet.glue_qh_quiet] with [qa = StA] and [s0 = 0];
    the [AvoidRun] premise comes free from
    [Checkers/ReachStI.inv_csteps_all].

    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import ReachStI.
From BBB4.Counters Require Import WTape LapGlue LapGlueQuiet MonoCounter
                                  KpCounter LapCertGlue.
Import ListNotations.

Section KpWallScan.

Variable tm : TM.
Variable qR qQ qP : St.
Variable t0 : nat.
Variable p0 : positive.

Hypothesis HR0 : tm qR S0 = Some (mkTrans S1 DL qQ).
Hypothesis HR1 : tm qR S1 = Some (mkTrans S0 DR qR).
Hypothesis HQ0 : tm qQ S0 = Some (mkTrans S0 DL qP).
Hypothesis HQ1 : tm qQ S1 = Some (mkTrans S1 DR qR).
Hypothesis HP0 : tm qP S0 = Some (mkTrans S0 DL qQ).
Hypothesis HP1 : tm qP S1 = Some (mkTrans S1 DR qP).

(** The three roles are exactly the non-[StA] states, and [StA] is not one
    of them: that is what makes [StA] the quiet state. *)
Hypothesis Hcover : forall q, q = StA \/ q = qR \/ q = qQ \/ q = qP.
Hypothesis HRA : qR <> StA.
Hypothesis HQA : qQ <> StA.
Hypothesis HPA : qP <> StA.

(** Totality and closure of the role set -- one [vm_compute] per row. *)
Hypothesis Hinv : inv_ok tm [qR; qQ; qP] = true.

(** The bootstrap, and the checked [StA]-free window below it. *)
Hypothesis Hboot : stepn tm t0 InitES = Some (lift (qQ, ([], S1, Kp p0))).
Hypothesis Hbq : forall n c, 0 < n < t0 ->
  stepn tm n InitES = Some c -> fst c <> StA.

Definition Cc (p : positive) : cconf := (qQ, ([], S1, Kp p)).

(** ** Units *)

Lemma uWQ : forall L R, csteps tm 1 (qQ,(L,S1,R)) = Some (qR,(S1::L,chd R,ctl R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HQ1.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

Lemma uWP : forall L R, csteps tm 1 (qP,(L,S1,R)) = Some (qP,(S1::L,chd R,ctl R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HP1.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

Lemma uRIP : forall L R, csteps tm 1 (qR,(L,S1,R)) = Some (qR,(S0::L,chd R,ctl R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HR1.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

Lemma uSTP : forall L R, csteps tm 1 (qR,(L,S0,R)) = Some (qQ,(ctl L,chd L,S1::R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HR0.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

Lemma uRETQ : forall L R, csteps tm 1 (qQ,(L,S0,R)) = Some (qP,(ctl L,chd L,S0::R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HQ0.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

Lemma uRETP : forall L R, csteps tm 1 (qP,(L,S0,R)) = Some (qQ,(ctl L,chd L,S0::R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HP0.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

(** What the return carries is "still one of the two"; which one flips. *)
Lemma uRET : forall q L R, (q = qQ \/ q = qP) ->
  exists q', (q' = qQ \/ q' = qP) /\
  csteps tm 1 (q,(L,S0,R)) = Some (q',(ctl L,chd L,S0::R)).
Proof.
  intros q L R [-> | ->].
  - exists qP. split; [auto | apply uRETQ].
  - exists qQ. split; [auto | apply uRETP].
Qed.

(** ** Phases *)

Lemma rep_cons : forall (u : list Sym) k L,
  rep u k ++ (u ++ L) = u ++ (rep u k ++ L).
Proof.
  intros u k L. rewrite app_assoc, rep_shift, <- app_assoc. reflexivity.
Qed.

(** The carry ripple: [k] set cells clear and cross the head rightward. *)
Lemma phRIP : forall k L w,
  csteps tm k (qR,(L,chd (rep [S1] k ++ w),ctl (rep [S1] k ++ w)))
    = Some (qR,(rep [S0] k ++ L,chd w,ctl w)).
Proof.
  induction k as [|k IH]; intros L w; [reflexivity |].
  cbn [rep app chd ctl].
  replace (S k) with (1 + k) at 1 by lia.
  rewrite csteps_add, (uRIP L (rep [S1] k ++ w)), IH.
  cbn [rep]. change (S0 :: L) with ([S0] ++ L).
  rewrite (rep_cons [S0] k L). reflexivity.
Qed.

(** The return sweep, its state flipping once per cell. *)
Lemma phRET : forall k q L R, (q = qQ \/ q = qP) ->
  exists q', (q' = qQ \/ q' = qP) /\
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
  csteps tm n (qQ,([],S1,rep [S1] k ++ w))
    = Some (qQ,([],S1,rep [S0] k ++ S1 :: ctl w)).
Proof.
  intros k w Hw. destruct k as [|m].
  - (* no carry: out one cell, set it, straight back to the wall *)
    exists (1 + 1). split; [lia |].
    cbn [rep app].
    rewrite csteps_add, (uWQ [] w), Hw, (uSTP [S1] (ctl w)).
    cbn [chd ctl rep app]. reflexivity.
  - (* the ripple runs, and the return lands on either of the pair *)
    assert (Hpre : csteps tm (1 + (S m + 1))
                     (qQ,([],S1,rep [S1] (S m) ++ w))
                   = Some (qQ,(rep [S0] m ++ [S1],S0,S1 :: ctl w))).
    { rewrite csteps_add, (uWQ [] (rep [S1] (S m) ++ w)).
      rewrite csteps_add, (phRIP (S m) [S1] w), Hw.
      rewrite (uSTP (rep [S0] (S m) ++ [S1]) (ctl w)).
      cbn [rep app chd ctl]. reflexivity. }
    destruct (phRET m qQ [S1] (S1 :: ctl w) (or_introl eq_refl))
      as (q' & [-> | ->] & Hret).
    + (* the return ended on [qQ], so the wall is reached on [qP]: [qP]
         scans one cell out, finds it clear, and hands back to [qQ] *)
      exists (1 + (S m + 1) + (m + (1 + (1 + 1)))). split; [lia |].
      rewrite csteps_add, Hpre, csteps_add, Hret.
      rewrite csteps_add, (uRETQ [S1] (rep [S0] m ++ S1 :: ctl w)).
      cbn [chd ctl].
      rewrite csteps_add, (uWP [] (S0 :: (rep [S0] m ++ S1 :: ctl w))).
      cbn [chd ctl].
      rewrite (uRETP [S1] (rep [S0] m ++ S1 :: ctl w)).
      cbn [chd ctl rep app]. reflexivity.
    + (* the return ended on [qP], so the wall is reached on [qQ]: done *)
      exists (1 + (S m + 1) + (m + 1)). split; [lia |].
      rewrite csteps_add, Hpre, csteps_add, Hret.
      rewrite (uRETP [S1] (rep [S0] m ++ S1 :: ctl w)).
      cbn [chd ctl rep app]. reflexivity.
Qed.

Lemma lapi : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 Ecv. unfold Cc.
  destruct (cview_some_K p j q0 Ecv) as (HKp & HKs).
  destruct (lap_shape j (S0 :: Kp q0) eq_refl) as (n & Hn & Hrun).
  exists n. split; [exact Hn |].
  rewrite HKp, Hrun, HKs. cbn [ctl]. reflexivity.
Qed.

Lemma lap_exact : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ c' = Cc (Pos.succ p) /\ 0 < n.
Proof.
  intro p. unfold Cc.
  destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - destruct (lapi p j q0 Ecv) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)). split; [exact Hrun | split; [reflexivity | exact Hn]].
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
  assert (Hin : InAllowed [qR; qQ; qP] (Cc p)) by (cbn; auto).
  pose proof (inv_csteps_all tm [qR; qQ; qP] Hinv m (Cc p) cm Hin Hst) as H.
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

    [qQ] is the anchor and [qR] is one step in.  [qP] is the return sweep's
    FIRST cell, so it needs a non-empty carry run -- which the anchor may not
    have.  The overflow anchor always does, and every anchor reaches one by
    interior laps ([LapCertGlue.vis_via_ovf], which is exactly why [lapi]
    closes exactly). *)
Lemma visP_shape : forall m w, chd w = S0 ->
  exists n c, csteps tm n (qQ,([],S1,rep [S1] (S m) ++ w)) = Some c
              /\ fst c = qP.
Proof.
  intros m w Hw.
  exists (1 + (S m + (1 + 1))),
    (qP,(ctl (rep [S0] m ++ [S1]),chd (rep [S0] m ++ [S1]),
         S0 :: S1 :: ctl w)).
  split; [| reflexivity].
  rewrite csteps_add, (uWQ [] (rep [S1] (S m) ++ w)).
  rewrite csteps_add, (phRIP (S m) [S1] w), Hw.
  rewrite csteps_add, (uSTP (rep [S0] (S m) ++ [S1]) (ctl w)).
  cbn [rep app chd ctl].
  apply (uRETQ (rep [S0] m ++ [S1]) (S1 :: ctl w)).
Qed.

Lemma vis_T : forall p q, q <> StA ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q Hq.
  destruct (Hcover q) as [-> | [-> | [-> | ->]]];
    [contradiction Hq; reflexivity | | |].
  - (* [qR]: one step off the wall *)
    exists 1, (qR,([S1],chd (Kp p),ctl (Kp p))). split;
      [apply (uWQ [] (Kp p)) | reflexivity].
  - exists 0, (Cc p). split; reflexivity.
  - (* [qP]: fires in every overflow lap, and every anchor reaches one *)
    apply (vis_via_ovf tm Cc lapi qP).
    intros p1 j Ecv.
    destruct (cview_none_K p1 j Ecv) as (HKp & _).
    unfold Cc. rewrite HKp, <- (app_nil_r (rep [S1] (S j))).
    exact (visP_shape j [] eq_refl).
Qed.

Lemma vis0_T : VisitsAt tm StA 0.
Proof. exists InitES. split; reflexivity. Qed.

(** ** The closer *)

Definition iqh (m : TM) : Prop :=
  NonHalt m /\ QHBound 2000 m /\ QuasiHaltsSt m.

Theorem kpwallscan_qh : iqh tm.
Proof.
  destruct (glue_qh_quiet tm Cc p0 StA t0 0 Hboot lap_Q
              (fun p q _ Hq => vis_T p q Hq) vis0_T Hbq)
    as (Hnh & Hqb & Hqh).
  split; [exact Hnh | split; [| exact Hqh]].
  apply (qhbound_mono 1 2000); [lia | exact Hqb].
Qed.

End KpWallScan.
