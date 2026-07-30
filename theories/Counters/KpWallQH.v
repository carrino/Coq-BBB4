(** * KpWallQH: the plain-counter WALL bouncer, as a quasihalting closer.

    A [1RB---] row whose three defined states form this shape:

      qW  0 -> 0 L qW     qW  1 -> 1 R qR1      (the wall / return sweep)
      qR1 0 -> 1 L qW     qR1 1 -> 0 R qR2      (the carry ripple, and its stop)
      qR2 0 -> 1 L qW     qR2 1 -> 0 R qR1

    is a plain base-2 counter ([KpCounter.Kp]) read at the anchor

      Cc p = (qW, ([], S1, Kp p))

    -- the head sitting ON the wall cell, the counter to its right, nothing
    to its left.  One lap is

      P1 . RIP^j . STP . RET^j

    ([qW] turns right off the wall; [qR1]/[qR2] alternate rightward clearing
    the carry run; the first blank stops them and turns left; [qW] sweeps
    back over the zeros just written until it pops the wall and IS the next
    anchor).  Measured at 2 + 2j steps, but the count is never written down:
    [LapGlue]'s lap obligation is existential in it.

    ** Why this is a QUASIHALTING closer

    On these rows [StA] fires once, at index 0, and is the target of no
    transition -- so the machine genuinely quasihalts with score 1 and
    [NeverQuasiHaltsSt] is FALSE for it.  The theorem is the census R_QH
    triple, via [LapGlueQuiet.glue_qh_quiet] with [qa = StA] and [s0 = 0].
    Its [AvoidRun] premise -- no lap may touch [StA] -- comes free from
    [Checkers/ReachStI.inv_csteps_all]: [[qW; qR1; qR2]] is total and closed,
    so no run from the anchor can reach [StA] at all.

    ** Why the alternation is handled existentially

    [qR1] and [qR2] agree on [S0] and differ only in each other's names on
    [S1], so the ripple flips between them and its parity is not determined
    by [j].  Nothing downstream cares: the stop step is the same from either.
    So the ripple lemma carries "the state is still one of the two" rather
    than naming it -- which is what lets ONE lap lemma cover both parities,
    and both the interior and the overflow branch ([chd [] = S0] makes the
    blank past the end of the counter behave exactly like the clear bit that
    stops an interior carry).

    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import ReachStI.
From BBB4.Counters Require Import WTape LapGlue LapGlueQuiet MonoCounter KpCounter.
Import ListNotations.

Section KpWallQH.

Variable tm : TM.
Variable qW qR1 qR2 : St.
Variable t0 : nat.

Hypothesis HW0 : tm qW  S0 = Some (mkTrans S0 DL qW).
Hypothesis HW1 : tm qW  S1 = Some (mkTrans S1 DR qR1).
Hypothesis H10 : tm qR1 S0 = Some (mkTrans S1 DL qW).
Hypothesis H11 : tm qR1 S1 = Some (mkTrans S0 DR qR2).
Hypothesis H20 : tm qR2 S0 = Some (mkTrans S1 DL qW).
Hypothesis H21 : tm qR2 S1 = Some (mkTrans S0 DR qR1).

(** The three roles are exactly the non-[StA] states, and [StA] is not one
    of them: that is what makes [StA] the quiet state. *)
Hypothesis Hcover : forall q, q = StA \/ q = qW \/ q = qR1 \/ q = qR2.
Hypothesis HWA : qW <> StA.
Hypothesis HR1A : qR1 <> StA.
Hypothesis HR2A : qR2 <> StA.

(** Totality and closure of the role set -- one [vm_compute] per row. *)
Hypothesis Hinv : inv_ok tm [qW; qR1; qR2] = true.

(** The bootstrap, and the checked [StA]-free window below it. *)
Hypothesis Hboot : stepn tm t0 InitES = Some (lift (qW, ([], S1, Kp 1))).
Hypothesis Hbq : forall n c, 0 < n < t0 -> stepn tm n InitES = Some c -> fst c <> StA.

Definition Cc (p : positive) : cconf := (qW, ([], S1, Kp p)).

(** ** Units *)

Lemma uP1 : forall L R, csteps tm 1 (qW,(L,S1,R)) = Some (qR1,(S1::L,chd R,ctl R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HW1.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

(** The return sweep pops whatever is nearest on the left; when that is the
    wall it becomes the head, which is the next anchor. *)
Lemma uRET : forall L R, csteps tm 1 (qW,(L,S0,R)) = Some (qW,(ctl L,chd L,S0::R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HW0.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

Lemma uSTP : forall q L R, (q = qR1 \/ q = qR2) ->
  csteps tm 1 (q,(L,S0,R)) = Some (qW,(ctl L,chd L,S1::R)).
Proof.
  intros q L R [-> | ->]; cbn [csteps cstep]; [rewrite H10 | rewrite H20];
    cbn [t_next t_dir t_write ctape_move]; reflexivity.
Qed.

Lemma uRIP1 : forall L R,
  csteps tm 1 (qR1,(L,S1,R)) = Some (qR2,(S0::L,chd R,ctl R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite H11.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

Lemma uRIP : forall q L R, (q = qR1 \/ q = qR2) ->
  exists q', (q' = qR1 \/ q' = qR2) /\
  csteps tm 1 (q,(L,S1,R)) = Some (q',(S0::L,chd R,ctl R)).
Proof.
  intros q L R [-> | ->].
  - exists qR2. split; [auto | apply uRIP1].
  - exists qR1. split; [auto |].
    cbn [csteps cstep]. rewrite H21.
    cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

(** ** Phases *)

Lemma rep_cons : forall (u : list Sym) k L,
  rep u k ++ (u ++ L) = u ++ (rep u k ++ L).
Proof.
  intros u k L. rewrite app_assoc, rep_shift, <- app_assoc. reflexivity.
Qed.

(** The carry ripple.  What is carried is "still one of the two". *)
Lemma phRIP : forall k q L w, (q = qR1 \/ q = qR2) ->
  exists q', (q' = qR1 \/ q' = qR2) /\
  csteps tm k (q,(L,S1,rep [S1] k ++ w)) = Some (q',(rep [S0] k ++ L,S1,w)).
Proof.
  induction k as [|k IH]; intros q L w Hq.
  - exists q. split; [exact Hq | reflexivity].
  - destruct (uRIP q L (S1 :: (rep [S1] k ++ w)) Hq) as (q2 & Hq2 & Hstep).
    cbn [chd ctl] in Hstep.
    destruct (IH q2 (S0::L) w Hq2) as (q' & Hq' & Hrun).
    exists q'. split; [exact Hq' |].
    cbn [rep app].
    replace (S k) with (1 + k) at 1 by lia.
    rewrite csteps_add, Hstep, Hrun.
    change (S0 :: L) with ([S0] ++ L).
    rewrite (rep_cons [S0] k L). reflexivity.
Qed.

(** The return sweep: [k] zeros cross the head, which stays [S0]. *)
Lemma phRET : forall k L R,
  csteps tm k (qW,(rep [S0] k ++ L,S0,R)) = Some (qW,(L,S0,rep [S0] k ++ R)).
Proof.
  induction k as [|k IH]; intros L R; [reflexivity |].
  assert (Hstep : csteps tm 1 (qW,(rep [S0] (S k) ++ L,S0,R))
                  = Some (qW,(rep [S0] k ++ L,S0,S0::R))).
  { cbn [rep app]. rewrite (uRET (S0 :: (rep [S0] k ++ L)) R). reflexivity. }
  replace (S k) with (1 + k) at 1 by lia.
  rewrite csteps_add, Hstep, IH.
  cbn [rep]. change (S0 :: R) with ([S0] ++ R).
  rewrite (rep_cons [S0] k R). reflexivity.
Qed.

(** ** The lap

    [w] is what lies beyond the carry run: [S0 :: Kp q0] in the interior,
    [[]] at overflow.  [chd [] = S0] makes those the same stop. *)
Lemma lap_shape : forall k w, chd w = S0 ->
  exists n, 0 < n /\
  csteps tm n (qW,([],S1,rep [S1] k ++ w))
    = Some (qW,([],S1,rep [S0] k ++ S1 :: ctl w)).
Proof.
  intros k w Hw. destruct k as [|k'].
  - cbn [rep app]. exists 2. split; [lia |].
    change 2 with (1 + 1).
    eapply csteps_chain. { apply (uP1 [] w). }
    rewrite Hw. apply (uSTP qR1 [S1] (ctl w) (or_introl eq_refl)).
  - destruct (phRIP k' qR1 [S1] w (or_introl eq_refl)) as (q' & Hq' & Hrip).
    exists (1 + (k' + (1 + (1 + (k' + 1))))). split; [lia |].
    cbn [rep app].
    eapply csteps_chain. { apply (uP1 [] (S1 :: (rep [S1] k' ++ w))). }
    cbn [chd ctl].
    eapply csteps_chain. { exact Hrip. }
    destruct (uRIP q' (rep [S0] k' ++ [S1]) w Hq') as (q2 & Hq2 & Hlast).
    eapply csteps_chain. { exact Hlast. }
    rewrite Hw.
    eapply csteps_chain.
    { apply (uSTP q2 (S0 :: (rep [S0] k' ++ [S1])) (ctl w) Hq2). }
    cbn [ctl chd].
    eapply csteps_chain. { apply (phRET k' [S1] (S1 :: ctl w)). }
    rewrite (uRET [S1] (rep [S0] k' ++ S1 :: ctl w)). reflexivity.
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
  assert (Hin : InAllowed [qW; qR1; qR2] (Cc p)) by (cbn; auto).
  pose proof (inv_csteps_all tm [qW; qR1; qR2] Hinv m (Cc p) cm Hin Hst) as H.
  unfold InAllowed in H. cbn in H.
  destruct H as [<- | [<- | [<- | []]]]; auto.
Qed.

Lemma lap_Q : forall p, (1 <= p)%positive ->
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

    [qW] is the anchor, [qR1] is one step in.  [qR2] needs a carry run, so
    when the low bit is clear the witness is taken in the NEXT lap -- whose
    low bit is set, because incrementing an even number sets it. *)
Lemma vis_T : forall p q, q <> StA ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q Hq. unfold Cc.
  destruct (Hcover q) as [-> | [-> | [-> | ->]]]; [contradiction Hq; reflexivity | | |].
  - exists 0, (qW,([],S1,Kp p)). split; reflexivity.
  - exists 1, (qR1,([S1],chd (Kp p),ctl (Kp p))). split;
      [apply (uP1 [] (Kp p)) | reflexivity].
  - destruct (cview p) as [j oq] eqn:Ecv.
    destruct j as [|j'].
    + destruct oq as [q0|].
      * destruct (cview_some_K p 0 q0 Ecv) as (HKp & _).
        exists 4, (qR2,([S0;S1],chd (Kp q0),ctl (Kp q0))). split; [| reflexivity].
        rewrite HKp. cbn [rep app].
        change 4 with (1 + (1 + (1 + 1))).
        eapply csteps_chain. { apply (uP1 [] (S0 :: Kp q0)). }
        cbn [chd ctl].
        eapply csteps_chain. { apply (uSTP qR1 [S1] (Kp q0) (or_introl eq_refl)). }
        cbn [ctl chd].
        eapply csteps_chain. { apply (uP1 [] (S1 :: Kp q0)). }
        cbn [chd ctl]. apply (uRIP1 [S1] (Kp q0)).
      * exfalso. destruct p; simpl in Ecv;
          [destruct (cview p); discriminate | discriminate | discriminate].
    + destruct oq as [q0|].
      * destruct (cview_some_K p (S j') q0 Ecv) as (HKp & _).
        set (w := rep [S1] j' ++ S0 :: Kp q0).
        exists 2, (qR2,([S0;S1],chd w,ctl w)). split; [| reflexivity].
        rewrite HKp. cbn [rep app]. fold w.
        change 2 with (1 + 1).
        eapply csteps_chain. { apply (uP1 [] (S1 :: w)). }
        cbn [chd ctl]. apply (uRIP1 [S1] w).
      * destruct (cview_none_K p j' Ecv) as (HKp & _).
        set (w := rep [S1] j').
        exists 2, (qR2,([S0;S1],chd w,ctl w)). split; [| reflexivity].
        rewrite HKp. cbn [rep]. fold w.
        change 2 with (1 + 1).
        eapply csteps_chain. { apply (uP1 [] (S1 :: w)). }
        cbn [chd ctl]. apply (uRIP1 [S1] w).
Qed.

Lemma vis0_T : VisitsAt tm StA 0.
Proof. exists InitES. split; reflexivity. Qed.

(** ** The closer *)

Definition iqh (m : TM) : Prop :=
  NonHalt m /\ QHBound 2000 m /\ QuasiHaltsSt m.

Theorem kpwall_qh : iqh tm.
Proof.
  destruct (glue_qh_quiet tm Cc 1 StA t0 0 Hboot lap_Q
              (fun p q _ Hq => vis_T p q Hq) vis0_T Hbq)
    as (Hnh & Hqb & Hqh).
  split; [exact Hnh | split; [| exact Hqh]].
  apply (qhbound_mono 1 2000); [lia | exact Hqb].
Qed.

End KpWallQH.
