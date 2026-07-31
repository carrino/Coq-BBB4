(** * Ter3WallB: the BASE-THREE wall bouncer whose OUTWARD sweep alternates.

    The second base-3 shape among the three-state core rows, after
    [Counters/Ter3Wall.v].  Its three defined states are

      qW  0 -> 0 L qW     qW  1 -> 1 R qX      (the return sweep, and the wall)
      qX  0 -> 1 L qW     qX  1 -> 0 R qY      (clear, and the even stop)
      qY  0 -> 1 L qX     qY  1 -> 0 R qX      (clear, and the odd stop)

    over the 2-cell digit words

      digit 0 = [S0; S0]     digit 1 = [S1; S0]     digit 2 = [S1; S1]

    -- the same radix as [Ter3Wall] but a different alphabet, and the
    increment writes its fresh [S1] in the digit's FIRST cell ([00 -> 10])
    where [Ter3Wall]'s writes it in the second ([00 -> 01]).  Measured by
    [tools/counters/radix_infer.py]: [4j + 2] and [4j + 4] on the two
    interior branches.

    ** The parity IS the branch

    The outward clear alternates [qX]/[qY], one cell each, and what stops it
    is the first clear cell.  A digit 0 stop is [S0;S0], so the run of set
    cells has EVEN length and the sweep arrives in [qX], which sets one cell
    and turns: [00 -> 10].  A digit 1 stop is [S1;S0], so the run is ODD and
    the sweep arrives in [qY], which sets the stop's cell, steps back onto
    the cell it just cleared and sets that too: [10 -> 11].  Both cost
    [2k + 2] steps in the run length [k].  So the two interior branches of
    base 3 are not two lap lemmas here -- they are the two PARITIES of one,
    and the closer states them as [lapE] and [lapO].

    Overflow is [lapE] at [w = []] ([chd [] = S0]); it closes one trailing
    blank short of the anchor, which [lift] cannot see.

    ** Why this is a QUASIHALTING closer

    [StA] fires once, at index 0, and is the target of no transition, so the
    machine quasihalts with score 1 and [NeverQuasiHaltsSt] is FALSE for it.
    The theorem is the census R_QH triple, via
    [Counters/LapGlueIx.glue_qh_quiet_ix]; the [AvoidRun] premise comes free
    from [Checkers/ReachStI.inv_csteps_all].

    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)

From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import ReachStI.
From BBB4.Counters Require Import WTape LapGlueQuiet LapGlueIx TernCounter.
Import ListNotations.

(** The trichotomy this shape's lap consumes.  [Ter3Wall]'s [TerStep] states
    the stop digit's rewrite in its own alphabet; this is the same three
    cases in THIS one, and the two interior cases differ by the PARITY of the
    set-cell run rather than by which lap lemma applies. *)
Definition TerStepB (Wf : tern -> list Sym) (nx : tern -> tern) : Prop :=
  forall t,
    (exists i u, Wf t = rep [S1] (2 * i) ++ [S0; S0] ++ u
            /\ Wf (nx t) = rep [S0] (2 * i) ++ [S1; S0] ++ u)
    \/ (exists i u, Wf t = rep [S1] (S (2 * i)) ++ [S0] ++ u
              /\ Wf (nx t) = rep [S0] (2 * i) ++ [S1; S1] ++ u)
    \/ (exists i, Wf t = rep [S1] (2 * i)
            /\ Wf (nx t) = rep [S0] (2 * i) ++ [S1; S0]).

(** The instance these rows use: digits [00]/[10]/[11], no terminator.
    (The terminator scheme of [TernCounter] does NOT fit this shape -- its
    overflow leaves an odd set-cell run whose lap sets two cells, where the
    increment wants a fresh digit 0 past the top.) *)
Lemma ter_stepB_nil : TerStepB (Tw [S0;S0] [S1;S0] [S1;S1] []) tsucc.
Proof.
  intro t. destruct (tview t) as [j r] eqn:Ev. destruct r as [[b t']|].
  - destruct b.
    + right; left. exists j, (Tw [S0;S0] [S1;S0] [S1;S1] [] t').
      destruct (tview_some1 [S0;S0] [S1;S0] [S1;S1] [] t j t' Ev) as (H1 & H2 & _).
      rewrite H1, H2, !rep_two.
      replace (2 * j) with (j + j) by lia. split; [| reflexivity].
      cbn [app]. rewrite rep_succ_r. reflexivity.
    + left. exists j, (Tw [S0;S0] [S1;S0] [S1;S1] [] t').
      destruct (tview_some0 [S0;S0] [S1;S0] [S1;S1] [] t j t' Ev) as (H1 & H2 & _).
      rewrite H1, H2, !rep_two.
      replace (2 * j) with (j + j) by lia. split; reflexivity.
  - right; right. exists j.
    destruct (tview_none [S0;S0] [S1;S0] [S1;S1] [] t j Ev) as (H1 & H2 & _).
    rewrite H1, H2, !rep_two, !app_nil_r.
    replace (2 * j) with (j + j) by lia. split; reflexivity.
Qed.

Section Ter3WallB.

Variable tm : TM.
Variable qW qX qY : St.
Variable t0 : nat.
Variable i0 : tern.

Hypothesis HW0 : tm qW S0 = Some (mkTrans S0 DL qW).
Hypothesis HW1 : tm qW S1 = Some (mkTrans S1 DR qX).
Hypothesis HX0 : tm qX S0 = Some (mkTrans S1 DL qW).
Hypothesis HX1 : tm qX S1 = Some (mkTrans S0 DR qY).
Hypothesis HY0 : tm qY S0 = Some (mkTrans S1 DL qX).
Hypothesis HY1 : tm qY S1 = Some (mkTrans S0 DR qX).

Hypothesis Hcover : forall q, q = StA \/ q = qW \/ q = qX \/ q = qY.
Hypothesis HWA : qW <> StA.
Hypothesis HXA : qX <> StA.
Hypothesis HYA : qY <> StA.

Hypothesis Hinv : inv_ok tm [qW; qX; qY] = true.

Variable Wf : tern -> list Sym.
Variable nx : tern -> tern.
Hypothesis Hstep : TerStepB Wf nx.

Hypothesis Hboot : stepn tm t0 InitES = Some (lift (qW, ([], S1, Wf i0))).
Hypothesis Hbq : forall n c, 0 < n < t0 ->
  stepn tm n InitES = Some c -> fst c <> StA.

Definition Cc (t : tern) : cconf := (qW, ([], S1, Wf t)).

(** ** Units *)

Lemma uP1 : forall L R, csteps tm 1 (qW,(L,S1,R)) = Some (qX,(S1::L,chd R,ctl R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HW1.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

Lemma uRET : forall L R, csteps tm 1 (qW,(L,S0,R)) = Some (qW,(ctl L,chd L,S0::R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HW0.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

Lemma uCX : forall L R, csteps tm 1 (qX,(L,S1,R)) = Some (qY,(S0::L,chd R,ctl R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HX1.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

Lemma uCY : forall L R, csteps tm 1 (qY,(L,S1,R)) = Some (qX,(S0::L,chd R,ctl R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HY1.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

(** The EVEN stop: [qX] on a clear cell sets it and turns left. *)
Lemma uSX : forall L R, csteps tm 1 (qX,(L,S0,R)) = Some (qW,(ctl L,chd L,S1::R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HX0.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

(** The ODD stop: [qY] sets it and steps back onto the cell it just cleared. *)
Lemma uSY : forall L R, csteps tm 1 (qY,(L,S0,R)) = Some (qX,(ctl L,chd L,S1::R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HY0.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

(** ** Phases *)

Lemma rep_cons : forall (u : list Sym) k L,
  rep u k ++ (u ++ L) = u ++ (rep u k ++ L).
Proof.
  intros u k L. rewrite app_assoc, rep_shift, <- app_assoc. reflexivity.
Qed.

(** The outward clear, two cells at a time: [qX] to [qY] and back. *)
Lemma phCLR : forall i L w,
  csteps tm (2 * i) (qX,(L,chd (rep [S1] (2 * i) ++ w),
                            ctl (rep [S1] (2 * i) ++ w)))
    = Some (qX,(rep [S0] (2 * i) ++ L,chd w,ctl w)).
Proof.
  induction i as [|i IH]; intros L w; [reflexivity |].
  replace (rep [S1] (2 * S i) ++ w)
    with (S1 :: S1 :: (rep [S1] (2 * i) ++ w))
    by (replace (2 * S i) with (S (S (2 * i))) by lia;
        cbn [rep app]; reflexivity).
  cbn [chd ctl].
  replace (2 * S i) with (1 + (1 + 2 * i)) by lia.
  rewrite csteps_add, (uCX L (S1 :: (rep [S1] (2 * i) ++ w))).
  cbn [chd ctl].
  rewrite csteps_add, (uCY (S0 :: L) (rep [S1] (2 * i) ++ w)), IH.
  replace (rep [S0] (1 + (1 + 2 * i)) ++ L)
    with ([S0] ++ ([S0] ++ (rep [S0] (2 * i) ++ L)))
    by (cbn [rep app]; reflexivity).
  change (S0 :: (S0 :: L)) with ([S0] ++ ([S0] ++ L)).
  rewrite (rep_cons [S0] (2 * i) ([S0] ++ L)),
          (rep_cons [S0] (2 * i) L). reflexivity.
Qed.

(** The return sweep: [k] clear cells cross the head leftward, in [qW]. *)
Lemma phRET : forall k L R,
  csteps tm k (qW,(rep [S0] k ++ L,S0,R)) = Some (qW,(L,S0,rep [S0] k ++ R)).
Proof.
  induction k as [|k IH]; intros L R; [reflexivity |].
  cbn [rep app].
  replace (S k) with (1 + k) at 1 by lia.
  rewrite csteps_add, (uRET (S0 :: (rep [S0] k ++ L)) R).
  cbn [chd ctl]. rewrite IH.
  cbn [rep]. change (S0 :: R) with ([S0] ++ R).
  rewrite (rep_cons [S0] k R). reflexivity.
Qed.

(** Return, then pop the wall: this IS the next anchor. *)
Lemma phW : forall m R,
  csteps tm (m + 1) (qW,(rep [S0] m ++ [S1],S0,R))
    = Some (qW,([],S1,S0 :: rep [S0] m ++ R)).
Proof.
  intros m R.
  rewrite csteps_add, (phRET m [S1] R), (uRET [S1] (rep [S0] m ++ R)).
  cbn [chd ctl]. reflexivity.
Qed.

(** [qX] sets the stop cell and the return runs home to the wall. *)
Lemma phHOME : forall k R,
  csteps tm (1 + k) (qX,(rep [S0] k ++ [S1],S0,R))
    = Some (qW,([],S1,rep [S0] k ++ S1 :: R)).
Proof.
  intros [|m] R.
  - cbn [rep app Nat.add]. rewrite (uSX [S1] R).
    cbn [chd ctl rep app]. reflexivity.
  - replace (1 + S m) with (1 + (m + 1)) by lia.
    cbn [rep app].
    rewrite csteps_add, (uSX (S0 :: (rep [S0] m ++ [S1])) R).
    cbn [chd ctl]. rewrite (phW m (S1 :: R)). cbn [rep app]. reflexivity.
Qed.

(** ** The lap, in its two parities *)

Lemma lapE : forall i w, chd w = S0 ->
  exists n, 0 < n /\
  csteps tm n (qW,([],S1,rep [S1] (2 * i) ++ w))
    = Some (qW,([],S1,rep [S0] (2 * i) ++ S1 :: ctl w)).
Proof.
  intros i w Hw. exists (1 + (2 * i + (1 + 2 * i))). split; [lia |].
  rewrite csteps_add, (uP1 [] (rep [S1] (2 * i) ++ w)).
  rewrite csteps_add, (phCLR i [S1] w), Hw.
  apply (phHOME (2 * i) (ctl w)).
Qed.

Lemma lapO : forall i w, chd w = S0 ->
  exists n, 0 < n /\
  csteps tm n (qW,([],S1,rep [S1] (S (2 * i)) ++ w))
    = Some (qW,([],S1,rep [S0] (2 * i) ++ S1 :: S1 :: ctl w)).
Proof.
  intros i w Hw.
  exists (1 + (2 * i + (1 + (1 + (1 + 2 * i))))). split; [lia |].
  replace (rep [S1] (S (2 * i)) ++ w)
    with (rep [S1] (2 * i) ++ (S1 :: w))
    by (change (S1 :: w) with ([S1] ++ w);
        rewrite (rep_cons [S1] (2 * i) w); reflexivity).
  rewrite csteps_add, (uP1 [] (rep [S1] (2 * i) ++ (S1 :: w))).
  rewrite csteps_add, (phCLR i [S1] (S1 :: w)).
  cbn [chd ctl].
  rewrite csteps_add, (uCX (rep [S0] (2 * i) ++ [S1]) w), Hw.
  rewrite csteps_add, (uSY (S0 :: (rep [S0] (2 * i) ++ [S1])) (ctl w)).
  cbn [chd ctl].
  apply (phHOME (2 * i) (S1 :: ctl w)).
Qed.

(** ** The lap on the counter *)

Lemma lap_Q : forall t,
  exists n c', csteps tm n (Cc t) = Some c'
               /\ lift c' = lift (Cc (nx t)) /\ 0 < n
               /\ AvoidRun tm StA n (Cc t).
Proof.
  intro t.
  assert (Havoid : forall n, AvoidRun tm StA n (Cc t)).
  { intros n m cm _ Hst.
    assert (Hin : InAllowed [qW; qX; qY] (Cc t)) by (cbn; auto).
    pose proof (inv_csteps_all tm [qW; qX; qY] Hinv m (Cc t) cm Hin Hst) as H.
    unfold InAllowed in H. cbn in H.
    destruct H as [<- | [<- | [<- | []]]]; auto. }
  unfold Cc.
  destruct (Hstep t) as [(i & u & H1 & H2) | [(i & u & H1 & H2) | (i & H1 & H2)]].
  - destruct (lapE i (S0 :: S0 :: u) eq_refl) as (n & Hn & Hrun).
    exists n. eexists. split; [rewrite H1; exact Hrun |].
    split; [| split; [exact Hn | apply Havoid]].
    rewrite H2. cbn [ctl app]. reflexivity.
  - destruct (lapO i (S0 :: u) eq_refl) as (n & Hn & Hrun).
    exists n. eexists. split; [rewrite H1; exact Hrun |].
    split; [| split; [exact Hn | apply Havoid]].
    rewrite H2. cbn [ctl app]. reflexivity.
  - (* overflow: one trailing blank short of the anchor, invisible to lift *)
    destruct (lapE i [] eq_refl) as (n & Hn & Hrun).
    exists n. eexists. split.
    { rewrite H1, <- (app_nil_r (rep [S1] (2 * i))). exact Hrun. }
    split; [| split; [exact Hn | apply Havoid]].
    rewrite H2. cbn [ctl app].
    replace (rep [S0] (2 * i) ++ [S1; S0])
      with ((rep [S0] (2 * i) ++ [S1]) ++ [S0])
      by (rewrite <- app_assoc; reflexivity).
    rewrite lift_app_blank. reflexivity.
Qed.

(** ** Visit witnesses

    [qW] is the anchor and [qX] is one step in.  [qY] is two steps in
    whenever the set-cell run is non-empty; when it is empty the lap sets the
    low digit's first cell, so ONE lap later the run is non-empty.  Both
    cases are [lapE] at [i = 0], so the witness needs no case analysis on the
    counter at all. *)
Lemma visY_shape : forall v, chd v = S1 ->
  exists k c, csteps tm k (qW,([],S1,v)) = Some c /\ fst c = qY.
Proof.
  intros v Hv.
  exists (1 + 1), (qY,(S0 :: [S1],chd (ctl v),ctl (ctl v))).
  split; [| reflexivity].
  rewrite csteps_add, (uP1 [] v), Hv. apply (uCX [S1] (ctl v)).
Qed.

Lemma visY_from : forall v,
  exists k c, csteps tm k (qW,([],S1,v)) = Some c /\ fst c = qY.
Proof.
  intro v. destruct (chd v) eqn:Hv.
  - destruct (lapE 0 v Hv) as (n & _ & Hr).
    replace (2 * 0) with 0 in Hr by lia. cbn [rep app] in Hr.
    destruct (visY_shape (S1 :: ctl v) eq_refl) as (k & c & Hk & Hc).
    exists (n + k), c. split; [| exact Hc].
    rewrite csteps_add, Hr. exact Hk.
  - apply visY_shape; exact Hv.
Qed.

Lemma vis_T : forall t q, q <> StA ->
  exists k c, csteps tm k (Cc t) = Some c /\ fst c = q.
Proof.
  intros t q Hq. unfold Cc.
  destruct (Hcover q) as [-> | [-> | [-> | ->]]];
    [contradiction Hq; reflexivity | | |].
  - exists 0, (qW,([],S1,Wf t)). split; reflexivity.
  - exists 1, (qX,([S1],chd (Wf t),ctl (Wf t))). split;
      [apply (uP1 [] (Wf t)) | reflexivity].
  - apply visY_from.
Qed.

Lemma vis0_T : VisitsAt tm StA 0.
Proof. exists InitES. split; reflexivity. Qed.

(** ** The closer *)

Definition iqh (m : TM) : Prop :=
  NonHalt m /\ QHBound 2000 m /\ QuasiHaltsSt m.

Theorem ter3wallb_qh : iqh tm.
Proof.
  destruct (glue_qh_quiet_ix tm tern nx Cc i0 StA t0 0 Hboot lap_Q
              (fun t q Hq => vis_T t q Hq) vis0_T Hbq)
    as (Hnh & Hqb & Hqh).
  split; [exact Hnh | split; [| exact Hqh]].
  apply (qhbound_mono 1 2000); [lia | exact Hqb].
Qed.

End Ter3WallB.
