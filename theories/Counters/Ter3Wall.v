(** * Ter3Wall: the BASE-THREE wall bouncer, as a quasihalting closer.

    A [1RB---] row whose three defined states form this shape:

      qW  0 -> 0 L qW     qW  1 -> 1 R qC      (the return sweep, and the wall)
      qC  0 -> 0 R qD     qC  1 -> 0 R qC      (the outward clear, and its stop)
      qD  0 -> 1 L qW     qD  1 -> 1 L qD      (the digit step up, and its turn)

    is a BASE-THREE counter, read at the anchor

      Cc t = (qW, ([], S1, Wf t))

    -- the head sitting ON the wall cell, the counter to its right, nothing
    to its left -- over the 2-cell digit words

      digit 0 = [S0; S0]     digit 1 = [S0; S1]     digit 2 = [S1; S1].

    [tools/counters/radix_infer.py] measured exactly this on
    [1RB---_0LB1RC_0RD0RC_1LB1LD]: 10^4 consecutive anchor snapshots and a
    lap of [4j + 4] in the carry length.  Read at base 2 the same row looks
    like a [Theta(3^j)] "EXP3" -- which is what [tools/closeout/residue_map.tsv]
    calls it, and why every base-2 emitter in the tree bounces off it.

    ** One lap

      P1 . CLR^2j . STEP . END

    [qW] turns right off the wall; [qC] runs rightward clearing the carry run
    (a digit 2 is [S1;S1], so [j] digits are [2j] cells and each costs one
    step); the first clear cell stops it and turns it into [qD], which steps
    the stop digit up ([00 -> 01] in one step, [01 -> 11] in two) and turns
    left; [qW] sweeps back over the cells just cleared until it pops the wall
    and IS the next anchor.  [4j + 4] steps on every branch, but the count is
    never written down: the lap obligation is existential in it.

    ** The counter enters as DATA

    The closer knows nothing about numerals: it takes a word function [Wf]
    and an increment [nx] satisfying [TernCounter.TerStep], which is the
    trichotomy of tape shapes a lap can meet --

      rep [S1] m ++ [S0;S0] ++ u  ->  rep [S0] (S m) ++ [S1] ++ u   (stop 0)
      rep [S1] m ++ [S0;S1] ++ u  ->  rep [S0] m ++ [S1;S1] ++ u    (stop 1)
      rep [S1] m                  ->  rep [S0] (S m) ++ [S1]        (overflow)

    Base 3 splits the interior in two -- the stop digit is 0 (one [qD] step)
    or 1 (two) -- where base 2 has a single one.  Overflow needs no third lap
    lemma: [chd [] = S0], so the blank pair past the counter's top digit
    behaves exactly like a stop digit 0, and [lap_shape0] at [w = []] closes
    it EXACTLY.  Both base-3 schemes of [TernCounter] -- with and without a
    terminator cell past the top digit ([ter_step_nil] / [ter_step_one]) --
    satisfy [TerStep], so this one closer serves both.

    ** Why this is a QUASIHALTING closer

    On these rows [StA] fires once, at index 0, and is the target of no
    transition -- so the machine genuinely quasihalts with score 1 and
    [NeverQuasiHaltsSt] is FALSE for it.  The theorem is the census R_QH
    triple, via [Counters/LapGlueIx.glue_qh_quiet_ix] -- [LapGlueQuiet] over
    an arbitrary index, because a base-3 counter has no [positive] to index
    by.  The [AvoidRun] premise comes free from
    [Checkers/ReachStI.inv_csteps_all]: [[qW; qC; qD]] is total and closed,
    so no run from the anchor can reach [StA] at all.

    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)

From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import ReachStI.
From BBB4.Counters Require Import WTape LapGlueQuiet LapGlueIx TernCounter.
Import ListNotations.

Section Ter3Wall.

Variable tm : TM.
Variable qW qC qD : St.
Variable t0 : nat.
Variable i0 : tern.

Hypothesis HW0 : tm qW S0 = Some (mkTrans S0 DL qW).
Hypothesis HW1 : tm qW S1 = Some (mkTrans S1 DR qC).
Hypothesis HC0 : tm qC S0 = Some (mkTrans S0 DR qD).
Hypothesis HC1 : tm qC S1 = Some (mkTrans S0 DR qC).
Hypothesis HD0 : tm qD S0 = Some (mkTrans S1 DL qW).
Hypothesis HD1 : tm qD S1 = Some (mkTrans S1 DL qD).

(** The three roles are exactly the non-[StA] states, and [StA] is not one
    of them: that is what makes [StA] the quiet state. *)
Hypothesis Hcover : forall q, q = StA \/ q = qW \/ q = qC \/ q = qD.
Hypothesis HWA : qW <> StA.
Hypothesis HCA : qC <> StA.
Hypothesis HDA : qD <> StA.

(** Totality and closure of the role set -- one [vm_compute] per row. *)
Hypothesis Hinv : inv_ok tm [qW; qC; qD] = true.

(** The counter, as DATA: a word function and an increment satisfying
    [TernCounter.TerStep] -- the three tape shapes a lap can meet.  Both
    base-3 schemes ([ter_step_nil] and [ter_step_one]) satisfy it, so one
    closer serves both. *)
Variable Wf : tern -> list Sym.
Variable nx : tern -> tern.
Hypothesis Hstep : TerStep Wf nx.

(** The bootstrap, and the checked [StA]-free window below it. *)
Hypothesis Hboot : stepn tm t0 InitES = Some (lift (qW, ([], S1, Wf i0))).
Hypothesis Hbq : forall n c, 0 < n < t0 ->
  stepn tm n InitES = Some c -> fst c <> StA.

Definition Cc (t : tern) : cconf := (qW, ([], S1, Wf t)).

(** ** Units *)

Lemma uP1 : forall L R, csteps tm 1 (qW,(L,S1,R)) = Some (qC,(S1::L,chd R,ctl R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HW1.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

Lemma uRET : forall L R, csteps tm 1 (qW,(L,S0,R)) = Some (qW,(ctl L,chd L,S0::R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HW0.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

Lemma uCLR : forall L R, csteps tm 1 (qC,(L,S1,R)) = Some (qC,(S0::L,chd R,ctl R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HC1.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

Lemma uSTP : forall L R, csteps tm 1 (qC,(L,S0,R)) = Some (qD,(S0::L,chd R,ctl R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HC0.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

Lemma uUP : forall L R, csteps tm 1 (qD,(L,S1,R)) = Some (qD,(ctl L,chd L,S1::R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HD1.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

Lemma uTURN : forall L R, csteps tm 1 (qD,(L,S0,R)) = Some (qW,(ctl L,chd L,S1::R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HD0.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

(** ** Phases *)

Lemma rep_cons : forall (u : list Sym) k L,
  rep u k ++ (u ++ L) = u ++ (rep u k ++ L).
Proof.
  intros u k L. rewrite app_assoc, rep_shift, <- app_assoc. reflexivity.
Qed.

(** The outward clear: [k] set cells cross the head rightward, in [qC]. *)
Lemma phCLR : forall k L w,
  csteps tm k (qC,(L,chd (rep [S1] k ++ w),ctl (rep [S1] k ++ w)))
    = Some (qC,(rep [S0] k ++ L,chd w,ctl w)).
Proof.
  induction k as [|k IH]; intros L w; [reflexivity |].
  cbn [rep app chd ctl].
  replace (S k) with (1 + k) at 1 by lia.
  rewrite csteps_add, (uCLR L (rep [S1] k ++ w)), IH.
  cbn [rep]. change (S0 :: L) with ([S0] ++ L).
  rewrite (rep_cons [S0] k L). reflexivity.
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

(** [qD] turns left off the stop digit and the return runs to the wall. *)
Lemma phEND : forall k R,
  csteps tm (1 + k) (qD,(rep [S0] k ++ [S1],S0,R))
    = Some (qW,([],S1,rep [S0] k ++ S1 :: R)).
Proof.
  intros [|k] R.
  - cbn [rep app Nat.add]. rewrite (uTURN [S1] R).
    cbn [chd ctl rep app]. reflexivity.
  - replace (1 + S k) with (1 + (k + 1)) by lia.
    cbn [rep app].
    rewrite csteps_add, (uTURN (S0 :: (rep [S0] k ++ [S1])) R).
    cbn [chd ctl]. rewrite (phW k (S1 :: R)). cbn [rep app]. reflexivity.
Qed.

(** The head leaves the wall and clears the carry run: this prefix is common
    to every branch, and it is where [qC] and (one step later) [qD] fire. *)
Lemma runC : forall k w,
  csteps tm (1 + k) (qW,([],S1,rep [S1] k ++ w))
    = Some (qC,(rep [S0] k ++ [S1],chd w,ctl w)).
Proof.
  intros k w.
  rewrite csteps_add, (uP1 [] (rep [S1] k ++ w)).
  rewrite (phCLR k [S1] w). reflexivity.
Qed.

(** ** The lap, in its two branches

    [w] is what lies beyond the carry run.  Stop digit 0 is [S0 :: S0 :: _],
    stop digit 1 is [S0 :: S1 :: _], and overflow is [[]] -- which [chd []
    = S0] makes the same lemma as stop digit 0. *)

Lemma lap_shape0 : forall k w, chd w = S0 -> chd (ctl w) = S0 ->
  exists n, 0 < n /\
  csteps tm n (qW,([],S1,rep [S1] k ++ w))
    = Some (qW,([],S1,rep [S0] (S k) ++ S1 :: ctl (ctl w))).
Proof.
  intros k w H1 H2. exists (1 + k + (1 + (1 + S k))). split; [lia |].
  rewrite csteps_add, (runC k w), H1.
  rewrite csteps_add, (uSTP (rep [S0] k ++ [S1]) (ctl w)), H2.
  change (S0 :: (rep [S0] k ++ [S1])) with (rep [S0] (S k) ++ [S1]).
  apply (phEND (S k) (ctl (ctl w))).
Qed.

Lemma lap_shape1 : forall k w, chd w = S0 -> chd (ctl w) = S1 ->
  exists n, 0 < n /\
  csteps tm n (qW,([],S1,rep [S1] k ++ w))
    = Some (qW,([],S1,rep [S0] k ++ S1 :: S1 :: ctl (ctl w))).
Proof.
  intros k w H1 H2. exists (1 + k + (1 + (1 + (1 + k)))). split; [lia |].
  rewrite csteps_add, (runC k w), H1.
  rewrite csteps_add, (uSTP (rep [S0] k ++ [S1]) (ctl w)), H2.
  rewrite csteps_add, (uUP (S0 :: (rep [S0] k ++ [S1])) (ctl (ctl w))).
  cbn [chd ctl].
  apply (phEND k (S1 :: ctl (ctl w))).
Qed.

(** ** The lap on the counter

    [TernCounter.TerStep]'s three shapes map one-to-one onto the two lap
    lemmas: a stop digit [00] or the overflow blank run goes through
    [lap_shape0], a stop digit [01] through [lap_shape1]. *)

Lemma lap_exact : forall t, exists n c',
  csteps tm n (Cc t) = Some c' /\ c' = Cc (nx t) /\ 0 < n.
Proof.
  intro t. unfold Cc.
  destruct (Hstep t) as [(m & u & H1 & H2) | [(m & u & H1 & H2) | (m & H1 & H2)]].
  - destruct (lap_shape0 m (S0 :: S0 :: u) eq_refl eq_refl)
      as (n & Hn & Hrun).
    exists n. eexists. split; [| split; [| exact Hn]].
    + rewrite H1. exact Hrun.
    + rewrite H2. cbn [ctl app]. reflexivity.
  - destruct (lap_shape1 m (S0 :: S1 :: u) eq_refl eq_refl)
      as (n & Hn & Hrun).
    exists n. eexists. split; [| split; [| exact Hn]].
    + rewrite H1. exact Hrun.
    + rewrite H2. cbn [ctl app]. reflexivity.
  - destruct (lap_shape0 m [] eq_refl eq_refl) as (n & Hn & Hrun).
    exists n. eexists. split; [| split; [| exact Hn]].
    + rewrite H1, <- (app_nil_r (rep [S1] m)). exact Hrun.
    + rewrite H2. cbn [ctl app]. reflexivity.
Qed.

(** ** No lap touches [StA] *)

Lemma avoid_from_anchor : forall t n, AvoidRun tm StA n (Cc t).
Proof.
  intros t n m cm _ Hst.
  assert (Hin : InAllowed [qW; qC; qD] (Cc t)) by (cbn; auto).
  pose proof (inv_csteps_all tm [qW; qC; qD] Hinv m (Cc t) cm Hin Hst) as H.
  unfold InAllowed in H. cbn in H.
  destruct H as [<- | [<- | [<- | []]]]; auto.
Qed.

Lemma lap_Q : forall t,
  exists n c', csteps tm n (Cc t) = Some c'
               /\ lift c' = lift (Cc (nx t)) /\ 0 < n
               /\ AvoidRun tm StA n (Cc t).
Proof.
  intro t. destruct (lap_exact t) as (n & c' & H1 & H2 & H3).
  exists n, c'. repeat split; try assumption.
  - rewrite H2. reflexivity.
  - apply avoid_from_anchor.
Qed.

(** ** Visit witnesses

    [qW] is the anchor and [qC] is one step in.  [qD] is one step past the
    end of the carry run, and the run's length is the only thing that varies
    -- so a single lemma, keyed off [chd w = S0], covers all three branches
    at once. *)
Lemma visD_shape : forall k w, chd w = S0 ->
  exists n c, csteps tm n (qW,([],S1,rep [S1] k ++ w)) = Some c /\ fst c = qD.
Proof.
  intros k w Hw.
  exists (1 + k + 1), (qD,(S0 :: (rep [S0] k ++ [S1]),chd (ctl w),ctl (ctl w))).
  split; [| reflexivity].
  rewrite csteps_add, (runC k w), Hw.
  apply (uSTP (rep [S0] k ++ [S1]) (ctl w)).
Qed.

Lemma vis_T : forall t q, q <> StA ->
  exists k c, csteps tm k (Cc t) = Some c /\ fst c = q.
Proof.
  intros t q Hq. unfold Cc.
  destruct (Hcover q) as [-> | [-> | [-> | ->]]];
    [contradiction Hq; reflexivity | | |].
  - exists 0, (qW,([],S1,Wf t)). split; reflexivity.
  - exists 1, (qC,([S1],chd (Wf t),ctl (Wf t))). split;
      [apply (uP1 [] (Wf t)) | reflexivity].
  - destruct (Hstep t)
      as [(m & u & H1 & _) | [(m & u & H1 & _) | (m & H1 & _)]];
      rewrite H1.
    + exact (visD_shape m (S0 :: S0 :: u) eq_refl).
    + exact (visD_shape m (S0 :: S1 :: u) eq_refl).
    + rewrite <- (app_nil_r (rep [S1] m)). exact (visD_shape m [] eq_refl).
Qed.

Lemma vis0_T : VisitsAt tm StA 0.
Proof. exists InitES. split; reflexivity. Qed.

(** ** The closer *)

Definition iqh (m : TM) : Prop :=
  NonHalt m /\ QHBound 2000 m /\ QuasiHaltsSt m.

Theorem ter3wall_qh : iqh tm.
Proof.
  destruct (glue_qh_quiet_ix tm tern nx Cc i0 StA t0 0 Hboot lap_Q
              (fun t q Hq => vis_T t q Hq) vis0_T Hbq)
    as (Hnh & Hqb & Hqh).
  split; [exact Hnh | split; [| exact Hqh]].
  apply (qhbound_mono 1 2000); [lia | exact Hqb].
Qed.

End Ter3Wall.
