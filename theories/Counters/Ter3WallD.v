(** * Ter3WallD: the BASE-THREE wall bouncer that is FOUR-state.

    The third base-3 shape, after [Counters/Ter3Wall.v] and
    [Counters/Ter3WallB.v], and the first one whose anchor state is the
    target of a transition.  Its four defined states are

      qA  0 -> 1 R qB     qA  1 -> 1 R qC     (the wall, and the return's turn)
      qB  0 -> 1 L qA     qB  1 -> 0 L qB     (the return sweep)
      qC  0 -> 1 L qD     qC  1 -> 0 R qD     (the outward clear, odd half)
      qD  0 -> 1 L qB     qD  1 -> 0 R qC     (the outward clear, even half)

    over [Ter3WallB]'s 2-cell digit words

      digit 0 = [S0; S0]     digit 1 = [S1; S0]     digit 2 = [S1; S1]

    -- the same alphabet and the same increment ([TernCounter.tsucc], whose
    overflow writes a fresh digit 1), so [Ter3WallB.TerStepB] and its
    instance [Ter3WallB.ter_stepB_nil] are reused VERBATIM.  What is new here
    is the machine side: a different sweep, a different lap, and a different
    closer.

    ** The anchor carries a MARKER cell

    [Ter3Wall] and [Ter3WallB] anchor at [(q, ([], S1, <digits>))] -- the head
    on the wall, the digits immediately to its right.  Here there is one more
    fixed [S1] between them,

      Cc t = (qA, ([], S1, S1 :: Wf t))

    and it is not decoration: the lap CLEARS it on the way out ([qC] on the
    marker) and the return's last step REWRITES it, which is what puts the
    head back on the wall in [qA].  [tools/counters/ter3_probe.py] reads the
    counter off this anchor over 75,006 consecutive visits with zero prefix
    and zero consecutive-value failures.

    ** The parity is the branch here too, for a different reason

    The outward clear alternates [qD]/[qC] one cell at a time, so what stops
    it is the parity of the set-cell run, exactly as in [Ter3WallB] -- but
    the two stops differ in their STATE rather than in how many cells they
    set.  An even run stops in [qD] on a clear cell, which sets it and turns
    ([00 -> 10]).  An odd run stops in [qC], which sets that cell, steps back
    onto the one [qD] just cleared and sets it too ([10 -> 11]).  So base 3's
    two interior branches are again the two parities of one sweep, and the
    lap is

      even (and overflow)   6i + 4
      odd                   6i + 6

    measured by [tools/counters/ter3_scan.py] as two affine branches with no
    third value in any carry class, and re-checked against the trichotomy's
    own case split over 50,003 consecutive laps with zero mismatches.

    ** Why this is a NEVER-quasihalting closer

    [Ter3Wall*]'s [StA] fires once and is the target of nothing, so those
    rows quasihalt and carry [iqh].  Here [qA] IS the anchor state and the
    target of [qB]'s [S0] transition: all four states recur at every anchor
    (measured -- every one of 37,502 laps contains all four), so the theorem
    is [NeverQuasiHaltsSt] and the closer is
    [Counters/LapGlueNeverIx.glue_neverqh_ix], the never-QH twin of
    [LapGlueIx.glue_qh_quiet_ix] over an arbitrary index.  There is no [AvoidRun]
    premise to discharge and no [inv_ok] side condition.

    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)

From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Census Require Import TNF_QH.
From BBB4.Counters Require Import WTape LapGlueNeverIx TernCounter Ter3WallB.
Import ListNotations.

Section Ter3WallD.

Variable tm : TM.
Variable qA qB qC qD : St.
Variable t0 : nat.
Variable i0 : tern.

Hypothesis HA0 : tm qA S0 = Some (mkTrans S1 DR qB).
Hypothesis HA1 : tm qA S1 = Some (mkTrans S1 DR qC).
Hypothesis HB0 : tm qB S0 = Some (mkTrans S1 DL qA).
Hypothesis HB1 : tm qB S1 = Some (mkTrans S0 DL qB).
Hypothesis HC0 : tm qC S0 = Some (mkTrans S1 DL qD).
Hypothesis HC1 : tm qC S1 = Some (mkTrans S0 DR qD).
Hypothesis HD0 : tm qD S0 = Some (mkTrans S1 DL qB).
Hypothesis HD1 : tm qD S1 = Some (mkTrans S0 DR qC).

(** All four roles are distinct states and there are no others -- this is
    what makes every state recur, and so what makes the theorem never-QH. *)
Hypothesis Hcover : forall q, q = qA \/ q = qB \/ q = qC \/ q = qD.

Variable Wf : tern -> list Sym.
Variable nx : tern -> tern.
Hypothesis Hstep : TerStepB Wf nx.

Definition Cc (t : tern) : cconf := (qA, ([], S1, S1 :: Wf t)).

Hypothesis Hboot : stepn tm t0 InitES = Some (lift (Cc i0)).

(** ** Units *)

Lemma uA1 : forall L R, csteps tm 1 (qA,(L,S1,R)) = Some (qC,(S1::L,chd R,ctl R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HA1.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

Lemma uA0 : forall L R, csteps tm 1 (qA,(L,S0,R)) = Some (qB,(S1::L,chd R,ctl R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HA0.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

Lemma uB0 : forall L R, csteps tm 1 (qB,(L,S0,R)) = Some (qA,(ctl L,chd L,S1::R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HB0.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

Lemma uB1 : forall L R, csteps tm 1 (qB,(L,S1,R)) = Some (qB,(ctl L,chd L,S0::R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HB1.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

Lemma uC0 : forall L R, csteps tm 1 (qC,(L,S0,R)) = Some (qD,(ctl L,chd L,S1::R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HC0.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

Lemma uC1 : forall L R, csteps tm 1 (qC,(L,S1,R)) = Some (qD,(S0::L,chd R,ctl R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HC1.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

Lemma uD0 : forall L R, csteps tm 1 (qD,(L,S0,R)) = Some (qB,(ctl L,chd L,S1::R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HD0.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

Lemma uD1 : forall L R, csteps tm 1 (qD,(L,S1,R)) = Some (qC,(S0::L,chd R,ctl R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HD1.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

(** ** Phases *)

Lemma rep_cons : forall (u : list Sym) k L,
  rep u k ++ (u ++ L) = u ++ (rep u k ++ L).
Proof.
  intros u k L. rewrite app_assoc, rep_shift, <- app_assoc. reflexivity.
Qed.

(** The outward clear, two cells at a time: [qD] to [qC] and back. *)
Lemma phCLR : forall i L w,
  csteps tm (2 * i) (qD,(L,chd (rep [S1] (2 * i) ++ w),
                           ctl (rep [S1] (2 * i) ++ w)))
    = Some (qD,(rep [S0] (2 * i) ++ L,chd w,ctl w)).
Proof.
  induction i as [|i IH]; intros L w; [reflexivity |].
  replace (rep [S1] (2 * S i) ++ w)
    with (S1 :: S1 :: (rep [S1] (2 * i) ++ w))
    by (replace (2 * S i) with (S (S (2 * i))) by lia;
        cbn [rep app]; reflexivity).
  cbn [chd ctl].
  replace (2 * S i) with (1 + (1 + 2 * i)) by lia.
  rewrite csteps_add, (uD1 L (S1 :: (rep [S1] (2 * i) ++ w))).
  cbn [chd ctl].
  rewrite csteps_add, (uC1 (S0 :: L) (rep [S1] (2 * i) ++ w)), IH.
  replace (rep [S0] (1 + (1 + 2 * i)) ++ L)
    with ([S0] ++ ([S0] ++ (rep [S0] (2 * i) ++ L)))
    by (cbn [rep app]; reflexivity).
  change (S0 :: (S0 :: L)) with ([S0] ++ ([S0] ++ L)).
  rewrite (rep_cons [S0] (2 * i) ([S0] ++ L)),
          (rep_cons [S0] (2 * i) L). reflexivity.
Qed.

(** The return sweep, FOUR steps per two cleared cells.  [qB] on a clear cell
    sets it and turns into [qA], which sets the cell to its right and turns
    back; the two [qB] steps that follow clear both again.  Net: the tape is
    unchanged and the head has moved two cells left, still in [qB] on [S0]. *)
Lemma phRET : forall k L R,
  csteps tm (4 * k) (qB,(rep [S0] (2 * k) ++ L,S0,R))
    = Some (qB,(L,S0,rep [S0] (2 * k) ++ R)).
Proof.
  induction k as [|k IH]; intros L R; [reflexivity |].
  replace (rep [S0] (2 * S k) ++ L)
    with (S0 :: S0 :: (rep [S0] (2 * k) ++ L))
    by (replace (2 * S k) with (S (S (2 * k))) by lia;
        cbn [rep app]; reflexivity).
  replace (4 * S k) with (1 + (1 + (1 + (1 + 4 * k)))) by lia.
  rewrite csteps_add,
    (uB0 (S0 :: (S0 :: (rep [S0] (2 * k) ++ L))) R).
  cbn [chd ctl].
  rewrite csteps_add, (uA0 (S0 :: (rep [S0] (2 * k) ++ L)) (S1 :: R)).
  cbn [chd ctl].
  rewrite csteps_add, (uB1 (S1 :: (S0 :: (rep [S0] (2 * k) ++ L))) R).
  cbn [chd ctl].
  rewrite csteps_add, (uB1 (S0 :: (rep [S0] (2 * k) ++ L)) (S0 :: R)).
  cbn [chd ctl]. rewrite IH.
  replace (rep [S0] (2 * S k) ++ R)
    with (S0 :: S0 :: (rep [S0] (2 * k) ++ R))
    by (replace (2 * S k) with (S (S (2 * k))) by lia;
        cbn [rep app]; reflexivity).
  change (S0 :: (S0 :: R)) with ([S0] ++ ([S0] ++ R)).
  rewrite (rep_cons [S0] (2 * k) ([S0] ++ R)),
          (rep_cons [S0] (2 * k) R). reflexivity.
Qed.

(** The clear leaves the marker cell at the FAR end of the zeros it wrote,
    so the stop's [ctl] has to pop one [S0] off a [rep] from the wrong side.
    This is [rep_cons] at the one instance every stop uses. *)
Lemma rep_pop : forall k T, rep [S0] k ++ (S0 :: T) = S0 :: (rep [S0] k ++ T).
Proof.
  intros k T. change (S0 :: T) with ([S0] ++ T). apply (rep_cons [S0] k T).
Qed.

(** Return, then rewrite the marker: this IS the next anchor. *)
Lemma phHOME : forall i R,
  csteps tm (4 * i + 1) (qB,(rep [S0] (2 * i) ++ [S1],S0,R))
    = Some (qA,([],S1,S1 :: rep [S0] (2 * i) ++ R)).
Proof.
  intros i R.
  rewrite csteps_add, (phRET i [S1] R),
          (uB0 [S1] (rep [S0] (2 * i) ++ R)).
  cbn [chd ctl]. reflexivity.
Qed.

(** ** The lap, in its two parities *)

(** The EVEN branch, and the overflow: the clear stops in [qD] on a clear
    cell, sets it, and the return runs home.  [6i + 4]. *)
Lemma lapE : forall i w, chd w = S0 ->
  exists n, 0 < n /\
  csteps tm n (qA,([],S1,S1 :: rep [S1] (2 * i) ++ w))
    = Some (qA,([],S1,S1 :: rep [S0] (2 * i) ++ S1 :: ctl w)).
Proof.
  intros i w Hw. exists (1 + (1 + (2 * i + (1 + (4 * i + 1))))). split; [lia |].
  rewrite csteps_add, (uA1 [] (S1 :: rep [S1] (2 * i) ++ w)).
  cbn [chd ctl].
  rewrite csteps_add, (uC1 [S1] (rep [S1] (2 * i) ++ w)).
  rewrite csteps_add, (phCLR i [S0; S1] w), Hw.
  rewrite (rep_pop (2 * i) [S1]).
  rewrite csteps_add, (uD0 (S0 :: (rep [S0] (2 * i) ++ [S1])) (ctl w)).
  cbn [chd ctl].
  apply (phHOME i (S1 :: ctl w)).
Qed.

(** The ODD branch: the clear stops in [qC], which sets that cell, steps back
    onto the one [qD] just cleared and sets it too.  [6i + 6]. *)
Lemma lapO : forall i w, chd w = S0 ->
  exists n, 0 < n /\
  csteps tm n (qA,([],S1,S1 :: rep [S1] (S (2 * i)) ++ w))
    = Some (qA,([],S1,S1 :: rep [S0] (2 * i) ++ S1 :: S1 :: ctl w)).
Proof.
  intros i w Hw.
  exists (1 + (1 + (2 * i + (1 + (1 + (1 + (4 * i + 1))))))). split; [lia |].
  replace (rep [S1] (S (2 * i)) ++ w)
    with (rep [S1] (2 * i) ++ (S1 :: w))
    by (change (S1 :: w) with ([S1] ++ w);
        rewrite (rep_cons [S1] (2 * i) w); reflexivity).
  rewrite csteps_add, (uA1 [] (S1 :: rep [S1] (2 * i) ++ (S1 :: w))).
  cbn [chd ctl].
  rewrite csteps_add, (uC1 [S1] (rep [S1] (2 * i) ++ (S1 :: w))).
  rewrite csteps_add, (phCLR i [S0; S1] (S1 :: w)).
  cbn [chd ctl].
  rewrite csteps_add, (uD1 (rep [S0] (2 * i) ++ [S0; S1]) w), Hw.
  rewrite csteps_add,
    (uC0 (S0 :: (rep [S0] (2 * i) ++ [S0; S1])) (ctl w)).
  cbn [chd ctl].
  rewrite (rep_pop (2 * i) [S1]).
  rewrite csteps_add,
    (uD0 (S0 :: (rep [S0] (2 * i) ++ [S1])) (S1 :: ctl w)).
  cbn [chd ctl].
  apply (phHOME i (S1 :: S1 :: ctl w)).
Qed.

(** ** The lap on the counter *)

Lemma lap_D : forall t,
  exists n c', csteps tm n (Cc t) = Some c'
               /\ lift c' = lift (Cc (nx t)) /\ 0 < n.
Proof.
  intro t. unfold Cc.
  destruct (Hstep t) as [(i & u & H1 & H2) | [(i & u & H1 & H2) | (i & H1 & H2)]].
  - destruct (lapE i (S0 :: S0 :: u) eq_refl) as (n & Hn & Hrun).
    exists n. eexists. split; [rewrite H1; exact Hrun |].
    split; [| exact Hn]. rewrite H2. cbn [ctl app]. reflexivity.
  - destruct (lapO i (S0 :: u) eq_refl) as (n & Hn & Hrun).
    exists n. eexists. split; [rewrite H1; exact Hrun |].
    split; [| exact Hn]. rewrite H2. cbn [ctl app]. reflexivity.
  - (* overflow: one trailing blank short of the anchor, invisible to lift *)
    destruct (lapE i [] eq_refl) as (n & Hn & Hrun).
    exists n. eexists. split.
    { rewrite H1, <- (app_nil_r (rep [S1] (2 * i))). exact Hrun. }
    split; [| exact Hn].
    rewrite H2. cbn [ctl app].
    replace (S1 :: rep [S0] (2 * i) ++ [S1; S0])
      with ((S1 :: rep [S0] (2 * i) ++ [S1]) ++ [S0])
      by (cbn [app]; rewrite <- app_assoc; reflexivity).
    rewrite lift_app_blank. reflexivity.
Qed.

(** ** Visit witnesses

    [qA] is the anchor, [qC] is one step in and [qD] two -- none of the three
    needs to know anything about the counter, because the marker cell the
    anchor carries is [S1] whatever [Wf t] is.  [qB] is where the clear
    stops, so it is the one witness that follows the trichotomy. *)
Lemma visB : forall t,
  exists k c, csteps tm k (Cc t) = Some c /\ fst c = qB.
Proof.
  intro t. unfold Cc.
  destruct (Hstep t) as [(i & u & H1 & _) | [(i & u & H1 & _) | (i & H1 & _)]].
  - eexists (1 + (1 + (2 * i + 1))). eexists. split.
    rewrite H1.
    rewrite csteps_add, (uA1 [] (S1 :: rep [S1] (2 * i) ++ ([S0;S0] ++ u))).
    cbn [chd ctl].
    rewrite csteps_add, (uC1 [S1] (rep [S1] (2 * i) ++ ([S0;S0] ++ u))).
    rewrite csteps_add, (phCLR i [S0; S1] ([S0;S0] ++ u)).
    cbn [chd ctl app].
    apply (uD0 (rep [S0] (2 * i) ++ [S0; S1]) (S0 :: u)).
    reflexivity.
  - eexists (1 + (1 + (2 * i + (1 + (1 + 1))))). eexists. split.
    rewrite H1.
    replace (rep [S1] (S (2 * i)) ++ ([S0] ++ u))
      with (rep [S1] (2 * i) ++ (S1 :: ([S0] ++ u)))
      by (change (S1 :: ([S0] ++ u)) with ([S1] ++ ([S0] ++ u));
          rewrite (rep_cons [S1] (2 * i) ([S0] ++ u)); reflexivity).
    rewrite csteps_add,
      (uA1 [] (S1 :: rep [S1] (2 * i) ++ (S1 :: ([S0] ++ u)))).
    cbn [chd ctl].
    rewrite csteps_add,
      (uC1 [S1] (rep [S1] (2 * i) ++ (S1 :: ([S0] ++ u)))).
    rewrite csteps_add, (phCLR i [S0; S1] (S1 :: ([S0] ++ u))).
    cbn [chd ctl].
    rewrite csteps_add, (uD1 (rep [S0] (2 * i) ++ [S0; S1]) ([S0] ++ u)).
    cbn [chd ctl app].
    rewrite csteps_add, (uC0 (S0 :: (rep [S0] (2 * i) ++ [S0; S1])) u).
    cbn [chd ctl app].
    apply (uD0 (rep [S0] (2 * i) ++ [S0; S1]) (S1 :: u)).
    reflexivity.
  - eexists (1 + (1 + (2 * i + 1))). eexists. split.
    rewrite H1, <- (app_nil_r (rep [S1] (2 * i))).
    rewrite csteps_add, (uA1 [] (S1 :: rep [S1] (2 * i) ++ [])).
    cbn [chd ctl].
    rewrite csteps_add, (uC1 [S1] (rep [S1] (2 * i) ++ [])).
    rewrite csteps_add, (phCLR i [S0; S1] []).
    cbn [chd ctl app].
    apply (uD0 (rep [S0] (2 * i) ++ [S0; S1]) []).
    reflexivity.
Qed.

Lemma vis_D : forall t q,
  exists k c, csteps tm k (Cc t) = Some c /\ fst c = q.
Proof.
  intros t q.
  destruct (Hcover q) as [-> | [-> | [-> | ->]]].
  - exists 0, (Cc t). split; reflexivity.
  - apply visB.
  - exists 1, (qC,([S1],chd (S1 :: Wf t),ctl (S1 :: Wf t))). split;
      [apply (uA1 [] (S1 :: Wf t)) | reflexivity].
  - exists (1 + 1), (qD,([S0;S1],chd (Wf t),ctl (Wf t))). split; [| reflexivity].
    unfold Cc.
    rewrite csteps_add, (uA1 [] (S1 :: Wf t)). cbn [chd ctl].
    apply (uC1 [S1] (Wf t)).
Qed.

(** ** The closer *)

Theorem ter3walld_nqh : NeverQuasiHaltsSt tm.
Proof.
  apply (glue_neverqh_ix tm tern nx Cc i0).
  - exists t0. exact Hboot.
  - exact lap_D.
  - exact vis_D.
Qed.

End Ter3WallD.
