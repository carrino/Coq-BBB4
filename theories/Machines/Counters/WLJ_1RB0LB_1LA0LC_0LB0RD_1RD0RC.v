(** * WLJ_1RB0LB_1LA0LC_0LB0RD_1RD0RC: erase/rebuild wall counter, machine 1RB0LB_1LA0LC_0LB0RD_1RD0RC.

    Auto-emitted by tools/counters/emit_wallj.py (UNTRUSTED emitter; the Coq
    kernel re-checks every line below).  Left-growth counter under the
    COMPLEMENTED interleave encoding [Jp], holding a fixed WALL on the far
    side (WALLLAP_NOTE.md, the erase/rebuild shape):

      Cc p = (StC, (Jp p ++ [S0], S0, [S0;S0;S1;S0]))

    The head stays BLANK across the whole lap; the carry runs as an
    erase-then-rebuild pass:

      ER^j  cycL [S1;S0] -> deposits [S0;S0]  (2 steps per pair) --
            erase the low set pairs, piling blanks onto the far side;
      ST    stop on the clear pair [S1;S1] (3 steps);
      RB^k  cycR [S0] -> [S1] (1 step per cell) -- rebuild, consuming
            the deposited blanks AND the wall's own (k = 2j+1+2);
      CL    right-open close (14 steps) rebuilding the wall.

    The overflow branch runs ER^(S j') -- the anchor tail completes a final
    [S1;S0] pair -- then a LEFT-OPEN stop off the deep tape edge (5
    steps) and the same rebuild/close.

    Anchoring the wall WITH its trailing blank makes the interior branch
    land EXACTLY, which is what carries the [tovf] well-founded induction
    for the deep visit witnesses.  Validated against the raw simulator on
    BOTH cview branches (interior p = 2..199, overflow K = 2..8; step
    counts AND landings).  Axiom footprint:
    [functional_extensionality_dep] (via CTape.lift). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter ILCounter JpCounter.
Import ListNotations.

Definition mk_1RB0LB_1LA0LC_0LB0RD_1RD0RC (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB0LB_1LA0LC_0LB0RD_1RD0RC.

(** 1RB0LB_1LA0LC_0LB0RD_1RD0RC *)
Definition tm_1RB0LB_1LA0LC_0LB0RD_1RD0RC : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DL StB
  | StB, S0 => mk S1 DL StA | StB, S1 => mk S0 DL StC
  | StC, S0 => mk S0 DL StB | StC, S1 => mk S0 DR StD
  | StD, S0 => mk S1 DR StD | StD, S1 => mk S0 DR StC end.
Local Notation tm := tm_1RB0LB_1LA0LC_0LB0RD_1RD0RC.

Definition Cc_1RB0LB_1LA0LC_0LB0RD_1RD0RC (p : positive) : cconf := (StC, (Jp p ++ [S0], S0, [S0;S0;S1;S0])).
Local Notation Cc := Cc_1RB0LB_1LA0LC_0LB0RD_1RD0RC.

(** ** The window units (each closed by [reflexivity]) *)
Lemma U_ER_1RB0LB_1LA0LC_0LB0RD_1RD0RC : wsteps true true tm 2 (StC,([S1;S0],S0,[])) = Some (StC,([],S0,[S0;S0])). Proof. reflexivity. Qed.
Lemma U_ST_1RB0LB_1LA0LC_0LB0RD_1RD0RC : wsteps true true tm 3 (StC,([S1;S1],S0,[])) = Some (StD,([S0],S0,[S0])). Proof. reflexivity. Qed.
Lemma U_RB_1RB0LB_1LA0LC_0LB0RD_1RD0RC : wsteps true true tm 1 (StD,([],S0,[S0])) = Some (StD,([S1],S0,[])). Proof. reflexivity. Qed.
Lemma U_CL_1RB0LB_1LA0LC_0LB0RD_1RD0RC : wsteps true false tm 14 (StD,([S1;S1],S0,[S1;S0])) = Some (StC,([],S0,[S0;S0;S1;S0])). Proof. reflexivity. Qed.
Lemma U_STO_1RB0LB_1LA0LC_0LB0RD_1RD0RC : wsteps false true tm 5 (StC,([],S0,[])) = Some (StD,([S0],S0,[S0])). Proof. reflexivity. Qed.
Lemma U_VO1_1RB0LB_1LA0LC_0LB0RD_1RD0RC : wsteps false true tm 2 (StC,([],S0,[])) = Some (StA,([],S0,[S1;S0])). Proof. reflexivity. Qed.
Lemma U_VE1_1RB0LB_1LA0LC_0LB0RD_1RD0RC : wsteps true true tm 1 (StC,([S1;S0],S0,[])) = Some (StB,([S0],S1,[S0])). Proof. reflexivity. Qed.
Lemma U_VO2_1RB0LB_1LA0LC_0LB0RD_1RD0RC : wsteps false true tm 5 (StC,([],S0,[])) = Some (StD,([S0],S0,[S0])). Proof. reflexivity. Qed.

(** ** Transported phases *)
Lemma phER_1RB0LB_1LA0LC_0LB0RD_1RD0RC : forall k L R, csteps tm (2*k) (StC,(rep [S1;S0] k ++ L,S0,R)) = Some (StC,(L,S0,rep [S0;S0] k ++ R)).
Proof. intros. pose proof (cycL _ _ _ _ _ _ _ U_ER_1RB0LB_1LA0LC_0LB0RD_1RD0RC k L R) as H; cbn [app] in H; exact H. Qed.
Lemma phST_1RB0LB_1LA0LC_0LB0RD_1RD0RC : forall L R, csteps tm 3 (StC,(S1::S1::L,S0,R)) = Some (StD,(S0::L,S0,S0::R)).
Proof. intros. pose proof (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_ST_1RB0LB_1LA0LC_0LB0RD_1RD0RC) as H; cbn [app] in H; exact H. Qed.
Lemma phRB_1RB0LB_1LA0LC_0LB0RD_1RD0RC : forall k L R, csteps tm (1*k) (StD,(L,S0,rep [S0] k ++ R)) = Some (StD,(rep [S1] k ++ L,S0,R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U_RB_1RB0LB_1LA0LC_0LB0RD_1RD0RC k L R). Qed.
Lemma phCL_1RB0LB_1LA0LC_0LB0RD_1RD0RC : forall L, csteps tm 14 (StD,(S1::S1::L,S0,[S1;S0])) = Some (StC,(L,S0,[S0;S0;S1;S0])).
Proof. intros. pose proof (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U_CL_1RB0LB_1LA0LC_0LB0RD_1RD0RC) as H; cbn [app] in H; exact H. Qed.
Lemma phSTO_1RB0LB_1LA0LC_0LB0RD_1RD0RC : forall R, csteps tm 5 (StC,([],S0,R)) = Some (StD,([S0],S0,S0::R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_STO_1RB0LB_1LA0LC_0LB0RD_1RD0RC). Qed.
Lemma phVO1_1RB0LB_1LA0LC_0LB0RD_1RD0RC : forall R, csteps tm 2 (StC,([],S0,R)) = Some (StA,([],S0,S1::S0::R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_VO1_1RB0LB_1LA0LC_0LB0RD_1RD0RC). Qed.
Lemma phVE1_1RB0LB_1LA0LC_0LB0RD_1RD0RC : forall L R, csteps tm 1 (StC,(S1::S0::L,S0,R)) = Some (StB,(S0::L,S1,S0::R)).
Proof. intros. pose proof (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_VE1_1RB0LB_1LA0LC_0LB0RD_1RD0RC) as H; cbn [app] in H; exact H. Qed.
Lemma phVO2_1RB0LB_1LA0LC_0LB0RD_1RD0RC : forall R, csteps tm 5 (StC,([],S0,R)) = Some (StD,([S0],S0,S0::R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_VO2_1RB0LB_1LA0LC_0LB0RD_1RD0RC). Qed.

(** The far side entering the rebuild: the erased pairs, the stop's blank,
    and the wall's own blanks form one run of 2 + 1 + 2j cells. *)
Lemma far_run_1RB0LB_1LA0LC_0LB0RD_1RD0RC : forall j, S0 :: rep [S0;S0] j ++ [S0;S0;S1;S0] = rep [S0] (S (2*j) + 2) ++ [S1;S0].
Proof.
  intro j. rewrite rep_add, rep_dbl. cbn [rep app]. rewrite <- !app_assoc.
  reflexivity.
Qed.

(** ** The interior lap: EXACT *)
Lemma lap_int_1RB0LB_1LA0LC_0LB0RD_1RD0RC : forall p j q0, cview p = (j, Some q0) ->
  exists n c', csteps tm n (Cc p) = Some c' /\ c' = Cc (Pos.succ p) /\ 0 < n.
Proof.
  intros p j q0 Ecv. unfold Cc_1RB0LB_1LA0LC_0LB0RD_1RD0RC.
  destruct (cview_some_J p j q0 Ecv) as (HJp & HJs).
  do 2 eexists. split; [|split].
  + rewrite HJp, <- app_assoc. cbn [app].
    eapply csteps_chain. { apply phER_1RB0LB_1LA0LC_0LB0RD_1RD0RC. }
    eapply csteps_chain. { apply phST_1RB0LB_1LA0LC_0LB0RD_1RD0RC. }
    rewrite far_run_1RB0LB_1LA0LC_0LB0RD_1RD0RC.
    eapply csteps_chain. { apply (phRB_1RB0LB_1LA0LC_0LB0RD_1RD0RC (S (2*j) + 2)). }
    replace (S (2*j) + 2) with (S (S (2*j + 1))) by lia.
    cbn [rep app].
    apply phCL_1RB0LB_1LA0LC_0LB0RD_1RD0RC.
  + rewrite HJs, rep_dbl, <- !app_assoc. cbn [app].
    replace (2 * j + 1) with (S (2 * j)) by lia.
    cbn [rep app]. rewrite rep_slide. reflexivity.
  + lia.
Qed.

(** ** The overflow lap *)
Lemma lap_ov_1RB0LB_1LA0LC_0LB0RD_1RD0RC : forall p j', cview p = (S j', None) ->
  exists n c', csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j' Ecv. unfold Cc_1RB0LB_1LA0LC_0LB0RD_1RD0RC.
  destruct (cview_none_J p j' Ecv) as (HJp & HJs).
  do 2 eexists. split; [|split].
  + rewrite HJp, <- app_assoc. cbn [app]. rewrite pair_fold.
    eapply csteps_chain. { apply (phER_1RB0LB_1LA0LC_0LB0RD_1RD0RC (S j')). }
    eapply csteps_chain. { apply phSTO_1RB0LB_1LA0LC_0LB0RD_1RD0RC. }
    rewrite far_run_1RB0LB_1LA0LC_0LB0RD_1RD0RC.
    eapply csteps_chain. { apply (phRB_1RB0LB_1LA0LC_0LB0RD_1RD0RC (S (2*(S j')) + 2)). }
    replace (S (2*(S j')) + 2) with (S (S (2*(S j') + 1))) by lia.
    cbn [rep app].
    apply phCL_1RB0LB_1LA0LC_0LB0RD_1RD0RC.
  + rewrite HJs, rep_dbl, <- !app_assoc. cbn [app].
    replace (2 * S j' + 1) with (S (2 * S j')) by lia.
    cbn [rep app]. rewrite rep_slide. reflexivity.
  + lia.
Qed.

Lemma lap_1RB0LB_1LA0LC_0LB0RD_1RD0RC : forall p, exists n c', csteps tm n (Cc p) = Some c' /\
  lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - destruct (lap_int_1RB0LB_1LA0LC_0LB0RD_1RD0RC p j q0 Ecv) as (n & c' & H1 & H2 & H3).
    exists n, c'. split; [exact H1|split; [rewrite H2; reflexivity|exact H3]].
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    exact (lap_ov_1RB0LB_1LA0LC_0LB0RD_1RD0RC p j' Ecv).
Qed.

Lemma boot_1RB0LB_1LA0LC_0LB0RD_1RD0RC : exists t0, stepn tm t0 InitES = Some (lift (Cc 2)).
Proof.
  exists 62.
  assert (H : match csteps tm 62 c0 with Some c => ceqb c (Cc 2) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 62 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits *)

(** StA fires only in the OVERFLOW stop; reach an all-ones counter by
    well-founded induction on [tovf] (interior laps close EXACTLY). *)
Lemma vis_D1_1RB0LB_1LA0LC_0LB0RD_1RD0RC : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = StA.
Proof.
  intro p; remember (tovf p) as fuel eqn:Ef; revert p Ef.
  induction fuel as [fuel IH] using (well_founded_induction lt_wf); intros p Ef.
  destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - assert (Hnz : tovf p <> 0).
    { intro H0. destruct (tovf0_allones p H0) as (jj & Hjj). rewrite Hjj in Ecv; discriminate. }
    destruct (lap_int_1RB0LB_1LA0LC_0LB0RD_1RD0RC p j q0 Ecv) as (n & c' & Hrun & Hc' & _). subst c'.
    destruct (IH (tovf (Pos.succ p)) (ltac:(rewrite tovf_succ by lia; lia)) (Pos.succ p) eq_refl) as (k & c & Hk & Hq).
    exists (n + k), c. rewrite csteps_add, Hrun. exact (conj Hk Hq).
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_J p j' Ecv) as (HJp & _).
    unfold Cc_1RB0LB_1LA0LC_0LB0RD_1RD0RC. eexists. eexists. split.
    + rewrite HJp, <- app_assoc. cbn [app]. rewrite pair_fold.
      eapply csteps_chain. { apply (phER_1RB0LB_1LA0LC_0LB0RD_1RD0RC (S j')). }
      apply phVO1_1RB0LB_1LA0LC_0LB0RD_1RD0RC.
    + reflexivity.
Qed.

(** StB: 1 steps into the erase unit.  At the anchor the unit is
    only present when j > 0, so route every p to an all-ones counter by
    well-founded induction on [tovf] (interior laps close EXACTLY) --
    the overflow anchor always starts with a full [S1;S0] pair. *)
Lemma vis_A1_1RB0LB_1LA0LC_0LB0RD_1RD0RC : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = StB.
Proof.
  intro p; remember (tovf p) as fuel eqn:Ef; revert p Ef.
  induction fuel as [fuel IH] using (well_founded_induction lt_wf); intros p Ef.
  destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - assert (Hnz : tovf p <> 0).
    { intro H0. destruct (tovf0_allones p H0) as (jj & Hjj). rewrite Hjj in Ecv; discriminate. }
    destruct (lap_int_1RB0LB_1LA0LC_0LB0RD_1RD0RC p j q0 Ecv) as (n & c' & Hrun & Hc' & _). subst c'.
    destruct (IH (tovf (Pos.succ p)) (ltac:(rewrite tovf_succ by lia; lia)) (Pos.succ p) eq_refl) as (k & c & Hk & Hq).
    exists (n + k), c. rewrite csteps_add, Hrun. exact (conj Hk Hq).
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_J p j' Ecv) as (HJp & _).
    unfold Cc_1RB0LB_1LA0LC_0LB0RD_1RD0RC. exists 1. eexists. split.
    + rewrite HJp, <- app_assoc. cbn [app]. rewrite pair_fold.
      cbn [rep app]. apply phVE1_1RB0LB_1LA0LC_0LB0RD_1RD0RC.
    + reflexivity.
Qed.

(** StD fires only in the OVERFLOW stop; reach an all-ones counter by
    well-founded induction on [tovf] (interior laps close EXACTLY). *)
Lemma vis_D2_1RB0LB_1LA0LC_0LB0RD_1RD0RC : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = StD.
Proof.
  intro p; remember (tovf p) as fuel eqn:Ef; revert p Ef.
  induction fuel as [fuel IH] using (well_founded_induction lt_wf); intros p Ef.
  destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - assert (Hnz : tovf p <> 0).
    { intro H0. destruct (tovf0_allones p H0) as (jj & Hjj). rewrite Hjj in Ecv; discriminate. }
    destruct (lap_int_1RB0LB_1LA0LC_0LB0RD_1RD0RC p j q0 Ecv) as (n & c' & Hrun & Hc' & _). subst c'.
    destruct (IH (tovf (Pos.succ p)) (ltac:(rewrite tovf_succ by lia; lia)) (Pos.succ p) eq_refl) as (k & c & Hk & Hq).
    exists (n + k), c. rewrite csteps_add, Hrun. exact (conj Hk Hq).
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_J p j' Ecv) as (HJp & _).
    unfold Cc_1RB0LB_1LA0LC_0LB0RD_1RD0RC. eexists. eexists. split.
    + rewrite HJp, <- app_assoc. cbn [app]. rewrite pair_fold.
      eapply csteps_chain. { apply (phER_1RB0LB_1LA0LC_0LB0RD_1RD0RC (S j')). }
      apply phVO2_1RB0LB_1LA0LC_0LB0RD_1RD0RC.
    + reflexivity.
Qed.

Lemma vis_1RB0LB_1LA0LC_0LB0RD_1RD0RC : forall p q, exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q. destruct q.
  - apply vis_D1_1RB0LB_1LA0LC_0LB0RD_1RD0RC.
  - apply vis_A1_1RB0LB_1LA0LC_0LB0RD_1RD0RC.
  - (* StC : the anchor state *)
    exists 0. eexists. split; reflexivity.
  - apply vis_D2_1RB0LB_1LA0LC_0LB0RD_1RD0RC.
Qed.

Theorem nqh_1RB0LB_1LA0LC_0LB0RD_1RD0RC : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc 2). - exact boot_1RB0LB_1LA0LC_0LB0RD_1RD0RC. - intros p _. apply lap_1RB0LB_1LA0LC_0LB0RD_1RD0RC. - intros p q _. apply vis_1RB0LB_1LA0LC_0LB0RD_1RD0RC. Qed.

Theorem nonhalt_1RB0LB_1LA0LC_0LB0RD_1RD0RC : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_1RB0LB_1LA0LC_0LB0RD_1RD0RC. Qed.
