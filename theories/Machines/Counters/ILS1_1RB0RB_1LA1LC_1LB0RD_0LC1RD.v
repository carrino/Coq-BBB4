(** * ILS1_1RB0RB_1LA1LC_1LB0RD_0LC1RD: lap-shape-1 interleaved binary counter,
    machine 1RB0RB_1LA1LC_1LB0RD_0LC1RD.

    Hand-authored template for lap shape 1 (`-CC|+CD|-DC|+CD`, 4 phases, the
    31-machine shape of tools/counter_lapshapes.tsv).  Comb-free interleaved
    binary counter under the complemented [Jp] encoding (JpCounter.v).  The
    anchor carries a blank far-side CELL, not the empty list:

      Cc p = (StC, (Jp p ++ [S0], S0, [S0]))

    so BOTH lap branches close EXACTLY (no lift on the lap): the frontier
    overshoot of the closing phase lands inside the [S0] window.  One lap
    Cc p -> Cc (p+1) is a FOUR-window chain (vs Interleave_TGT's six):

      RIP  leftward carry ripple over the low set-bit pairs (cycL, 2 steps
           per pair, j pairs where cview p = (j, _)); the anchor's blank
           head rotates through as the ripple unit's own data cell, so
           there is no P1 prologue window;
      STPI interior stop (cview p = (j, Some q)): flip the first clear
           pair, turn right (3 steps);
      STPO overflow stop (cview p = (S j', None)): bounce off the deep-left
           tape edge through StA, growing the counter (7 steps, left-open);
      RET  rightward return over the deposited ones (cycR, 1 step per cell);
      FIN  close at the frontier: step past it, retreat, zero the last one,
           re-anchor (4 steps).

    The decomposition was differentially validated against the raw simulator
    on both cview branches for p = 1..160 plus sparse p up to 2^13 (step
    counts AND exact configurations; interior n = 4j+8, overflow n = 4j'+14).
    Axiom footprint: [functional_extensionality_dep] (via CTape.lift). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter ILCounter JpCounter.
Import ListNotations.

Definition mk_1RB0RB_1LA1LC_1LB0RD_0LC1RD (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB0RB_1LA1LC_1LB0RD_0LC1RD.

(** 1RB0RB_1LA1LC_1LB0RD_0LC1RD *)
Definition tm_1RB0RB_1LA1LC_1LB0RD_0LC1RD : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DR StB
  | StB, S0 => mk S1 DL StA | StB, S1 => mk S1 DL StC
  | StC, S0 => mk S1 DL StB | StC, S1 => mk S0 DR StD
  | StD, S0 => mk S0 DL StC | StD, S1 => mk S1 DR StD end.
Local Notation tm := tm_1RB0RB_1LA1LC_1LB0RD_0LC1RD.

Definition Cc_1RB0RB_1LA1LC_1LB0RD_0LC1RD (p : positive) : cconf := (StC, (Jp p ++ [S0], S0, [S0])).
Local Notation Cc := Cc_1RB0RB_1LA1LC_1LB0RD_0LC1RD.

(** ** The four lap unit windows + the visit units (each closed by [reflexivity]) *)
Lemma U_RIP_1RB0RB_1LA1LC_1LB0RD_0LC1RD : wsteps true true tm 2 (StC,([S1;S0],S0,[])) = Some (StC,([],S0,[S1;S1])). Proof. reflexivity. Qed.
Lemma U_STPI_1RB0RB_1LA1LC_1LB0RD_0LC1RD : wsteps true true tm 3 (StC,([S1;S1],S0,[])) = Some (StD,([S0],S1,[S1])). Proof. reflexivity. Qed.
Lemma U_STPO_1RB0RB_1LA1LC_1LB0RD_0LC1RD : wsteps false true tm 7 (StC,([S1;S0],S0,[])) = Some (StD,([S0],S1,[S1;S1;S1])). Proof. reflexivity. Qed.
Lemma U_RET_1RB0RB_1LA1LC_1LB0RD_0LC1RD : wsteps true true tm 1 (StD,([],S1,[S1])) = Some (StD,([S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_FIN_1RB0RB_1LA1LC_1LB0RD_0LC1RD : wsteps true true tm 4 (StD,([],S1,[S0])) = Some (StC,([],S0,[S0])). Proof. reflexivity. Qed.
Lemma U_VA_1RB0RB_1LA1LC_1LB0RD_0LC1RD : wsteps false true tm 4 (StC,([S1;S0],S0,[])) = Some (StA,([],S0,[S1;S1;S1;S1])). Proof. reflexivity. Qed.
Lemma U_VB_1RB0RB_1LA1LC_1LB0RD_0LC1RD : wsteps true true tm 1 (StC,([S1],S0,[])) = Some (StB,([],S1,[S1])). Proof. reflexivity. Qed.

(** ** Transported phases (framing = each unit's bl/br) *)
Lemma phRIP_1RB0RB_1LA1LC_1LB0RD_0LC1RD : forall k L R, csteps tm (2*k) (StC,(rep [S1;S0] k ++ L,S0,R)) = Some (StC,(L,S0,rep [S1;S1] k ++ R)).
Proof. intros. pose proof (cycL _ _ _ _ _ _ _ U_RIP_1RB0RB_1LA1LC_1LB0RD_0LC1RD k L R) as H; cbn [app] in H; exact H. Qed.
Lemma phSTPI_1RB0RB_1LA1LC_1LB0RD_0LC1RD : forall L R, csteps tm 3 (StC,(S1::S1::L,S0,R)) = Some (StD,(S0::L,S1,S1::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_STPI_1RB0RB_1LA1LC_1LB0RD_0LC1RD). Qed.
Lemma phSTPO_1RB0RB_1LA1LC_1LB0RD_0LC1RD : forall R, csteps tm 7 (StC,([S1;S0],S0,R)) = Some (StD,([S0],S1,S1::S1::S1::R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_STPO_1RB0RB_1LA1LC_1LB0RD_0LC1RD). Qed.
Lemma phRET_1RB0RB_1LA1LC_1LB0RD_0LC1RD : forall k L R, csteps tm (1*k) (StD,(L,S1,rep [S1] k ++ R)) = Some (StD,(rep [S1] k ++ L,S1,R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U_RET_1RB0RB_1LA1LC_1LB0RD_0LC1RD k L R). Qed.
Lemma phFIN_1RB0RB_1LA1LC_1LB0RD_0LC1RD : forall L R, csteps tm 4 (StD,(L,S1,S0::R)) = Some (StC,(L,S0,S0::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_FIN_1RB0RB_1LA1LC_1LB0RD_0LC1RD). Qed.
Lemma phVA_1RB0RB_1LA1LC_1LB0RD_0LC1RD : forall R, csteps tm 4 (StC,([S1;S0],S0,R)) = Some (StA,([],S0,S1::S1::S1::S1::R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_VA_1RB0RB_1LA1LC_1LB0RD_0LC1RD). Qed.
Lemma phVB_1RB0RB_1LA1LC_1LB0RD_0LC1RD : forall L R, csteps tm 1 (StC,(S1::L,S0,R)) = Some (StB,(L,S1,S1::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_VB_1RB0RB_1LA1LC_1LB0RD_0LC1RD). Qed.

(** EXACT lap on BOTH branches: iterate to the next anchor with the exact
    config.  The [S0] far-side cell makes the frontier close an ordinary
    closed window, so no lift is needed anywhere in the chain. *)
Lemma lap_exact_1RB0RB_1LA1LC_1LB0RD_0LC1RD : forall p, exists n c', csteps tm n (Cc p) = Some c' /\ c' = Cc (Pos.succ p) /\ 0 < n.
Proof.
  intros p.
  destruct (cview p) as [j oq] eqn:Ecv. unfold Cc_1RB0RB_1LA1LC_1LB0RD_0LC1RD.
  destruct oq as [q0|].
  - destruct (cview_some_J p j q0 Ecv) as (HJp & HJs).
    do 2 eexists. split; [|split].
    + rewrite HJp, <- app_assoc. cbn [app].
      eapply csteps_chain. { apply phRIP_1RB0RB_1LA1LC_1LB0RD_0LC1RD. }
      eapply csteps_chain. { apply phSTPI_1RB0RB_1LA1LC_1LB0RD_0LC1RD. }
      rewrite rep_dbl.
      change (S1 :: rep [S1] (2*j) ++ [S0]) with (rep [S1] (S (2*j)) ++ [S0]).
      eapply csteps_chain. { apply (phRET_1RB0RB_1LA1LC_1LB0RD_0LC1RD (S (2*j))). }
      apply phFIN_1RB0RB_1LA1LC_1LB0RD_0LC1RD.
    + rewrite HJs, rep_dbl, <- app_assoc. cbn [app].
      rewrite <- rep_slide. reflexivity.
    + lia.
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_J p j' Ecv) as (HJp & HJs).
    do 2 eexists. split; [|split].
    + rewrite HJp, <- app_assoc. cbn [app].
      eapply csteps_chain. { apply phRIP_1RB0RB_1LA1LC_1LB0RD_0LC1RD. }
      eapply csteps_chain. { apply phSTPO_1RB0RB_1LA1LC_1LB0RD_0LC1RD. }
      rewrite rep_dbl.
      change (S1 :: S1 :: S1 :: rep [S1] (2*j') ++ [S0]) with (rep [S1] (S (S (S (2*j')))) ++ [S0]).
      eapply csteps_chain. { apply (phRET_1RB0RB_1LA1LC_1LB0RD_0LC1RD (S (S (S (2*j'))))). }
      apply phFIN_1RB0RB_1LA1LC_1LB0RD_0LC1RD.
    + rewrite HJs, rep_dbl.
      replace (2 * S j') with (S (S (2 * j'))) by lia.
      rewrite <- app_assoc. cbn [app]. rewrite <- rep_slide. reflexivity.
    + lia.
Qed.

Lemma lap_1RB0RB_1LA1LC_1LB0RD_0LC1RD : forall p, exists n c', csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof. intro p. destruct (lap_exact_1RB0RB_1LA1LC_1LB0RD_0LC1RD p) as (n & c' & Hr & Hc & Hn).
  exists n, c'. split; [exact Hr | split; [rewrite Hc; reflexivity | exact Hn]]. Qed.

Lemma boot_1RB0RB_1LA1LC_1LB0RD_0LC1RD : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 23.
  assert (H : match csteps tm 23 c0 with Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 23 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** StA fires only inside the OVERFLOW stop; reach an all-ones counter by
    well-founded induction on [tovf] (strictly decreasing along interior
    laps, which close EXACTLY), then run the stop prefix. *)
Lemma vis_A_1RB0RB_1LA1LC_1LB0RD_0LC1RD : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = StA.
Proof.
  intro p; remember (tovf p) as fuel eqn:Ef; revert p Ef.
  induction fuel as [fuel IH] using (well_founded_induction lt_wf); intros p Ef.
  destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - assert (Hnz : tovf p <> 0).
    { intro H0. destruct (tovf0_allones p H0) as (jj & Hjj). rewrite Hjj in Ecv; discriminate. }
    destruct (lap_exact_1RB0RB_1LA1LC_1LB0RD_0LC1RD p) as (n & c' & Hrun & Hc' & _). subst c'.
    destruct (IH (tovf (Pos.succ p)) (ltac:(rewrite tovf_succ by lia; lia)) (Pos.succ p) eq_refl) as (k & c & Hk & Hq).
    exists (n + k), c. rewrite csteps_add, Hrun. exact (conj Hk Hq).
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_J p j' Ecv) as (HJp & _).
    unfold Cc_1RB0RB_1LA1LC_1LB0RD_0LC1RD. eexists. eexists. split.
    * rewrite HJp, <- app_assoc. cbn [app].
      eapply csteps_chain. { apply phRIP_1RB0RB_1LA1LC_1LB0RD_0LC1RD. }
      apply phVA_1RB0RB_1LA1LC_1LB0RD_0LC1RD.
    * reflexivity.
Qed.

(** StD is entered by BOTH stop windows, so every lap visits it: case on
    [cview] and run ripple + the matching stop. *)
Lemma vis_D_1RB0RB_1LA1LC_1LB0RD_0LC1RD : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = StD.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - destruct (cview_some_J p j q0 Ecv) as (HJp & _).
    unfold Cc_1RB0RB_1LA1LC_1LB0RD_0LC1RD. eexists. eexists. split.
    + rewrite HJp, <- app_assoc. cbn [app].
      eapply csteps_chain. { apply phRIP_1RB0RB_1LA1LC_1LB0RD_0LC1RD. }
      apply phSTPI_1RB0RB_1LA1LC_1LB0RD_0LC1RD.
    + reflexivity.
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_J p j' Ecv) as (HJp & _).
    unfold Cc_1RB0RB_1LA1LC_1LB0RD_0LC1RD. eexists. eexists. split.
    + rewrite HJp, <- app_assoc. cbn [app].
      eapply csteps_chain. { apply phRIP_1RB0RB_1LA1LC_1LB0RD_0LC1RD. }
      apply phSTPO_1RB0RB_1LA1LC_1LB0RD_0LC1RD.
    + reflexivity.
Qed.

Lemma vis_1RB0RB_1LA1LC_1LB0RD_0LC1RD : forall p q, exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q. destruct q.
  - apply vis_A_1RB0RB_1LA1LC_1LB0RD_0LC1RD.
  - (* StB : 1 step from the anchor *)
    destruct (Jp_head p) as (w & Hw). unfold Cc_1RB0RB_1LA1LC_1LB0RD_0LC1RD.
    rewrite Hw. cbn [app]. exists 1. eexists. split.
    + apply phVB_1RB0RB_1LA1LC_1LB0RD_0LC1RD.
    + reflexivity.
  - (* StC : the anchor state *)
    exists 0. eexists. split; reflexivity.
  - apply vis_D_1RB0RB_1LA1LC_1LB0RD_0LC1RD.
Qed.

Theorem nqh_1RB0RB_1LA1LC_1LB0RD_0LC1RD : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc 1). - exact boot_1RB0RB_1LA1LC_1LB0RD_0LC1RD. - intros p _. apply lap_1RB0RB_1LA1LC_1LB0RD_0LC1RD. - intros p q _. apply vis_1RB0RB_1LA1LC_1LB0RD_0LC1RD. Qed.

Theorem nonhalt_1RB0RB_1LA1LC_1LB0RD_0LC1RD : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_1RB0RB_1LA1LC_1LB0RD_0LC1RD. Qed.
