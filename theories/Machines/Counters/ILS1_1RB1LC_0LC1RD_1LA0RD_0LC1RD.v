(** * ILS1_1RB1LC_0LC1RD_1LA0RD_0LC1RD: lap-shape-1 interleaved binary counter, machine
    1RB1LC_0LC1RD_1LA0RD_0LC1RD.

    Auto-emitted by tools/counters/emit_shape1.py (UNTRUSTED emitter; the Coq
    kernel re-checks every line below), cloning the hand-authored reference
    board ILS1_1RB0RB_1LA1LC_1LB0RD_0LC1RD.v.  Left-growth counter under the
    complemented interleave encoding [Jp] (JpCounter.v), anchored at

      Cc p = (StC, (Jp p ++ [S0], S0, [S0]))

    -- the counter on the LEFT list nearest-first, a blank head at the fixed
    right frontier, and a blank far-side CELL (not the empty list).  One lap
    Cc p -> Cc (p+1) is a FOUR-window chain: RIP leftward carry ripple (cycL,
    2 steps per low set pair; no P1 prologue -- the anchor's blank head
    rotates through as the unit's own data cell); STPI interior stop (3
    steps) / STPO overflow stop off the deep-left edge (5 steps,
    left-open); RET rightward return (cycR, 1 step per deposited cell,
    count 1+2j interior / 1+2j' overflow); FIN frontier close (4
    steps, shared by both branches).  The INTERIOR branch closes EXACTLY
    (feeding the deep-visit induction); the overflow branch closes up to one trailing blank on the left (the wall case).

    Step counts were derived by exact symbolic replay and the decomposition
    was differentially validated against the raw simulator on BOTH cview
    branches (step counts AND exact configurations, p = 1..160 plus sparse
    p up to 2^13).  Axiom footprint: [functional_extensionality_dep] (via
    CTape.lift). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter ILCounter JpCounter.
Import ListNotations.

Definition mk_1RB1LC_0LC1RD_1LA0RD_0LC1RD (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB1LC_0LC1RD_1LA0RD_0LC1RD.

(** 1RB1LC_0LC1RD_1LA0RD_0LC1RD *)
Definition tm_1RB1LC_0LC1RD_1LA0RD_0LC1RD : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DL StC
  | StB, S0 => mk S0 DL StC | StB, S1 => mk S1 DR StD
  | StC, S0 => mk S1 DL StA | StC, S1 => mk S0 DR StD
  | StD, S0 => mk S0 DL StC | StD, S1 => mk S1 DR StD end.
Local Notation tm := tm_1RB1LC_0LC1RD_1LA0RD_0LC1RD.

Definition Cc_1RB1LC_0LC1RD_1LA0RD_0LC1RD (p : positive) : cconf := (StC, (Jp p ++ [S0], S0, [S0])).
Local Notation Cc := Cc_1RB1LC_0LC1RD_1LA0RD_0LC1RD.

(** ** The four lap unit windows + the visit units (each closed by [reflexivity]) *)
Lemma U_RIP_1RB1LC_0LC1RD_1LA0RD_0LC1RD : wsteps true true tm 2 (StC,([S1;S0],S0,[])) = Some (StC,([],S0,[S1;S1])). Proof. reflexivity. Qed.
Lemma U_STPI_1RB1LC_0LC1RD_1LA0RD_0LC1RD : wsteps true true tm 3 (StC,([S1;S1],S0,[])) = Some (StD,([S0],S1,[S1])). Proof. reflexivity. Qed.
Lemma U_STPO_1RB1LC_0LC1RD_1LA0RD_0LC1RD : wsteps false true tm 5 (StC,([S1;S0],S0,[])) = Some (StD,([S1;S1],S1,[S1])). Proof. reflexivity. Qed.
Lemma U_RET_1RB1LC_0LC1RD_1LA0RD_0LC1RD : wsteps true true tm 1 (StD,([],S1,[S1])) = Some (StD,([S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_FIN_1RB1LC_0LC1RD_1LA0RD_0LC1RD : wsteps true true tm 4 (StD,([],S1,[S0])) = Some (StC,([],S0,[S0])). Proof. reflexivity. Qed.
Lemma U_VZ_1RB1LC_0LC1RD_1LA0RD_0LC1RD : wsteps false true tm 4 (StC,([S1;S0],S0,[])) = Some (StB,([S1],S1,[S1;S1])). Proof. reflexivity. Qed.
Lemma U_VX_1RB1LC_0LC1RD_1LA0RD_0LC1RD : wsteps true true tm 1 (StC,([S1],S0,[])) = Some (StA,([],S1,[S1])). Proof. reflexivity. Qed.

(** ** Transported phases (framing = each unit's bl/br) *)
Lemma phRIP_1RB1LC_0LC1RD_1LA0RD_0LC1RD : forall k L R, csteps tm (2*k) (StC,(rep [S1;S0] k ++ L,S0,R)) = Some (StC,(L,S0,rep [S1;S1] k ++ R)).
Proof. intros. pose proof (cycL _ _ _ _ _ _ _ U_RIP_1RB1LC_0LC1RD_1LA0RD_0LC1RD k L R) as H; cbn [app] in H; exact H. Qed.
Lemma phSTPI_1RB1LC_0LC1RD_1LA0RD_0LC1RD : forall L R, csteps tm 3 (StC,(S1::S1::L,S0,R)) = Some (StD,(S0::L,S1,S1::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_STPI_1RB1LC_0LC1RD_1LA0RD_0LC1RD). Qed.
Lemma phSTPO_1RB1LC_0LC1RD_1LA0RD_0LC1RD : forall R, csteps tm 5 (StC,([S1;S0],S0,R)) = Some (StD,([S1;S1],S1,S1::R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_STPO_1RB1LC_0LC1RD_1LA0RD_0LC1RD). Qed.
Lemma phRET_1RB1LC_0LC1RD_1LA0RD_0LC1RD : forall k L R, csteps tm (1*k) (StD,(L,S1,rep [S1] k ++ R)) = Some (StD,(rep [S1] k ++ L,S1,R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U_RET_1RB1LC_0LC1RD_1LA0RD_0LC1RD k L R). Qed.
Lemma phFIN_1RB1LC_0LC1RD_1LA0RD_0LC1RD : forall L R, csteps tm 4 (StD,(L,S1,S0::R)) = Some (StC,(L,S0,S0::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_FIN_1RB1LC_0LC1RD_1LA0RD_0LC1RD). Qed.
Lemma phVZ_1RB1LC_0LC1RD_1LA0RD_0LC1RD : forall R, csteps tm 4 (StC,([S1;S0],S0,R)) = Some (StB,([S1],S1,S1::S1::R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_VZ_1RB1LC_0LC1RD_1LA0RD_0LC1RD). Qed.
Lemma phVX_1RB1LC_0LC1RD_1LA0RD_0LC1RD : forall L R, csteps tm 1 (StC,(S1::L,S0,R)) = Some (StA,(L,S1,S1::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_VX_1RB1LC_0LC1RD_1LA0RD_0LC1RD). Qed.

(** ** The lap

    Interior branch: EXACT (the next anchor on the nose) -- the deep-visit
    induction below chains on this equality. *)
Lemma lap_int_1RB1LC_0LC1RD_1LA0RD_0LC1RD : forall p j q0, cview p = (j, Some q0) ->
  exists n c', csteps tm n (Cc p) = Some c' /\ c' = Cc (Pos.succ p) /\ 0 < n.
Proof.
  intros p j q0 Ecv. unfold Cc_1RB1LC_0LC1RD_1LA0RD_0LC1RD.
  destruct (cview_some_J p j q0 Ecv) as (HJp & HJs).
  do 2 eexists. split; [|split].
  + rewrite HJp, <- app_assoc. cbn [app].
    eapply csteps_chain. { apply phRIP_1RB1LC_0LC1RD_1LA0RD_0LC1RD. }
    eapply csteps_chain. { apply phSTPI_1RB1LC_0LC1RD_1LA0RD_0LC1RD. }
    rewrite rep_dbl.
    change (S1 :: rep [S1] (2*j) ++ [S0]) with (rep [S1] (S (2*j)) ++ [S0]).
    eapply csteps_chain. { apply (phRET_1RB1LC_0LC1RD_1LA0RD_0LC1RD (S (2*j))). }
    apply phFIN_1RB1LC_0LC1RD_1LA0RD_0LC1RD.
  + rewrite HJs, rep_dbl, <- app_assoc. cbn [app].
    rewrite <- rep_slide. reflexivity.
  + lia.
Qed.

(** Fold the next anchor's counter into a single run of ones. *)
Lemma fold_tgt_1RB1LC_0LC1RD_1LA0RD_0LC1RD : forall k, (rep [S1;S1] k ++ [S1]) ++ [S0] = rep [S1] (S (2*k)) ++ [S0].
Proof. intro k. rewrite rep_dbl, rep_shift. reflexivity. Qed.

(** Fold the overflow stop's left deposit into the run of ones. *)
Lemma fold_ovL_1RB1LC_0LC1RD_1LA0RD_0LC1RD : forall k, rep [S1] k ++ [S1;S1] = rep [S1] (k + 2) ++ [].
Proof. intro k. rewrite rep_add, <- !app_assoc. reflexivity. Qed.

(** Wall-overflow close: the overflow rebuilds the wall one cell deeper and
    consumes the anchor's synthetic deep blank; the two agree under [lift]. *)
Lemma lift_lblank_1RB1LC_0LC1RD_1LA0RD_0LC1RD : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma closeO_1RB1LC_0LC1RD_1LA0RD_0LC1RD : forall a b (q : St) (h : Sym) r, a = b ->
  lift (q,(rep [S1] a ++ [], h, r)) = lift (q,(rep [S1] b ++ [S0], h, r)).
Proof.
  intros a b q h r ->.
  replace (rep [S1] b ++ [S0]) with ((rep [S1] b ++ []) ++ [S0])
    by (rewrite <- app_assoc; reflexivity).
  rewrite lift_lblank_1RB1LC_0LC1RD_1LA0RD_0LC1RD. reflexivity.
Qed.

Lemma lap_ov_1RB1LC_0LC1RD_1LA0RD_0LC1RD : forall p j', cview p = (S j', None) ->
  exists n c', csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j' Ecv. unfold Cc_1RB1LC_0LC1RD_1LA0RD_0LC1RD.
  destruct (cview_none_J p j' Ecv) as (HJp & HJs).
  do 2 eexists. split; [|split].
  + rewrite HJp, <- app_assoc. cbn [app].
    eapply csteps_chain. { apply phRIP_1RB1LC_0LC1RD_1LA0RD_0LC1RD. }
    eapply csteps_chain. { apply phSTPO_1RB1LC_0LC1RD_1LA0RD_0LC1RD. }
    rewrite rep_dbl.
    change (S1 :: rep [S1] (2*j') ++ [S0]) with (rep [S1] (S (2*j')) ++ [S0]).
    eapply csteps_chain. { apply (phRET_1RB1LC_0LC1RD_1LA0RD_0LC1RD (S (2*j'))). }
    apply phFIN_1RB1LC_0LC1RD_1LA0RD_0LC1RD.
  + rewrite HJs, fold_tgt_1RB1LC_0LC1RD_1LA0RD_0LC1RD, fold_ovL_1RB1LC_0LC1RD_1LA0RD_0LC1RD. apply closeO_1RB1LC_0LC1RD_1LA0RD_0LC1RD. lia.
  + lia.
Qed.

Lemma lap_1RB1LC_0LC1RD_1LA0RD_0LC1RD : forall p, exists n c', csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - destruct (lap_int_1RB1LC_0LC1RD_1LA0RD_0LC1RD p j q0 Ecv) as (n & c' & H1 & H2 & H3).
    exists n, c'. split; [exact H1|split; [rewrite H2; reflexivity|exact H3]].
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    exact (lap_ov_1RB1LC_0LC1RD_1LA0RD_0LC1RD p j' Ecv).
Qed.

Lemma boot_1RB1LC_0LC1RD_1LA0RD_0LC1RD : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 10.
  assert (H : match csteps tm 10 c0 with Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 10 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** StB fires only inside the OVERFLOW stop; reach an all-ones counter by
    well-founded induction on [tovf] (strictly decreasing along interior
    laps, which close EXACTLY), then run the stop prefix. *)
Lemma vis_Z_1RB1LC_0LC1RD_1LA0RD_0LC1RD : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = StB.
Proof.
  intro p; remember (tovf p) as fuel eqn:Ef; revert p Ef.
  induction fuel as [fuel IH] using (well_founded_induction lt_wf); intros p Ef.
  destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - assert (Hnz : tovf p <> 0).
    { intro H0. destruct (tovf0_allones p H0) as (jj & Hjj). rewrite Hjj in Ecv; discriminate. }
    destruct (lap_int_1RB1LC_0LC1RD_1LA0RD_0LC1RD p j q0 Ecv) as (n & c' & Hrun & Hc' & _). subst c'.
    destruct (IH (tovf (Pos.succ p)) (ltac:(rewrite tovf_succ by lia; lia)) (Pos.succ p) eq_refl) as (k & c & Hk & Hq).
    exists (n + k), c. rewrite csteps_add, Hrun. exact (conj Hk Hq).
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_J p j' Ecv) as (HJp & _).
    unfold Cc_1RB1LC_0LC1RD_1LA0RD_0LC1RD. eexists. eexists. split.
    * rewrite HJp, <- app_assoc. cbn [app].
      eapply csteps_chain. { apply phRIP_1RB1LC_0LC1RD_1LA0RD_0LC1RD. }
      apply phVZ_1RB1LC_0LC1RD_1LA0RD_0LC1RD.
    * reflexivity.
Qed.

(** StD is entered by BOTH stop windows, so every lap visits it: case on
    [cview] and run ripple + the matching stop. *)
Lemma vis_T_1RB1LC_0LC1RD_1LA0RD_0LC1RD : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = StD.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - destruct (cview_some_J p j q0 Ecv) as (HJp & _).
    unfold Cc_1RB1LC_0LC1RD_1LA0RD_0LC1RD. eexists. eexists. split.
    + rewrite HJp, <- app_assoc. cbn [app].
      eapply csteps_chain. { apply phRIP_1RB1LC_0LC1RD_1LA0RD_0LC1RD. }
      apply phSTPI_1RB1LC_0LC1RD_1LA0RD_0LC1RD.
    + reflexivity.
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_J p j' Ecv) as (HJp & _).
    unfold Cc_1RB1LC_0LC1RD_1LA0RD_0LC1RD. eexists. eexists. split.
    + rewrite HJp, <- app_assoc. cbn [app].
      eapply csteps_chain. { apply phRIP_1RB1LC_0LC1RD_1LA0RD_0LC1RD. }
      apply phSTPO_1RB1LC_0LC1RD_1LA0RD_0LC1RD.
    + reflexivity.
Qed.

Lemma vis_1RB1LC_0LC1RD_1LA0RD_0LC1RD : forall p q, exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q. destruct q.
  - (* StA : 1 step from the anchor *)
    destruct (Jp_head p) as (w & Hw). unfold Cc_1RB1LC_0LC1RD_1LA0RD_0LC1RD.
    rewrite Hw. cbn [app]. exists 1. eexists. split.
    + apply phVX_1RB1LC_0LC1RD_1LA0RD_0LC1RD.
    + reflexivity.
  - apply vis_Z_1RB1LC_0LC1RD_1LA0RD_0LC1RD.
  - (* StC : the anchor state *)
    exists 0. eexists. split; reflexivity.
  - apply vis_T_1RB1LC_0LC1RD_1LA0RD_0LC1RD.
Qed.

Theorem nqh_1RB1LC_0LC1RD_1LA0RD_0LC1RD : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc 1). - exact boot_1RB1LC_0LC1RD_1LA0RD_0LC1RD. - intros p _. apply lap_1RB1LC_0LC1RD_1LA0RD_0LC1RD. - intros p q _. apply vis_1RB1LC_0LC1RD_1LA0RD_0LC1RD. Qed.

Theorem nonhalt_1RB1LC_0LC1RD_1LA0RD_0LC1RD : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_1RB1LC_0LC1RD_1LA0RD_0LC1RD. Qed.
