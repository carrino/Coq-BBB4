(** * ILC_1RB1LC_1LB1RA_1LA0RD_0LA1RD: comb-free interleaved binary counter, machine
    1RB1LC_1LB1RA_1LA0RD_0LA1RD.

    Auto-emitted by tools/counters/emit_interleave.py (UNTRUSTED emitter; the
    Coq kernel re-checks everything below).  Left-growth counter under the
    complemented interleave encoding [Jp] (JpCounter.v).  The anchor is

      Cc p = (StD, (Jp p ++ [S0;S1;S0], S0, []))

    -- the counter on the LEFT list nearest-first, a blank head at the fixed
    right frontier, empty right side, no comb.  One lap Cc p -> Cc (p+1) is a
    single sweep:

      P1   prologue: read the frontier, turn left into the counter;
      RIP  leftward carry ripple over the low set-bit pairs (cycL, 2
           steps per pair, j pairs where cview p = (j, _));
      STPI interior stop -- flip the first clear pair (cview p = (j,Some q));
      STPO overflow stop off the DEEP-LEFT tape edge (cview p = (S j,None)),
           growing the counter by a fresh most-significant pair;
      RET  rightward return over the deposited cells (cycR);
      FIN  close at the frontier.

    All six windows were derived by simulation and the whole decomposition was
    differentially validated against the raw simulator on both cview branches
    for p = 1..160 plus sparse p up to 2^14 (step counts AND configurations).
    Axiom footprint: [functional_extensionality_dep] (via CTape.lift). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter ILCounter JpCounter.
Import ListNotations.

Definition mk_1RB1LC_1LB1RA_1LA0RD_0LA1RD (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB1LC_1LB1RA_1LA0RD_0LA1RD.

(** 1RB1LC_1LB1RA_1LA0RD_0LA1RD *)
Definition tm_1RB1LC_1LB1RA_1LA0RD_0LA1RD : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DL StC
  | StB, S0 => mk S1 DL StB | StB, S1 => mk S1 DR StA
  | StC, S0 => mk S1 DL StA | StC, S1 => mk S0 DR StD
  | StD, S0 => mk S0 DL StA | StD, S1 => mk S1 DR StD end.
Local Notation tm := tm_1RB1LC_1LB1RA_1LA0RD_0LA1RD.

Definition Cc_1RB1LC_1LB1RA_1LA0RD_0LA1RD (p : positive) : cconf := (StD, (Jp p ++ [S0;S1;S0], S0, [])).
Local Notation Cc := Cc_1RB1LC_1LB1RA_1LA0RD_0LA1RD.

(** ** The six lap unit windows (each closed by [reflexivity]) *)
Lemma U_P1_1RB1LC_1LB1RA_1LA0RD_0LA1RD : wsteps true true tm 1 (StD,([S1],S0,[])) = Some (StA,([],S1,[S0])). Proof. reflexivity. Qed.
Lemma U_RIP_1RB1LC_1LB1RA_1LA0RD_0LA1RD : wsteps true true tm 2 (StA,([S0;S1],S1,[])) = Some (StA,([],S1,[S1;S1])). Proof. reflexivity. Qed.
Lemma U_STPI_1RB1LC_1LB1RA_1LA0RD_0LA1RD : wsteps true true tm 2 (StA,([S1],S1,[])) = Some (StD,([S0],S1,[])). Proof. reflexivity. Qed.
Lemma U_STPO_1RB1LC_1LB1RA_1LA0RD_0LA1RD : wsteps false true tm 8 (StA,([S0;S1;S0],S1,[])) = Some (StD,([S0;S1],S1,[S1;S1])). Proof. reflexivity. Qed.
Lemma U_RET_1RB1LC_1LB1RA_1LA0RD_0LA1RD : wsteps true true tm 1 (StD,([],S1,[S1])) = Some (StD,([S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_FIN_1RB1LC_1LB1RA_1LA0RD_0LA1RD : wsteps true true tm 1 (StD,([],S1,[S0])) = Some (StD,([S1],S0,[])). Proof. reflexivity. Qed.

(** ** Transported phases (framing = each unit's bl/br) *)
Lemma phP1_1RB1LC_1LB1RA_1LA0RD_0LA1RD : forall L R, csteps tm 1 (StD,(S1::L,S0,R)) = Some (StA,(L,S1,S0::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_P1_1RB1LC_1LB1RA_1LA0RD_0LA1RD). Qed.
Lemma phRIP_1RB1LC_1LB1RA_1LA0RD_0LA1RD : forall k L R, csteps tm (2*k) (StA,(rep [S0;S1] k ++ L,S1,R)) = Some (StA,(L,S1,rep [S1;S1] k ++ R)).
Proof. intros. pose proof (cycL _ _ _ _ _ _ _ U_RIP_1RB1LC_1LB1RA_1LA0RD_0LA1RD k L R) as H; cbn [app] in H; exact H. Qed.
Lemma phSTPI_1RB1LC_1LB1RA_1LA0RD_0LA1RD : forall L R, csteps tm 2 (StA,(S1::L,S1,R)) = Some (StD,(S0::L,S1,R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_STPI_1RB1LC_1LB1RA_1LA0RD_0LA1RD). Qed.
Lemma phSTPO_1RB1LC_1LB1RA_1LA0RD_0LA1RD : forall R, csteps tm 8 (StA,([S0;S1;S0],S1,R)) = Some (StD,([S0;S1],S1,S1::S1::R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_STPO_1RB1LC_1LB1RA_1LA0RD_0LA1RD). Qed.
Lemma phRET_1RB1LC_1LB1RA_1LA0RD_0LA1RD : forall k L R, csteps tm (1*k) (StD,(L,S1,rep [S1] k ++ R)) = Some (StD,(rep [S1] k ++ L,S1,R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U_RET_1RB1LC_1LB1RA_1LA0RD_0LA1RD k L R). Qed.
Lemma phFIN_1RB1LC_1LB1RA_1LA0RD_0LA1RD : forall L R, csteps tm 1 (StD,(L,S1,S0::R)) = Some (StD,(S1::L,S0,R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_FIN_1RB1LC_1LB1RA_1LA0RD_0LA1RD). Qed.

(** ** The lap *)

(** Interior branch: EXACT (the next anchor on the nose) -- the deep-visit
    induction below chains on this equality. *)
Lemma lap_int_1RB1LC_1LB1RA_1LA0RD_0LA1RD : forall p j q0, cview p = (j, Some q0) ->
  exists n c', csteps tm n (Cc p) = Some c' /\ c' = Cc (Pos.succ p) /\ 0 < n.
Proof.
  intros p j q0 Ecv. unfold Cc_1RB1LC_1LB1RA_1LA0RD_0LA1RD.
  destruct (cview_some_J p j q0 Ecv) as (HJp & HJs).
  do 2 eexists. split; [|split].
  + rewrite HJp, <- app_assoc.
    change (rep [S1;S0] j ++ (S1 :: S1 :: Jp q0) ++ [S0;S1;S0])
      with (rep [S1;S0] j ++ [S1] ++ (S1 :: Jp q0 ++ [S0;S1;S0])).
    rewrite app_assoc, pair_rot.
    eapply csteps_chain. { apply phP1_1RB1LC_1LB1RA_1LA0RD_0LA1RD. }
    eapply csteps_chain. { apply phRIP_1RB1LC_1LB1RA_1LA0RD_0LA1RD. }
    eapply csteps_chain. { apply phSTPI_1RB1LC_1LB1RA_1LA0RD_0LA1RD. }
    rewrite rep_dbl.
    eapply csteps_chain. { apply (phRET_1RB1LC_1LB1RA_1LA0RD_0LA1RD (2*j)). }
    apply phFIN_1RB1LC_1LB1RA_1LA0RD_0LA1RD.
  + rewrite HJs, rep_dbl. cbn [Nat.mul]. rewrite rep_slide, <- !app_assoc. reflexivity.
  + lia.
Qed.

(** Fold the next anchor's counter into a single run of ones. *)
Lemma fold_tgt_1RB1LC_1LB1RA_1LA0RD_0LA1RD : forall k, (rep [S1;S1] k ++ [S1]) ++ [S0;S1;S0] = rep [S1] (S (2*k)) ++ [S0;S1;S0].
Proof. intro k. rewrite rep_dbl, rep_shift. reflexivity. Qed.

(** The lap's last step deposits one more [S1], and the overflow stop leaves
    [[S0;S1]] at the deep edge: fold both into the run of ones. *)
Lemma fold_ov_1RB1LC_1LB1RA_1LA0RD_0LA1RD : forall k, S1 :: rep [S1] k ++ [S0;S1] = rep [S1] (S k + 0) ++ [S0;S1].
Proof. intro k. rewrite rep_add, <- !app_assoc. reflexivity. Qed.

Lemma lift_l_blank_1RB1LC_1LB1RA_1LA0RD_0LA1RD : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma close_1RB1LC_1LB1RA_1LA0RD_0LA1RD : forall a b q h, a = b ->
  lift (q,(rep [S1] a ++ [S0;S1], h, [])) = lift (q,(rep [S1] b ++ [S0;S1;S0], h, [])).
Proof. intros a b q h ->.
  replace (rep [S1] b ++ [S0;S1;S0]) with ((rep [S1] b ++ [S0;S1]) ++ [S0])
    by (rewrite <- app_assoc; reflexivity).
  rewrite lift_l_blank_1RB1LC_1LB1RA_1LA0RD_0LA1RD. reflexivity. Qed.

Lemma lap_1RB1LC_1LB1RA_1LA0RD_0LA1RD : forall p, exists n c', csteps tm n (Cc p) = Some c' /\
  lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:Ecv.
  destruct oq as [q0|].
  - destruct (lap_int_1RB1LC_1LB1RA_1LA0RD_0LA1RD p j q0 Ecv) as (n & c' & H1 & H2 & H3).
    exists n, c'. split; [exact H1|split; [rewrite H2; reflexivity|exact H3]].
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_J p j' Ecv) as (HJp & HJs).
    unfold Cc_1RB1LC_1LB1RA_1LA0RD_0LA1RD. do 2 eexists. split; [|split].
    + rewrite HJp, pair_rot.
      eapply csteps_chain. { apply phP1_1RB1LC_1LB1RA_1LA0RD_0LA1RD. }
      eapply csteps_chain. { apply phRIP_1RB1LC_1LB1RA_1LA0RD_0LA1RD. }
      eapply csteps_chain. { apply phSTPO_1RB1LC_1LB1RA_1LA0RD_0LA1RD. }
      rewrite rep_dbl.
      change (S1::S1::rep [S1] (2*j') ++ [S0]) with (rep [S1] (S (S (2*j'))) ++ [S0]).
      eapply csteps_chain. { apply (phRET_1RB1LC_1LB1RA_1LA0RD_0LA1RD (S (S (2*j')))). }
      apply phFIN_1RB1LC_1LB1RA_1LA0RD_0LA1RD.
    + rewrite HJs, fold_tgt_1RB1LC_1LB1RA_1LA0RD_0LA1RD, fold_ov_1RB1LC_1LB1RA_1LA0RD_0LA1RD.
      apply close_1RB1LC_1LB1RA_1LA0RD_0LA1RD. lia.
    + lia.
Qed.

Lemma boot_1RB1LC_1LB1RA_1LA0RD_0LA1RD : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 14.
  assert (H : match csteps tm 14 c0 with Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 14 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** The deep state StB is only visited inside the OVERFLOW stop; reach an
    all-ones counter by well-founded induction on [tovf] (which strictly
    decreases along the interior laps) and then run the stop prefix. *)
Lemma U_VD1_1RB1LC_1LB1RA_1LA0RD_0LA1RD : wsteps false true tm 5 (StA,([S0;S1;S0],S1,[])) = Some (StB,([S1],S1,[S1;S1;S1])). Proof. reflexivity. Qed.
Lemma phVD1_1RB1LC_1LB1RA_1LA0RD_0LA1RD : forall R, csteps tm 5 (StA,([S0;S1;S0],S1,R)) = Some (StB,([S1],S1,S1::S1::S1::R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_VD1_1RB1LC_1LB1RA_1LA0RD_0LA1RD). Qed.

Lemma vis_deep1_1RB1LC_1LB1RA_1LA0RD_0LA1RD : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = StB.
Proof.
  intro p; remember (tovf p) as fuel eqn:Ef; revert p Ef.
  induction fuel as [fuel IH] using (well_founded_induction lt_wf); intros p Ef.
  destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - assert (Hnz : tovf p <> 0).
    { intro H0. destruct (tovf0_allones p H0) as (jj & Hjj). rewrite Hjj in Ecv; discriminate. }
    destruct (lap_int_1RB1LC_1LB1RA_1LA0RD_0LA1RD p j q0 Ecv) as (n & c' & Hrun & Hc' & _). subst c'.
    destruct (IH (tovf (Pos.succ p)) (ltac:(rewrite tovf_succ by lia; lia)) (Pos.succ p) eq_refl) as (k & c & Hk & Hq).
    exists (n + k), c. rewrite csteps_add, Hrun. exact (conj Hk Hq).
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_J p j' Ecv) as (HJp & _).
    unfold Cc_1RB1LC_1LB1RA_1LA0RD_0LA1RD. eexists. eexists. split.
    * rewrite HJp, pair_rot.
      eapply csteps_chain. { apply phP1_1RB1LC_1LB1RA_1LA0RD_0LA1RD. }
      eapply csteps_chain. { apply phRIP_1RB1LC_1LB1RA_1LA0RD_0LA1RD. }
      apply phVD1_1RB1LC_1LB1RA_1LA0RD_0LA1RD.
    * reflexivity.
Qed.

(** ** Bounded anchor prefixes for the shallow states *)
Lemma phV1_1RB1LC_1LB1RA_1LA0RD_0LA1RD : forall x L R, csteps tm 1 (StD,(S1::x::L,S0,R)) = Some (StA,(x::L,S1,S0::R)).
Proof. intros. reflexivity. Qed.
Lemma phV2_1RB1LC_1LB1RA_1LA0RD_0LA1RD : forall x L R, csteps tm 2 (StD,(S1::x::L,S0,R)) = Some (StC,(L,x,S1::S0::R)).
Proof. intros. reflexivity. Qed.

Lemma vis_1RB1LC_1LB1RA_1LA0RD_0LA1RD : forall p q, exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q. destruct (Jp_head p) as (w & Hw). unfold Cc_1RB1LC_1LB1RA_1LA0RD_0LA1RD. destruct q.
  - (* StA : 1 steps from the anchor (p = 1 apart) *)
    rewrite Hw. destruct w as [|x w'].
    + exists 1. eexists. split; [vm_compute; reflexivity | reflexivity].
    + exists 1. eexists. split.
      * change ((S1 :: x :: w') ++ [S0;S1;S0]) with (S1 :: x :: (w' ++ [S0;S1;S0])).
        apply phV1_1RB1LC_1LB1RA_1LA0RD_0LA1RD.
      * reflexivity.
  - (* StB : deep (overflow) state *)
    apply (vis_deep1_1RB1LC_1LB1RA_1LA0RD_0LA1RD p).
  - (* StC : 2 steps from the anchor (p = 1 apart) *)
    rewrite Hw. destruct w as [|x w'].
    + exists 2. eexists. split; [vm_compute; reflexivity | reflexivity].
    + exists 2. eexists. split.
      * change ((S1 :: x :: w') ++ [S0;S1;S0]) with (S1 :: x :: (w' ++ [S0;S1;S0])).
        apply phV2_1RB1LC_1LB1RA_1LA0RD_0LA1RD.
      * reflexivity.
  - (* StD : the anchor state *)
    exists 0. eexists. split; reflexivity.
Qed.

Theorem nqh_1RB1LC_1LB1RA_1LA0RD_0LA1RD : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc 1). - exact boot_1RB1LC_1LB1RA_1LA0RD_0LA1RD. - intros p _. apply lap_1RB1LC_1LB1RA_1LA0RD_0LA1RD. - intros p q _. apply vis_1RB1LC_1LB1RA_1LA0RD_0LA1RD. Qed.

Theorem nonhalt_1RB1LC_1LB1RA_1LA0RD_0LA1RD : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_1RB1LC_1LB1RA_1LA0RD_0LA1RD. Qed.
