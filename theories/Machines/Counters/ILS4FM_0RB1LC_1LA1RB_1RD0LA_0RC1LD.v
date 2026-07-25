(** * ILS4F_0RB1LC_1LA1RB_1RD0LA_0RC1LD: frontier-flip [Ip] interleaved binary counter, machine
    0RB1LC_1LA1RB_1RD0LA_0RC1LD (the affine half of the `+XY|-YX|+XY` lap-shape family).

    Auto-emitted by tools/counters/emit_shape4.py --flip (UNTRUSTED emitter;
    the Coq kernel re-checks every line below).  Left-growth counter under
    the DIRECT interleave encoding [Ip] (ILCounter.v), anchored at

      Cc p = (StB, (Ip p ++ [S1;S0], S0, [S0]))

    -- a blank head at the frontier and a blank far-side CELL.  One lap:

      P1   flip the frontier cell inside the far window (2 steps,
           returning to StB);
      RIP  leftward 1-cell run (cycL, 1 step per cell, THROUGH the LSB
           marker: 2j+1 cells interior, 2j'+2 incl the wall on overflow);
      STPI/TRN  pop the clear bit, turn right (interior, 1+1);
      STPO bounce off the synthetic deep blank (2 steps, overflow);
      RET  rightward rewrite cycle [S1;S1] -> [S0;S1] (cycR, 2 steps
           per pair; j pairs interior, S j' on overflow);
      FIN  frontier close (3 steps, interior, EXACT) / FIN2 overflow
           close (7 steps, open-right past the far cell, eating the
           last return pair's S0; closes one LEFT blank short -> lift).

    Derived by exact symbolic replay; differentially validated against the
    raw simulator on BOTH cview branches (counts AND exact configurations,
    p = 1..160 plus sparse p to 2^13).  Axiom footprint:
    [functional_extensionality_dep] (via CTape.lift). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From Coq Require Import FunctionalExtensionality.
From BBB4.Counters Require Import WTape LapGlue MonoCounter ILCounter JpCounter.
Import ListNotations.

Definition mk_0RB1LC_1LA1RB_1RD0LA_0RC1LD (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_0RB1LC_1LA1RB_1RD0LA_0RC1LD.

(** 0RB1LC_1LA1RB_1RD0LA_0RC1LD *)
(** 0RB1LC_1LA1RB_1RD0LA_0RC1LD -- the real machine (its counter grows RIGHT). *)
Definition tm_0RB1LC_1LA1RB_1RD0LA_0RC1LD : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S1 DL StC
  | StB, S0 => mk S1 DL StA | StB, S1 => mk S1 DR StB
  | StC, S0 => mk S1 DR StD | StC, S1 => mk S0 DL StA
  | StD, S0 => mk S0 DR StC | StD, S1 => mk S1 DL StD end.

(** Its mirror 0LB1RC_1RA1LB_1LD0RA_0LC1RD: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_0RB1LC_1LA1RB_1RD0LA_0RC1LD : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DL StB | StA, S1 => mk S1 DR StC
  | StB, S0 => mk S1 DR StA | StB, S1 => mk S1 DL StB
  | StC, S0 => mk S1 DL StD | StC, S1 => mk S0 DR StA
  | StD, S0 => mk S0 DL StC | StD, S1 => mk S1 DR StD end.
Local Notation tm := tmm_0RB1LC_1LA1RB_1RD0LA_0RC1LD.

Lemma mirror_ok_0RB1LC_1LA1RB_1RD0LA_0RC1LD : mirror_tm tm_0RB1LC_1LA1RB_1RD0LA_0RC1LD = tmm_0RB1LC_1LA1RB_1RD0LA_0RC1LD.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_0RB1LC_1LA1RB_1RD0LA_0RC1LD (p : positive) : cconf := (StB, (Ip p ++ [S1;S0], S0, [S0])).
Local Notation Cc := Cc_0RB1LC_1LA1RB_1RD0LA_0RC1LD.

(** ** The lap unit windows (each closed by [reflexivity]) *)
Lemma U_P1_0RB1LC_1LA1RB_1RD0LA_0RC1LD : wsteps true true tm 2 (StB,([],S0,[S0])) = Some (StB,([],S1,[S0])). Proof. reflexivity. Qed.
Lemma U_RIP_0RB1LC_1LA1RB_1RD0LA_0RC1LD : wsteps true true tm 1 (StB,([S1],S1,[])) = Some (StB,([],S1,[S1])). Proof. reflexivity. Qed.
Lemma U_STPI_0RB1LC_1LA1RB_1RD0LA_0RC1LD : wsteps true true tm 1 (StB,([S0],S1,[])) = Some (StB,([],S0,[S1])). Proof. reflexivity. Qed.
Lemma U_TRN_0RB1LC_1LA1RB_1RD0LA_0RC1LD : wsteps true true tm 1 (StB,([],S0,[S1])) = Some (StA,([S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_RET_0RB1LC_1LA1RB_1RD0LA_0RC1LD : wsteps true true tm 2 (StA,([],S1,[S1;S1])) = Some (StA,([S0;S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_FIN_0RB1LC_1LA1RB_1RD0LA_0RC1LD : wsteps true true tm 3 (StA,([],S1,[S1;S0])) = Some (StB,([S1],S0,[S0])). Proof. reflexivity. Qed.
Lemma U_STPO_0RB1LC_1LA1RB_1RD0LA_0RC1LD : wsteps false true tm 2 (StB,([S0],S1,[])) = Some (StA,([S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_FIN2_0RB1LC_1LA1RB_1RD0LA_0RC1LD : wsteps true false tm 7 (StA,([],S1,[S0])) = Some (StB,([S1],S0,[S0])). Proof. reflexivity. Qed.
Lemma U_VZ_0RB1LC_1LA1RB_1RD0LA_0RC1LD : wsteps true false tm 2 (StA,([],S1,[S0])) = Some (StD,([],S1,[S1])). Proof. reflexivity. Qed.

(** ** Transported phases (framing = each unit's bl/br) *)
Lemma phP1_0RB1LC_1LA1RB_1RD0LA_0RC1LD : forall L R, csteps tm 2 (StB,(L,S0,S0::R)) = Some (StB,(L,S1,S0::R)).
Proof. intros. pose proof (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_P1_0RB1LC_1LA1RB_1RD0LA_0RC1LD) as H; cbn [app] in H; exact H. Qed.
Lemma phRIP_0RB1LC_1LA1RB_1RD0LA_0RC1LD : forall k L R, csteps tm (1*k) (StB,(rep [S1] k ++ L,S1,R)) = Some (StB,(L,S1,rep [S1] k ++ R)).
Proof. intros. pose proof (cycL _ _ _ _ _ _ _ U_RIP_0RB1LC_1LA1RB_1RD0LA_0RC1LD k L R) as H; cbn [app] in H; exact H. Qed.
Lemma phSTPI_0RB1LC_1LA1RB_1RD0LA_0RC1LD : forall L R, csteps tm 1 (StB,(S0::L,S1,R)) = Some (StB,(L,S0,S1::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_STPI_0RB1LC_1LA1RB_1RD0LA_0RC1LD). Qed.
Lemma phTRN_0RB1LC_1LA1RB_1RD0LA_0RC1LD : forall L R, csteps tm 1 (StB,(L,S0,S1::R)) = Some (StA,(S1::L,S1,R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_TRN_0RB1LC_1LA1RB_1RD0LA_0RC1LD). Qed.
Lemma phRET_0RB1LC_1LA1RB_1RD0LA_0RC1LD : forall k L R, csteps tm (2*k) (StA,(L,S1,rep [S1;S1] k ++ R)) = Some (StA,(rep [S0;S1] k ++ L,S1,R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U_RET_0RB1LC_1LA1RB_1RD0LA_0RC1LD k L R). Qed.
Lemma phFIN_0RB1LC_1LA1RB_1RD0LA_0RC1LD : forall L R, csteps tm 3 (StA,(L,S1,S1::S0::R)) = Some (StB,(S1::L,S0,S0::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_FIN_0RB1LC_1LA1RB_1RD0LA_0RC1LD). Qed.
Lemma phSTPO_0RB1LC_1LA1RB_1RD0LA_0RC1LD : forall R, csteps tm 2 (StB,([S0],S1,R)) = Some (StA,([S1],S1,R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_STPO_0RB1LC_1LA1RB_1RD0LA_0RC1LD). Qed.
Lemma phFIN2_0RB1LC_1LA1RB_1RD0LA_0RC1LD : forall L, csteps tm 7 (StA,(L,S1,[S0])) = Some (StB,(S1::L,S0,[S0])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U_FIN2_0RB1LC_1LA1RB_1RD0LA_0RC1LD). Qed.
Lemma phVD_0RB1LC_1LA1RB_1RD0LA_0RC1LD : forall x L R, csteps tm 1 (StA,(L,S1,x::R)) = Some (StC,(S1::L,x,R)).
Proof. intros. reflexivity. Qed.
Lemma phVZ_0RB1LC_1LA1RB_1RD0LA_0RC1LD : forall L, csteps tm 2 (StA,(L,S1,[S0])) = Some (StD,(L,S1,[S1])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U_VZ_0RB1LC_1LA1RB_1RD0LA_0RC1LD). Qed.

(** ** The lap

    Interior branch: EXACT (the next anchor on the nose) -- the deep-visit
    induction below chains on this equality. *)
Lemma lap_int_0RB1LC_1LA1RB_1RD0LA_0RC1LD : forall p j q0, cview p = (j, Some q0) ->
  exists n c', csteps tm n (Cc p) = Some c' /\ c' = Cc (Pos.succ p) /\ 0 < n.
Proof.
  intros p j q0 Ecv. unfold Cc_0RB1LC_1LA1RB_1RD0LA_0RC1LD.
  destruct (cview_some_I p j q0 Ecv) as (HIp & HIs).
  do 2 eexists. split; [|split].
  + rewrite HIp, <- app_assoc. cbn [app].
    rewrite rep_dbl, <- rep_slide.
    eapply csteps_chain. { apply phP1_0RB1LC_1LA1RB_1RD0LA_0RC1LD. }
    eapply csteps_chain. { apply (phRIP_0RB1LC_1LA1RB_1RD0LA_0RC1LD (S (2*j))). }
    eapply csteps_chain. { apply phSTPI_0RB1LC_1LA1RB_1RD0LA_0RC1LD. }
    eapply csteps_chain. { apply phTRN_0RB1LC_1LA1RB_1RD0LA_0RC1LD. }
    change (rep [S1] (S (2*j)) ++ [S0]) with (S1 :: rep [S1] (2*j) ++ [S0]).
    rewrite rep_slide, <- rep_dbl.
    eapply csteps_chain. { apply (phRET_0RB1LC_1LA1RB_1RD0LA_0RC1LD j). }
    apply phFIN_0RB1LC_1LA1RB_1RD0LA_0RC1LD.
  + rewrite HIs, <- app_assoc. cbn [app].
    change (rep [S1;S0] j ++ S1 :: S1 :: (Ip q0 ++ [S1;S0]))
      with (rep [S1;S0] j ++ [S1] ++ (S1 :: (Ip q0 ++ [S1;S0]))).
    rewrite app_assoc, pair_rot. reflexivity.
  + lia.
Qed.

Lemma lift_lblank_0RB1LC_1LA1RB_1RD0LA_0RC1LD : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

(** Wall-overflow close: the overflow rebuilds the wall one cell deeper and
    consumes the anchor's synthetic deep blank; the two agree under [lift]. *)
Lemma closeO_0RB1LC_1LA1RB_1RD0LA_0RC1LD : forall (l : list Sym) q h r,
  lift (q,(l ++ [S1],h,r)) = lift (q,(l ++ [S1;S0],h,r)).
Proof.
  intros.
  replace (l ++ [S1;S0]) with ((l ++ [S1]) ++ [S0])
    by (rewrite <- app_assoc; reflexivity).
  rewrite lift_lblank_0RB1LC_1LA1RB_1RD0LA_0RC1LD. reflexivity.
Qed.

Lemma lap_ov_0RB1LC_1LA1RB_1RD0LA_0RC1LD : forall p j', cview p = (S j', None) ->
  exists n c', csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j' Ecv. unfold Cc_0RB1LC_1LA1RB_1RD0LA_0RC1LD.
  destruct (cview_none_I p j' Ecv) as (HIp & HIs).
  do 2 eexists. split; [|split].
  + rewrite HIp, <- app_assoc. cbn [app].
    rewrite rep_dbl, <- !rep_slide.
    eapply csteps_chain. { apply phP1_0RB1LC_1LA1RB_1RD0LA_0RC1LD. }
    eapply csteps_chain. { apply (phRIP_0RB1LC_1LA1RB_1RD0LA_0RC1LD (S (S (2*j')))). }
    eapply csteps_chain. { apply phSTPO_0RB1LC_1LA1RB_1RD0LA_0RC1LD. }
    change (rep [S1] (S (S (2*j'))) ++ [S0])
      with (S1 :: S1 :: rep [S1] (2*j') ++ [S0]).
    rewrite <- rep_dbl.
    change (S1 :: S1 :: rep [S1;S1] j' ++ [S0])
      with (rep [S1;S1] (S j') ++ [S0]).
    eapply csteps_chain. { apply (phRET_0RB1LC_1LA1RB_1RD0LA_0RC1LD (S j')). }
    apply phFIN2_0RB1LC_1LA1RB_1RD0LA_0RC1LD.
  + rewrite HIs, <- app_assoc. cbn [app].
    change (rep [S1;S0] (S j') ++ S1 :: S1::S0::[])
      with (rep [S1;S0] (S j') ++ [S1] ++ [S1;S0]).
    rewrite app_assoc, pair_rot.
    apply (closeO_0RB1LC_1LA1RB_1RD0LA_0RC1LD (S1 :: rep [S0;S1] (S j'))).
  + lia.
Qed.

Lemma lap_0RB1LC_1LA1RB_1RD0LA_0RC1LD : forall p, exists n c', csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - destruct (lap_int_0RB1LC_1LA1RB_1RD0LA_0RC1LD p j q0 Ecv) as (n & c' & H1 & H2 & H3).
    exists n, c'. split; [exact H1|split; [rewrite H2; reflexivity|exact H3]].
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    exact (lap_ov_0RB1LC_1LA1RB_1RD0LA_0RC1LD p j' Ecv).
Qed.

Lemma boot_0RB1LC_1LA1RB_1RD0LA_0RC1LD : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 12.
  assert (H : match csteps tm 12 c0 with Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 12 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits *)

(** StD fires only inside the overflow close; reach the close's entry
    landmark by well-founded induction on [tovf] (strictly decreasing along
    interior laps, which close EXACTLY), then run a prefix of the close. *)
Lemma reach_fin2_0RB1LC_1LA1RB_1RD0LA_0RC1LD : forall p, exists k L, csteps tm k (Cc p) = Some (StA,(S0::L,S1,[S0])).
Proof.
  intro p; remember (tovf p) as fuel eqn:Ef; revert p Ef.
  induction fuel as [fuel IH] using (well_founded_induction lt_wf); intros p Ef.
  destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - assert (Hnz : tovf p <> 0).
    { intro H0. destruct (tovf0_allones p H0) as (jj & Hjj). rewrite Hjj in Ecv; discriminate. }
    destruct (lap_int_0RB1LC_1LA1RB_1RD0LA_0RC1LD p j q0 Ecv) as (n & c' & Hrun & Hc' & _). subst c'.
    destruct (IH (tovf (Pos.succ p)) (ltac:(rewrite tovf_succ by lia; lia)) (Pos.succ p) eq_refl) as (k & L & Hk).
    exists (n + k), L. rewrite csteps_add, Hrun. exact Hk.
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_I p j' Ecv) as (HIp & _).
    unfold Cc_0RB1LC_1LA1RB_1RD0LA_0RC1LD. eexists. eexists.
    rewrite HIp, <- app_assoc. cbn [app].
    rewrite rep_dbl, <- !rep_slide.
    eapply csteps_chain. { apply phP1_0RB1LC_1LA1RB_1RD0LA_0RC1LD. }
    eapply csteps_chain. { apply (phRIP_0RB1LC_1LA1RB_1RD0LA_0RC1LD (S (S (2*j')))). }
    eapply csteps_chain. { apply phSTPO_0RB1LC_1LA1RB_1RD0LA_0RC1LD. }
    change (rep [S1] (S (S (2*j'))) ++ [S0])
      with (S1 :: S1 :: rep [S1] (2*j') ++ [S0]).
    rewrite <- rep_dbl.
    change (S1 :: S1 :: rep [S1;S1] j' ++ [S0])
      with (rep [S1;S1] (S j') ++ [S0]).
    apply (phRET_0RB1LC_1LA1RB_1RD0LA_0RC1LD (S j')).
Qed.

Lemma vis_Z_0RB1LC_1LA1RB_1RD0LA_0RC1LD : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = StD.
Proof.
  intro p. destruct (reach_fin2_0RB1LC_1LA1RB_1RD0LA_0RC1LD p) as (k & L & Hk).
  exists (k + 2). eexists. rewrite csteps_add, Hk. split.
  - apply phVZ_0RB1LC_1LA1RB_1RD0LA_0RC1LD.
  - reflexivity.
Qed.

(** StA is entered by TRN (interior) and the overflow stop; StC one step
    later (the return partner never branches on the popped cell). *)
Lemma vis_R_0RB1LC_1LA1RB_1RD0LA_0RC1LD : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = StA.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - destruct (cview_some_I p j q0 Ecv) as (HIp & _).
    unfold Cc_0RB1LC_1LA1RB_1RD0LA_0RC1LD. eexists. eexists. split.
    + rewrite HIp, <- app_assoc. cbn [app].
      rewrite rep_dbl, <- rep_slide.
      eapply csteps_chain. { apply phP1_0RB1LC_1LA1RB_1RD0LA_0RC1LD. }
      eapply csteps_chain. { apply (phRIP_0RB1LC_1LA1RB_1RD0LA_0RC1LD (S (2*j))). }
      eapply csteps_chain. { apply phSTPI_0RB1LC_1LA1RB_1RD0LA_0RC1LD. }
      apply phTRN_0RB1LC_1LA1RB_1RD0LA_0RC1LD.
    + reflexivity.
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_I p j' Ecv) as (HIp & _).
    unfold Cc_0RB1LC_1LA1RB_1RD0LA_0RC1LD. eexists. eexists. split.
    + rewrite HIp, <- app_assoc. cbn [app].
      rewrite rep_dbl, <- !rep_slide.
      eapply csteps_chain. { apply phP1_0RB1LC_1LA1RB_1RD0LA_0RC1LD. }
      eapply csteps_chain. { apply (phRIP_0RB1LC_1LA1RB_1RD0LA_0RC1LD (S (S (2*j')))). }
      apply phSTPO_0RB1LC_1LA1RB_1RD0LA_0RC1LD.
    + reflexivity.
Qed.

Lemma vis_D_0RB1LC_1LA1RB_1RD0LA_0RC1LD : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = StC.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - destruct (cview_some_I p j q0 Ecv) as (HIp & _).
    unfold Cc_0RB1LC_1LA1RB_1RD0LA_0RC1LD. eexists. eexists. split.
    + rewrite HIp, <- app_assoc. cbn [app].
      rewrite rep_dbl, <- rep_slide.
      eapply csteps_chain. { apply phP1_0RB1LC_1LA1RB_1RD0LA_0RC1LD. }
      eapply csteps_chain. { apply (phRIP_0RB1LC_1LA1RB_1RD0LA_0RC1LD (S (2*j))). }
      eapply csteps_chain. { apply phSTPI_0RB1LC_1LA1RB_1RD0LA_0RC1LD. }
      eapply csteps_chain. { apply phTRN_0RB1LC_1LA1RB_1RD0LA_0RC1LD. }
      change (rep [S1] (S (2*j)) ++ [S0]) with (S1 :: rep [S1] (2*j) ++ [S0]).
      apply phVD_0RB1LC_1LA1RB_1RD0LA_0RC1LD.
    + reflexivity.
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_I p j' Ecv) as (HIp & _).
    unfold Cc_0RB1LC_1LA1RB_1RD0LA_0RC1LD. eexists. eexists. split.
    + rewrite HIp, <- app_assoc. cbn [app].
      rewrite rep_dbl, <- !rep_slide.
      eapply csteps_chain. { apply phP1_0RB1LC_1LA1RB_1RD0LA_0RC1LD. }
      eapply csteps_chain. { apply (phRIP_0RB1LC_1LA1RB_1RD0LA_0RC1LD (S (S (2*j')))). }
      eapply csteps_chain. { apply phSTPO_0RB1LC_1LA1RB_1RD0LA_0RC1LD. }
      change (rep [S1] (S (S (2*j'))) ++ [S0])
        with (S1 :: rep [S1] (S (2*j')) ++ [S0]).
      apply phVD_0RB1LC_1LA1RB_1RD0LA_0RC1LD.
    + reflexivity.
Qed.

Lemma vis_0RB1LC_1LA1RB_1RD0LA_0RC1LD : forall p q, exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q. destruct q.
  - apply vis_R_0RB1LC_1LA1RB_1RD0LA_0RC1LD.
  - (* StB : the anchor state *)
    exists 0. eexists. split; reflexivity.
  - apply vis_D_0RB1LC_1LA1RB_1RD0LA_0RC1LD.
  - apply vis_Z_0RB1LC_1LA1RB_1RD0LA_0RC1LD.
Qed.

Theorem nqhm_0RB1LC_1LA1RB_1RD0LA_0RC1LD : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc 1). - exact boot_0RB1LC_1LA1RB_1RD0LA_0RC1LD. - intros p _. apply lap_0RB1LC_1LA1RB_1RD0LA_0RC1LD. - intros p q _. apply vis_0RB1LC_1LA1RB_1RD0LA_0RC1LD. Qed.

Theorem nqh_0RB1LC_1LA1RB_1RD0LA_0RC1LD : NeverQuasiHaltsSt tm_0RB1LC_1LA1RB_1RD0LA_0RC1LD.
Proof. apply (mirror_never_qh tm_0RB1LC_1LA1RB_1RD0LA_0RC1LD). rewrite mirror_ok_0RB1LC_1LA1RB_1RD0LA_0RC1LD. exact nqhm_0RB1LC_1LA1RB_1RD0LA_0RC1LD. Qed.

Theorem nonhalt_0RB1LC_1LA1RB_1RD0LA_0RC1LD : NonHalt tm_0RB1LC_1LA1RB_1RD0LA_0RC1LD.
Proof. apply never_qh_nonhalt, nqh_0RB1LC_1LA1RB_1RD0LA_0RC1LD. Qed.
