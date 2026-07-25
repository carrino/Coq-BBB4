(** * ILS4F_1RB1RD_0LC1RD_1RB1LC_1LA0RB: frontier-flip [Ip] interleaved binary counter, machine
    1RB1RD_0LC1RD_1RB1LC_1LA0RB (the affine half of the `+XY|-YX|+XY` lap-shape family).

    Auto-emitted by tools/counters/emit_shape4.py --flip (UNTRUSTED emitter;
    the Coq kernel re-checks every line below).  Left-growth counter under
    the DIRECT interleave encoding [Ip] (ILCounter.v), anchored at

      Cc p = (StC, (Ip p ++ [S1;S0], S0, [S0]))

    -- a blank head at the frontier and a blank far-side CELL.  One lap:

      P1   flip the frontier cell inside the far window (2 steps,
           returning to StC);
      RIP  leftward 1-cell run (cycL, 1 step per cell, THROUGH the LSB
           marker: 2j+1 cells interior, 2j'+2 incl the wall on overflow);
      STPI/TRN  pop the clear bit, turn right (interior, 1+1);
      STPO bounce off the synthetic deep blank (2 steps, overflow);
      RET  rightward rewrite cycle [S1;S1] -> [S0;S1] (cycR, 2 steps
           per pair; j pairs interior, S j' on overflow);
      FIN  frontier close (3 steps, interior, EXACT) / FIN2 overflow
           close (5 steps, open-right past the far cell, eating the
           last return pair's S0; closes one LEFT blank short -> lift).

    Derived by exact symbolic replay; differentially validated against the
    raw simulator on BOTH cview branches (counts AND exact configurations,
    p = 1..160 plus sparse p to 2^13).  Axiom footprint:
    [functional_extensionality_dep] (via CTape.lift). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter ILCounter JpCounter.
Import ListNotations.

Definition mk_1RB1RD_0LC1RD_1RB1LC_1LA0RB (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB1RD_0LC1RD_1RB1LC_1LA0RB.

(** 1RB1RD_0LC1RD_1RB1LC_1LA0RB *)
Definition tm_1RB1RD_0LC1RD_1RB1LC_1LA0RB : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DR StD
  | StB, S0 => mk S0 DL StC | StB, S1 => mk S1 DR StD
  | StC, S0 => mk S1 DR StB | StC, S1 => mk S1 DL StC
  | StD, S0 => mk S1 DL StA | StD, S1 => mk S0 DR StB end.
Local Notation tm := tm_1RB1RD_0LC1RD_1RB1LC_1LA0RB.

Definition Cc_1RB1RD_0LC1RD_1RB1LC_1LA0RB (p : positive) : cconf := (StC, (Ip p ++ [S1;S0], S0, [S0])).
Local Notation Cc := Cc_1RB1RD_0LC1RD_1RB1LC_1LA0RB.

(** ** The lap unit windows (each closed by [reflexivity]) *)
Lemma U_P1_1RB1RD_0LC1RD_1RB1LC_1LA0RB : wsteps true true tm 2 (StC,([],S0,[S0])) = Some (StC,([],S1,[S0])). Proof. reflexivity. Qed.
Lemma U_RIP_1RB1RD_0LC1RD_1RB1LC_1LA0RB : wsteps true true tm 1 (StC,([S1],S1,[])) = Some (StC,([],S1,[S1])). Proof. reflexivity. Qed.
Lemma U_STPI_1RB1RD_0LC1RD_1RB1LC_1LA0RB : wsteps true true tm 1 (StC,([S0],S1,[])) = Some (StC,([],S0,[S1])). Proof. reflexivity. Qed.
Lemma U_TRN_1RB1RD_0LC1RD_1RB1LC_1LA0RB : wsteps true true tm 1 (StC,([],S0,[S1])) = Some (StB,([S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_RET_1RB1RD_0LC1RD_1RB1LC_1LA0RB : wsteps true true tm 2 (StB,([],S1,[S1;S1])) = Some (StB,([S0;S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_FIN_1RB1RD_0LC1RD_1RB1LC_1LA0RB : wsteps true true tm 3 (StB,([],S1,[S1;S0])) = Some (StC,([S1],S0,[S0])). Proof. reflexivity. Qed.
Lemma U_STPO_1RB1RD_0LC1RD_1RB1LC_1LA0RB : wsteps false true tm 2 (StC,([S0],S1,[])) = Some (StB,([S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_FIN2_1RB1RD_0LC1RD_1RB1LC_1LA0RB : wsteps true false tm 5 (StB,([],S1,[S0])) = Some (StC,([S1],S0,[S0])). Proof. reflexivity. Qed.
Lemma U_VZ_1RB1RD_0LC1RD_1RB1LC_1LA0RB : wsteps true false tm 2 (StB,([],S1,[S0])) = Some (StA,([],S1,[S1])). Proof. reflexivity. Qed.

(** ** Transported phases (framing = each unit's bl/br) *)
Lemma phP1_1RB1RD_0LC1RD_1RB1LC_1LA0RB : forall L R, csteps tm 2 (StC,(L,S0,S0::R)) = Some (StC,(L,S1,S0::R)).
Proof. intros. pose proof (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_P1_1RB1RD_0LC1RD_1RB1LC_1LA0RB) as H; cbn [app] in H; exact H. Qed.
Lemma phRIP_1RB1RD_0LC1RD_1RB1LC_1LA0RB : forall k L R, csteps tm (1*k) (StC,(rep [S1] k ++ L,S1,R)) = Some (StC,(L,S1,rep [S1] k ++ R)).
Proof. intros. pose proof (cycL _ _ _ _ _ _ _ U_RIP_1RB1RD_0LC1RD_1RB1LC_1LA0RB k L R) as H; cbn [app] in H; exact H. Qed.
Lemma phSTPI_1RB1RD_0LC1RD_1RB1LC_1LA0RB : forall L R, csteps tm 1 (StC,(S0::L,S1,R)) = Some (StC,(L,S0,S1::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_STPI_1RB1RD_0LC1RD_1RB1LC_1LA0RB). Qed.
Lemma phTRN_1RB1RD_0LC1RD_1RB1LC_1LA0RB : forall L R, csteps tm 1 (StC,(L,S0,S1::R)) = Some (StB,(S1::L,S1,R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_TRN_1RB1RD_0LC1RD_1RB1LC_1LA0RB). Qed.
Lemma phRET_1RB1RD_0LC1RD_1RB1LC_1LA0RB : forall k L R, csteps tm (2*k) (StB,(L,S1,rep [S1;S1] k ++ R)) = Some (StB,(rep [S0;S1] k ++ L,S1,R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U_RET_1RB1RD_0LC1RD_1RB1LC_1LA0RB k L R). Qed.
Lemma phFIN_1RB1RD_0LC1RD_1RB1LC_1LA0RB : forall L R, csteps tm 3 (StB,(L,S1,S1::S0::R)) = Some (StC,(S1::L,S0,S0::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_FIN_1RB1RD_0LC1RD_1RB1LC_1LA0RB). Qed.
Lemma phSTPO_1RB1RD_0LC1RD_1RB1LC_1LA0RB : forall R, csteps tm 2 (StC,([S0],S1,R)) = Some (StB,([S1],S1,R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_STPO_1RB1RD_0LC1RD_1RB1LC_1LA0RB). Qed.
Lemma phFIN2_1RB1RD_0LC1RD_1RB1LC_1LA0RB : forall L, csteps tm 5 (StB,(L,S1,[S0])) = Some (StC,(S1::L,S0,[S0])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U_FIN2_1RB1RD_0LC1RD_1RB1LC_1LA0RB). Qed.
Lemma phVD_1RB1RD_0LC1RD_1RB1LC_1LA0RB : forall x L R, csteps tm 1 (StB,(L,S1,x::R)) = Some (StD,(S1::L,x,R)).
Proof. intros. reflexivity. Qed.
Lemma phVZ_1RB1RD_0LC1RD_1RB1LC_1LA0RB : forall L, csteps tm 2 (StB,(L,S1,[S0])) = Some (StA,(L,S1,[S1])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U_VZ_1RB1RD_0LC1RD_1RB1LC_1LA0RB). Qed.

(** ** The lap

    Interior branch: EXACT (the next anchor on the nose) -- the deep-visit
    induction below chains on this equality. *)
Lemma lap_int_1RB1RD_0LC1RD_1RB1LC_1LA0RB : forall p j q0, cview p = (j, Some q0) ->
  exists n c', csteps tm n (Cc p) = Some c' /\ c' = Cc (Pos.succ p) /\ 0 < n.
Proof.
  intros p j q0 Ecv. unfold Cc_1RB1RD_0LC1RD_1RB1LC_1LA0RB.
  destruct (cview_some_I p j q0 Ecv) as (HIp & HIs).
  do 2 eexists. split; [|split].
  + rewrite HIp, <- app_assoc. cbn [app].
    rewrite rep_dbl, <- rep_slide.
    eapply csteps_chain. { apply phP1_1RB1RD_0LC1RD_1RB1LC_1LA0RB. }
    eapply csteps_chain. { apply (phRIP_1RB1RD_0LC1RD_1RB1LC_1LA0RB (S (2*j))). }
    eapply csteps_chain. { apply phSTPI_1RB1RD_0LC1RD_1RB1LC_1LA0RB. }
    eapply csteps_chain. { apply phTRN_1RB1RD_0LC1RD_1RB1LC_1LA0RB. }
    change (rep [S1] (S (2*j)) ++ [S0]) with (S1 :: rep [S1] (2*j) ++ [S0]).
    rewrite rep_slide, <- rep_dbl.
    eapply csteps_chain. { apply (phRET_1RB1RD_0LC1RD_1RB1LC_1LA0RB j). }
    apply phFIN_1RB1RD_0LC1RD_1RB1LC_1LA0RB.
  + rewrite HIs, <- app_assoc. cbn [app].
    change (rep [S1;S0] j ++ S1 :: S1 :: (Ip q0 ++ [S1;S0]))
      with (rep [S1;S0] j ++ [S1] ++ (S1 :: (Ip q0 ++ [S1;S0]))).
    rewrite app_assoc, pair_rot. reflexivity.
  + lia.
Qed.

Lemma lift_lblank_1RB1RD_0LC1RD_1RB1LC_1LA0RB : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

(** Wall-overflow close: the overflow rebuilds the wall one cell deeper and
    consumes the anchor's synthetic deep blank; the two agree under [lift]. *)
Lemma closeO_1RB1RD_0LC1RD_1RB1LC_1LA0RB : forall (l : list Sym) q h r,
  lift (q,(l ++ [S1],h,r)) = lift (q,(l ++ [S1;S0],h,r)).
Proof.
  intros.
  replace (l ++ [S1;S0]) with ((l ++ [S1]) ++ [S0])
    by (rewrite <- app_assoc; reflexivity).
  rewrite lift_lblank_1RB1RD_0LC1RD_1RB1LC_1LA0RB. reflexivity.
Qed.

Lemma lap_ov_1RB1RD_0LC1RD_1RB1LC_1LA0RB : forall p j', cview p = (S j', None) ->
  exists n c', csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j' Ecv. unfold Cc_1RB1RD_0LC1RD_1RB1LC_1LA0RB.
  destruct (cview_none_I p j' Ecv) as (HIp & HIs).
  do 2 eexists. split; [|split].
  + rewrite HIp, <- app_assoc. cbn [app].
    rewrite rep_dbl, <- !rep_slide.
    eapply csteps_chain. { apply phP1_1RB1RD_0LC1RD_1RB1LC_1LA0RB. }
    eapply csteps_chain. { apply (phRIP_1RB1RD_0LC1RD_1RB1LC_1LA0RB (S (S (2*j')))). }
    eapply csteps_chain. { apply phSTPO_1RB1RD_0LC1RD_1RB1LC_1LA0RB. }
    change (rep [S1] (S (S (2*j'))) ++ [S0])
      with (S1 :: S1 :: rep [S1] (2*j') ++ [S0]).
    rewrite <- rep_dbl.
    change (S1 :: S1 :: rep [S1;S1] j' ++ [S0])
      with (rep [S1;S1] (S j') ++ [S0]).
    eapply csteps_chain. { apply (phRET_1RB1RD_0LC1RD_1RB1LC_1LA0RB (S j')). }
    apply phFIN2_1RB1RD_0LC1RD_1RB1LC_1LA0RB.
  + rewrite HIs, <- app_assoc. cbn [app].
    change (rep [S1;S0] (S j') ++ S1 :: S1::S0::[])
      with (rep [S1;S0] (S j') ++ [S1] ++ [S1;S0]).
    rewrite app_assoc, pair_rot.
    apply (closeO_1RB1RD_0LC1RD_1RB1LC_1LA0RB (S1 :: rep [S0;S1] (S j'))).
  + lia.
Qed.

Lemma lap_1RB1RD_0LC1RD_1RB1LC_1LA0RB : forall p, exists n c', csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - destruct (lap_int_1RB1RD_0LC1RD_1RB1LC_1LA0RB p j q0 Ecv) as (n & c' & H1 & H2 & H3).
    exists n, c'. split; [exact H1|split; [rewrite H2; reflexivity|exact H3]].
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    exact (lap_ov_1RB1RD_0LC1RD_1RB1LC_1LA0RB p j' Ecv).
Qed.

Lemma boot_1RB1RD_0LC1RD_1RB1LC_1LA0RB : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 9.
  assert (H : match csteps tm 9 c0 with Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 9 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits *)

(** StA fires only inside the overflow close; reach the close's entry
    landmark by well-founded induction on [tovf] (strictly decreasing along
    interior laps, which close EXACTLY), then run a prefix of the close. *)
Lemma reach_fin2_1RB1RD_0LC1RD_1RB1LC_1LA0RB : forall p, exists k L, csteps tm k (Cc p) = Some (StB,(S0::L,S1,[S0])).
Proof.
  intro p; remember (tovf p) as fuel eqn:Ef; revert p Ef.
  induction fuel as [fuel IH] using (well_founded_induction lt_wf); intros p Ef.
  destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - assert (Hnz : tovf p <> 0).
    { intro H0. destruct (tovf0_allones p H0) as (jj & Hjj). rewrite Hjj in Ecv; discriminate. }
    destruct (lap_int_1RB1RD_0LC1RD_1RB1LC_1LA0RB p j q0 Ecv) as (n & c' & Hrun & Hc' & _). subst c'.
    destruct (IH (tovf (Pos.succ p)) (ltac:(rewrite tovf_succ by lia; lia)) (Pos.succ p) eq_refl) as (k & L & Hk).
    exists (n + k), L. rewrite csteps_add, Hrun. exact Hk.
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_I p j' Ecv) as (HIp & _).
    unfold Cc_1RB1RD_0LC1RD_1RB1LC_1LA0RB. eexists. eexists.
    rewrite HIp, <- app_assoc. cbn [app].
    rewrite rep_dbl, <- !rep_slide.
    eapply csteps_chain. { apply phP1_1RB1RD_0LC1RD_1RB1LC_1LA0RB. }
    eapply csteps_chain. { apply (phRIP_1RB1RD_0LC1RD_1RB1LC_1LA0RB (S (S (2*j')))). }
    eapply csteps_chain. { apply phSTPO_1RB1RD_0LC1RD_1RB1LC_1LA0RB. }
    change (rep [S1] (S (S (2*j'))) ++ [S0])
      with (S1 :: S1 :: rep [S1] (2*j') ++ [S0]).
    rewrite <- rep_dbl.
    change (S1 :: S1 :: rep [S1;S1] j' ++ [S0])
      with (rep [S1;S1] (S j') ++ [S0]).
    apply (phRET_1RB1RD_0LC1RD_1RB1LC_1LA0RB (S j')).
Qed.

Lemma vis_Z_1RB1RD_0LC1RD_1RB1LC_1LA0RB : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = StA.
Proof.
  intro p. destruct (reach_fin2_1RB1RD_0LC1RD_1RB1LC_1LA0RB p) as (k & L & Hk).
  exists (k + 2). eexists. rewrite csteps_add, Hk. split.
  - apply phVZ_1RB1RD_0LC1RD_1RB1LC_1LA0RB.
  - reflexivity.
Qed.

(** StB is entered by TRN (interior) and the overflow stop; StD one step
    later (the return partner never branches on the popped cell). *)
Lemma vis_R_1RB1RD_0LC1RD_1RB1LC_1LA0RB : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = StB.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - destruct (cview_some_I p j q0 Ecv) as (HIp & _).
    unfold Cc_1RB1RD_0LC1RD_1RB1LC_1LA0RB. eexists. eexists. split.
    + rewrite HIp, <- app_assoc. cbn [app].
      rewrite rep_dbl, <- rep_slide.
      eapply csteps_chain. { apply phP1_1RB1RD_0LC1RD_1RB1LC_1LA0RB. }
      eapply csteps_chain. { apply (phRIP_1RB1RD_0LC1RD_1RB1LC_1LA0RB (S (2*j))). }
      eapply csteps_chain. { apply phSTPI_1RB1RD_0LC1RD_1RB1LC_1LA0RB. }
      apply phTRN_1RB1RD_0LC1RD_1RB1LC_1LA0RB.
    + reflexivity.
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_I p j' Ecv) as (HIp & _).
    unfold Cc_1RB1RD_0LC1RD_1RB1LC_1LA0RB. eexists. eexists. split.
    + rewrite HIp, <- app_assoc. cbn [app].
      rewrite rep_dbl, <- !rep_slide.
      eapply csteps_chain. { apply phP1_1RB1RD_0LC1RD_1RB1LC_1LA0RB. }
      eapply csteps_chain. { apply (phRIP_1RB1RD_0LC1RD_1RB1LC_1LA0RB (S (S (2*j')))). }
      apply phSTPO_1RB1RD_0LC1RD_1RB1LC_1LA0RB.
    + reflexivity.
Qed.

Lemma vis_D_1RB1RD_0LC1RD_1RB1LC_1LA0RB : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = StD.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - destruct (cview_some_I p j q0 Ecv) as (HIp & _).
    unfold Cc_1RB1RD_0LC1RD_1RB1LC_1LA0RB. eexists. eexists. split.
    + rewrite HIp, <- app_assoc. cbn [app].
      rewrite rep_dbl, <- rep_slide.
      eapply csteps_chain. { apply phP1_1RB1RD_0LC1RD_1RB1LC_1LA0RB. }
      eapply csteps_chain. { apply (phRIP_1RB1RD_0LC1RD_1RB1LC_1LA0RB (S (2*j))). }
      eapply csteps_chain. { apply phSTPI_1RB1RD_0LC1RD_1RB1LC_1LA0RB. }
      eapply csteps_chain. { apply phTRN_1RB1RD_0LC1RD_1RB1LC_1LA0RB. }
      change (rep [S1] (S (2*j)) ++ [S0]) with (S1 :: rep [S1] (2*j) ++ [S0]).
      apply phVD_1RB1RD_0LC1RD_1RB1LC_1LA0RB.
    + reflexivity.
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_I p j' Ecv) as (HIp & _).
    unfold Cc_1RB1RD_0LC1RD_1RB1LC_1LA0RB. eexists. eexists. split.
    + rewrite HIp, <- app_assoc. cbn [app].
      rewrite rep_dbl, <- !rep_slide.
      eapply csteps_chain. { apply phP1_1RB1RD_0LC1RD_1RB1LC_1LA0RB. }
      eapply csteps_chain. { apply (phRIP_1RB1RD_0LC1RD_1RB1LC_1LA0RB (S (S (2*j')))). }
      eapply csteps_chain. { apply phSTPO_1RB1RD_0LC1RD_1RB1LC_1LA0RB. }
      change (rep [S1] (S (S (2*j'))) ++ [S0])
        with (S1 :: rep [S1] (S (2*j')) ++ [S0]).
      apply phVD_1RB1RD_0LC1RD_1RB1LC_1LA0RB.
    + reflexivity.
Qed.

Lemma vis_1RB1RD_0LC1RD_1RB1LC_1LA0RB : forall p q, exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q. destruct q.
  - apply vis_Z_1RB1RD_0LC1RD_1RB1LC_1LA0RB.
  - apply vis_R_1RB1RD_0LC1RD_1RB1LC_1LA0RB.
  - (* StC : the anchor state *)
    exists 0. eexists. split; reflexivity.
  - apply vis_D_1RB1RD_0LC1RD_1RB1LC_1LA0RB.
Qed.

Theorem nqh_1RB1RD_0LC1RD_1RB1LC_1LA0RB : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc 1). - exact boot_1RB1RD_0LC1RD_1RB1LC_1LA0RB. - intros p _. apply lap_1RB1RD_0LC1RD_1RB1LC_1LA0RB. - intros p q _. apply vis_1RB1RD_0LC1RD_1RB1LC_1LA0RB. Qed.

Theorem nonhalt_1RB1RD_0LC1RD_1RB1LC_1LA0RB : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_1RB1RD_0LC1RD_1RB1LC_1LA0RB. Qed.
