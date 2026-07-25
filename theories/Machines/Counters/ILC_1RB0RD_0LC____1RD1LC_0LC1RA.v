(** * ILC_1RB0RD_0LC____1RD1LC_0LC1RA: comb-free interleaved binary counter, machine 1RB0RD_0LC---_1RD1LC_0LC1RA.

    Auto-emitted by tools/counters/emit_ip.py (UNTRUSTED emitter; the Coq
    kernel re-checks every line below).  Left-growth counter under the DIRECT
    interleave encoding [Ip] (ILCounter.v), anchored at

      Cc p = (StC, (Ip p ++ [S1], S1, [S0]))

    -- the counter on the LEFT list nearest-first, the frontier cell S1
    under the head, and a far side of [S0] (a blank CELL, not the empty list:
    the closing phase steps one cell past the frontier, and carrying the blank
    keeps that excursion inside a closed window).

    One lap Cc p -> Cc (p+1) is a single sweep: P1 prologue; RIP leftward carry
    ripple over the low set-bit pairs (cycL, 2 steps per pair); STPI
    interior stop / STPO overflow stop off the deep-left edge; RET rightward
    return (cycR, 2 steps per pair); FIN close.  Under [Ip] the ripple
    reads [rep [S1;S1] j] and the return writes [rep [S0;S1] j], so the return
    count is j -- under [Jp] the pairs swap and it is 2j.

    Step counts were derived by simulation and the decomposition was
    differentially validated against the raw simulator on BOTH cview branches
    for p = 2..99 (step counts AND exact configurations).

    Axiom footprint: [functional_extensionality_dep] (via CTape.lift). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From Coq Require Import FunctionalExtensionality.
From BBB4.Counters Require Import WTape LapGlue MonoCounter ILCounter JpCounter.
Import ListNotations.

Definition mk_1RB0RD_0LC____1RD1LC_0LC1RA (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB0RD_0LC____1RD1LC_0LC1RA.

(** 1RB0RD_0LC---_1RD1LC_0LC1RA *)
Definition tm_1RB0RD_0LC____1RD1LC_0LC1RA : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DR StD
  | StB, S0 => mk S0 DL StC | StB, S1 => None
  | StC, S0 => mk S1 DR StD | StC, S1 => mk S1 DL StC
  | StD, S0 => mk S0 DL StC | StD, S1 => mk S1 DR StA end.
Local Notation tm := tm_1RB0RD_0LC____1RD1LC_0LC1RA.

Definition Cc_1RB0RD_0LC____1RD1LC_0LC1RA (p : positive) : cconf := (StC, (Ip p ++ [S1], S1, [S0])).
Local Notation Cc := Cc_1RB0RD_0LC____1RD1LC_0LC1RA.

(** ** The lap unit windows (each closed by [reflexivity]) *)
Lemma U_P1_1RB0RD_0LC____1RD1LC_0LC1RA : wsteps true true tm 1 (StC,([S1],S1,[])) = Some (StC,([],S1,[S1])). Proof. reflexivity. Qed.
Lemma U_RIP_1RB0RD_0LC____1RD1LC_0LC1RA : wsteps true true tm 2 (StC,([S1;S1],S1,[])) = Some (StC,([],S1,[S1;S1])). Proof. reflexivity. Qed.
Lemma U_STPI_1RB0RD_0LC____1RD1LC_0LC1RA : wsteps true true tm 2 (StC,([S0],S1,[])) = Some (StD,([S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_STPO_1RB0RD_0LC____1RD1LC_0LC1RA : wsteps false true tm 3 (StC,([S1],S1,[])) = Some (StD,([S1],S1,[S1])). Proof. reflexivity. Qed.
Lemma U_RET_1RB0RD_0LC____1RD1LC_0LC1RA : wsteps true true tm 2 (StD,([],S1,[S1;S1])) = Some (StD,([S0;S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_FINI_1RB0RD_0LC____1RD1LC_0LC1RA : wsteps true true tm 5 (StD,([],S1,[S1;S0])) = Some (StC,([S1],S1,[S0])). Proof. reflexivity. Qed.
Lemma U_FINO_1RB0RD_0LC____1RD1LC_0LC1RA : wsteps true false tm 3 (StD,([],S1,[S0])) = Some (StC,([S1],S1,[S0])). Proof. reflexivity. Qed.

(** ** Transported phases (framing = each unit's bl/br) *)
Lemma phP1_1RB0RD_0LC____1RD1LC_0LC1RA : forall L R, csteps tm 1 (StC,(S1::L,S1,R)) = Some (StC,(L,S1,S1::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_P1_1RB0RD_0LC____1RD1LC_0LC1RA). Qed.
Lemma phRIP_1RB0RD_0LC____1RD1LC_0LC1RA : forall k L R, csteps tm (2*k) (StC,(rep [S1;S1] k ++ L,S1,R)) = Some (StC,(L,S1,rep [S1;S1] k ++ R)).
Proof. intros. pose proof (cycL _ _ _ _ _ _ _ U_RIP_1RB0RD_0LC____1RD1LC_0LC1RA k L R) as H; cbn [app] in H; exact H. Qed.
Lemma phSTPI_1RB0RD_0LC____1RD1LC_0LC1RA : forall L R, csteps tm 2 (StC,(S0::L,S1,R)) = Some (StD,(S1::L,S1,R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_STPI_1RB0RD_0LC____1RD1LC_0LC1RA). Qed.
Lemma phSTPO_1RB0RD_0LC____1RD1LC_0LC1RA : forall R, csteps tm 3 (StC,([S1],S1,R)) = Some (StD,([S1],S1,S1::R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_STPO_1RB0RD_0LC____1RD1LC_0LC1RA). Qed.
Lemma phRET_1RB0RD_0LC____1RD1LC_0LC1RA : forall k L R, csteps tm (2*k) (StD,(L,S1,rep [S1;S1] k ++ R)) = Some (StD,(rep [S0;S1] k ++ L,S1,R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U_RET_1RB0RD_0LC____1RD1LC_0LC1RA k L R). Qed.
Lemma phFINI_1RB0RD_0LC____1RD1LC_0LC1RA : forall L R, csteps tm 5 (StD,(L,S1,S1::S0::R)) = Some (StC,(S1::L,S1,S0::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_FINI_1RB0RD_0LC____1RD1LC_0LC1RA). Qed.
Lemma phFINO_1RB0RD_0LC____1RD1LC_0LC1RA : forall L, csteps tm 3 (StD,(L,S1,[S0])) = Some (StC,(S1::L,S1,[S0])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U_FINO_1RB0RD_0LC____1RD1LC_0LC1RA). Qed.

(** After the overflow stop the deposited run is one cell short of a whole
    pair; fold the prologue's deposit back in so the return cycle applies. *)
Lemma ov_R_1RB0RD_0LC____1RD1LC_0LC1RA : forall j, S1::rep [S1;S1] j ++ S1::[S0] = rep [S1;S1] (S j) ++ [S0].
Proof.
  induction j.
  - reflexivity.
  - cbn [rep] in *. rewrite <- !app_assoc in *. cbn [app] in *.
    f_equal. f_equal. exact IHj.
Qed.

(** ** The lap *)
Lemma lap_int_1RB0RD_0LC____1RD1LC_0LC1RA : forall p j q0, cview p = (j, Some q0) ->
  exists n c', csteps tm n (Cc p) = Some c' /\ c' = Cc (Pos.succ p) /\ 0 < n.
Proof.
  intros p j q0 Ecv. unfold Cc_1RB0RD_0LC____1RD1LC_0LC1RA.
  destruct (cview_some_I p j q0 Ecv) as (HIp & HIs).
  do 2 eexists. split; [|split].
  - rewrite HIp, <- app_assoc.
    change (rep [S1;S1] j ++ (S1 :: S0 :: Ip q0) ++ [S1])
      with (rep [S1;S1] j ++ [S1] ++ (S0 :: Ip q0 ++ [S1])).
    rewrite app_assoc, pair_rot.
    eapply csteps_chain. { apply phP1_1RB0RD_0LC____1RD1LC_0LC1RA. }
    eapply csteps_chain. { apply phRIP_1RB0RD_0LC____1RD1LC_0LC1RA. }
    eapply csteps_chain. { apply phSTPI_1RB0RD_0LC____1RD1LC_0LC1RA. }
    eapply csteps_chain. { apply (phRET_1RB0RD_0LC____1RD1LC_0LC1RA j). }
    apply phFINI_1RB0RD_0LC____1RD1LC_0LC1RA.
  - rewrite HIs, <- app_assoc.
    change ((S1 :: S1 :: Ip q0) ++ [S1]) with ([S1] ++ (S1 :: Ip q0 ++ [S1])).
    rewrite app_assoc, pair_rot. reflexivity.
  - lia.
Qed.

Lemma lap_ov_1RB0RD_0LC____1RD1LC_0LC1RA : forall p j', cview p = (S j', None) ->
  exists n c', csteps tm n (Cc p) = Some c' /\ c' = Cc (Pos.succ p) /\ 0 < n.
Proof.
  intros p j' Ecv. unfold Cc_1RB0RD_0LC____1RD1LC_0LC1RA.
  destruct (cview_none_I p j' Ecv) as (HIp & HIs).
  do 2 eexists. split; [|split].
  - rewrite HIp, pair_rot.
    eapply csteps_chain. { apply phP1_1RB0RD_0LC____1RD1LC_0LC1RA. }
    eapply csteps_chain. { apply phRIP_1RB0RD_0LC____1RD1LC_0LC1RA. }
    eapply csteps_chain. { apply phSTPO_1RB0RD_0LC____1RD1LC_0LC1RA. }
    rewrite ov_R_1RB0RD_0LC____1RD1LC_0LC1RA.
    eapply csteps_chain. { apply (phRET_1RB0RD_0LC____1RD1LC_0LC1RA (S j')). }
    apply phFINO_1RB0RD_0LC____1RD1LC_0LC1RA.
  - rewrite HIs, pair_rot. reflexivity.
  - lia.
Qed.

Lemma lap_exact_1RB0RD_0LC____1RD1LC_0LC1RA : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ c' = Cc (Pos.succ p) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - exact (lap_int_1RB0RD_0LC____1RD1LC_0LC1RA p j q0 Ecv).
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv;
        [destruct (cview p); discriminate|discriminate|discriminate]. }
    exact (lap_ov_1RB0RD_0LC____1RD1LC_0LC1RA p j' Ecv).
Qed.

Lemma lap_1RB0RD_0LC____1RD1LC_0LC1RA : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (lap_exact_1RB0RD_0LC____1RD1LC_0LC1RA p) as (n & c' & Hr & Hc & Hn).
  exists n, c'. split; [exact Hr | split; [rewrite Hc; reflexivity | exact Hn]].
Qed.

Lemma boot_1RB0RD_0LC____1RD1LC_0LC1RA : exists t0, stepn tm t0 InitES = Some (lift (Cc 2)).
Proof.
  exists 16.
  assert (H : match csteps tm 16 c0 with Some c => ceqb c (Cc 2) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 16 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state is witnessed from one common landmark -- the configuration the
    OVERFLOW close starts from -- reached by well-founded induction on [tovf],
    which strictly decreases along interior laps.  That is what covers the
    log-rare carry states (they fire only inside the overflow close, at
    doubling intervals, so no bounded anchor prefix reaches them). *)
Lemma reach_fino_1RB0RD_0LC____1RD1LC_0LC1RA : forall p, exists k L, csteps tm k (Cc p) = Some (StD,(L,S1,[S0])).
Proof.
  intro p; remember (tovf p) as fuel eqn:Ef; revert p Ef.
  induction fuel as [fuel IH] using (well_founded_induction lt_wf); intros p Ef.
  destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - assert (Hnz : tovf p <> 0).
    { intro H0. destruct (tovf0_allones p H0) as (jj & Hjj). rewrite Hjj in Ecv; discriminate. }
    destruct (lap_int_1RB0RD_0LC____1RD1LC_0LC1RA p j q0 Ecv) as (n & c' & Hrun & Hc' & _). subst c'.
    destruct (IH (tovf (Pos.succ p)) (ltac:(rewrite tovf_succ by lia; lia))
                 (Pos.succ p) eq_refl) as (k & L & Hk).
    exists (n + k), L. rewrite csteps_add, Hrun. exact Hk.
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv;
        [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_I p j' Ecv) as (HIp & _).
    unfold Cc_1RB0RD_0LC____1RD1LC_0LC1RA. eexists. eexists.
    rewrite HIp, pair_rot.
    eapply csteps_chain. { apply phP1_1RB0RD_0LC____1RD1LC_0LC1RA. }
    eapply csteps_chain. { apply phRIP_1RB0RD_0LC____1RD1LC_0LC1RA. }
    eapply csteps_chain. { apply phSTPO_1RB0RD_0LC____1RD1LC_0LC1RA. }
    rewrite ov_R_1RB0RD_0LC____1RD1LC_0LC1RA.
    apply (phRET_1RB0RD_0LC____1RD1LC_0LC1RA (S j')).
Qed.

Lemma phVA_1RB0RD_0LC____1RD1LC_0LC1RA : forall L, csteps tm 1 (StD,(L,S1,[S0])) = Some (StA,(S1::L,S0,[])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L
  (ltac:(reflexivity) : wsteps true false tm 1 (StD,([],S1,[S0])) = Some (StA,([S1],S0,[])))). Qed.
Lemma phVB_1RB0RD_0LC____1RD1LC_0LC1RA : forall L, csteps tm 2 (StD,(L,S1,[S0])) = Some (StB,(S1::S1::L,S0,[])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L
  (ltac:(reflexivity) : wsteps true false tm 2 (StD,([],S1,[S0])) = Some (StB,([S1;S1],S0,[])))). Qed.

Lemma vis_1RB0RD_0LC____1RD1LC_0LC1RA : forall p q, exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q. destruct q.
  - (* StA : 1 steps into the overflow close *)
    destruct (reach_fino_1RB0RD_0LC____1RD1LC_0LC1RA p) as (k & L & Hk).
    exists (k + 1). eexists. rewrite csteps_add, Hk.
    split; [apply phVA_1RB0RD_0LC____1RD1LC_0LC1RA | reflexivity].
  - (* StB : 2 steps into the overflow close *)
    destruct (reach_fino_1RB0RD_0LC____1RD1LC_0LC1RA p) as (k & L & Hk).
    exists (k + 2). eexists. rewrite csteps_add, Hk.
    split; [apply phVB_1RB0RD_0LC____1RD1LC_0LC1RA | reflexivity].
  - (* StC : the anchor state *)
    exists 0. eexists. split; reflexivity.
  - (* StD : the overflow-close landmark *)
    destruct (reach_fino_1RB0RD_0LC____1RD1LC_0LC1RA p) as (k & L & Hk).
    exists k. eexists. split; [exact Hk | reflexivity].
Qed.

Lemma nqhm_1RB0RD_0LC____1RD1LC_0LC1RA : NeverQuasiHaltsSt tm.
Proof.
  apply (glue_neverqh tm Cc 2).
  - exact boot_1RB0RD_0LC____1RD1LC_0LC1RA.
  - intros p _. apply lap_1RB0RD_0LC____1RD1LC_0LC1RA.
  - intros p q _. apply vis_1RB0RD_0LC____1RD1LC_0LC1RA.
Qed.

Theorem nqh_1RB0RD_0LC____1RD1LC_0LC1RA : NeverQuasiHaltsSt tm_1RB0RD_0LC____1RD1LC_0LC1RA.
Proof. exact nqhm_1RB0RD_0LC____1RD1LC_0LC1RA. Qed.

Theorem nonhalt_1RB0RD_0LC____1RD1LC_0LC1RA : NonHalt tm_1RB0RD_0LC____1RD1LC_0LC1RA.
Proof. apply never_qh_nonhalt, nqh_1RB0RD_0LC____1RD1LC_0LC1RA. Qed.
