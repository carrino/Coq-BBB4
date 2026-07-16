(** * Gray_19: the gray_counter machine #19, 1RB0RD_1LC0LB_1RA0LB_1RD0RC.

    The only machine of the BBB harness's [gray_counter] family
    (certificate results/counter19.cert: comb (1 0), edge state C,
    hoff -1).  The left-edge anchor over the counter [p] is

      S(p) = (10)^(p+2) [0] Wg(p),  head one cell LEFT of the comb
      on a blank, state C,

    where [Wg p] writes G = gray(p) = p xor (p >> 1) in 3-cell slots
    [bit; 0; 0] (LSB first, trimmed at the top marker).  One lap
    S(p) -> S(p+1): the head crosses the comb rightward (a 4-step
    cycle over two comb units, shifting the comb one cell left), and
    since G(p+1) = G(p) xor 2^j with j = fst (cview p), it flips
    exactly slot j: for p odd a D-run fills the empty low slots with
    1s up to the marker at slot j-1, clears it, and a 3-cell C/A/B
    push flips slot j (B complements whatever it reads and turns);
    for p even (j = 0) the flip happens right at the comb end; on
    overflow p = 2^j - 1 the flip extends the working area by one
    slot.  The return sweep restores the marker, erases the fills,
    and rebuilds the comb one unit longer.  Since p grows forever
    and every lap visits every state, the machine never quasihalts.

    Phase decomposition validated differentially against the raw
    simulator for p = 3..250 (tools/counters/lap19.py, ALL OK). *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB0RD_1LC0LB_1RA0LB_1RD0RC *)
Definition tm_19 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DR StD
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S0 DL StB
  | StC, S0 => mk S1 DR StA | StC, S1 => mk S0 DL StB
  | StD, S0 => mk S1 DR StD | StD, S1 => mk S0 DR StC
  end.

(** ** The anchor family *)

Definition Cc (p : positive) : cconf :=
  (StC, ([], S0, rep [S1; S0] (Pos.to_nat p + 2) ++ S0 :: Wg p)).

(** ** The unit runs (windowed, each checked by [reflexivity]) *)

(** U2: rightward crossing of two comb units (4 steps, comb shifts
    one cell left). *)
Lemma U2 : wsteps true true tm_19 4 (StC, ([], S0, [S1; S0; S1; S0]))
           = Some (StC, ([S0; S1; S0; S1], S0, [])).
Proof. reflexivity. Qed.

(** U3o: odd-comb entry -- the trailing comb unit feeds the D-run. *)
Lemma U3o : wsteps true true tm_19 3 (StC, ([], S0, [S1; S0; S0]))
            = Some (StD, ([S1; S0; S1], S0, [])).
Proof. reflexivity. Qed.

(** UDf: the D-run fills one empty slot cell per step. *)
Lemma UDf : wsteps true true tm_19 1 (StD, ([], S0, [S0]))
            = Some (StD, ([S1], S0, [])).
Proof. reflexivity. Qed.

(** U7i: the D-run clears the slot j-1 marker (interior). *)
Lemma U7i : wsteps true true tm_19 2 (StD, ([], S0, [S1; S0]))
            = Some (StC, ([S0; S1], S0, [])).
Proof. reflexivity. Qed.

(** U7e: the D-run clears the TOP marker (overflow; right edge). *)
Lemma U7e : wsteps true false tm_19 2 (StD, ([], S0, [S1]))
            = Some (StC, ([S0; S1], S0, [])).
Proof. reflexivity. Qed.

(** U8e: gap push into blank territory (overflow; right edge). *)
Lemma U8e : wsteps true false tm_19 2 (StC, ([], S0, []))
            = Some (StB, ([S1; S1], S0, [])).
Proof. reflexivity. Qed.

(** U3e0/U3e1: gap push up to the flip cell (B reads it next). *)
Lemma U3e0 : wsteps true true tm_19 2 (StC, ([], S0, [S0; S0]))
             = Some (StB, ([S1; S1], S0, [])).
Proof. reflexivity. Qed.

Lemma U3e1 : wsteps true true tm_19 2 (StC, ([], S0, [S0; S1]))
             = Some (StB, ([S1; S1], S1, [])).
Proof. reflexivity. Qed.

(** U4s: B sets a clear cell and turns (the flip, marker restore). *)
Lemma U4s : wsteps true true tm_19 1 (StB, ([S1], S0, []))
            = Some (StC, ([], S1, [S1])).
Proof. reflexivity. Qed.

(** U5s: C clears a set cell moving left. *)
Lemma U5s : wsteps true true tm_19 1 (StC, ([S1], S1, []))
            = Some (StB, ([], S1, [S0])).
Proof. reflexivity. Qed.

(** U5b0: B clears a set cell, landing on a clear one. *)
Lemma U5b0 : wsteps true true tm_19 1 (StB, ([S0], S1, []))
             = Some (StB, ([], S0, [S0])).
Proof. reflexivity. Qed.

(** UB1: B clears a run of set cells (1 step per cell). *)
Lemma UB1 : wsteps true true tm_19 1 (StB, ([S1], S1, []))
            = Some (StB, ([], S1, [S0])).
Proof. reflexivity. Qed.

(** Uret: the return cycle rebuilding the comb (2 steps per unit). *)
Lemma Uret : wsteps true true tm_19 2 (StB, ([S1; S0], S0, []))
             = Some (StB, ([], S0, [S0; S1])).
Proof. reflexivity. Qed.

(** U6e: the left-edge turnaround into the next anchor. *)
Lemma U6e : wsteps false true tm_19 3 (StB, ([S1], S0, []))
            = Some (StC, ([], S0, [S1; S0; S1])).
Proof. reflexivity. Qed.

(** Visit witnesses: A after 1 step, D after 2. *)
Lemma UV1 : wsteps true true tm_19 1 (StC, ([], S0, [S1]))
            = Some (StA, ([S1], S1, [])).
Proof. reflexivity. Qed.

Lemma UV2 : wsteps true true tm_19 2 (StC, ([], S0, [S1; S0]))
            = Some (StD, ([S0; S1], S0, [])).
Proof. reflexivity. Qed.

(** ** Transported phases (cons-normal forms) *)

Lemma phU2 : forall k L R,
  csteps tm_19 (4 * k) (StC, (L, S0, rep [S1; S0; S1; S0] k ++ R))
  = Some (StC, (rep [S0; S1; S0; S1] k ++ L, S0, R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U2 k L R). Qed.

Lemma phU3o : forall L R,
  csteps tm_19 3 (StC, (L, S0, S1 :: S0 :: S0 :: R))
  = Some (StD, (S1 :: S0 :: S1 :: L, S0, R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U3o). Qed.

Lemma phUDf : forall k L R,
  csteps tm_19 k (StD, (L, S0, rep [S0] k ++ R))
  = Some (StD, (rep [S1] k ++ L, S0, R)).
Proof.
  intros.
  pose proof (cycR _ _ _ _ _ _ UDf k L R) as H.
  rewrite Nat.mul_1_l in H. exact H.
Qed.

Lemma phU7i : forall L R,
  csteps tm_19 2 (StD, (L, S0, S1 :: S0 :: R))
  = Some (StC, (S0 :: S1 :: L, S0, R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U7i). Qed.

Lemma phU7e : forall L,
  csteps tm_19 2 (StD, (L, S0, [S1]))
  = Some (StC, (S0 :: S1 :: L, S0, [])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U7e). Qed.

Lemma phU8e : forall L,
  csteps tm_19 2 (StC, (L, S0, []))
  = Some (StB, (S1 :: S1 :: L, S0, [])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U8e). Qed.

(** The flip approach is one lemma for both flip-cell values. *)
Lemma phU3e : forall x L R,
  csteps tm_19 2 (StC, (L, S0, S0 :: x :: R))
  = Some (StB, (S1 :: S1 :: L, x, R)).
Proof.
  intros. destruct x.
  - exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U3e0).
  - exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U3e1).
Qed.

Lemma phU4s : forall L R,
  csteps tm_19 1 (StB, (S1 :: L, S0, R))
  = Some (StC, (L, S1, S1 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U4s). Qed.

Lemma phU5s : forall L R,
  csteps tm_19 1 (StC, (S1 :: L, S1, R))
  = Some (StB, (L, S1, S0 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U5s). Qed.

Lemma phU5b0 : forall L R,
  csteps tm_19 1 (StB, (S0 :: L, S1, R))
  = Some (StB, (L, S0, S0 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U5b0). Qed.

Lemma phUB1 : forall k L R,
  csteps tm_19 k (StB, (rep [S1] k ++ L, S1, R))
  = Some (StB, (L, S1, rep [S0] k ++ R)).
Proof.
  intros.
  pose proof (cycL _ _ _ _ _ _ _ UB1 k L R) as H.
  rewrite Nat.mul_1_l in H. cbn [app] in H. exact H.
Qed.

Lemma phUret : forall k L R,
  csteps tm_19 (2 * k) (StB, (rep [S1; S0] k ++ L, S0, R))
  = Some (StB, (L, S0, rep [S0; S1] k ++ R)).
Proof.
  intros.
  pose proof (cycL _ _ _ _ _ _ _ Uret k L R) as H.
  cbn [app] in H. exact H.
Qed.

Lemma phU6e : forall R,
  csteps tm_19 3 (StB, ([S1], S0, R))
  = Some (StC, ([], S0, S1 :: S0 :: S1 :: R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U6e). Qed.

Lemma phUV1 : forall L R,
  csteps tm_19 1 (StC, (L, S0, S1 :: R))
  = Some (StA, (S1 :: L, S1, R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R UV1). Qed.

Lemma phUV2 : forall L R,
  csteps tm_19 2 (StC, (L, S0, S1 :: S0 :: R))
  = Some (StD, (S0 :: S1 :: L, S0, R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R UV2). Qed.

(** Definitional fold for the two flip-adjacent set cells. *)
Lemma ones2 : forall X : list Sym, S1 :: S1 :: X = rep [S1] 2 ++ X.
Proof. reflexivity. Qed.

(** ** The lap *)

Lemma lap_19 : forall p, (3 <= p)%positive ->
  exists n c', csteps tm_19 n (Cc p) = Some c' /\
               lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p Hp.
  destruct p as [r | q |].
  - (* p = xI r: odd comb, the D-run reaches slot j *)
    set (m := Pos.to_nat r).
    destruct (cview r) as [j o] eqn:Ecv.
    assert (Ep : cview (xI r) = (S j, o))
      by (simpl; rewrite Ecv; reflexivity).
    unfold Cc.
    replace (Pos.to_nat (xI r) + 2) with (2 * S m + 1)
      by (unfold m; rewrite Pos2Nat.inj_xI; lia).
    replace (Pos.to_nat (Pos.succ (xI r)) + 2) with (S (S (2 * m)) + 2)
      by (unfold m; rewrite Pos2Nat.inj_succ, Pos2Nat.inj_xI; lia).
    rewrite comb_odd.
    destruct o as [q0 |].
    + (* interior: flip slot S j, marker at slot j restored *)
      destruct (Wg_some _ _ _ Ep) as (HW1 & HW2).
      rewrite HW1, HW2, Wg_xO, Wg_xI, rep_trip.
      destruct (oddb q0) eqn:Hb.
      * (* clear flip *)
        do 2 eexists. split; [| split].
        { eapply csteps_chain. { apply phU2. }
          eapply csteps_chain. { apply phU3o. }
          eapply csteps_chain. { apply phUDf. }
          eapply csteps_chain. { apply phU7i. }
          eapply csteps_chain. { apply phU3e. }
          rewrite ones2.
          eapply csteps_chain. { apply phUB1. }
          eapply csteps_chain. { apply phU5b0. }
          eapply csteps_chain. { apply phU4s. }
          rewrite <- rep_slide.
          eapply csteps_chain. { apply phU5s. }
          eapply csteps_chain. { apply phUB1. }
          eapply csteps_chain. { apply phU5b0. }
          rewrite cross_ret2.
          eapply csteps_chain. { apply phUret. }
          apply phU6e. }
        rewrite comb_refold, <- rep_slide.
        reflexivity.
        lia.
      * (* set flip *)
        do 2 eexists. split; [| split].
        { eapply csteps_chain. { apply phU2. }
          eapply csteps_chain. { apply phU3o. }
          eapply csteps_chain. { apply phUDf. }
          eapply csteps_chain. { apply phU7i. }
          eapply csteps_chain. { apply phU3e. }
          eapply csteps_chain. { apply phU4s. }
          eapply csteps_chain. { apply phU5s. }
          eapply csteps_chain. { apply phU5b0. }
          eapply csteps_chain. { apply phU4s. }
          rewrite <- rep_slide.
          eapply csteps_chain. { apply phU5s. }
          eapply csteps_chain. { apply phUB1. }
          eapply csteps_chain. { apply phU5b0. }
          rewrite cross_ret2.
          eapply csteps_chain. { apply phUret. }
          apply phU6e. }
        rewrite comb_refold, <- rep_slide.
        reflexivity.
        lia.
    + (* overflow: the flip extends the working area *)
      destruct (Wg_none _ _ Ep) as (HW1 & HW2).
      rewrite HW1, HW2, rep_trip.
      do 2 eexists. split; [| split].
      { eapply csteps_chain. { apply phU2. }
        eapply csteps_chain. { apply phU3o. }
        eapply csteps_chain. { apply phUDf. }
        eapply csteps_chain. { apply phU7e. }
        eapply csteps_chain. { apply phU8e. }
        eapply csteps_chain. { apply phU4s. }
        eapply csteps_chain. { apply phU5s. }
        eapply csteps_chain. { apply phU5b0. }
        eapply csteps_chain. { apply phU4s. }
        rewrite <- rep_slide.
        eapply csteps_chain. { apply phU5s. }
        eapply csteps_chain. { apply phUB1. }
        eapply csteps_chain. { apply phU5b0. }
        rewrite cross_ret2.
        eapply csteps_chain. { apply phUret. }
        apply phU6e. }
      rewrite comb_refold, <- rep_slide.
      reflexivity.
      lia.
  - (* p = xO q: even comb, flip right at the comb end *)
    set (m := Pos.to_nat q).
    unfold Cc.
    change (Pos.succ (xO q)) with (xI q).
    replace (Pos.to_nat (xO q) + 2) with (2 * S m)
      by (unfold m; rewrite Pos2Nat.inj_xO; lia).
    replace (Pos.to_nat (xI q) + 2) with (S (2 * m) + 2)
      by (unfold m; rewrite Pos2Nat.inj_xI; lia).
    rewrite comb_even, Wg_xO, Wg_xI.
    destruct (oddb q) eqn:Hb.
    + (* clear flip *)
      do 2 eexists. split; [| split].
      { eapply csteps_chain. { apply phU2. }
        eapply csteps_chain. { apply phU3e. }
        rewrite ones2.
        eapply csteps_chain. { apply phUB1. }
        rewrite cross_ret.
        eapply csteps_chain. { apply phU5b0. }
        eapply csteps_chain. { apply phUret. }
        apply phU6e. }
      rewrite comb_refold.
      reflexivity.
      lia.
    + (* set flip *)
      do 2 eexists. split; [| split].
      { eapply csteps_chain. { apply phU2. }
        eapply csteps_chain. { apply phU3e. }
        eapply csteps_chain. { apply phU4s. }
        eapply csteps_chain. { apply phU5s. }
        rewrite cross_ret.
        eapply csteps_chain. { apply phU5b0. }
        eapply csteps_chain. { apply phUret. }
        apply phU6e. }
      rewrite comb_refold.
      reflexivity.
      lia.
  - (* p = xH: excluded by 3 <= p *)
    lia.
Qed.

(** ** Bootstrap, visits, and the theorem *)

Lemma boot_19 : exists t0, stepn tm_19 t0 InitES = Some (lift (Cc 3)).
Proof.
  exists 64.
  assert (H : match csteps tm_19 64 c0 with
              | Some c => ceqb c (Cc 3)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm_19 64 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
  f_equal. apply ceqb_lift. exact H.
Qed.

Lemma vis_19 : forall p q, (3 <= p)%positive ->
  exists k c, csteps tm_19 k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q Hp.
  destruct q.
  - (* A: one step into the comb *)
    unfold Cc.
    replace (Pos.to_nat p + 2) with (S (S (Pos.to_nat p))) by lia.
    cbn [rep app].
    exists 1. eexists. split; [apply phUV1 | reflexivity].
  - (* B: first reached at the flip cell *)
    destruct p as [r | q' |].
    + (* odd comb *)
      set (m := Pos.to_nat r).
      destruct (cview r) as [j o] eqn:Ecv.
      assert (Ep : cview (xI r) = (S j, o))
        by (simpl; rewrite Ecv; reflexivity).
      unfold Cc.
      replace (Pos.to_nat (xI r) + 2) with (2 * S m + 1)
        by (unfold m; rewrite Pos2Nat.inj_xI; lia).
      rewrite comb_odd.
      destruct o as [q0 |].
      * destruct (Wg_some _ _ _ Ep) as (HW1 & _).
        rewrite HW1, Wg_xO, rep_trip.
        do 2 eexists. split.
        { eapply csteps_chain. { apply phU2. }
          eapply csteps_chain. { apply phU3o. }
          eapply csteps_chain. { apply phUDf. }
          eapply csteps_chain. { apply phU7i. }
          apply phU3e. }
        reflexivity.
      * destruct (Wg_none _ _ Ep) as (HW1 & _).
        rewrite HW1, rep_trip.
        do 2 eexists. split.
        { eapply csteps_chain. { apply phU2. }
          eapply csteps_chain. { apply phU3o. }
          eapply csteps_chain. { apply phUDf. }
          eapply csteps_chain. { apply phU7e. }
          apply phU8e. }
        reflexivity.
    + (* even comb *)
      set (m := Pos.to_nat q').
      unfold Cc.
      replace (Pos.to_nat (xO q') + 2) with (2 * S m)
        by (unfold m; rewrite Pos2Nat.inj_xO; lia).
      rewrite comb_even, Wg_xO.
      do 2 eexists. split.
      { eapply csteps_chain. { apply phU2. }
        apply phU3e. }
      reflexivity.
    + lia.
  - (* C: the anchor itself *)
    exists 0. eexists. split; reflexivity.
  - (* D: two steps into the comb *)
    unfold Cc.
    replace (Pos.to_nat p + 2) with (S (S (Pos.to_nat p))) by lia.
    cbn [rep app].
    exists 2. eexists. split; [apply phUV2 | reflexivity].
Qed.

(** #19 never quasihalts: bbchallenge 1RB0RD_1LC0LB_1RA0LB_1RD0RC. *)
Theorem nqh_1RB0RD_1LC0LB_1RA0LB_1RD0RC : NeverQuasiHaltsSt tm_19.
Proof.
  apply (glue_neverqh tm_19 Cc 3).
  - exact boot_19.
  - exact lap_19.
  - intros p q Hp. apply vis_19; exact Hp.
Qed.

Theorem tm_19_nonhalt : NonHalt tm_19.
Proof. apply never_qh_nonhalt, nqh_1RB0RD_1LC0LB_1RA0LB_1RD0RC. Qed.
