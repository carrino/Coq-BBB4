(** * Mono2_38: the mono2_counter machine #38, 1RB1RD_1LC1LB_0LD0LB_1RD0RA.

    Second machine of the BBB harness's [mono2_counter] family
    (certificate results/counter38.cert: prefix (1), comb (011),
    edge state B, hoff 0, comb_step 2, base_a 1, bootstrap a0 = 2).
    #38 shares its A/B/D rows with #39 and differs only in C0, but
    its comb grows by TWO units per lap; the left-edge anchor over
    p = a+1 is

      C(p) = prefix 1 . (011)^(2p-1) . Wm2(p),  head on the prefix,
      state B,

    with the same interleaved-marker working area [Wm2].  One lap is
    two out-and-back sweeps: sweep 1 crosses the comb (3-step cycle,
    rotated 110 view), performs the v-increment on the working area
    (2-step climb; overflow extends the area), returns (3-step
    rebuild cycle) and extends the comb region three cells left;
    sweep 2 re-crosses everything, rebuilds the comb phase at the
    working-area junction, and returns, extending another three
    cells.  Decomposition validated differentially against the raw
    simulator for p = 3..251 (tools/counters/lap38.py, ALL OK). *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB1RD_1LC1LB_0LD0LB_1RD0RA *)
Definition tm_38 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DR StD
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DL StB
  | StC, S0 => mk S0 DL StD | StC, S1 => mk S0 DL StB
  | StD, S0 => mk S1 DR StD | StD, S1 => mk S0 DR StA
  end.

(** ** The anchor family *)

Definition Cc (p : positive) : cconf :=
  (StB, ([], S1, rep [S0; S1; S1] (2 * Pos.to_nat p - 1) ++ Wm2 p)).

(** ** The unit runs (windowed, each checked by [reflexivity]) *)

(** UP1: sweep-1 prologue -- the prefix moves three cells left. *)
Lemma UP1 : wsteps false true tm_38 7 (StB, ([], S1, [S0]))
            = Some (StD, ([S1; S0; S1; S1], S0, [])).
Proof. reflexivity. Qed.

(** U2: rightward crossing of one comb unit (rotated 110 view). *)
Lemma U2 : wsteps true true tm_38 3 (StD, ([], S0, [S1; S1; S0]))
           = Some (StD, ([S1; S0; S1], S0, [])).
Proof. reflexivity. Qed.

(** U2b: the comb exit onto the leading working-area marker. *)
Lemma U2b : wsteps true true tm_38 3 (StD, ([], S0, [S1; S1; S1]))
            = Some (StD, ([S1; S0; S1], S1, [])).
Proof. reflexivity. Qed.

(** U3: the climb -- one set bit of v per marker-bit pair. *)
Lemma U3 : wsteps true true tm_38 2 (StD, ([], S1, [S1; S1]))
           = Some (StD, ([S1; S0], S1, [])).
Proof. reflexivity. Qed.

(** U4: the increment -- the first clear bit is set. *)
Lemma U4 : wsteps true true tm_38 2 (StD, ([], S1, [S0; S1]))
           = Some (StB, ([S1; S0], S1, [])).
Proof. reflexivity. Qed.

(** U4e: overflow -- the set bit goes past the top marker. *)
Lemma U4e : wsteps true false tm_38 2 (StD, ([], S1, []))
            = Some (StB, ([S1; S0], S0, [])).
Proof. reflexivity. Qed.

(** U5: the turnaround at a marker (kept). *)
Lemma U5 : wsteps true true tm_38 1 (StB, ([S1], S1, []))
           = Some (StB, ([], S1, [S1])).
Proof. reflexivity. Qed.

(** U6: a set cell is kept on the way back. *)
Lemma U6 : wsteps true true tm_38 1 (StB, ([S0], S1, []))
           = Some (StB, ([], S0, [S1])).
Proof. reflexivity. Qed.

(** U7: return over the climb -- markers restored, bits cleared. *)
Lemma U7 : wsteps true true tm_38 2 (StB, ([S1; S0], S0, []))
           = Some (StB, ([], S0, [S0; S1])).
Proof. reflexivity. Qed.

(** U8: set a clear cell, stepping onto a set one. *)
Lemma U8 : wsteps true true tm_38 1 (StB, ([S1], S0, []))
           = Some (StC, ([], S1, [S1])).
Proof. reflexivity. Qed.

(** U10: clear a set cell, stepping onto a clear one. *)
Lemma U10 : wsteps true true tm_38 1 (StC, ([S0], S1, []))
            = Some (StB, ([], S0, [S0])).
Proof. reflexivity. Qed.

(** U10b: clear a set cell, stepping onto a set one. *)
Lemma U10b : wsteps true true tm_38 1 (StC, ([S1], S1, []))
             = Some (StB, ([], S1, [S0])).
Proof. reflexivity. Qed.

(** Ur1: leftward comb rebuild (3 steps per unit). *)
Lemma Ur1 : wsteps true true tm_38 3 (StB, ([S0; S1; S1], S1, []))
            = Some (StB, ([], S1, [S0; S1; S1])).
Proof. reflexivity. Qed.

(** UP2: sweep-2 prologue at the left edge. *)
Lemma UP2 : wsteps false true tm_38 4 (StB, ([], S1, []))
            = Some (StD, ([S1], S0, [S1; S1])).
Proof. reflexivity. Qed.

(** U2c: sweep-2's junction -- the comb phase is rebuilt over the
    working-area boundary. *)
Lemma U2c : wsteps true true tm_38 3 (StD, ([], S0, [S1; S0; S1]))
            = Some (StB, ([S1; S0; S1], S1, [])).
Proof. reflexivity. Qed.

(** Visit witnesses: C after 2 steps, D after 3, A after 6. *)
Lemma UV2 : wsteps false true tm_38 2 (StB, ([], S1, []))
            = Some (StC, ([], S0, [S1; S1])).
Proof. reflexivity. Qed.

Lemma UV3 : wsteps false true tm_38 3 (StB, ([], S1, []))
            = Some (StD, ([], S0, [S0; S1; S1])).
Proof. reflexivity. Qed.

Lemma UV6 : wsteps false true tm_38 6 (StB, ([], S1, []))
            = Some (StA, ([S0; S1; S1], S1, [])).
Proof. reflexivity. Qed.

(** ** Transported phases (cons-normal forms) *)

Lemma phUP1 : forall R,
  csteps tm_38 7 (StB, ([], S1, S0 :: R))
  = Some (StD, ([S1; S0; S1; S1], S0, R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R UP1). Qed.

Lemma phU2 : forall k L R,
  csteps tm_38 (3 * k) (StD, (L, S0, rep [S1; S1; S0] k ++ R))
  = Some (StD, (rep [S1; S0; S1] k ++ L, S0, R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U2 k L R). Qed.

Lemma phU2b : forall L R,
  csteps tm_38 3 (StD, (L, S0, S1 :: S1 :: S1 :: R))
  = Some (StD, (S1 :: S0 :: S1 :: L, S1, R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U2b). Qed.

Lemma phU3 : forall k L R,
  csteps tm_38 (2 * k) (StD, (L, S1, rep [S1; S1] k ++ R))
  = Some (StD, (rep [S1; S0] k ++ L, S1, R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U3 k L R). Qed.

Lemma phU4 : forall L R,
  csteps tm_38 2 (StD, (L, S1, S0 :: S1 :: R))
  = Some (StB, (S1 :: S0 :: L, S1, R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U4). Qed.

Lemma phU4e : forall L,
  csteps tm_38 2 (StD, (L, S1, []))
  = Some (StB, (S1 :: S0 :: L, S0, [])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U4e). Qed.

Lemma phU5 : forall L R,
  csteps tm_38 1 (StB, (S1 :: L, S1, R))
  = Some (StB, (L, S1, S1 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U5). Qed.

Lemma phU6 : forall L R,
  csteps tm_38 1 (StB, (S0 :: L, S1, R))
  = Some (StB, (L, S0, S1 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U6). Qed.

Lemma phU7 : forall k L R,
  csteps tm_38 (2 * k) (StB, (rep [S1; S0] k ++ L, S0, R))
  = Some (StB, (L, S0, rep [S0; S1] k ++ R)).
Proof.
  intros.
  pose proof (cycL _ _ _ _ _ _ _ U7 k L R) as H.
  cbn [app] in H. exact H.
Qed.

Lemma phU8 : forall L R,
  csteps tm_38 1 (StB, (S1 :: L, S0, R))
  = Some (StC, (L, S1, S1 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U8). Qed.

Lemma phU10 : forall L R,
  csteps tm_38 1 (StC, (S0 :: L, S1, R))
  = Some (StB, (L, S0, S0 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U10). Qed.

Lemma phU10b : forall L R,
  csteps tm_38 1 (StC, (S1 :: L, S1, R))
  = Some (StB, (L, S1, S0 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U10b). Qed.

Lemma phUr1 : forall k L R,
  csteps tm_38 (3 * k) (StB, (rep [S0; S1; S1] k ++ L, S1, R))
  = Some (StB, (L, S1, rep [S0; S1; S1] k ++ R)).
Proof.
  intros.
  pose proof (cycL _ _ _ _ _ _ _ Ur1 k L R) as H.
  cbn [app] in H. exact H.
Qed.

Lemma phUP2 : forall R,
  csteps tm_38 4 (StB, ([], S1, R))
  = Some (StD, ([S1], S0, S1 :: S1 :: R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R UP2). Qed.

Lemma phU2c : forall L R,
  csteps tm_38 3 (StD, (L, S0, S1 :: S0 :: S1 :: R))
  = Some (StB, (S1 :: S0 :: S1 :: L, S1, R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U2c). Qed.

Lemma phUV2 : forall R,
  csteps tm_38 2 (StB, ([], S1, R))
  = Some (StC, ([], S0, S1 :: S1 :: R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R UV2). Qed.

Lemma phUV3 : forall R,
  csteps tm_38 3 (StB, ([], S1, R))
  = Some (StD, ([], S0, S0 :: S1 :: S1 :: R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R UV3). Qed.

Lemma phUV6 : forall R,
  csteps tm_38 6 (StB, ([], S1, R))
  = Some (StA, ([S0; S1; S1], S1, R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R UV6). Qed.

(** ** The lap *)

Lemma lap_38 : forall p, (3 <= p)%positive ->
  exists n c', csteps tm_38 n (Cc p) = Some c' /\
               lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p Hp.
  assert (H3 : 3 <= Pos.to_nat p).
  { change 3 with (Pos.to_nat 3). apply Pos2Nat.inj_le. exact Hp. }
  set (mm := 2 * Pos.to_nat p - 3).
  unfold Cc.
  replace (2 * Pos.to_nat p - 1) with (S (S mm)) by (unfold mm; lia).
  replace (2 * Pos.to_nat (Pos.succ p) - 1) with (S (S (S (S mm))))
    by (unfold mm; rewrite Pos2Nat.inj_succ; lia).
  destruct (cview p) as [j o] eqn:Ecv.
  destruct o as [q |].
  - (* interior carry on v *)
    destruct (Wm2_some _ _ _ Ecv) as (HW1 & HW2).
    destruct (Wm2_head q) as (wq & Hwq).
    rewrite HW1, HW2, Hwq.
    do 2 eexists. split; [| split].
    { rewrite rep011_expose.
      eapply csteps_chain. { apply phUP1. }
      rewrite rot_cross2, ones2_slide.
      eapply csteps_chain. { apply phU2. }
      eapply csteps_chain. { apply phU2b. }
      eapply csteps_chain. { apply phU3. }
      eapply csteps_chain. { apply phU4. }
      eapply csteps_chain. { apply phU5. }
      eapply csteps_chain. { apply phU6. }
      eapply csteps_chain. { apply phU7. }
      eapply csteps_chain. { apply phU8. }
      eapply csteps_chain. { apply phU10. }
      eapply csteps_chain. { apply phU8. }
      rewrite rep101_expose.
      eapply csteps_chain. { apply phU10b. }
      rewrite rot_cross3, rep_snoc3.
      eapply csteps_chain. { apply phUr1. }
      eapply csteps_chain. { apply phU6. }
      eapply csteps_chain. { apply phU8. }
      eapply csteps_chain. { apply phU10b. }
      (* sweep 2 *)
      eapply csteps_chain. { apply phUP2. }
      rewrite <- rep011_expose, rot_cross2, rep_snoc3.
      eapply csteps_chain. { apply phU2. }
      eapply csteps_chain. { apply phU2c. }
      eapply csteps_chain. { apply phU5. }
      eapply csteps_chain. { apply phU6. }
      eapply csteps_chain. { apply phU8. }
      rewrite rep101_expose.
      eapply csteps_chain. { apply phU10b. }
      rewrite rot_cross3.
      eapply csteps_chain. { apply phUr1. }
      eapply csteps_chain. { apply phU6. }
      eapply csteps_chain. { apply phU8. }
      apply phU10b. }
    { rewrite <- rep011_expose, rep_snoc3, rot_ret.
      reflexivity. }
    lia.
  - (* overflow: v = 2^k - 1, the area extends *)
    destruct j as [| j'].
    { exfalso.
      destruct p as [x|x|]; simpl in Ecv;
        [destruct (cview x); discriminate | discriminate | discriminate]. }
    destruct (Wm2_none _ _ Ecv) as (HW1 & HW2).
    rewrite HW1, HW2.
    do 2 eexists. split; [| split].
    { rewrite rep011_expose.
      eapply csteps_chain. { apply phUP1. }
      rewrite rot_cross2, ones2_slide.
      eapply csteps_chain. { apply phU2. }
      eapply csteps_chain. { apply phU2b. }
      eapply csteps_chain. { apply phU3. }
      eapply csteps_chain. { apply phU4e. }
      eapply csteps_chain. { apply phU8. }
      eapply csteps_chain. { apply phU10. }
      eapply csteps_chain. { apply phU7. }
      eapply csteps_chain. { apply phU8. }
      eapply csteps_chain. { apply phU10. }
      eapply csteps_chain. { apply phU8. }
      rewrite rep101_expose.
      eapply csteps_chain. { apply phU10b. }
      rewrite rot_cross3, rep_snoc3.
      eapply csteps_chain. { apply phUr1. }
      eapply csteps_chain. { apply phU6. }
      eapply csteps_chain. { apply phU8. }
      eapply csteps_chain. { apply phU10b. }
      (* sweep 2 *)
      eapply csteps_chain. { apply phUP2. }
      rewrite <- rep011_expose, rot_cross2, rep_snoc3.
      eapply csteps_chain. { apply phU2. }
      eapply csteps_chain. { apply phU2c. }
      eapply csteps_chain. { apply phU5. }
      eapply csteps_chain. { apply phU6. }
      eapply csteps_chain. { apply phU8. }
      rewrite rep101_expose.
      eapply csteps_chain. { apply phU10b. }
      rewrite rot_cross3.
      eapply csteps_chain. { apply phUr1. }
      eapply csteps_chain. { apply phU6. }
      eapply csteps_chain. { apply phU8. }
      apply phU10b. }
    { rewrite <- rep011_expose, rep_snoc3, rot_ret, rep_snoc2.
      reflexivity. }
    lia.
Qed.

(** ** Bootstrap, visits, and the theorem *)

Lemma boot_38 : exists t0, stepn tm_38 t0 InitES = Some (lift (Cc 3)).
Proof.
  exists 125.
  assert (H : match csteps tm_38 125 c0 with
              | Some c => ceqb c (Cc 3)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm_38 125 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
  f_equal. apply ceqb_lift. exact H.
Qed.

Lemma vis_38 : forall p q, (3 <= p)%positive ->
  exists k c, csteps tm_38 k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q _.
  unfold Cc.
  destruct q.
  - exists 6. eexists. split; [apply phUV6 | reflexivity].
  - exists 0. eexists. split; reflexivity.
  - exists 2. eexists. split; [apply phUV2 | reflexivity].
  - exists 3. eexists. split; [apply phUV3 | reflexivity].
Qed.

(** #38 never quasihalts: bbchallenge 1RB1RD_1LC1LB_0LD0LB_1RD0RA. *)
Theorem nqh_1RB1RD_1LC1LB_0LD0LB_1RD0RA : NeverQuasiHaltsSt tm_38.
Proof.
  apply (glue_neverqh tm_38 Cc 3).
  - exact boot_38.
  - exact lap_38.
  - intros p q Hp. apply vis_38; exact Hp.
Qed.

Theorem tm_38_nonhalt : NonHalt tm_38.
Proof. apply never_qh_nonhalt, nqh_1RB1RD_1LC1LB_0LD0LB_1RD0RA. Qed.
