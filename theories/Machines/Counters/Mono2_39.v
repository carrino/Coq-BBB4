(** * Mono2_39: the mono2_counter machine #39, 1RB1RD_1LC1LB_1LD0LB_1RD0RA.

    First machine of the BBB harness's [mono2_counter] family
    (certificate results/counter39.cert: prefix (1), comb (110),
    edge state C, hoff 0, bootstrap a0 = 2).  The left-edge anchor
    over p = a+1 is

      C(p) = prefix 1 . (110)^(p-1) . Wm2(p),  head on the prefix,
      state C,

    with [Wm2] the interleaved-marker working area (markers 1 at
    even cells, the bits of v = p - 2^k at odd cells LSB first,
    ending at the top marker).  One lap C(p) -> C(p+1): a 7-step
    prologue rebuilds the prefix three cells left, a 3-step cycle
    crosses comb-plus-leading-marker in the rotated (101) view, a
    2-step climb crosses the low set bits of v (marker cleared, bit
    kept), the first clear bit is set -- or the working area extends
    by one marker-bit pair on overflow v = 2^k - 1 -- and the return
    sweep restores the markers, clears the climbed bits and rebuilds
    the comb one unit longer.  Decomposition validated differentially
    against the raw simulator for p = 3..251
    (tools/counters/lap39.py, ALL OK). *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB1RD_1LC1LB_1LD0LB_1RD0RA *)
Definition tm_39 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DR StD
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DL StB
  | StC, S0 => mk S1 DL StD | StC, S1 => mk S0 DL StB
  | StD, S0 => mk S1 DR StD | StD, S1 => mk S0 DR StA
  end.

(** ** The anchor family *)

Definition Cc (p : positive) : cconf :=
  (StC, ([], S1, rep [S1; S1; S0] (Pos.to_nat p - 1) ++ Wm2 p)).

(** ** The unit runs (windowed, each checked by [reflexivity]) *)

(** U1: prologue -- the prefix moves three cells left. *)
Lemma U1 : wsteps false true tm_39 7 (StC, ([], S1, [S1]))
           = Some (StD, ([S1; S1; S0; S1], S1, [])).
Proof. reflexivity. Qed.

(** U2: rightward crossing of one comb unit (rotated 101 view). *)
Lemma U2 : wsteps true true tm_39 3 (StD, ([], S1, [S1; S0; S1]))
           = Some (StD, ([S1; S1; S0], S1, [])).
Proof. reflexivity. Qed.

(** U3: the climb -- one set bit of v per marker-bit pair. *)
Lemma U3 : wsteps true true tm_39 2 (StD, ([], S1, [S1; S1]))
           = Some (StD, ([S1; S0], S1, [])).
Proof. reflexivity. Qed.

(** U4: the increment -- the first clear bit is set. *)
Lemma U4 : wsteps true true tm_39 2 (StD, ([], S1, [S0; S1]))
           = Some (StB, ([S1; S0], S1, [])).
Proof. reflexivity. Qed.

(** U4e: overflow -- the set bit goes past the top marker. *)
Lemma U4e : wsteps true false tm_39 2 (StD, ([], S1, []))
            = Some (StB, ([S1; S0], S0, [])).
Proof. reflexivity. Qed.

(** U5: the turnaround at the next marker (kept). *)
Lemma U5 : wsteps true true tm_39 1 (StB, ([S1], S1, []))
           = Some (StB, ([], S1, [S1])).
Proof. reflexivity. Qed.

(** U6: the set bit is kept on the way back. *)
Lemma U6 : wsteps true true tm_39 1 (StB, ([S0], S1, []))
           = Some (StB, ([], S0, [S1])).
Proof. reflexivity. Qed.

(** U7: return over the climb -- markers restored, bits cleared. *)
Lemma U7 : wsteps true true tm_39 2 (StB, ([S1; S0], S0, []))
           = Some (StB, ([], S0, [S0; S1])).
Proof. reflexivity. Qed.

(** U8: restore a cleared marker, stepping onto a set cell. *)
Lemma U8 : wsteps true true tm_39 1 (StB, ([S1], S0, []))
           = Some (StC, ([], S1, [S1])).
Proof. reflexivity. Qed.

(** U10: clear the overshoot bit (overflow return). *)
Lemma U10 : wsteps true true tm_39 1 (StC, ([S0], S1, []))
            = Some (StB, ([], S0, [S0])).
Proof. reflexivity. Qed.

(** U9: leftward comb rebuild (3 steps per unit). *)
Lemma U9 : wsteps true true tm_39 3 (StC, ([S1; S0; S1], S1, []))
           = Some (StC, ([], S1, [S1; S1; S0])).
Proof. reflexivity. Qed.

(** Visit witnesses: B after 1 step, D after 3, A after 5. *)
Lemma UV1 : wsteps false true tm_39 1 (StC, ([], S1, []))
            = Some (StB, ([], S0, [S0])).
Proof. reflexivity. Qed.

Lemma UV3 : wsteps false true tm_39 3 (StC, ([], S1, []))
            = Some (StD, ([], S0, [S1; S1; S0])).
Proof. reflexivity. Qed.

Lemma UV5 : wsteps false true tm_39 5 (StC, ([], S1, []))
            = Some (StA, ([S0; S1], S1, [S0])).
Proof. reflexivity. Qed.

(** ** Transported phases (cons-normal forms) *)

Lemma phU1 : forall R,
  csteps tm_39 7 (StC, ([], S1, S1 :: R))
  = Some (StD, ([S1; S1; S0; S1], S1, R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U1). Qed.

Lemma phU2 : forall k L R,
  csteps tm_39 (3 * k) (StD, (L, S1, rep [S1; S0; S1] k ++ R))
  = Some (StD, (rep [S1; S1; S0] k ++ L, S1, R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U2 k L R). Qed.

Lemma phU3 : forall k L R,
  csteps tm_39 (2 * k) (StD, (L, S1, rep [S1; S1] k ++ R))
  = Some (StD, (rep [S1; S0] k ++ L, S1, R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U3 k L R). Qed.

Lemma phU4 : forall L R,
  csteps tm_39 2 (StD, (L, S1, S0 :: S1 :: R))
  = Some (StB, (S1 :: S0 :: L, S1, R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U4). Qed.

Lemma phU4e : forall L,
  csteps tm_39 2 (StD, (L, S1, []))
  = Some (StB, (S1 :: S0 :: L, S0, [])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U4e). Qed.

Lemma phU5 : forall L R,
  csteps tm_39 1 (StB, (S1 :: L, S1, R))
  = Some (StB, (L, S1, S1 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U5). Qed.

Lemma phU6 : forall L R,
  csteps tm_39 1 (StB, (S0 :: L, S1, R))
  = Some (StB, (L, S0, S1 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U6). Qed.

Lemma phU7 : forall k L R,
  csteps tm_39 (2 * k) (StB, (rep [S1; S0] k ++ L, S0, R))
  = Some (StB, (L, S0, rep [S0; S1] k ++ R)).
Proof.
  intros.
  pose proof (cycL _ _ _ _ _ _ _ U7 k L R) as H.
  cbn [app] in H. exact H.
Qed.

Lemma phU8 : forall L R,
  csteps tm_39 1 (StB, (S1 :: L, S0, R))
  = Some (StC, (L, S1, S1 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U8). Qed.

Lemma phU10 : forall L R,
  csteps tm_39 1 (StC, (S0 :: L, S1, R))
  = Some (StB, (L, S0, S0 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U10). Qed.

Lemma phU9 : forall k L R,
  csteps tm_39 (3 * k) (StC, (rep [S1; S0; S1] k ++ L, S1, R))
  = Some (StC, (L, S1, rep [S1; S1; S0] k ++ R)).
Proof.
  intros.
  pose proof (cycL _ _ _ _ _ _ _ U9 k L R) as H.
  cbn [app] in H. exact H.
Qed.

Lemma phUV1 : forall R,
  csteps tm_39 1 (StC, ([], S1, R)) = Some (StB, ([], S0, S0 :: R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R UV1). Qed.

Lemma phUV3 : forall R,
  csteps tm_39 3 (StC, ([], S1, R))
  = Some (StD, ([], S0, S1 :: S1 :: S0 :: R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R UV3). Qed.

Lemma phUV5 : forall R,
  csteps tm_39 5 (StC, ([], S1, R))
  = Some (StA, ([S0; S1], S1, S0 :: R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R UV5). Qed.

(** ** The lap *)

Lemma lap_39 : forall p, (3 <= p)%positive ->
  exists n c', csteps tm_39 n (Cc p) = Some c' /\
               lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p Hp.
  assert (H3 : 3 <= Pos.to_nat p).
  { change 3 with (Pos.to_nat 3). apply Pos2Nat.inj_le. exact Hp. }
  set (mm := Pos.to_nat p - 2).
  unfold Cc.
  replace (Pos.to_nat p - 1) with (S mm) by (unfold mm; lia).
  replace (Pos.to_nat (Pos.succ p) - 1) with (S (S mm))
    by (unfold mm; rewrite Pos2Nat.inj_succ; lia).
  destruct (cview p) as [j o] eqn:Ecv.
  destruct o as [q |].
  - (* interior carry on v *)
    destruct (Wm2_some _ _ _ Ecv) as (HW1 & HW2).
    destruct (Wm2_head q) as (wq & Hwq).
    rewrite HW1, HW2, Hwq.
    do 2 eexists. split; [| split].
    { rewrite rep110_expose.
      eapply csteps_chain. { apply phU1. }
      rewrite ones2_slide, rot_cross, rep_snoc3.
      eapply csteps_chain. { apply phU2. }
      eapply csteps_chain. { apply phU3. }
      eapply csteps_chain. { apply phU4. }
      eapply csteps_chain. { apply phU5. }
      eapply csteps_chain. { apply phU6. }
      eapply csteps_chain. { apply phU7. }
      rewrite rep110_expose.
      eapply csteps_chain. { apply phU8. }
      rewrite rot_cross, rep_snoc3, rep_snoc3.
      apply phU9. }
    { rewrite rot_ret.
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
    { rewrite rep110_expose.
      eapply csteps_chain. { apply phU1. }
      rewrite ones2_slide, rot_cross, rep_snoc3.
      eapply csteps_chain. { apply phU2. }
      eapply csteps_chain. { apply phU3. }
      eapply csteps_chain. { apply phU4e. }
      eapply csteps_chain. { apply phU8. }
      eapply csteps_chain. { apply phU10. }
      eapply csteps_chain. { apply phU7. }
      rewrite rep110_expose.
      eapply csteps_chain. { apply phU8. }
      rewrite rot_cross, rep_snoc3, rep_snoc3.
      apply phU9. }
    { rewrite rot_ret, rep_snoc2.
      reflexivity. }
    lia.
Qed.

(** ** Bootstrap, visits, and the theorem *)

Lemma boot_39 : exists t0, stepn tm_39 t0 InitES = Some (lift (Cc 3)).
Proof.
  exists 38.
  assert (H : match csteps tm_39 38 c0 with
              | Some c => ceqb c (Cc 3)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm_39 38 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
  f_equal. apply ceqb_lift. exact H.
Qed.

Lemma vis_39 : forall p q, (3 <= p)%positive ->
  exists k c, csteps tm_39 k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q _.
  unfold Cc.
  destruct q.
  - exists 5. eexists. split; [apply phUV5 | reflexivity].
  - exists 1. eexists. split; [apply phUV1 | reflexivity].
  - exists 0. eexists. split; reflexivity.
  - exists 3. eexists. split; [apply phUV3 | reflexivity].
Qed.

(** #39 never quasihalts: bbchallenge 1RB1RD_1LC1LB_1LD0LB_1RD0RA. *)
Theorem nqh_1RB1RD_1LC1LB_1LD0LB_1RD0RA : NeverQuasiHaltsSt tm_39.
Proof.
  apply (glue_neverqh tm_39 Cc 3).
  - exact boot_39.
  - exact lap_39.
  - intros p q Hp. apply vis_39; exact Hp.
Qed.

Theorem tm_39_nonhalt : NonHalt tm_39.
Proof. apply never_qh_nonhalt, nqh_1RB1RD_1LC1LB_1LD0LB_1RD0RA. Qed.
