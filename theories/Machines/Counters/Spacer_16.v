(** * Spacer_16: the spacer_counter machine #16, 1RB0RC_1RC1LB_1LD0RC_0LB0LA.

    First machine of the BBB harness's [spacer_counter] family
    (certificate results/counter16.cert: edge state C, voff 0,
    zoff 2, bootstrap a0 = 2).  The anchor is a RIGHT-frontier event

      S(m) = B(m) 11 0^(2m+2) 1,  head on the frontier 1, state C,

    with the counter in plain big-endian binary left of a 11
    separator and a spacer of 2m+2 zeros.  One lap: the frontier
    digs two cells into the spacer, then a 5-step translated cycle
    transcribes the remaining spacer zeros into a 1-run right of the
    head (the marker-carrying [cycLW] cycle); at the separator a
    1-step/cell run climbs the low set bits, the carry stops at the
    first clear bit (or writes a new most-significant 1 into blank
    territory on overflow m = 2^j - 1), and a 1-step/cell return
    sweep converts the whole 1-run into the new, two-longer spacer.
    The lap ends exactly at S(m+1) -- no trailing-blank slack in
    either shape.  Decomposition validated differentially against
    the raw simulator for m = 2..200 upstream. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB0RC_1RC1LB_1LD0RC_0LB0LA *)
Definition tm_16 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DR StC
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S1 DL StB
  | StC, S0 => mk S1 DL StD | StC, S1 => mk S0 DR StC
  | StD, S0 => mk S0 DL StB | StD, S1 => mk S0 DL StA
  end.

(** S(p): spacer of [2 to_nat p + 2] zeros, separator 11, then the
    counter bits (LSB nearest) in the left list; the head holds the
    frontier 1 and the right half-tape is blank. *)
Definition Cc (p : positive) : cconf :=
  (StC, (rep [S0] (2 * Pos.to_nat p + 2) ++ S1 :: S1 :: Bp p, S1, [])).

(** ** The unit runs *)

(** U1: the frontier digs two cells into the spacer. *)
Lemma U1 : wsteps true false tm_16 8 (StC, ([S0; S0], S1, []))
           = Some (StC, ([S1; S1], S1, [S1])).
Proof. reflexivity. Qed.

(** U2: second dig, launching the transcription marker. *)
Lemma U2 : wsteps true false tm_16 9 (StC, ([S1; S1; S0], S1, [S1]))
           = Some (StD, ([S1; S0], S0, [S1; S1; S1])).
Proof. reflexivity. Qed.

(** U3: the transcription cycle -- one spacer zero becomes one 1 on
    the right of the head, under a carried 1-marker. *)
Lemma U3 : wsteps true true tm_16 5 (StD, ([S1; S0], S0, []))
           = Some (StD, ([S1], S0, [S1])).
Proof. reflexivity. Qed.

(** U4: the marker dissolves at the separator. *)
Lemma U4 : wsteps true true tm_16 1 (StD, ([S1], S0, []))
           = Some (StB, ([], S1, [S0])).
Proof. reflexivity. Qed.

(** U5: the carry climb (1 step per set bit or separator 1). *)
Lemma U5 : wsteps true true tm_16 1 (StB, ([S1], S1, []))
           = Some (StB, ([], S1, [S1])).
Proof. reflexivity. Qed.

(** U6/U7: interior carry stop -- flip the first clear bit. *)
Lemma U6 : wsteps true true tm_16 1 (StB, ([S0], S1, []))
           = Some (StB, ([], S0, [S1])).
Proof. reflexivity. Qed.

Lemma U7 : wsteps true true tm_16 1 (StB, ([], S0, [S1]))
           = Some (StC, ([S1], S1, [])).
Proof. reflexivity. Qed.

(** U8: overflow stop -- a new most-significant 1 into the blank. *)
Lemma U8 : wsteps false true tm_16 3 (StB, ([S1], S1, [S1]))
           = Some (StC, ([S1], S1, [S1; S1])).
Proof. reflexivity. Qed.

(** U9: the return sweep (one 1 becomes one spacer 0 per step). *)
Lemma U9 : wsteps true true tm_16 1 (StC, ([], S1, [S1]))
           = Some (StC, ([S0], S1, [])).
Proof. reflexivity. Qed.

(** U9b: landing on the marker zero left by the carry launch. *)
Lemma U9b : wsteps true true tm_16 1 (StC, ([], S1, [S0]))
            = Some (StC, ([S0], S0, [])).
Proof. reflexivity. Qed.

(** U10: rebuild the separator over three zeros. *)
Lemma U10 : wsteps true true tm_16 7 (StC, ([S0; S0; S0], S0, []))
            = Some (StC, ([S1; S1], S1, [S1])).
Proof. reflexivity. Qed.

(** Visit witnesses: D after 2 steps, B after 3, A after 15. *)
Lemma UV2 : wsteps true false tm_16 2 (StC, ([], S1, []))
            = Some (StD, ([], S0, [S1])).
Proof. reflexivity. Qed.

Lemma UV3 : wsteps true false tm_16 3 (StC, ([S0], S1, []))
            = Some (StB, ([], S0, [S0; S1])).
Proof. reflexivity. Qed.

Lemma UV15 : wsteps true false tm_16 15 (StC, ([S0; S0; S0], S1, []))
             = Some (StA, ([S1; S0], S1, [S0; S1; S1])).
Proof. reflexivity. Qed.

(** ** Transported phases *)

Lemma phU1 : forall L,
  csteps tm_16 8 (StC, (S0 :: S0 :: L, S1, []))
  = Some (StC, (S1 :: S1 :: L, S1, [S1])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U1). Qed.

Lemma phU2 : forall L,
  csteps tm_16 9 (StC, (S1 :: S1 :: S0 :: L, S1, [S1]))
  = Some (StD, (S1 :: S0 :: L, S0, [S1; S1; S1])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U2). Qed.

Lemma phU3 : forall k L R,
  csteps tm_16 (5 * k) (StD, (S1 :: rep [S0] k ++ L, S0, R))
  = Some (StD, (S1 :: L, S0, rep [S1] k ++ R)).
Proof.
  intros.
  pose proof (cycLW _ _ _ _ [S1] _ _ _ U3 k L R) as H; cbn [app] in H.
  exact H.
Qed.

Lemma phU4 : forall L R,
  csteps tm_16 1 (StD, (S1 :: L, S0, R)) = Some (StB, (L, S1, S0 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U4). Qed.

Lemma phU5 : forall k L R,
  csteps tm_16 k (StB, (rep [S1] k ++ L, S1, R))
  = Some (StB, (L, S1, rep [S1] k ++ R)).
Proof.
  intros.
  pose proof (cycL _ _ _ _ _ _ _ U5 k L R) as H.
  rewrite Nat.mul_1_l in H; cbn [app] in H.
  exact H.
Qed.

Lemma phU6 : forall L R,
  csteps tm_16 1 (StB, (S0 :: L, S1, R)) = Some (StB, (L, S0, S1 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U6). Qed.

Lemma phU7 : forall L R,
  csteps tm_16 1 (StB, (L, S0, S1 :: R)) = Some (StC, (S1 :: L, S1, R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U7). Qed.

Lemma phU8 : forall R,
  csteps tm_16 3 (StB, ([S1], S1, S1 :: R))
  = Some (StC, ([S1], S1, S1 :: S1 :: R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U8). Qed.

Lemma phU9 : forall k L R,
  csteps tm_16 k (StC, (L, S1, rep [S1] k ++ R))
  = Some (StC, (rep [S0] k ++ L, S1, R)).
Proof.
  intros.
  pose proof (cycR _ _ _ _ _ _ U9 k L R) as H.
  rewrite Nat.mul_1_l in H. exact H.
Qed.

Lemma phU9b : forall L R,
  csteps tm_16 1 (StC, (L, S1, S0 :: R)) = Some (StC, (S0 :: L, S0, R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U9b). Qed.

Lemma phU10 : forall L R,
  csteps tm_16 7 (StC, (S0 :: S0 :: S0 :: L, S0, R))
  = Some (StC, (S1 :: S1 :: L, S1, S1 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U10). Qed.

Lemma phUV2 : forall L,
  csteps tm_16 2 (StC, (L, S1, [])) = Some (StD, (L, S0, [S1])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L UV2). Qed.

Lemma phUV3 : forall L,
  csteps tm_16 3 (StC, (S0 :: L, S1, [])) = Some (StB, (L, S0, [S0; S1])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L UV3). Qed.

Lemma phUV15 : forall L,
  csteps tm_16 15 (StC, (S0 :: S0 :: S0 :: L, S1, []))
  = Some (StA, (S1 :: S0 :: L, S1, [S0; S1; S1])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L UV15). Qed.

(** ** Conversion folds (all definitional) *)

Lemma spacer_fold : forall m X,
  S0 :: S0 :: S0 :: S0 :: rep [S0] m ++ X
  = rep [S0] (S (S (S (S m)))) ++ X.
Proof. reflexivity. Qed.

Lemma ones_fold : forall j X,
  S1 :: S1 :: rep [S1] j ++ X = rep [S1] (S (S j)) ++ X.
Proof. reflexivity. Qed.

Lemma ones_open : forall j X,
  rep [S1] (S j) ++ X = S1 :: rep [S1] j ++ X.
Proof. reflexivity. Qed.

Lemma ones_fold_nil : forall j,
  S1 :: S1 :: rep [S1] j = rep [S1] (S (S j)) ++ [].
Proof. intros. rewrite app_nil_r. reflexivity. Qed.

Lemma zeros_open3 : forall j X,
  S0 :: rep [S0] (S (S j)) ++ X = S0 :: S0 :: S0 :: rep [S0] j ++ X.
Proof. reflexivity. Qed.

(** ** The lap *)

Lemma lap_16 : forall p, (2 <= p)%positive ->
  exists n c', csteps tm_16 n (Cc p) = Some c' /\
               lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p Hp2.
  assert (Ha2 : 2 <= Pos.to_nat p).
  { change 2 with (Pos.to_nat 2). apply Pos2Nat.inj_le. exact Hp2. }
  destruct (cview p) as [j oq] eqn:Ecv.
  unfold Cc.
  rewrite Pos2Nat.inj_succ.
  destruct (Pos.to_nat p) as [|[|m]] eqn:Ha; [lia | lia |].
  replace (2 * S (S m) + 2) with (S (S (S (S (S (S (2 * m)))))))
    by lia.
  replace (2 * S (S (S m)) + 2) with (S (S (S (S (2 * m)))) + 4)
    by lia.
  cbn [rep app].
  destruct oq as [q0|].
  - (* interior carry *)
    destruct (cview_some_B p j q0 Ecv) as (HBp & HBs).
    do 2 eexists. split; [|split].
    + eapply csteps_chain. { apply phU1. }
      eapply csteps_chain. { apply phU2. }
      rewrite spacer_fold.
      eapply csteps_chain. { apply phU3. }
      eapply csteps_chain. { apply phU4. }
      rewrite HBp, ones_fold.
      eapply csteps_chain. { apply phU5. }
      eapply csteps_chain. { apply phU6. }
      eapply csteps_chain. { apply phU7. }
      eapply csteps_chain. { apply phU9. }
      eapply csteps_chain. { apply phU9b. }
      rewrite zeros_open3.
      eapply csteps_chain. { apply phU10. }
      rewrite rep_slide.
      change ([S1; S1; S1; S1] : list Sym) with (rep [S1] 4).
      rewrite <- rep_add.
      rewrite <- (app_nil_r (rep [S1] (S (S (S (S (2 * m)))) + 4))).
      apply phU9.
    + rewrite HBs. reflexivity.
    + lia.
  - (* overflow: m = 2^j - 1 *)
    destruct (cview_none_B p j Ecv) as (HBp & HBs).
    do 2 eexists. split; [|split].
    + eapply csteps_chain. { apply phU1. }
      eapply csteps_chain. { apply phU2. }
      rewrite spacer_fold.
      eapply csteps_chain. { apply phU3. }
      eapply csteps_chain. { apply phU4. }
      rewrite HBp, ones_fold_nil.
      replace (rep [S1] (S (S j))) with (rep [S1] (S j) ++ [S1]).
      2: { rewrite rep_shift. reflexivity. }
      rewrite <- app_assoc; cbn [app].
      eapply csteps_chain. { apply phU5. }
      rewrite ones_open.
      eapply csteps_chain. { apply phU8. }
      rewrite ones_fold.
      eapply csteps_chain. { apply phU9. }
      eapply csteps_chain. { apply phU9b. }
      rewrite zeros_open3.
      eapply csteps_chain. { apply phU10. }
      rewrite rep_slide.
      change ([S1; S1; S1; S1] : list Sym) with (rep [S1] 4).
      rewrite <- rep_add.
      rewrite <- (app_nil_r (rep [S1] (S (S (S (S (2 * m)))) + 4))).
      apply phU9.
    + rewrite HBs. reflexivity.
    + lia.
Qed.

(** ** Bootstrap, visits, and the theorem *)

Lemma boot_16 : exists t0, stepn tm_16 t0 InitES = Some (lift (Cc 2)).
Proof.
  exists 100.
  assert (H : match csteps tm_16 100 c0 with
              | Some c => ceqb c (Cc 2)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm_16 100 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
  f_equal. apply ceqb_lift. exact H.
Qed.

Lemma vis_16 : forall p q, (2 <= p)%positive ->
  exists k c, csteps tm_16 k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q Hp2.
  assert (Ha2 : 2 <= Pos.to_nat p).
  { change 2 with (Pos.to_nat 2). apply Pos2Nat.inj_le. exact Hp2. }
  unfold Cc.
  destruct (Pos.to_nat p) as [|[|m]] eqn:Ha; [lia | lia |].
  replace (2 * S (S m) + 2) with (S (S (S (S (S (S (2 * m)))))))
    by lia.
  cbn [rep app].
  destruct q.
  - exists 15. eexists. split; [apply phUV15 | reflexivity].
  - exists 3. eexists. split; [apply phUV3 | reflexivity].
  - exists 0. eexists. split; reflexivity.
  - exists 2. eexists. split; [apply phUV2 | reflexivity].
Qed.

(** #16 never quasihalts: bbchallenge 1RB0RC_1RC1LB_1LD0RC_0LB0LA. *)
Theorem nqh_1RB0RC_1RC1LB_1LD0RC_0LB0LA : NeverQuasiHaltsSt tm_16.
Proof.
  apply (glue_neverqh tm_16 Cc 2).
  - exact boot_16.
  - exact lap_16.
  - intros p q Hp. apply vis_16; exact Hp.
Qed.

Theorem tm_16_nonhalt : NonHalt tm_16.
Proof. apply never_qh_nonhalt, nqh_1RB0RC_1RC1LB_1LD0RC_0LB0LA. Qed.
