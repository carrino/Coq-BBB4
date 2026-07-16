(** * Spacer_23: the spacer_counter machine #23, 1RB1LA_1LC0RB_0LA0LD_1RD0RB.

    Third machine of the BBB harness's [spacer_counter] family
    (certificate results/counter23.cert: edge state B, voff -1,
    zoff 2, bootstrap a0 = 2).  Same right-frontier anchor and lap
    geometry as #16 (theories/Machines/Counters/Spacer_16.v) with
    the state roles permuted; because voff = -1 the anchor counter
    is one below the harness's traversal count, so the spacer is
    2m+4 and the bootstrap lands on S(1) -- the lap therefore runs
    from every positive.  Validated differentially for
    m = 1..200 upstream. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB1LA_1LC0RB_0LA0LD_1RD0RB *)
Definition tm_23 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DL StA
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S0 DR StB
  | StC, S0 => mk S0 DL StA | StC, S1 => mk S0 DL StD
  | StD, S0 => mk S1 DR StD | StD, S1 => mk S0 DR StB
  end.

(** S(p): spacer of [2 to_nat p + 4] zeros, separator 11, counter
    bits (LSB nearest) in the left list; head on the frontier 1. *)
Definition Cc (p : positive) : cconf :=
  (StB, (rep [S0] (2 * Pos.to_nat p + 4) ++ S1 :: S1 :: Bp p, S1, [])).

(** ** The unit runs *)

Lemma U1 : wsteps true false tm_23 8 (StB, ([S0; S0], S1, []))
           = Some (StD, ([S1; S1], S1, [S1])).
Proof. reflexivity. Qed.

Lemma U2 : wsteps true false tm_23 9 (StD, ([S1; S1; S0], S1, [S1]))
           = Some (StC, ([S1; S0], S0, [S1; S1; S1])).
Proof. reflexivity. Qed.

Lemma U3 : wsteps true true tm_23 5 (StC, ([S1; S0], S0, []))
           = Some (StC, ([S1], S0, [S1])).
Proof. reflexivity. Qed.

Lemma U4 : wsteps true true tm_23 1 (StC, ([S1], S0, []))
           = Some (StA, ([], S1, [S0])).
Proof. reflexivity. Qed.

Lemma U5 : wsteps true true tm_23 1 (StA, ([S1], S1, []))
           = Some (StA, ([], S1, [S1])).
Proof. reflexivity. Qed.

Lemma U6 : wsteps true true tm_23 1 (StA, ([S0], S1, []))
           = Some (StA, ([], S0, [S1])).
Proof. reflexivity. Qed.

Lemma U7 : wsteps true true tm_23 1 (StA, ([], S0, [S1]))
           = Some (StB, ([S1], S1, [])).
Proof. reflexivity. Qed.

Lemma U8 : wsteps false true tm_23 3 (StA, ([S1], S1, [S1]))
           = Some (StB, ([S1], S1, [S1; S1])).
Proof. reflexivity. Qed.

Lemma U9 : wsteps true true tm_23 1 (StB, ([], S1, [S1]))
           = Some (StB, ([S0], S1, [])).
Proof. reflexivity. Qed.

Lemma U9b : wsteps true true tm_23 1 (StB, ([], S1, [S0]))
            = Some (StB, ([S0], S0, [])).
Proof. reflexivity. Qed.

Lemma U10 : wsteps true true tm_23 8 (StB, ([S0; S0; S0], S0, []))
            = Some (StB, ([S0; S1; S1], S1, [])).
Proof. reflexivity. Qed.

(** Visit witnesses: C after 2 steps, A after 3, D after 6. *)
Lemma UV2 : wsteps true false tm_23 2 (StB, ([], S1, []))
            = Some (StC, ([], S0, [S1])).
Proof. reflexivity. Qed.

Lemma UV3 : wsteps true false tm_23 3 (StB, ([S0], S1, []))
            = Some (StA, ([], S0, [S0; S1])).
Proof. reflexivity. Qed.

Lemma UV6 : wsteps true false tm_23 6 (StB, ([S0; S0], S1, []))
            = Some (StD, ([], S0, [S0; S1; S1])).
Proof. reflexivity. Qed.

(** ** Transported phases *)

Lemma phU1 : forall L,
  csteps tm_23 8 (StB, (S0 :: S0 :: L, S1, []))
  = Some (StD, (S1 :: S1 :: L, S1, [S1])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U1). Qed.

Lemma phU2 : forall L,
  csteps tm_23 9 (StD, (S1 :: S1 :: S0 :: L, S1, [S1]))
  = Some (StC, (S1 :: S0 :: L, S0, [S1; S1; S1])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U2). Qed.

Lemma phU3 : forall k L R,
  csteps tm_23 (5 * k) (StC, (S1 :: rep [S0] k ++ L, S0, R))
  = Some (StC, (S1 :: L, S0, rep [S1] k ++ R)).
Proof.
  intros.
  pose proof (cycLW _ _ _ _ [S1] _ _ _ U3 k L R) as H; cbn [app] in H.
  exact H.
Qed.

Lemma phU4 : forall L R,
  csteps tm_23 1 (StC, (S1 :: L, S0, R)) = Some (StA, (L, S1, S0 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U4). Qed.

Lemma phU5 : forall k L R,
  csteps tm_23 k (StA, (rep [S1] k ++ L, S1, R))
  = Some (StA, (L, S1, rep [S1] k ++ R)).
Proof.
  intros.
  pose proof (cycL _ _ _ _ _ _ _ U5 k L R) as H.
  rewrite Nat.mul_1_l in H; cbn [app] in H.
  exact H.
Qed.

Lemma phU6 : forall L R,
  csteps tm_23 1 (StA, (S0 :: L, S1, R)) = Some (StA, (L, S0, S1 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U6). Qed.

Lemma phU7 : forall L R,
  csteps tm_23 1 (StA, (L, S0, S1 :: R)) = Some (StB, (S1 :: L, S1, R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U7). Qed.

Lemma phU8 : forall R,
  csteps tm_23 3 (StA, ([S1], S1, S1 :: R))
  = Some (StB, ([S1], S1, S1 :: S1 :: R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U8). Qed.

Lemma phU9 : forall k L R,
  csteps tm_23 k (StB, (L, S1, rep [S1] k ++ R))
  = Some (StB, (rep [S0] k ++ L, S1, R)).
Proof.
  intros.
  pose proof (cycR _ _ _ _ _ _ U9 k L R) as H.
  rewrite Nat.mul_1_l in H. exact H.
Qed.

Lemma phU9b : forall L R,
  csteps tm_23 1 (StB, (L, S1, S0 :: R)) = Some (StB, (S0 :: L, S0, R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U9b). Qed.

Lemma phU10 : forall L R,
  csteps tm_23 8 (StB, (S0 :: S0 :: S0 :: L, S0, R))
  = Some (StB, (S0 :: S1 :: S1 :: L, S1, R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U10). Qed.

Lemma phUV2 : forall L,
  csteps tm_23 2 (StB, (L, S1, [])) = Some (StC, (L, S0, [S1])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L UV2). Qed.

Lemma phUV3 : forall L,
  csteps tm_23 3 (StB, (S0 :: L, S1, [])) = Some (StA, (L, S0, [S0; S1])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L UV3). Qed.

Lemma phUV6 : forall L,
  csteps tm_23 6 (StB, (S0 :: S0 :: L, S1, []))
  = Some (StD, (L, S0, [S0; S1; S1])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L UV6). Qed.

(** ** Conversion folds *)

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

Lemma zeros_openS : forall k X,
  rep [S0] (S k) ++ X = S0 :: rep [S0] k ++ X.
Proof. reflexivity. Qed.

(** ** The lap *)

Lemma lap_23 : forall p, (1 <= p)%positive ->
  exists n c', csteps tm_23 n (Cc p) = Some c' /\
               lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p _.
  pose proof (Pos2Nat.is_pos p) as Hpos.
  destruct (cview p) as [j oq] eqn:Ecv.
  unfold Cc.
  rewrite Pos2Nat.inj_succ.
  destruct (Pos.to_nat p) as [|m] eqn:Ha; [lia |].
  replace (2 * S m + 4) with (S (S (S (S (S (S (2 * m)))))))
    by lia.
  replace (2 * S (S m) + 4) with (S (S (S (S (S (2 * m)))) + 3))
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
      change ([S1; S1; S1] : list Sym) with (rep [S1] 3).
      rewrite <- rep_add.
      rewrite <- (app_nil_r (rep [S1] (S (S (S (S (2 * m)))) + 3))).
      apply phU9.
    + rewrite HBs, rep_slide. reflexivity.
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
      change ([S1; S1; S1] : list Sym) with (rep [S1] 3).
      rewrite <- rep_add.
      rewrite <- (app_nil_r (rep [S1] (S (S (S (S (2 * m)))) + 3))).
      apply phU9.
    + rewrite HBs, rep_slide. reflexivity.
    + lia.
Qed.

(** ** Bootstrap, visits, and the theorem *)

Lemma boot_23 : exists t0, stepn tm_23 t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 78.
  assert (H : match csteps tm_23 78 c0 with
              | Some c => ceqb c (Cc 1)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm_23 78 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
  f_equal. apply ceqb_lift. exact H.
Qed.

Lemma vis_23 : forall p q, (1 <= p)%positive ->
  exists k c, csteps tm_23 k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q _.
  pose proof (Pos2Nat.is_pos p) as Hpos.
  unfold Cc.
  destruct (Pos.to_nat p) as [|m] eqn:Ha; [lia |].
  replace (2 * S m + 4) with (S (S (S (S (S (S (2 * m)))))))
    by lia.
  cbn [rep app].
  destruct q.
  - exists 3. eexists. split; [apply phUV3 | reflexivity].
  - exists 0. eexists. split; reflexivity.
  - exists 2. eexists. split; [apply phUV2 | reflexivity].
  - exists 6. eexists. split; [apply phUV6 | reflexivity].
Qed.

(** #23 never quasihalts: bbchallenge 1RB1LA_1LC0RB_0LA0LD_1RD0RB. *)
Theorem nqh_1RB1LA_1LC0RB_0LA0LD_1RD0RB : NeverQuasiHaltsSt tm_23.
Proof.
  apply (glue_neverqh tm_23 Cc 1).
  - exact boot_23.
  - exact lap_23.
  - intros p q Hp. apply vis_23; exact Hp.
Qed.

Theorem tm_23_nonhalt : NonHalt tm_23.
Proof. apply never_qh_nonhalt, nqh_1RB1LA_1LC0RB_0LA0LD_1RD0RB. Qed.
