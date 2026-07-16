(** * Mono_31: the mono_counter machine #31, 1RB1LD_1RC0RB_0LA1RB_0LD1LA.

    Third machine of the BBB harness's [mono_counter] family
    (certificate results/counter31.cert: comb 110, edge state B,
    hoff +1, bootstrap a0 = 2).  Same anchor family as #10/#26 but a
    leaner lap: the comb crossings are 3-step cycles with no
    intra-unit turnarounds, the increment's carry is a 2-step cycle,
    and the sweep-2 return fuses with the increment walk-back.  The
    head rests one cell INSIDE the comb (state B on the second comb
    cell).  Phase decomposition validated differentially against the
    raw simulator for a = 2..300 upstream. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB1LD_1RC0RB_0LA1RB_0LD1LA *)
Definition tm_31 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DL StD
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S0 DR StB
  | StC, S0 => mk S0 DL StA | StC, S1 => mk S1 DR StB
  | StD, S0 => mk S0 DL StD | StD, S1 => mk S1 DL StA
  end.

(** C(p): head on the second comb cell, state B; left list holds the
    first comb cell, the rest of the comb sits rotated in r. *)
Definition Cc (p : positive) : cconf :=
  (StB, ([S1], S1,
         rep [S0; S1; S1] (Pos.to_nat p - 1) ++ S0 :: Wp p)).

(** ** The unit runs *)

(** U2: rightward comb crossing (3 steps, monotone). *)
Lemma U2 : wsteps true true tm_31 3 (StB, ([], S1, [S0; S1; S1]))
           = Some (StB, ([S1; S1; S0], S1, [])).
Proof. reflexivity. Qed.

(** U3: turnaround at the working area (also sweep-3's fix-up). *)
Lemma U3 : wsteps true true tm_31 4 (StB, ([], S1, [S0; S0]))
           = Some (StD, ([], S0, [S1; S0])).
Proof. reflexivity. Qed.

(** U3v: the same turnaround at the right tape edge (overflow). *)
Lemma U3v : wsteps true false tm_31 4 (StB, ([], S1, [S0]))
            = Some (StD, ([], S0, [S1; S0])).
Proof. reflexivity. Qed.

(** U4: leftward comb crossing (3 steps). *)
Lemma U4 : wsteps true true tm_31 3 (StD, ([S1; S1; S0], S0, []))
           = Some (StD, ([], S0, [S1; S1; S0])).
Proof. reflexivity. Qed.

(** U5: left-edge turnaround / event closer (3 steps). *)
Lemma U5 : wsteps false true tm_31 3 (StD, ([S1], S0, []))
           = Some (StB, ([S1], S1, [S0])).
Proof. reflexivity. Qed.

(** U6z: the whole increment when the low bit is 0. *)
Lemma U6z : wsteps true true tm_31 8 (StB, ([], S1, [S0; S1; S0; S0]))
            = Some (StD, ([], S0, [S1; S1; S1; S0])).
Proof. reflexivity. Qed.

(** U6a: increment approach onto a set low bit. *)
Lemma U6a : wsteps true true tm_31 4 (StB, ([], S1, [S0; S1; S0; S1]))
            = Some (StC, ([S1; S1; S1; S0], S1, [])).
Proof. reflexivity. Qed.

(** U7: carry cycle (2 steps per further set bit). *)
Lemma U7 : wsteps true true tm_31 2 (StC, ([], S1, [S0; S1]))
           = Some (StC, ([S1; S1], S1, [])).
Proof. reflexivity. Qed.

(** U8 / U8v: carry stop at an interior 0 bit / past the area. *)
Lemma U8 : wsteps true true tm_31 3 (StC, ([], S1, [S0; S0]))
           = Some (StA, ([S1], S1, [S0])).
Proof. reflexivity. Qed.

Lemma U8v : wsteps true false tm_31 3 (StC, ([], S1, []))
            = Some (StA, ([S1], S1, [S0])).
Proof. reflexivity. Qed.

(** U9: walk back over the written 1-blocks; U9g re-enters the comb. *)
Lemma U9 : wsteps true true tm_31 2 (StA, ([S1; S1], S1, []))
           = Some (StA, ([], S1, [S1; S1])).
Proof. reflexivity. Qed.

Lemma U9g : wsteps true true tm_31 1 (StA, ([S0], S1, []))
            = Some (StD, ([], S0, [S1])).
Proof. reflexivity. Qed.

(** U10: sweep-3 zap of a leftover 1 (1 step each). *)
Lemma U10 : wsteps true true tm_31 1 (StB, ([], S1, [S1]))
            = Some (StB, ([S0], S1, [])).
Proof. reflexivity. Qed.

(** U11: sweep-3 walk back over the zapped zeros (1 step each). *)
Lemma U11 : wsteps true true tm_31 1 (StD, ([S0], S0, []))
            = Some (StD, ([], S0, [S0])).
Proof. reflexivity. Qed.

(** Visit witness: state C two steps into a crossing. *)
Lemma UVC : wsteps true true tm_31 2 (StB, ([], S1, [S0; S1]))
            = Some (StC, ([S1; S0], S1, [])).
Proof. reflexivity. Qed.

(** Visit witness: state A two steps into the edge turnaround. *)
Lemma UVA : wsteps false true tm_31 2 (StD, ([S1], S0, []))
            = Some (StA, ([], S0, [S1; S0])).
Proof. reflexivity. Qed.

(** ** Transported phases *)

Lemma phU2 : forall k L R,
  csteps tm_31 (3 * k) (StB, (L, S1, rep [S0; S1; S1] k ++ R))
  = Some (StB, (rep [S1; S1; S0] k ++ L, S1, R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U2 k L R). Qed.

Lemma phU2one : forall L R,
  csteps tm_31 3 (StB, (L, S1, S0 :: S1 :: S1 :: R))
  = Some (StB, (S1 :: S1 :: S0 :: L, S1, R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U2). Qed.

Lemma phU3 : forall L R,
  csteps tm_31 4 (StB, (L, S1, S0 :: S0 :: R))
  = Some (StD, (L, S0, S1 :: S0 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U3). Qed.

Lemma phU3v : forall L,
  csteps tm_31 4 (StB, (L, S1, [S0]))
  = Some (StD, (L, S0, [S1; S0])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U3v). Qed.

Lemma phU4 : forall k L R,
  csteps tm_31 (3 * k) (StD, (rep [S1; S1; S0] k ++ L, S0, R))
  = Some (StD, (L, S0, rep [S1; S1; S0] k ++ R)).
Proof.
  intros.
  pose proof (cycL _ _ _ _ _ _ _ U4 k L R) as H; cbn [app] in H.
  exact H.
Qed.

Lemma phU5 : forall R,
  csteps tm_31 3 (StD, ([S1], S0, R))
  = Some (StB, ([S1], S1, S0 :: R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U5). Qed.

Lemma phU6z : forall L R,
  csteps tm_31 8 (StB, (L, S1, S0 :: S1 :: S0 :: S0 :: R))
  = Some (StD, (L, S0, S1 :: S1 :: S1 :: S0 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U6z). Qed.

Lemma phU6a : forall L R,
  csteps tm_31 4 (StB, (L, S1, S0 :: S1 :: S0 :: S1 :: R))
  = Some (StC, (S1 :: S1 :: S1 :: S0 :: L, S1, R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U6a). Qed.

Lemma phU7 : forall k L R,
  csteps tm_31 (2 * k) (StC, (L, S1, rep [S0; S1] k ++ R))
  = Some (StC, (rep [S1; S1] k ++ L, S1, R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U7 k L R). Qed.

Lemma phU8 : forall L R,
  csteps tm_31 3 (StC, (L, S1, S0 :: S0 :: R))
  = Some (StA, (S1 :: L, S1, S0 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U8). Qed.

Lemma phU8v : forall L,
  csteps tm_31 3 (StC, (L, S1, []))
  = Some (StA, (S1 :: L, S1, [S0])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U8v). Qed.

Lemma phU9 : forall k L R,
  csteps tm_31 (2 * k) (StA, (rep [S1; S1] k ++ L, S1, R))
  = Some (StA, (L, S1, rep [S1; S1] k ++ R)).
Proof.
  intros.
  pose proof (cycL _ _ _ _ _ _ _ U9 k L R) as H; cbn [app] in H.
  exact H.
Qed.

Lemma phU9g : forall L R,
  csteps tm_31 1 (StA, (S0 :: L, S1, R))
  = Some (StD, (L, S0, S1 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U9g). Qed.

Lemma phU10 : forall k L R,
  csteps tm_31 k (StB, (L, S1, rep [S1] k ++ R))
  = Some (StB, (rep [S0] k ++ L, S1, R)).
Proof.
  intros.
  pose proof (cycR _ _ _ _ _ _ U10 k L R) as H.
  rewrite Nat.mul_1_l in H. exact H.
Qed.

Lemma phU11 : forall k L R,
  csteps tm_31 k (StD, (rep [S0] k ++ L, S0, R))
  = Some (StD, (L, S0, rep [S0] k ++ R)).
Proof.
  intros.
  pose proof (cycL _ _ _ _ _ _ _ U11 k L R) as H.
  rewrite Nat.mul_1_l in H; cbn [app] in H.
  exact H.
Qed.

Lemma phUVC : forall L R,
  csteps tm_31 2 (StB, (L, S1, S0 :: S1 :: R))
  = Some (StC, (S1 :: S0 :: L, S1, R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R UVC). Qed.

Lemma phUVA : forall R,
  csteps tm_31 2 (StD, ([S1], S0, R))
  = Some (StA, ([], S0, S1 :: S0 :: R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R UVA). Qed.

(** ** Alignment rewrites *)

(** The one-cell comb rotation of this anchor. *)
Lemma rot31 : forall k X,
  S0 :: rep [S1; S1; S0] k ++ X = rep [S0; S1; S1] k ++ S0 :: X.
Proof.
  induction k; intros; cbn [rep app].
  - reflexivity.
  - now rewrite IHk.
Qed.

(** The increment deposit fuses into walk-back blocks. *)
Lemma align31a : forall j X,
  S1 :: rep [S1; S1] j ++ S1 :: S1 :: S1 :: S0 :: X
  = rep [S1; S1] (S (S j)) ++ S0 :: X.
Proof.
  intros.
  rewrite !rep_dbl.
  replace (2 * S (S j)) with (S (S (S (S (2 * j))))) by lia.
  cbn [rep app].
  rewrite !rep_slide.
  reflexivity.
Qed.

(** The dirty block after one sweep-3 crossing is a flat 1-run. *)
Lemma align31b : forall j X,
  S1 :: rep [S1; S1] j ++ S0 :: X = rep [S1] (S (2 * j)) ++ S0 :: X.
Proof.
  intros. rewrite rep_dbl. reflexivity.
Qed.

(** Final working areas. *)
Lemma final31_int : forall j wq,
  rep [S0] (S (2 * j)) ++ S1 :: S0 :: wq
  = rep [S0; S0] j ++ S0 :: S1 :: S0 :: wq.
Proof.
  intros.
  rewrite rep_dbl; cbn [rep app].
  rewrite rep_slide.
  reflexivity.
Qed.

Lemma final31_ov : forall j,
  S0 :: rep [S0] (S (2 * j)) ++ [S1; S0]
  = (S0 :: rep [S0; S0] j ++ [S0; S1]) ++ [S0].
Proof.
  intros.
  rewrite rep_dbl; cbn [rep app].
  rewrite <- !app_assoc; cbn [app].
  rewrite !rep_slide.
  reflexivity.
Qed.

(** ** The lap *)

Lemma lap_31 : forall p, (2 <= p)%positive ->
  exists n c', csteps tm_31 n (Cc p) = Some c' /\
               lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p Hp2.
  assert (Ha2 : 2 <= Pos.to_nat p).
  { change 2 with (Pos.to_nat 2). apply Pos2Nat.inj_le. exact Hp2. }
  destruct (Wp_head p) as (wp' & Hwp).
  destruct (cview p) as [j oq] eqn:Ecv.
  unfold Cc.
  rewrite Pos2Nat.inj_succ.
  destruct (Pos.to_nat p) as [|[|m]] eqn:Ha; [lia | lia |].
  cbn [Nat.sub].
  destruct oq as [q0|].
  - (* interior carry *)
    destruct (cview_some_W p j q0 Ecv) as (HWp & HWs).
    destruct (Wp_head q0) as (wq & Hwq).
    destruct j as [|j'].
    + (* low bit 0 *)
      do 2 eexists. split; [|split].
      * (* sweep 1 *)
        eapply csteps_chain. { apply phU2. }
        rewrite Hwp.
        eapply csteps_chain. { apply phU3. }
        rewrite <- Hwp.
        eapply csteps_chain. { apply phU4. }
        eapply csteps_chain. { apply phU5. }
        rewrite rot31.
        (* sweep 2: increment on a clear low bit *)
        eapply csteps_chain. { apply phU2. }
        rewrite HWp.
        change (rep [S0; S1] 0 ++ S0 :: S0 :: Wp q0)
          with (S0 :: S0 :: Wp q0).
        rewrite Hwq.
        eapply csteps_chain. { apply phU6z. }
        rewrite <- Hwq.
        eapply csteps_chain. { apply phU4. }
        eapply csteps_chain. { apply phU5. }
        rewrite rot31.
        (* sweep 3 *)
        eapply csteps_chain. { apply phU2. }
        eapply csteps_chain. { apply phU2one. }
        change (S1 :: S0 :: Wp q0)
          with (rep [S1] (S (2 * 0)) ++ S0 :: Wp q0).
        eapply csteps_chain. { apply phU10. }
        rewrite Hwq.
        eapply csteps_chain. { apply phU3. }
        eapply csteps_chain. { apply phU11. }
        change (S1 :: S1 :: S0 :: rep [S1; S1; S0] (S m) ++ [S1])
          with (rep [S1; S1; S0] (S (S m)) ++ [S1]).
        eapply csteps_chain. { apply phU4. }
        apply phU5.
      * rewrite HWs, Hwq, rot31, final31_int.
        reflexivity.
      * lia.
    + (* low bit 1: carry run *)
      do 2 eexists. split; [|split].
      * (* sweep 1 *)
        eapply csteps_chain. { apply phU2. }
        rewrite Hwp.
        eapply csteps_chain. { apply phU3. }
        rewrite <- Hwp.
        eapply csteps_chain. { apply phU4. }
        eapply csteps_chain. { apply phU5. }
        rewrite rot31.
        (* sweep 2: carry *)
        eapply csteps_chain. { apply phU2. }
        rewrite HWp.
        change (rep [S0; S1] (S j') ++ S0 :: S0 :: Wp q0)
          with (S0 :: S1 :: (rep [S0; S1] j' ++ S0 :: S0 :: Wp q0)).
        eapply csteps_chain. { apply phU6a. }
        eapply csteps_chain. { apply phU7. }
        rewrite Hwq.
        eapply csteps_chain. { apply phU8. }
        rewrite align31a.
        eapply csteps_chain. { apply phU9. }
        eapply csteps_chain. { apply phU9g. }
        eapply csteps_chain. { apply phU4. }
        eapply csteps_chain. { apply phU5. }
        rewrite rot31.
        (* sweep 3 *)
        eapply csteps_chain. { apply phU2. }
        change (S0 :: S1 :: rep [S1; S1] (S (S j')) ++ S0 :: S0 :: wq)
          with (S0 :: S1 :: S1 :: (S1 :: rep [S1; S1] (S j') ++
                                   S0 :: S0 :: wq)).
        eapply csteps_chain. { apply phU2one. }
        rewrite align31b.
        eapply csteps_chain. { apply phU10. }
        eapply csteps_chain. { apply phU3. }
        eapply csteps_chain. { apply phU11. }
        change (S1 :: S1 :: S0 :: rep [S1; S1; S0] (S m) ++ [S1])
          with (rep [S1; S1; S0] (S (S m)) ++ [S1]).
        eapply csteps_chain. { apply phU4. }
        apply phU5.
      * rewrite HWs, Hwq, rot31, final31_int.
        reflexivity.
      * lia.
  - (* overflow *)
    destruct (cview_none_W p j Ecv) as (HWp & HWs).
    destruct j as [|j'].
    { exfalso. rewrite HWp in Hwp. discriminate. }
    do 2 eexists. split; [|split].
    + (* sweep 1 *)
      eapply csteps_chain. { apply phU2. }
      rewrite Hwp.
      eapply csteps_chain. { apply phU3. }
      rewrite <- Hwp.
      eapply csteps_chain. { apply phU4. }
      eapply csteps_chain. { apply phU5. }
      rewrite rot31.
      (* sweep 2: carry off the right end *)
      eapply csteps_chain. { apply phU2. }
      rewrite HWp.
      change (rep [S0; S1] (S j') : list Sym)
        with (S0 :: S1 :: rep [S0; S1] j').
      rewrite <- (app_nil_r (rep [S0; S1] j')).
      eapply csteps_chain. { apply phU6a. }
      eapply csteps_chain. { apply phU7. }
      eapply csteps_chain. { apply phU8v. }
      rewrite align31a.
      eapply csteps_chain. { apply phU9. }
      eapply csteps_chain. { apply phU9g. }
      eapply csteps_chain. { apply phU4. }
      eapply csteps_chain. { apply phU5. }
      rewrite rot31.
      (* sweep 3 *)
      eapply csteps_chain. { apply phU2. }
      change (S0 :: S1 :: rep [S1; S1] (S (S j')) ++ [S0])
        with (S0 :: S1 :: S1 :: (S1 :: rep [S1; S1] (S j') ++ [S0])).
      eapply csteps_chain. { apply phU2one. }
      rewrite align31b.
      eapply csteps_chain. { apply phU10. }
      eapply csteps_chain. { apply phU3v. }
      eapply csteps_chain. { apply phU11. }
      change (S1 :: S1 :: S0 :: rep [S1; S1; S0] (S m) ++ [S1])
        with (rep [S1; S1; S0] (S (S m)) ++ [S1]).
      eapply csteps_chain. { apply phU4. }
      apply phU5.
    + rewrite HWs, rot31, final31_ov, app_assoc, lift_app_blank.
      reflexivity.
    + lia.
Qed.

(** ** Bootstrap, visits, and the theorem *)

Lemma boot_31 : exists t0, stepn tm_31 t0 InitES = Some (lift (Cc 2)).
Proof.
  exists 56.
  assert (H : match csteps tm_31 56 c0 with
              | Some c => ceqb c (Cc 2)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm_31 56 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
  f_equal. apply ceqb_lift. exact H.
Qed.

Lemma vis_31 : forall p q, (2 <= p)%positive ->
  exists k c, csteps tm_31 k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q Hp2.
  assert (Ha2 : 2 <= Pos.to_nat p).
  { change 2 with (Pos.to_nat 2). apply Pos2Nat.inj_le. exact Hp2. }
  destruct (Wp_head p) as (wp' & Hwp).
  unfold Cc.
  destruct (Pos.to_nat p) as [|[|m]] eqn:Ha; [lia | lia |].
  cbn [Nat.sub].
  destruct q.
  - (* A: through one full descent, two steps into the edge turn *)
    do 2 eexists. split; [|shelve].
    eapply csteps_chain. { apply phU2. }
    rewrite Hwp.
    eapply csteps_chain. { apply phU3. }
    eapply csteps_chain. { apply phU4. }
    apply phUVA.
    Unshelve. reflexivity.
  - exists 0. eexists. split; reflexivity.
  - (* C: two steps into the first crossing *)
    do 2 eexists. split; [|shelve].
    cbn [rep app].
    apply phUVC.
    Unshelve. reflexivity.
  - (* D: through the first sweep's turnaround *)
    do 2 eexists. split; [|shelve].
    eapply csteps_chain. { apply phU2. }
    rewrite Hwp.
    apply phU3.
    Unshelve. reflexivity.
Qed.

(** #31 never quasihalts: bbchallenge 1RB1LD_1RC0RB_0LA1RB_0LD1LA. *)
Theorem nqh_1RB1LD_1RC0RB_0LA1RB_0LD1LA : NeverQuasiHaltsSt tm_31.
Proof.
  apply (glue_neverqh tm_31 Cc 2).
  - exact boot_31.
  - exact lap_31.
  - intros p q Hp. apply vis_31; exact Hp.
Qed.

Theorem tm_31_nonhalt : NonHalt tm_31.
Proof. apply never_qh_nonhalt, nqh_1RB1LD_1RC0RB_0LA1RB_0LD1LA. Qed.
