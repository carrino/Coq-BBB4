(** * Mono_26: the mono_counter machine #26, 1RB1LC_0LC0RB_1RD1LA_1RB0LA.

    Second machine of the BBB harness's [mono_counter] family
    (certificate results/counter26.cert: comb 110, edge state A,
    hoff -1, bootstrap a0 = 2).  Same anchor family and identical
    three-sweep lap geometry as #10 (theories/Machines/Counters/
    Mono_10.v) -- the two machines drive the same unit-run shapes
    with different transition tables.  The anchor differs by one
    cell: the head rests on the blank LEFT of the comb in state A,
    so the prologue is 1 step (not 2) and the event closer 6 steps
    (not 5).  The phase decomposition was validated differentially
    against the raw simulator for a = 2..300 upstream. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB1LC_0LC0RB_1RD1LA_1RB0LA *)
Definition tm_26 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DL StC
  | StB, S0 => mk S0 DL StC | StB, S1 => mk S0 DR StB
  | StC, S0 => mk S1 DR StD | StC, S1 => mk S1 DL StA
  | StD, S0 => mk S1 DR StB | StD, S1 => mk S0 DL StA
  end.

(** C(p): head on the blank left of the comb, state A; the whole
    comb-plus-working-area (110)^a W(p) sits in the right list. *)
Definition Cc (p : positive) : cconf :=
  (StA, ([], S0,
         S1 :: rep [S1; S0; S1] (Pos.to_nat p - 1) ++ S1 :: S0 :: Wp p)).

(** ** The unit runs *)

(** U1: prologue -- extend the comb start one cell left. *)
Lemma U1 : wsteps false true tm_26 1 (StA, ([], S0, [S1]))
           = Some (StB, ([S1], S1, [])).
Proof. reflexivity. Qed.

Lemma U2 : wsteps true true tm_26 5 (StB, ([], S1, [S1; S0; S1]))
           = Some (StB, ([S1; S1; S0], S1, [])).
Proof. reflexivity. Qed.

Lemma U3 : wsteps true true tm_26 6 (StB, ([], S1, [S1; S0; S0]))
           = Some (StC, ([S1; S0], S1, [S0])).
Proof. reflexivity. Qed.

Lemma U4 : wsteps true true tm_26 5 (StC, ([S1; S0; S1], S1, []))
           = Some (StC, ([], S1, [S1; S0; S1])).
Proof. reflexivity. Qed.

Lemma U5 : wsteps false true tm_26 7 (StC, ([S1; S0; S1], S1, []))
           = Some (StB, ([S1], S1, [S1; S0; S1])).
Proof. reflexivity. Qed.

Lemma U6 : wsteps true true tm_26 4 (StB, ([], S1, [S0; S1]))
           = Some (StB, ([S1; S1], S1, [])).
Proof. reflexivity. Qed.

Lemma U7 : wsteps true true tm_26 5 (StB, ([], S1, [S0; S0; S0]))
           = Some (StC, ([S1], S1, [S0; S0])).
Proof. reflexivity. Qed.

Lemma U8 : wsteps true true tm_26 2 (StC, ([S1; S1], S1, []))
           = Some (StC, ([], S1, [S1; S1])).
Proof. reflexivity. Qed.

Lemma U9 : wsteps true false tm_26 5 (StB, ([], S1, []))
           = Some (StC, ([S1], S1, [S0])).
Proof. reflexivity. Qed.

Lemma U10 : wsteps true true tm_26 2 (StB, ([], S1, [S1; S1]))
            = Some (StB, ([S0; S0], S1, [])).
Proof. reflexivity. Qed.

Lemma U11 : wsteps true true tm_26 7 (StB, ([S0], S1, [S0; S0]))
            = Some (StC, ([], S0, [S1; S1; S0])).
Proof. reflexivity. Qed.

Lemma U12 : wsteps true true tm_26 3 (StC, ([S0], S0, [S1]))
            = Some (StC, ([], S0, [S1; S0])).
Proof. reflexivity. Qed.

Lemma U13 : wsteps true true tm_26 3 (StC, ([S1], S0, [S1]))
            = Some (StC, ([], S1, [S1; S0])).
Proof. reflexivity. Qed.

Lemma U14 : wsteps true false tm_26 7 (StB, ([S0], S1, [S0]))
            = Some (StC, ([], S0, [S1; S1; S0])).
Proof. reflexivity. Qed.

(** U15: the event closer -- 6 steps back onto the blank left of the
    freshly extended comb, in the edge state A. *)
Lemma U15 : wsteps false true tm_26 6 (StC, ([S1; S0; S1], S1, []))
            = Some (StA, ([], S0, [S1; S1; S0; S1])).
Proof. reflexivity. Qed.

(** Visit witnesses: C after 4 steps, D after 5, from an anchor. *)
Lemma UV4 : wsteps false true tm_26 4 (StA, ([], S0, [S1; S1; S0]))
            = Some (StC, ([S0; S1], S0, [S0])).
Proof. reflexivity. Qed.

Lemma UV5 : wsteps false true tm_26 5 (StA, ([], S0, [S1; S1; S0]))
            = Some (StD, ([S1; S0; S1], S0, [])).
Proof. reflexivity. Qed.

(** ** Transported phases *)

Lemma phU1 : forall R,
  csteps tm_26 1 (StA, ([], S0, S1 :: R)) = Some (StB, ([S1], S1, R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U1). Qed.

Lemma phU2 : forall k L R,
  csteps tm_26 (5 * k) (StB, (L, S1, rep [S1; S0; S1] k ++ R))
  = Some (StB, (rep [S1; S1; S0] k ++ L, S1, R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U2 k L R). Qed.

Lemma phU3 : forall L R,
  csteps tm_26 6 (StB, (L, S1, S1 :: S0 :: S0 :: R))
  = Some (StC, (S1 :: S0 :: L, S1, S0 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U3). Qed.

Lemma phU4 : forall k L R,
  csteps tm_26 (5 * k) (StC, (rep [S1; S0; S1] k ++ L, S1, R))
  = Some (StC, (L, S1, rep [S1; S0; S1] k ++ R)).
Proof.
  intros.
  pose proof (cycL _ _ _ _ _ _ _ U4 k L R) as H; cbn [app] in H.
  exact H.
Qed.

Lemma phU5 : forall R,
  csteps tm_26 7 (StC, ([S1; S0; S1], S1, R))
  = Some (StB, ([S1], S1, S1 :: S0 :: S1 :: R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U5). Qed.

Lemma phU6 : forall k L R,
  csteps tm_26 (4 * k) (StB, (L, S1, rep [S0; S1] k ++ R))
  = Some (StB, (rep [S1; S1] k ++ L, S1, R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U6 k L R). Qed.

Lemma phU7 : forall L R,
  csteps tm_26 5 (StB, (L, S1, S0 :: S0 :: S0 :: R))
  = Some (StC, (S1 :: L, S1, S0 :: S0 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U7). Qed.

Lemma phU8 : forall k L R,
  csteps tm_26 (2 * k) (StC, (rep [S1; S1] k ++ L, S1, R))
  = Some (StC, (L, S1, rep [S1; S1] k ++ R)).
Proof.
  intros.
  pose proof (cycL _ _ _ _ _ _ _ U8 k L R) as H; cbn [app] in H.
  exact H.
Qed.

Lemma phU9 : forall L,
  csteps tm_26 5 (StB, (L, S1, []))
  = Some (StC, (S1 :: L, S1, [S0])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U9). Qed.

Lemma phU10 : forall k L R,
  csteps tm_26 (2 * k) (StB, (L, S1, rep [S1; S1] k ++ R))
  = Some (StB, (rep [S0; S0] k ++ L, S1, R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U10 k L R). Qed.

Lemma phU11 : forall L R,
  csteps tm_26 7 (StB, (S0 :: L, S1, S0 :: S0 :: R))
  = Some (StC, (L, S0, S1 :: S1 :: S0 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U11). Qed.

Lemma phU12 : forall k L R,
  csteps tm_26 (3 * k) (StC, (rep [S0] k ++ L, S0, S1 :: R))
  = Some (StC, (L, S0, S1 :: rep [S0] k ++ R)).
Proof. intros. exact (cycL _ _ _ _ _ _ _ U12 k L R). Qed.

Lemma phU13 : forall L R,
  csteps tm_26 3 (StC, (S1 :: L, S0, S1 :: R))
  = Some (StC, (L, S1, S1 :: S0 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U13). Qed.

Lemma phU14 : forall L,
  csteps tm_26 7 (StB, (S0 :: L, S1, [S0]))
  = Some (StC, (L, S0, [S1; S1; S0])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U14). Qed.

Lemma phU15 : forall R,
  csteps tm_26 6 (StC, ([S1; S0; S1], S1, R))
  = Some (StA, ([], S0, S1 :: S1 :: S0 :: S1 :: R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U15). Qed.

Lemma phUV4 : forall R,
  csteps tm_26 4 (StA, ([], S0, S1 :: S1 :: S0 :: R))
  = Some (StC, ([S0; S1], S0, S0 :: R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R UV4). Qed.

Lemma phUV5 : forall R,
  csteps tm_26 5 (StA, ([], S0, S1 :: S1 :: S0 :: R))
  = Some (StD, ([S1; S0; S1], S0, R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R UV5). Qed.

(** The overflow final area with #26's leading anchor cell. *)
Lemma final_r_ov26 : forall m j,
  S1 :: S1 :: S0 :: S1 :: (rep [S1; S0; S1] (S m) ++
    S1 :: S0 :: (rep [S0] (S (2 * j)) ++ [S1; S0]))
  = (S1 :: rep [S1; S0; S1] (S (S m)) ++
     S1 :: S0 :: (rep [S0; S0] j ++ [S0; S1])) ++ [S0].
Proof.
  intros. rewrite <- app_comm_cons.
  f_equal. apply final_r_ov.
Qed.

(** ** The lap *)

Lemma lap_26 : forall p, (2 <= p)%positive ->
  exists n c', csteps tm_26 n (Cc p) = Some c' /\
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
    do 2 eexists. split; [|split].
    + eapply csteps_chain. { apply phU1. }
      eapply csteps_chain. { apply phU2. }
      rewrite Hwp.
      eapply csteps_chain. { apply phU3. }
      rewrite rot_cross, <- Hwp.
      eapply csteps_chain. { apply phU4. }
      eapply csteps_chain. { apply phU5. }
      change (S1 :: S0 :: S1 :: (rep [S1; S0; S1] (S m) ++ Wp p))
        with (rep [S1; S0; S1] (S (S m)) ++ Wp p).
      eapply csteps_chain. { apply phU2. }
      rewrite HWp.
      eapply csteps_chain. { apply phU6. }
      rewrite Hwq.
      eapply csteps_chain. { apply phU7. }
      rewrite alignS2.
      eapply csteps_chain. { apply phU8. }
      eapply csteps_chain. { apply phU4. }
      eapply csteps_chain. { apply phU5. }
      change (S1 :: S0 :: S1 :: (rep [S1; S0; S1] (S m) ++
                rep [S1; S1] (S j) ++ S0 :: S0 :: wq))
        with (rep [S1; S0; S1] (S (S m)) ++
                rep [S1; S1] (S j) ++ S0 :: S0 :: wq).
      eapply csteps_chain. { apply phU2. }
      eapply csteps_chain. { apply phU10. }
      rewrite align00.
      eapply csteps_chain. { apply phU11. }
      eapply csteps_chain. { apply phU12. }
      rewrite alignL3.
      eapply csteps_chain. { apply phU13. }
      eapply csteps_chain. { apply phU4. }
      apply phU15.
    + rewrite HWs, Hwq, final_r_int.
      reflexivity.
    + lia.
  - (* overflow *)
    destruct (cview_none_W p j Ecv) as (HWp & HWs).
    do 2 eexists. split; [|split].
    + eapply csteps_chain. { apply phU1. }
      eapply csteps_chain. { apply phU2. }
      rewrite Hwp.
      eapply csteps_chain. { apply phU3. }
      rewrite rot_cross, <- Hwp.
      eapply csteps_chain. { apply phU4. }
      eapply csteps_chain. { apply phU5. }
      change (S1 :: S0 :: S1 :: (rep [S1; S0; S1] (S m) ++ Wp p))
        with (rep [S1; S0; S1] (S (S m)) ++ Wp p).
      eapply csteps_chain. { apply phU2. }
      rewrite HWp, <- (app_nil_r (rep [S0; S1] j)).
      eapply csteps_chain. { apply phU6. }
      eapply csteps_chain. { apply phU9. }
      rewrite alignS2.
      eapply csteps_chain. { apply phU8. }
      eapply csteps_chain. { apply phU4. }
      eapply csteps_chain. { apply phU5. }
      change (S1 :: S0 :: S1 :: (rep [S1; S0; S1] (S m) ++
                rep [S1; S1] (S j) ++ [S0]))
        with (rep [S1; S0; S1] (S (S m)) ++ rep [S1; S1] (S j) ++ [S0]).
      eapply csteps_chain. { apply phU2. }
      eapply csteps_chain. { apply phU10. }
      rewrite align00.
      eapply csteps_chain. { apply phU14. }
      change ([S1; S1; S0]) with (S1 :: [S1; S0]).
      eapply csteps_chain. { apply phU12. }
      rewrite alignL3.
      eapply csteps_chain. { apply phU13. }
      eapply csteps_chain. { apply phU4. }
      apply phU15.
    + rewrite HWs, final_r_ov26, lift_app_blank.
      reflexivity.
    + lia.
Qed.

(** ** Bootstrap, visits, and the theorem *)

Lemma boot_26 : exists t0, stepn tm_26 t0 InitES = Some (lift (Cc 2)).
Proof.
  exists 102.
  assert (H : match csteps tm_26 102 c0 with
              | Some c => ceqb c (Cc 2)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm_26 102 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
  f_equal. apply ceqb_lift. exact H.
Qed.

Lemma vis_26 : forall p q, (2 <= p)%positive ->
  exists k c, csteps tm_26 k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q Hp2.
  assert (Ha2 : 2 <= Pos.to_nat p).
  { change 2 with (Pos.to_nat 2). apply Pos2Nat.inj_le. exact Hp2. }
  unfold Cc.
  destruct (Pos.to_nat p) as [|[|m]] eqn:Ha; [lia | lia |].
  cbn [Nat.sub].
  destruct q.
  - exists 0. eexists. split; reflexivity.
  - exists 1. eexists. split; [apply phU1 | reflexivity].
  - exists 4. eexists. split.
    + change (S1 :: rep [S1; S0; S1] (S m) ++ S1 :: S0 :: Wp p)
        with (S1 :: S1 :: S0 :: (S1 :: rep [S1; S0; S1] m ++
                                 S1 :: S0 :: Wp p)).
      apply phUV4.
    + reflexivity.
  - exists 5. eexists. split.
    + change (S1 :: rep [S1; S0; S1] (S m) ++ S1 :: S0 :: Wp p)
        with (S1 :: S1 :: S0 :: (S1 :: rep [S1; S0; S1] m ++
                                 S1 :: S0 :: Wp p)).
      apply phUV5.
    + reflexivity.
Qed.

(** #26 never quasihalts: bbchallenge 1RB1LC_0LC0RB_1RD1LA_1RB0LA. *)
Theorem nqh_1RB1LC_0LC0RB_1RD1LA_1RB0LA : NeverQuasiHaltsSt tm_26.
Proof.
  apply (glue_neverqh tm_26 Cc 2).
  - exact boot_26.
  - exact lap_26.
  - intros p q Hp. apply vis_26; exact Hp.
Qed.

Theorem tm_26_nonhalt : NonHalt tm_26.
Proof. apply never_qh_nonhalt, nqh_1RB1LC_0LC0RB_1RD1LA_1RB0LA. Qed.
