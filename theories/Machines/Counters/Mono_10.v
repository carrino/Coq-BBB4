(** * Mono_10: the mono_counter machine #10, 1RB0LD_0LC0RB_1RA1LD_1RB1LC.

    First machine of the BBB harness's [mono_counter] family
    (certificate results/counter10.cert: comb 110, edge state C,
    hoff 0, bootstrap a0 = 2).  The left-edge anchor is

      C(a) = (110)^a W(a),  head on the comb start, state C,

    where W(a) writes a in binary at odd cells (bit i at offset
    2i+1 from the comb end).  One lap C(a) -> C(a+1) makes three
    sweeps over the comb (each comb unit crossing is a 5-step
    translated cycle), performs the binary increment on the second
    sweep (a 4-step carry cycle across the low set bits) and
    normalizes the working area on the third (2-step zap and 3-step
    walk-back cycles).  Since a grows forever and every lap visits
    every state near its start, the machine never quasihalts.

    The proof is the WTape phase decomposition validated
    differentially against the raw simulator for a = 2..2000
    upstream (tools/symlap10 in the session notes): fifteen unit
    runs U1-U15 (each closed by [reflexivity] on [wsteps]),
    transported into [csteps] context by [wsteps_frame*] and
    iterated by [cycR]/[cycL].  The counter is a [positive]; the
    carry structure of the increment is read off by [cview]
    (number of low set bits, and the rest), and the two lap shapes
    -- interior carry and overflow a = 2^j - 1 -- end in the next
    anchor exactly resp. up to one trailing blank. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB0LD_0LC0RB_1RA1LD_1RB1LC *)
Definition tm_10 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DL StD
  | StB, S0 => mk S0 DL StC | StB, S1 => mk S0 DR StB
  | StC, S0 => mk S1 DR StA | StC, S1 => mk S1 DL StD
  | StD, S0 => mk S1 DR StB | StD, S1 => mk S1 DL StC
  end.

(** ** The anchor family *)

(** Working area: [a] in binary at odd cells, LSB first ([xI] = low
    bit 1).  Every [Wp] starts with the even pad cell [S0]. *)
Fixpoint Wp (p : positive) : list Sym :=
  match p with
  | xH => [S0; S1]
  | xO q => S0 :: S0 :: Wp q
  | xI q => S0 :: S1 :: Wp q
  end.

(** C(p): comb of [to_nat p] units then W(p), head on the comb start.
    The tape right of the head is the rotated form
    (101)^(a-1) 10 W(p) of (110)^a W(p) minus its head cell. *)
Definition Cc (p : positive) : cconf :=
  (StC, ([], S1,
         rep [S1; S0; S1] (Pos.to_nat p - 1) ++ S1 :: S0 :: Wp p)).

(** Carry view: number of low set bits, and what is above them
    ([None] iff p = 2^j - 1, the overflow shape). *)
Fixpoint cview (p : positive) : nat * option positive :=
  match p with
  | xH => (1, None)
  | xO q => (0, Some q)
  | xI q => let '(j, r) := cview q in (S j, r)
  end.

Lemma Wp_head : forall p, exists w, Wp p = S0 :: w.
Proof. destruct p; simpl; eauto. Qed.

Lemma cview_some_W : forall p j q, cview p = (j, Some q) ->
  Wp p = rep [S0; S1] j ++ S0 :: S0 :: Wp q /\
  Wp (Pos.succ p) = rep [S0; S0] j ++ S0 :: S1 :: Wp q.
Proof.
  induction p; intros j q H; simpl in H.
  - destruct (cview p) as [j' r] eqn:E.
    inversion H; subst j r.
    destruct (IHp j' q eq_refl) as (H1 & H2).
    split; simpl.
    + rewrite H1. reflexivity.
    + rewrite H2. reflexivity.
  - inversion H; subst j q. split; reflexivity.
  - discriminate.
Qed.

Lemma cview_none_W : forall p j, cview p = (j, None) ->
  Wp p = rep [S0; S1] j /\
  Wp (Pos.succ p) = rep [S0; S0] j ++ [S0; S1].
Proof.
  induction p; intros j H; simpl in H.
  - destruct (cview p) as [j' r] eqn:E.
    inversion H; subst j r.
    destruct (IHp j' eq_refl) as (H1 & H2).
    split; simpl.
    + rewrite H1. reflexivity.
    + rewrite H2. reflexivity.
  - discriminate.
  - inversion H; subst j. split; reflexivity.
Qed.

(** ** The unit runs (windowed, each checked by [reflexivity]) *)

(** U1: prologue -- extend the comb start one cell left. *)
Lemma U1 : wsteps false true tm_10 2 (StC, ([], S1, []))
           = Some (StB, ([S1], S1, [])).
Proof. reflexivity. Qed.

(** U2: rightward comb crossing (110 -> 011, +3 cells / 5 steps). *)
Lemma U2 : wsteps true true tm_10 5 (StB, ([], S1, [S1; S0; S1]))
           = Some (StB, ([S1; S1; S0], S1, [])).
Proof. reflexivity. Qed.

(** U3: sweep-1 turnaround at the working area. *)
Lemma U3 : wsteps true true tm_10 6 (StB, ([], S1, [S1; S0; S0]))
           = Some (StC, ([S1; S0], S1, [S0])).
Proof. reflexivity. Qed.

(** U4: leftward comb crossing. *)
Lemma U4 : wsteps true true tm_10 5 (StC, ([S1; S0; S1], S1, []))
           = Some (StC, ([], S1, [S1; S0; S1])).
Proof. reflexivity. Qed.

(** U5: left-edge turnaround (runs at the tape edge; 7 steps). *)
Lemma U5 : wsteps false true tm_10 7 (StC, ([S1; S0; S1], S1, []))
           = Some (StB, ([S1], S1, [S1; S0; S1])).
Proof. reflexivity. Qed.

(** U6: increment approach / carry cycle (one low set bit each). *)
Lemma U6 : wsteps true true tm_10 4 (StB, ([], S1, [S0; S1]))
           = Some (StB, ([S1; S1], S1, [])).
Proof. reflexivity. Qed.

(** U7: carry stop at an interior 0 bit. *)
Lemma U7 : wsteps true true tm_10 5 (StB, ([], S1, [S0; S0; S0]))
           = Some (StC, ([S1], S1, [S0; S0])).
Proof. reflexivity. Qed.

(** U8: walk back over the freshly written 1-blocks. *)
Lemma U8 : wsteps true true tm_10 2 (StC, ([S1; S1], S1, []))
           = Some (StC, ([], S1, [S1; S1])).
Proof. reflexivity. Qed.

(** U9: carry stop past the working area (overflow; right edge). *)
Lemma U9 : wsteps true false tm_10 5 (StB, ([], S1, []))
           = Some (StC, ([S1], S1, [S0])).
Proof. reflexivity. Qed.

(** U10: sweep-3 zap of a dirty 11 pair. *)
Lemma U10 : wsteps true true tm_10 2 (StB, ([], S1, [S1; S1]))
            = Some (StB, ([S0; S0], S1, [])).
Proof. reflexivity. Qed.

(** U11: sweep-3 turnaround behind the zapped region. *)
Lemma U11 : wsteps true true tm_10 7 (StB, ([S0], S1, [S0; S0]))
            = Some (StC, ([], S0, [S1; S1; S0])).
Proof. reflexivity. Qed.

(** U12: walk-back cycle writing the new zero pairs. *)
Lemma U12 : wsteps true true tm_10 3 (StC, ([S0], S0, [S1]))
            = Some (StC, ([], S0, [S1; S0])).
Proof. reflexivity. Qed.

(** U13: last walk-back step, re-entering the comb. *)
Lemma U13 : wsteps true true tm_10 3 (StC, ([S1], S0, [S1]))
            = Some (StC, ([], S1, [S1; S0])).
Proof. reflexivity. Qed.

(** U14: sweep-3 turnaround in the overflow shape (right edge). *)
Lemma U14 : wsteps true false tm_10 7 (StB, ([S0], S1, [S0]))
            = Some (StC, ([], S0, [S1; S1; S0])).
Proof. reflexivity. Qed.

(** U15: the event prefix of the edge turnaround: the run is at the
    next anchor after 5 of U5's 7 steps. *)
Lemma U15 : wsteps false true tm_10 5 (StC, ([S1; S0; S1], S1, []))
            = Some (StC, ([], S1, [S1; S0; S1])).
Proof. reflexivity. Qed.

(** Visit witnesses: states D (1 step) and A (6 steps) from an anchor. *)
Lemma UV1 : wsteps false true tm_10 1 (StC, ([], S1, []))
            = Some (StD, ([], S0, [S1])).
Proof. reflexivity. Qed.

Lemma UV6 : wsteps false true tm_10 6 (StC, ([], S1, [S1; S0; S1]))
            = Some (StA, ([S1; S0; S1], S0, [S1])).
Proof. reflexivity. Qed.

(** ** Transported phases (cons-normal forms) *)

Lemma phU1 : forall R,
  csteps tm_10 2 (StC, ([], S1, R)) = Some (StB, ([S1], S1, R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U1). Qed.

Lemma phU2 : forall k L R,
  csteps tm_10 (5 * k) (StB, (L, S1, rep [S1; S0; S1] k ++ R))
  = Some (StB, (rep [S1; S1; S0] k ++ L, S1, R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U2 k L R). Qed.

Lemma phU3 : forall L R,
  csteps tm_10 6 (StB, (L, S1, S1 :: S0 :: S0 :: R))
  = Some (StC, (S1 :: S0 :: L, S1, S0 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U3). Qed.

Lemma phU4 : forall k L R,
  csteps tm_10 (5 * k) (StC, (rep [S1; S0; S1] k ++ L, S1, R))
  = Some (StC, (L, S1, rep [S1; S0; S1] k ++ R)).
Proof.
  intros.
  pose proof (cycL _ _ _ _ _ _ _ U4 k L R) as H; cbn [app] in H.
  exact H.
Qed.

Lemma phU5 : forall R,
  csteps tm_10 7 (StC, ([S1; S0; S1], S1, R))
  = Some (StB, ([S1], S1, S1 :: S0 :: S1 :: R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U5). Qed.

Lemma phU6 : forall k L R,
  csteps tm_10 (4 * k) (StB, (L, S1, rep [S0; S1] k ++ R))
  = Some (StB, (rep [S1; S1] k ++ L, S1, R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U6 k L R). Qed.

Lemma phU7 : forall L R,
  csteps tm_10 5 (StB, (L, S1, S0 :: S0 :: S0 :: R))
  = Some (StC, (S1 :: L, S1, S0 :: S0 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U7). Qed.

Lemma phU8 : forall k L R,
  csteps tm_10 (2 * k) (StC, (rep [S1; S1] k ++ L, S1, R))
  = Some (StC, (L, S1, rep [S1; S1] k ++ R)).
Proof.
  intros.
  pose proof (cycL _ _ _ _ _ _ _ U8 k L R) as H; cbn [app] in H.
  exact H.
Qed.

Lemma phU9 : forall L,
  csteps tm_10 5 (StB, (L, S1, []))
  = Some (StC, (S1 :: L, S1, [S0])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U9). Qed.

Lemma phU10 : forall k L R,
  csteps tm_10 (2 * k) (StB, (L, S1, rep [S1; S1] k ++ R))
  = Some (StB, (rep [S0; S0] k ++ L, S1, R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U10 k L R). Qed.

Lemma phU11 : forall L R,
  csteps tm_10 7 (StB, (S0 :: L, S1, S0 :: S0 :: R))
  = Some (StC, (L, S0, S1 :: S1 :: S0 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U11). Qed.

Lemma phU12 : forall k L R,
  csteps tm_10 (3 * k) (StC, (rep [S0] k ++ L, S0, S1 :: R))
  = Some (StC, (L, S0, S1 :: rep [S0] k ++ R)).
Proof. intros. exact (cycL _ _ _ _ _ _ _ U12 k L R). Qed.

Lemma phU13 : forall L R,
  csteps tm_10 3 (StC, (S1 :: L, S0, S1 :: R))
  = Some (StC, (L, S1, S1 :: S0 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U13). Qed.

Lemma phU14 : forall L,
  csteps tm_10 7 (StB, (S0 :: L, S1, [S0]))
  = Some (StC, (L, S0, [S1; S1; S0])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U14). Qed.

Lemma phU15 : forall R,
  csteps tm_10 5 (StC, ([S1; S0; S1], S1, R))
  = Some (StC, ([], S1, S1 :: S0 :: S1 :: R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U15). Qed.

Lemma phUV1 : forall R,
  csteps tm_10 1 (StC, ([], S1, R)) = Some (StD, ([], S0, S1 :: R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R UV1). Qed.

Lemma phUV6 : forall R,
  csteps tm_10 6 (StC, ([], S1, S1 :: S0 :: S1 :: R))
  = Some (StA, ([S1; S0; S1], S0, S1 :: R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R UV6). Qed.

(** ** Alignment rewrites *)

(** A crossed comb boundary rotates: 10 (110)^k X = (101)^k 10 X. *)
Lemma rot_cross : forall k X,
  S1 :: S0 :: rep [S1; S1; S0] k ++ X
  = rep [S1; S0; S1] k ++ S1 :: S0 :: X.
Proof.
  induction k; intros; cbn [rep app].
  - reflexivity.
  - now rewrite IHk.
Qed.

(** After the carry stop, the pushed 1 fuses with the carry blocks
    and the comb top into walk-back blocks over the rotated comb. *)
Lemma alignS2 : forall j k,
  S1 :: rep [S1; S1] j ++ rep [S1; S1; S0] (S k) ++ [S1]
  = rep [S1; S1] (S j) ++ rep [S1; S0; S1] k ++ [S1; S0; S1].
Proof.
  intros.
  rewrite !rep_dbl.
  replace (2 * S j) with (S (S (2 * j))) by lia.
  cbn [rep app].
  rewrite !rep_slide.
  rewrite rot_cross.
  reflexivity.
Qed.

(** The zapped pairs expose a single leading zero cell. *)
Lemma align00 : forall j X,
  rep [S0; S0] (S j) ++ X = S0 :: rep [S0] (S (2 * j)) ++ X.
Proof.
  intros; cbn [rep app].
  now rewrite rep_dbl.
Qed.

(** The comb top after sweep 3 re-rotates for the final descent. *)
Lemma alignL3 : forall k,
  rep [S1; S1; S0] (S k) ++ [S1]
  = S1 :: rep [S1; S0; S1] k ++ [S1; S0; S1].
Proof.
  intros; cbn [rep app].
  now rewrite rot_cross.
Qed.

(** Final working areas. *)
Lemma final_r_int : forall m j wq,
  S1 :: S0 :: S1 :: (rep [S1; S0; S1] (S m) ++
    S1 :: S0 :: (rep [S0] (S (2 * j)) ++ S1 :: S0 :: wq))
  = rep [S1; S0; S1] (S (S m)) ++
    S1 :: S0 :: (rep [S0; S0] j ++ S0 :: S1 :: S0 :: wq).
Proof.
  intros; cbn [rep app].
  rewrite rep_dbl, rep_slide.
  reflexivity.
Qed.

Lemma final_r_ov : forall m j,
  S1 :: S0 :: S1 :: (rep [S1; S0; S1] (S m) ++
    S1 :: S0 :: (rep [S0] (S (2 * j)) ++ [S1; S0]))
  = (rep [S1; S0; S1] (S (S m)) ++
     S1 :: S0 :: (rep [S0; S0] j ++ [S0; S1])) ++ [S0].
Proof.
  intros; cbn [rep app].
  rewrite rep_dbl, <- !app_assoc.
  cbn [app].
  rewrite rep_slide, <- !app_assoc.
  cbn [app].
  reflexivity.
Qed.

(** ** The lap *)

Lemma lap_10 : forall p, (2 <= p)%positive ->
  exists n c', csteps tm_10 n (Cc p) = Some c' /\
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
  - (* interior carry: p = 1^j 0 q0 *)
    destruct (cview_some_W p j q0 Ecv) as (HWp & HWs).
    destruct (Wp_head q0) as (wq & Hwq).
    do 2 eexists. split; [|split].
    + (* sweep 1 *)
      eapply csteps_chain. { apply phU1. }
      eapply csteps_chain. { apply phU2. }
      rewrite Hwp.
      eapply csteps_chain. { apply phU3. }
      rewrite rot_cross, <- Hwp.
      eapply csteps_chain. { apply phU4. }
      eapply csteps_chain. { apply phU5. }
      change (S1 :: S0 :: S1 :: (rep [S1; S0; S1] (S m) ++ Wp p))
        with (rep [S1; S0; S1] (S (S m)) ++ Wp p).
      (* sweep 2: comb, then the increment *)
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
      (* sweep 3: comb, zap, walk back *)
      eapply csteps_chain. { apply phU2. }
      eapply csteps_chain. { apply phU10. }
      rewrite align00.
      eapply csteps_chain. { apply phU11. }
      eapply csteps_chain. { apply phU12. }
      rewrite alignL3.
      eapply csteps_chain. { apply phU13. }
      eapply csteps_chain. { apply phU4. }
      apply phU15.
    + (* the reached configuration is the next anchor *)
      rewrite HWs, Hwq, final_r_int.
      reflexivity.
    + lia.
  - (* overflow: p = 2^j - 1 *)
    destruct (cview_none_W p j Ecv) as (HWp & HWs).
    do 2 eexists. split; [|split].
    + (* sweep 1 *)
      eapply csteps_chain. { apply phU1. }
      eapply csteps_chain. { apply phU2. }
      rewrite Hwp.
      eapply csteps_chain. { apply phU3. }
      rewrite rot_cross, <- Hwp.
      eapply csteps_chain. { apply phU4. }
      eapply csteps_chain. { apply phU5. }
      change (S1 :: S0 :: S1 :: (rep [S1; S0; S1] (S m) ++ Wp p))
        with (rep [S1; S0; S1] (S (S m)) ++ Wp p).
      (* sweep 2: comb, carry off the right end *)
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
      (* sweep 3 *)
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
    + (* next anchor up to the trailing blank *)
      rewrite HWs, final_r_ov, lift_app_blank.
      reflexivity.
    + lia.
Qed.

(** ** Bootstrap, visits, and the theorem *)

Lemma boot_10 : exists t0, stepn tm_10 t0 InitES = Some (lift (Cc 2)).
Proof.
  exists 101.
  assert (H : match csteps tm_10 101 c0 with
              | Some c => ceqb c (Cc 2)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm_10 101 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
  f_equal. apply ceqb_lift. exact H.
Qed.

Lemma vis_10 : forall p q, (2 <= p)%positive ->
  exists k c, csteps tm_10 k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q Hp2.
  assert (Ha2 : 2 <= Pos.to_nat p).
  { change 2 with (Pos.to_nat 2). apply Pos2Nat.inj_le. exact Hp2. }
  unfold Cc.
  destruct (Pos.to_nat p) as [|[|m]] eqn:Ha; [lia | lia |].
  cbn [Nat.sub].
  destruct q.
  - exists 6. eexists. split.
    + change (rep [S1; S0; S1] (S m) ++ S1 :: S0 :: Wp p)
        with (S1 :: S0 :: S1 :: (rep [S1; S0; S1] m ++ S1 :: S0 :: Wp p)).
      apply phUV6.
    + reflexivity.
  - exists 2. eexists. split; [apply phU1 | reflexivity].
  - exists 0. eexists. split; reflexivity.
  - exists 1. eexists. split; [apply phUV1 | reflexivity].
Qed.

(** #10 never quasihalts: bbchallenge 1RB0LD_0LC0RB_1RA1LD_1RB1LC. *)
Theorem nqh_1RB0LD_0LC0RB_1RA1LD_1RB1LC : NeverQuasiHaltsSt tm_10.
Proof.
  apply (glue_neverqh tm_10 Cc 2).
  - exact boot_10.
  - exact lap_10.
  - intros p q Hp. apply vis_10; exact Hp.
Qed.

Theorem tm_10_nonhalt : NonHalt tm_10.
Proof. apply never_qh_nonhalt, nqh_1RB0LD_0LC0RB_1RA1LD_1RB1LC. Qed.
