(** * Interleave_18: the interleave_counter machine #18,
      1RB0RD_1LB0LC_1LD1LB_1RA1RD.

    First machine of the BBB harness's [interleave_counter] family
    (certificate results/counter18.cert: edge state A, amin 4).  The
    right-frontier anchor is

      D(n) = E(n) (110)^(2n) 1,  head one cell right of the frontier
      (a blank), state A,

    with the counter n interleaved into E(n) left of the comb (see
    ILCounter).  One lap D(n) -> D(n+1) makes two sweeps through the
    mid shape M(n) = E(n+1) 010 (110)^(2n) 1: sweep 1 crosses the
    comb leftward (3-step translated cycle), increments the
    interleaved counter (2-step carry cycle across the low set-bit
    pairs, interior stop at the first clear bit / overflow off the
    left tape edge) and recrosses (2-step pair cycle, 3-step comb
    cycle); sweep 2 rewrites the 010 junction locally and grows the
    comb by the second unit.  Both lap shapes end exactly at D(n+1)
    -- no trailing-blank slack.  Decomposition validated
    differentially against the raw simulator for n = 4..300
    (tools/counters/lap18.py). *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter ILCounter.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB0RD_1LB0LC_1LD1LB_1RA1RD *)
Definition tm_18 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DR StD
  | StB, S0 => mk S1 DL StB | StB, S1 => mk S0 DL StC
  | StC, S0 => mk S1 DL StD | StC, S1 => mk S1 DL StB
  | StD, S0 => mk S1 DR StA | StD, S1 => mk S1 DR StD
  end.

(** D(p): frontier 1, comb of [2 to_nat p] units (reversed on the
    left list), then the interleaved counter. *)
Definition Cc (p : positive) : cconf :=
  (StA, (S1 :: rep [S0; S1; S1] (2 * Pos.to_nat p) ++ Ip p, S0, [])).

(** ** The unit runs (windowed, each checked by [reflexivity]) *)

(** U1: prologue -- extend the frontier, turn into the comb. *)
Lemma U1 : wsteps true false tm_18 3 (StA, ([S1], S0, []))
           = Some (StC, ([], S1, [S0; S1])).
Proof. reflexivity. Qed.

(** U2: leftward comb crossing (110 -> 011 shifted, 3 steps/unit). *)
Lemma U2 : wsteps true true tm_18 3 (StC, ([S0; S1; S1], S1, []))
           = Some (StC, ([], S1, [S0; S1; S1])).
Proof. reflexivity. Qed.

(** U3: the carry cycle across a set-bit pair (2 steps/pair). *)
Lemma U3 : wsteps true true tm_18 2 (StC, ([S1; S1], S1, []))
           = Some (StC, ([], S1, [S0; S1])).
Proof. reflexivity. Qed.

(** U4i: interior carry stop -- flip the clear-bit pair. *)
Lemma U4i : wsteps true true tm_18 6 (StC, ([S1; S0; S1], S1, []))
            = Some (StA, ([S1; S1; S1], S1, [])).
Proof. reflexivity. Qed.

(** U4o: overflow stop -- a fresh MSB pair beyond the tape edge. *)
Lemma U4o : wsteps false true tm_18 6 (StC, ([S1], S1, []))
            = Some (StA, ([S1; S0; S1], S1, [])).
Proof. reflexivity. Qed.

(** U5: rightward recross of the flipped pairs (2 steps/pair). *)
Lemma U5 : wsteps true true tm_18 2 (StA, ([], S1, [S0; S1]))
           = Some (StA, ([S1; S0], S1, [])).
Proof. reflexivity. Qed.

(** UJ2: the pair/comb junction. *)
Lemma UJ2 : wsteps true true tm_18 1 (StA, ([], S1, [S1]))
            = Some (StD, ([S0], S1, [])).
Proof. reflexivity. Qed.

(** U10: rightward comb recross (3 steps/unit). *)
Lemma U10 : wsteps true true tm_18 3 (StD, ([], S1, [S0; S1; S1]))
            = Some (StD, ([S0; S1; S1], S1, [])).
Proof. reflexivity. Qed.

(** U11: frontier extension closing a sweep (right tape edge). *)
Lemma U11 : wsteps true false tm_18 4 (StD, ([], S1, [S0; S1]))
            = Some (StA, ([S1; S0; S1; S1], S0, [])).
Proof. reflexivity. Qed.

(** U9: sweep-2 turnaround rewriting the 010 junction. *)
Lemma U9 : wsteps true true tm_18 8 (StC, ([S0; S1; S0; S1], S1, []))
           = Some (StD, ([S0; S1; S1; S1], S1, [])).
Proof. reflexivity. Qed.

(** Visit witnesses: B after 1 step, and D via 3-step stop prefixes. *)
Lemma UV1 : wsteps true false tm_18 1 (StA, ([S1], S0, []))
            = Some (StB, ([S1; S1], S0, [])).
Proof. reflexivity. Qed.

Lemma UVDi : wsteps true true tm_18 3 (StC, ([S1; S0; S1], S1, []))
             = Some (StD, ([], S1, [S1; S0; S1])).
Proof. reflexivity. Qed.

Lemma UVDo : wsteps false true tm_18 3 (StC, ([S1], S1, []))
             = Some (StD, ([], S0, [S1; S0; S1])).
Proof. reflexivity. Qed.

(** ** Transported phases (cons-normal forms) *)

Lemma phU1 : forall L,
  csteps tm_18 3 (StA, (S1 :: L, S0, []))
  = Some (StC, (L, S1, [S0; S1])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U1). Qed.

Lemma phU2 : forall k L R,
  csteps tm_18 (3 * k) (StC, (rep [S0; S1; S1] k ++ L, S1, R))
  = Some (StC, (L, S1, rep [S0; S1; S1] k ++ R)).
Proof.
  intros.
  pose proof (cycL _ _ _ _ _ _ _ U2 k L R) as H; cbn [app] in H.
  exact H.
Qed.

Lemma phU3 : forall k L R,
  csteps tm_18 (2 * k) (StC, (rep [S1; S1] k ++ L, S1, R))
  = Some (StC, (L, S1, rep [S0; S1] k ++ R)).
Proof.
  intros.
  pose proof (cycL _ _ _ _ _ _ _ U3 k L R) as H; cbn [app] in H.
  exact H.
Qed.

Lemma phU4i : forall L R,
  csteps tm_18 6 (StC, (S1 :: S0 :: S1 :: L, S1, R))
  = Some (StA, (S1 :: S1 :: S1 :: L, S1, R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U4i). Qed.

Lemma phU4o : forall R,
  csteps tm_18 6 (StC, ([S1], S1, R))
  = Some (StA, ([S1; S0; S1], S1, R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U4o). Qed.

Lemma phU5 : forall k L R,
  csteps tm_18 (2 * k) (StA, (L, S1, rep [S0; S1] k ++ R))
  = Some (StA, (rep [S1; S0] k ++ L, S1, R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U5 k L R). Qed.

Lemma phUJ2 : forall L R,
  csteps tm_18 1 (StA, (L, S1, S1 :: R))
  = Some (StD, (S0 :: L, S1, R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R UJ2). Qed.

Lemma phU10 : forall k L R,
  csteps tm_18 (3 * k) (StD, (L, S1, rep [S0; S1; S1] k ++ R))
  = Some (StD, (rep [S0; S1; S1] k ++ L, S1, R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U10 k L R). Qed.

Lemma phU11 : forall L,
  csteps tm_18 4 (StD, (L, S1, [S0; S1]))
  = Some (StA, (S1 :: S0 :: S1 :: S1 :: L, S0, [])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U11). Qed.

Lemma phU9 : forall L R,
  csteps tm_18 8 (StC, (S0 :: S1 :: S0 :: S1 :: L, S1, R))
  = Some (StD, (S0 :: S1 :: S1 :: S1 :: L, S1, R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U9). Qed.

Lemma phUV1 : forall L,
  csteps tm_18 1 (StA, (S1 :: L, S0, []))
  = Some (StB, (S1 :: S1 :: L, S0, [])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L UV1). Qed.

Lemma phUVDi : forall L R,
  csteps tm_18 3 (StC, (S1 :: S0 :: S1 :: L, S1, R))
  = Some (StD, (L, S1, S1 :: S0 :: S1 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R UVDi). Qed.

Lemma phUVDo : forall R,
  csteps tm_18 3 (StC, ([S1], S1, R))
  = Some (StD, ([], S0, S1 :: S0 :: S1 :: R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R UVDo). Qed.

(** ** The lap *)

Lemma lap_18 : forall p,
  exists n c', csteps tm_18 n (Cc p) = Some c' /\
               lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p.
  pose proof (Pos2Nat.is_pos p) as Hpos.
  destruct (cview p) as [j oq] eqn:Ecv.
  unfold Cc.
  rewrite Pos2Nat.inj_succ.
  destruct (Pos.to_nat p) as [|m] eqn:Ha; [lia|].
  replace (2 * S m) with (S (S (2 * m))) by lia.
  replace (2 * S (S m)) with (S (S (S (S (2 * m))))) by lia.
  destruct (Ip_head (Pos.succ p)) as (w & Hw).
  destruct oq as [q0|].
  - (* interior carry: the low set-bit pairs flip, the stop pair sets *)
    destruct (cview_some_I p j q0 Ecv) as (HIp & HIs).
    destruct (Ip_head q0) as (iq & Hiq).
    do 2 eexists. split; [|split].
    + (* sweep 1: comb, carry, recross *)
      eapply csteps_chain. { apply phU1. }
      eapply csteps_chain. { apply phU2. }
      rewrite HIp.
      eapply csteps_chain. { apply phU3. }
      rewrite Hiq.
      eapply csteps_chain. { apply phU4i. }
      change (rep [S0; S1] j ++ rep [S0; S1; S1] (S (S (2 * m))) ++ [S0; S1])
        with (rep [S0; S1] j ++ S0 :: S1 ::
                (S1 :: rep [S0; S1; S1] (S (2 * m)) ++ [S0; S1])).
      rewrite (pair_fold S0 S1 j).
      eapply csteps_chain. { apply phU5. }
      eapply csteps_chain. { apply phUJ2. }
      eapply csteps_chain. { apply phU10. }
      eapply csteps_chain. { apply phU11. }
      (* mid anchor reached: refold E(n+1) and run sweep 2 *)
      change (S1 :: S0 :: S1 :: S1 :: rep [S0; S1; S1] (S (2 * m)) ++
                S0 :: rep [S1; S0] (S j) ++ S1 :: S1 :: S1 :: iq)
        with (S1 :: rep [S0; S1; S1] (S (S (2 * m))) ++
                S0 :: S1 :: S0 :: rep [S1; S0] j ++ S1 :: S1 :: S1 :: iq).
      rewrite <- Hiq, <- HIs, Hw.
      eapply csteps_chain. { apply phU1. }
      eapply csteps_chain. { apply phU2. }
      eapply csteps_chain. { apply phU9. }
      eapply csteps_chain. { apply phU10. }
      apply phU11.
    + (* the reached configuration is the next anchor *)
      rewrite Hw.
      change (S1 :: S0 :: S1 :: S1 :: rep [S0; S1; S1] (S (S (2 * m))) ++
                S0 :: S1 :: S1 :: S1 :: w)
        with (S1 :: rep [S0; S1; S1] (S (S (S (2 * m)))) ++
                [S0; S1; S1] ++ S1 :: w).
      rewrite app_assoc, rep_shift, <- app_assoc.
      reflexivity.
    + lia.
  - (* overflow: p = 2^j - 1, fresh MSB pair off the tape edge *)
    destruct j as [|j'].
    { exfalso.
      destruct p; simpl in Ecv;
        [destruct (cview p); discriminate | discriminate | discriminate]. }
    destruct (cview_none_I p j' Ecv) as (HIp & HIs).
    do 2 eexists. split; [|split].
    + (* sweep 1 *)
      eapply csteps_chain. { apply phU1. }
      eapply csteps_chain. { apply phU2. }
      rewrite HIp.
      eapply csteps_chain. { apply phU3. }
      eapply csteps_chain. { apply phU4o. }
      change (rep [S0; S1] j' ++ rep [S0; S1; S1] (S (S (2 * m))) ++ [S0; S1])
        with (rep [S0; S1] j' ++ S0 :: S1 ::
                (S1 :: rep [S0; S1; S1] (S (2 * m)) ++ [S0; S1])).
      rewrite (pair_fold S0 S1 j').
      eapply csteps_chain. { apply phU5. }
      eapply csteps_chain. { apply phUJ2. }
      eapply csteps_chain. { apply phU10. }
      eapply csteps_chain. { apply phU11. }
      (* mid anchor reached: fold the fresh MSB pair into E(n+1) *)
      change (S1 :: S0 :: S1 :: S1 :: rep [S0; S1; S1] (S (2 * m)) ++
                S0 :: rep [S1; S0] (S j') ++ [S1; S0; S1])
        with (S1 :: rep [S0; S1; S1] (S (S (2 * m))) ++
                S0 :: S1 :: S0 :: (rep [S1; S0] j' ++ S1 :: S0 :: [S1])).
      rewrite (pair_fold S1 S0 j').
      rewrite <- HIs, Hw.
      eapply csteps_chain. { apply phU1. }
      eapply csteps_chain. { apply phU2. }
      eapply csteps_chain. { apply phU9. }
      eapply csteps_chain. { apply phU10. }
      apply phU11.
    + (* next anchor *)
      rewrite Hw.
      change (S1 :: S0 :: S1 :: S1 :: rep [S0; S1; S1] (S (S (2 * m))) ++
                S0 :: S1 :: S1 :: S1 :: w)
        with (S1 :: rep [S0; S1; S1] (S (S (S (2 * m)))) ++
                [S0; S1; S1] ++ S1 :: w).
      rewrite app_assoc, rep_shift, <- app_assoc.
      reflexivity.
    + lia.
Qed.

(** ** Bootstrap, visits, and the theorem *)

Lemma boot_18 : exists t0, stepn tm_18 t0 InitES = Some (lift (Cc 4)).
Proof.
  exists 256.
  assert (H : match csteps tm_18 256 c0 with
              | Some c => ceqb c (Cc 4)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm_18 256 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
  f_equal. apply ceqb_lift. exact H.
Qed.

Lemma vis_18 : forall p q,
  exists k c, csteps tm_18 k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q.
  pose proof (Pos2Nat.is_pos p) as Hpos.
  unfold Cc.
  destruct q.
  - exists 0. eexists. split; reflexivity.
  - exists 1. eexists. split; [apply phUV1 | reflexivity].
  - exists 3. eexists. split; [apply phU1 | reflexivity].
  - (* StD: chain to the carry stop, whose 3-step prefix visits D *)
    destruct (cview p) as [j oq] eqn:Ecv.
    destruct oq as [q0|].
    + destruct (cview_some_I p j q0 Ecv) as (HIp & _).
      destruct (Ip_head q0) as (iq & Hiq).
      eexists (3 + (3 * (2 * Pos.to_nat p) + (2 * j + 3))). eexists. split.
      * eapply csteps_chain. { apply phU1. }
        eapply csteps_chain. { apply phU2. }
        rewrite HIp.
        eapply csteps_chain. { apply phU3. }
        rewrite Hiq.
        apply phUVDi.
      * reflexivity.
    + destruct j as [|j'].
      { exfalso.
        destruct p; simpl in Ecv;
          [destruct (cview p); discriminate | discriminate | discriminate]. }
      destruct (cview_none_I p j' Ecv) as (HIp & _).
      eexists (3 + (3 * (2 * Pos.to_nat p) + (2 * j' + 3))). eexists. split.
      * eapply csteps_chain. { apply phU1. }
        eapply csteps_chain. { apply phU2. }
        rewrite HIp.
        eapply csteps_chain. { apply phU3. }
        apply phUVDo.
      * reflexivity.
Qed.

(** #18 never quasihalts: bbchallenge 1RB0RD_1LB0LC_1LD1LB_1RA1RD. *)
Theorem nqh_1RB0RD_1LB0LC_1LD1LB_1RA1RD : NeverQuasiHaltsSt tm_18.
Proof.
  apply (glue_neverqh tm_18 Cc 4).
  - exact boot_18.
  - intros p _. apply lap_18.
  - intros p q _. apply vis_18.
Qed.

Theorem tm_18_nonhalt : NonHalt tm_18.
Proof. apply never_qh_nonhalt, nqh_1RB0RD_1LB0LC_1LD1LB_1RA1RD. Qed.
