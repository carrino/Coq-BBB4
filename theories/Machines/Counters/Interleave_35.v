(** * Interleave_35: the interleave_counter machine #35,
      1RB1RA_0RC0RA_1LC0LD_1LA1LC.

    Second machine of the BBB harness's [interleave_counter] family
    (certificate results/counter35.cert: edge state A, amin 4).  Same
    anchor family and lap geometry as #18 (Interleave_18):

      D(n) = E(n) (110)^(2n) 1,  head one cell right of the frontier
      (a blank), state A,

    two sweeps through M(n) = E(n+1) 010 (110)^(2n) 1.  Only the unit
    tables differ: the prologue is 5 steps and deposits a 3-cell
    frontier window, the leftward crossing runs in a D-frame and the
    recross pairs in a B-frame.  Decomposition validated
    differentially against the raw simulator for n = 4..300
    (tools/counters/lap35.py). *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter ILCounter.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB1RA_0RC0RA_1LC0LD_1LA1LC *)
Definition tm_35 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DR StA
  | StB, S0 => mk S0 DR StC | StB, S1 => mk S0 DR StA
  | StC, S0 => mk S1 DL StC | StC, S1 => mk S0 DL StD
  | StD, S0 => mk S1 DL StA | StD, S1 => mk S1 DL StC
  end.

Definition Cc (p : positive) : cconf :=
  (StA, (S1 :: rep [S0; S1; S1] (2 * Pos.to_nat p) ++ Ip p, S0, [])).

(** ** The unit runs *)

(** U1: prologue -- extend the frontier, turn into the comb. *)
Lemma U1 : wsteps true false tm_35 5 (StA, ([S1], S0, []))
           = Some (StD, ([], S1, [S0; S1; S1])).
Proof. reflexivity. Qed.

(** U2: leftward comb crossing (3 steps/unit, D-frame). *)
Lemma U2 : wsteps true true tm_35 3 (StD, ([S0; S1; S1], S1, []))
           = Some (StD, ([], S1, [S0; S1; S1])).
Proof. reflexivity. Qed.

(** U3: the carry cycle across a set-bit pair (2 steps/pair). *)
Lemma U3 : wsteps true true tm_35 2 (StD, ([S1; S1], S1, []))
           = Some (StD, ([], S1, [S0; S1])).
Proof. reflexivity. Qed.

(** U4i: interior carry stop -- flip the clear-bit pair. *)
Lemma U4i : wsteps true true tm_35 6 (StD, ([S1; S0; S1], S1, []))
            = Some (StB, ([S1; S1; S1], S1, [])).
Proof. reflexivity. Qed.

(** U4o: overflow stop -- a fresh MSB pair beyond the tape edge. *)
Lemma U4o : wsteps false true tm_35 6 (StD, ([S1], S1, []))
            = Some (StB, ([S1; S0; S1], S1, [])).
Proof. reflexivity. Qed.

(** U5: rightward recross of the flipped pairs (2 steps/pair). *)
Lemma U5 : wsteps true true tm_35 2 (StB, ([], S1, [S0; S1]))
           = Some (StB, ([S1; S0], S1, [])).
Proof. reflexivity. Qed.

(** UJ2: the pair/comb junction. *)
Lemma UJ2 : wsteps true true tm_35 1 (StB, ([], S1, [S1]))
            = Some (StA, ([S0], S1, [])).
Proof. reflexivity. Qed.

(** U10: rightward comb recross (3 steps/unit, A-frame). *)
Lemma U10 : wsteps true true tm_35 3 (StA, ([], S1, [S0; S1; S1]))
            = Some (StA, ([S0; S1; S1], S1, [])).
Proof. reflexivity. Qed.

(** U11: frontier extension closing a sweep (right tape edge). *)
Lemma U11 : wsteps true false tm_35 4 (StA, ([], S1, [S0; S1; S1]))
            = Some (StA, ([S1; S0; S1; S1], S0, [])).
Proof. reflexivity. Qed.

(** U9: sweep-2 turnaround rewriting the 010 junction. *)
Lemma U9 : wsteps true true tm_35 8 (StD, ([S0; S1; S0; S1], S1, []))
           = Some (StA, ([S0; S1; S1; S1], S1, [])).
Proof. reflexivity. Qed.

(** Visit witnesses: B after 1 step, C after 2 (D is U1's exit). *)
Lemma UV1 : wsteps true false tm_35 1 (StA, ([S1], S0, []))
            = Some (StB, ([S1; S1], S0, [])).
Proof. reflexivity. Qed.

Lemma UV2 : wsteps true false tm_35 2 (StA, ([S1], S0, []))
            = Some (StC, ([S0; S1; S1], S0, [])).
Proof. reflexivity. Qed.

(** ** Transported phases *)

Lemma phU1 : forall L,
  csteps tm_35 5 (StA, (S1 :: L, S0, []))
  = Some (StD, (L, S1, [S0; S1; S1])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U1). Qed.

Lemma phU2 : forall k L R,
  csteps tm_35 (3 * k) (StD, (rep [S0; S1; S1] k ++ L, S1, R))
  = Some (StD, (L, S1, rep [S0; S1; S1] k ++ R)).
Proof.
  intros.
  pose proof (cycL _ _ _ _ _ _ _ U2 k L R) as H; cbn [app] in H.
  exact H.
Qed.

Lemma phU3 : forall k L R,
  csteps tm_35 (2 * k) (StD, (rep [S1; S1] k ++ L, S1, R))
  = Some (StD, (L, S1, rep [S0; S1] k ++ R)).
Proof.
  intros.
  pose proof (cycL _ _ _ _ _ _ _ U3 k L R) as H; cbn [app] in H.
  exact H.
Qed.

Lemma phU4i : forall L R,
  csteps tm_35 6 (StD, (S1 :: S0 :: S1 :: L, S1, R))
  = Some (StB, (S1 :: S1 :: S1 :: L, S1, R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U4i). Qed.

Lemma phU4o : forall R,
  csteps tm_35 6 (StD, ([S1], S1, R))
  = Some (StB, ([S1; S0; S1], S1, R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U4o). Qed.

Lemma phU5 : forall k L R,
  csteps tm_35 (2 * k) (StB, (L, S1, rep [S0; S1] k ++ R))
  = Some (StB, (rep [S1; S0] k ++ L, S1, R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U5 k L R). Qed.

Lemma phUJ2 : forall L R,
  csteps tm_35 1 (StB, (L, S1, S1 :: R))
  = Some (StA, (S0 :: L, S1, R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R UJ2). Qed.

Lemma phU10 : forall k L R,
  csteps tm_35 (3 * k) (StA, (L, S1, rep [S0; S1; S1] k ++ R))
  = Some (StA, (rep [S0; S1; S1] k ++ L, S1, R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U10 k L R). Qed.

Lemma phU11 : forall L,
  csteps tm_35 4 (StA, (L, S1, [S0; S1; S1]))
  = Some (StA, (S1 :: S0 :: S1 :: S1 :: L, S0, [])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U11). Qed.

Lemma phU9 : forall L R,
  csteps tm_35 8 (StD, (S0 :: S1 :: S0 :: S1 :: L, S1, R))
  = Some (StA, (S0 :: S1 :: S1 :: S1 :: L, S1, R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U9). Qed.

Lemma phUV1 : forall L,
  csteps tm_35 1 (StA, (S1 :: L, S0, []))
  = Some (StB, (S1 :: S1 :: L, S0, [])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L UV1). Qed.

Lemma phUV2 : forall L,
  csteps tm_35 2 (StA, (S1 :: L, S0, []))
  = Some (StC, (S0 :: S1 :: S1 :: L, S0, [])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L UV2). Qed.

(** ** The lap *)

Lemma lap_35 : forall p,
  exists n c', csteps tm_35 n (Cc p) = Some c' /\
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
  - (* interior carry *)
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
      change (rep [S0; S1] j ++ rep [S0; S1; S1] (S (S (2 * m)))
                ++ [S0; S1; S1])
        with (rep [S0; S1] j ++ S0 :: S1 ::
                (S1 :: rep [S0; S1; S1] (S (2 * m)) ++ [S0; S1; S1])).
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
      change (rep [S0; S1] j' ++ rep [S0; S1; S1] (S (S (2 * m)))
                ++ [S0; S1; S1])
        with (rep [S0; S1] j' ++ S0 :: S1 ::
                (S1 :: rep [S0; S1; S1] (S (2 * m)) ++ [S0; S1; S1])).
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

Lemma boot_35 : exists t0, stepn tm_35 t0 InitES = Some (lift (Cc 4)).
Proof.
  exists 272.
  assert (H : match csteps tm_35 272 c0 with
              | Some c => ceqb c (Cc 4)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm_35 272 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
  f_equal. apply ceqb_lift. exact H.
Qed.

Lemma vis_35 : forall p q,
  exists k c, csteps tm_35 k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q.
  unfold Cc.
  destruct q.
  - exists 0. eexists. split; reflexivity.
  - exists 1. eexists. split; [apply phUV1 | reflexivity].
  - exists 2. eexists. split; [apply phUV2 | reflexivity].
  - exists 5. eexists. split; [apply phU1 | reflexivity].
Qed.

(** #35 never quasihalts: bbchallenge 1RB1RA_0RC0RA_1LC0LD_1LA1LC. *)
Theorem nqh_1RB1RA_0RC0RA_1LC0LD_1LA1LC : NeverQuasiHaltsSt tm_35.
Proof.
  apply (glue_neverqh tm_35 Cc 4).
  - exact boot_35.
  - intros p _. apply lap_35.
  - intros p q _. apply vis_35.
Qed.

Theorem tm_35_nonhalt : NonHalt tm_35.
Proof. apply never_qh_nonhalt, nqh_1RB1RA_0RC0RA_1LC0LD_1LA1LC. Qed.
