(** * Periodic bouncer sweeps beside an opaque token word.

    The local transition hypotheses describe seven instructions; [C1]
    belongs to the token transducer and is deliberately unconstrained.
    All runs here preserve the opaque tail exactly, including its finite
    list representation. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.

Section TokenSweeps.
Variable tm : TM.
Hypothesis HA0 : tm StA S0 = Some (mkTrans S0 DR StB).
Hypothesis HA1 : tm StA S1 = Some (mkTrans S0 DR StA).
Hypothesis HB0 : tm StB S0 = Some (mkTrans S1 DL StC).
Hypothesis HB1 : tm StB S1 = Some (mkTrans S1 DR StA).
Hypothesis HC0 : tm StC S0 = Some (mkTrans S0 DL StD).
Hypothesis HD0 : tm StD S0 = Some (mkTrans S1 DL StA).
Hypothesis HD1 : tm StD S1 = Some (mkTrans S1 DL StB).

Local Ltac sweep_compute :=
  repeat (cbn [csteps cstep ctape_move chd ctl t_write t_dir t_next];
          first [rewrite HA0 | rewrite HA1 | rewrite HB0 | rewrite HB1 |
                 rewrite HC0 | rewrite HD0 | rewrite HD1]); reflexivity.

Lemma token_sweep_out3 : forall L R,
  csteps tm 3 (StA, (L, S1, S0 :: S1 :: R)) =
  Some (StA, (S1 :: S0 :: S0 :: L, chd R, ctl R)).
Proof. intros; sweep_compute. Qed.

Lemma token_sweep_back3 : forall L R,
  csteps tm 3 (StC, (S1 :: S0 :: S0 :: L, S0, R)) =
  Some (StC, (L, S0, S1 :: S1 :: S0 :: R)).
Proof. intros; sweep_compute. Qed.

Lemma token_sweep_rep_push : forall u k L,
  rep u k ++ (u ++ L) = rep u (S k) ++ L.
Proof.
  intros. rewrite app_assoc, rep_shift. reflexivity.
Qed.

Lemma token_sweep_out : forall k L Y,
  csteps tm (3 * k)
    (StA, (L, chd (rep [S1; S0; S1] k ++ Y),
                  ctl (rep [S1; S0; S1] k ++ Y))) =
  Some (StA, (rep [S1; S0; S0] k ++ L, chd Y, ctl Y)).
Proof.
  induction k as [|k IH]; intros L Y; [reflexivity|].
  replace (3 * S k) with (3 + 3 * k) by lia.
  rewrite csteps_add. cbn [rep app chd ctl].
  rewrite token_sweep_out3, IH.
  change (Some (StA, (rep [S1;S0;S0] k ++ ([S1;S0;S0] ++ L), chd Y, ctl Y)) =
    Some (StA, (rep [S1;S0;S0] (S k) ++ L, chd Y, ctl Y))).
  rewrite token_sweep_rep_push. reflexivity.
Qed.

Lemma token_sweep_back : forall k L R,
  csteps tm (3 * k) (StC, (rep [S1;S0;S0] k ++ L, S0, R)) =
  Some (StC, (L, S0, rep [S1;S1;S0] k ++ R)).
Proof.
  induction k as [|k IH]; intros L R; [reflexivity|].
  replace (3 * S k) with (3 + 3 * k) by lia.
  rewrite csteps_add. cbn [rep app].
  rewrite token_sweep_back3, IH.
  change (Some (StC, (L, S0, rep [S1;S1;S0] k ++ ([S1;S1;S0] ++ R))) =
    Some (StC, (L, S0, rep [S1;S1;S0] (S k) ++ R))).
  rewrite token_sweep_rep_push. reflexivity.
Qed.

Lemma token_sweep_rotation : forall k,
  rep [S1;S1;S0] k ++ [S1] = S1 :: rep [S1;S0;S1] k.
Proof. intro k. symmetry. exact (rep_rot S1 [S1;S0] k). Qed.

Lemma token_sweep_first_out : forall k L,
  csteps tm (3*k+1) (StA, (L, S1, rep [S1;S0;S1] k)) =
  Some (StA, (rep [S1;S0;S0] k ++ S0 :: L, S0, [])).
Proof.
  intros k L. replace (3*k+1) with (1+3*k) by lia.
  rewrite csteps_add.
  assert (H : csteps tm 1 (StA, (L,S1,rep [S1;S0;S1] k)) =
    Some (StA, (S0::L, chd (rep [S1;S0;S1] k), ctl (rep [S1;S0;S1] k)))).
  { sweep_compute. }
  rewrite H.
  pose proof (token_sweep_out k (S0::L) []) as E.
  rewrite app_nil_r in E. exact E.
Qed.

Lemma token_sweep_turn : forall L,
  csteps tm 2 (StA, (L, S0, [])) = Some (StC, (L, S0, [S1])).
Proof. intros; sweep_compute. Qed.

Lemma token_sweep_first_back : forall k L,
  csteps tm (6*k+3) (StA, (L, S1, rep [S1;S0;S1] k)) =
  Some (StC, (S0::L, S0, rep [S1;S1;S0] k ++ [S1])).
Proof.
  intros k L. replace (6*k+3) with ((3*k+1)+(2+3*k)) by lia.
  rewrite csteps_add, token_sweep_first_out, csteps_add, token_sweep_turn.
  apply token_sweep_back.
Qed.

Lemma token_sweep_first : forall k L,
  csteps tm (6*k+5) (StA, (L, S1, rep [S1;S0;S1] k)) =
  Some (StA, (ctl L, chd L, rep [S1;S0;S1] (S k))).
Proof.
  intros k L. replace (6*k+5) with ((6*k+3)+2) by lia.
  rewrite csteps_add, token_sweep_first_back, token_sweep_rotation.
  cbn [rep app]. sweep_compute.
Qed.

Lemma token_sweep_second : forall k Y,
  csteps tm (6*k+9) (StA, (Y, S0, rep [S1;S0;S1] (S k))) =
  Some (StC, (S0::Y, S1, rep [S1;S1;S0] (S k) ++ [S1])).
Proof.
  intros k Y.
  assert (Hentry : csteps tm 4 (StA, (Y,S0,rep [S1;S0;S1] (S k))) =
    Some (StA, (S1::S0::S1::S0::Y,
      chd (rep [S1;S0;S1] k), ctl (rep [S1;S0;S1] k)))).
  { cbn [rep app]. sweep_compute. }
  replace (6*k+9) with (4+(3*k+(2+(3*k+3)))) by lia.
  rewrite csteps_add, Hentry, csteps_add.
  pose proof (token_sweep_out k (S1::S0::S1::S0::Y) []) as E.
  rewrite app_nil_r in E. rewrite E. cbn [chd ctl].
  rewrite csteps_add, token_sweep_turn, csteps_add, token_sweep_back.
  cbn [rep app]. sweep_compute.
Qed.

Lemma token_sweep_finish : forall n X,
  csteps tm (12*n+12)
    (StB, (X, S1, rep [S1;S1;S0] (2*n+1) ++ [S1])) =
  Some (StA, (X, S1, rep [S1;S0;S1] (2*n+2))).
Proof.
  intros n X. rewrite token_sweep_rotation.
  replace (12*n+12) with (1+(6*(2*n+1)+5)) by lia.
  rewrite csteps_add.
  assert (H : csteps tm 1 (StB,(X,S1,S1::rep [S1;S0;S1] (2*n+1))) =
    Some (StA,(S1::X,S1,rep [S1;S0;S1] (2*n+1)))).
  { sweep_compute. }
  rewrite H, token_sweep_first. cbn [ctl chd].
  replace (S (2*n+1)) with (2*n+2) by lia. reflexivity.
Qed.

Lemma token_sweeps : forall n Y,
  csteps tm (24*n+38) (StA, (S0::Y,S1,rep [S1;S0;S1] (2*n+2))) =
  Some (StC, (S0::Y,S1,rep [S1;S1;S0] (2*n+3) ++ [S1])).
Proof.
  intros n Y.
  replace (24*n+38) with ((6*(2*n+2)+5)+(6*(2*n+2)+9)) by lia.
  rewrite csteps_add, token_sweep_first. cbn [ctl chd].
  rewrite token_sweep_second.
  replace (S (2*n+2)) with (2*n+3) by lia. reflexivity.
Qed.

(** Every instruction used by the periodic sweep is witnessed in its
    first pass, so no unbounded search or ranking is needed for liveness. *)
Lemma token_sweep_fire : forall k L t,
  t <> (StC,S1) ->
  exists j c,
    csteps tm j (StA, (L,S1,rep [S1;S0;S1] (S k))) = Some c /\
    cinstr c = t.
Proof.
  intros k L [q s] Ht. destruct q, s.
  - exists (3*S k+1). eexists. split.
    + apply token_sweep_first_out.
    + reflexivity.
  - exists 0, (StA,(L,S1,rep [S1;S0;S1] (S k))). split; reflexivity.
  - exists (3*S k+2). eexists. split.
    + replace (3*S k+2) with ((3*S k+1)+1) by lia.
      rewrite csteps_add, token_sweep_first_out. sweep_compute.
    + reflexivity.
  - exists 3. eexists. split.
    + cbn [rep app]. sweep_compute.
    + reflexivity.
  - exists (6*S k+3). eexists. split.
    + apply token_sweep_first_back.
    + reflexivity.
  - exfalso. apply Ht. reflexivity.
  - exists (6*S k+4). eexists. split.
    + replace (6*S k+4) with ((6*S k+3)+1) by lia.
      rewrite csteps_add, token_sweep_first_back. sweep_compute.
    + reflexivity.
  - exists (3*S k+4). eexists. split.
    + replace (3*S k+4) with ((3*S k+1)+3) by lia.
      rewrite csteps_add, token_sweep_first_out. cbn [rep app]. sweep_compute.
    + reflexivity.
Qed.

End TokenSweeps.
