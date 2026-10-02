(** * Periodic sweeps whose left turnaround moves right.

    These sweeps preserve an arbitrary finite counter word [L].  The
    [C1] instruction belongs to a separate transducer and is unconstrained.
    The block traversals reuse [TokenSweepTr]; only the turnaround differs. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape TokenSweepTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.

Section MovingSweep.
Variable tm : TM.
Hypothesis HA0 : tm StA S0 = Some (mkTrans S0 DR StB).
Hypothesis HA1 : tm StA S1 = Some (mkTrans S0 DR StA).
Hypothesis HB0 : tm StB S0 = Some (mkTrans S1 DL StC).
Hypothesis HB1 : tm StB S1 = Some (mkTrans S1 DR StA).
Hypothesis HC0 : tm StC S0 = Some (mkTrans S0 DL StD).
Hypothesis HD0 : tm StD S0 = Some (mkTrans S1 DR StA).
Hypothesis HD1 : tm StD S1 = Some (mkTrans S1 DL StB).

Local Ltac moving_compute :=
  repeat (cbn [csteps cstep ctape_move chd ctl t_write t_dir t_next];
          first [rewrite HA0 | rewrite HA1 | rewrite HB0 | rewrite HB1 |
                 rewrite HC0 | rewrite HD0 | rewrite HD1]); reflexivity.

Lemma moving_sweep_first_out : forall k L,
  csteps tm (3*k+1) (StA, (L, S1, rep [S1;S0;S1] k)) =
  Some (StA, (rep [S1;S0;S0] k ++ S0 :: L, S0, [])).
Proof. intros; apply token_sweep_first_out; assumption. Qed.

Lemma moving_sweep_first_back : forall k L,
  csteps tm (6*k+3) (StA, (L, S1, rep [S1;S0;S1] k)) =
  Some (StC, (S0::L, S0, rep [S1;S1;S0] k ++ [S1])).
Proof. intros; apply token_sweep_first_back; assumption. Qed.

Lemma moving_sweep_out : forall k L Y,
  csteps tm (3 * k)
    (StA, (L, chd (rep [S1;S0;S1] k ++ Y),
                  ctl (rep [S1;S0;S1] k ++ Y))) =
  Some (StA, (rep [S1;S0;S0] k ++ L, chd Y, ctl Y)).
Proof. intros; apply token_sweep_out; assumption. Qed.

Lemma moving_sweep_back : forall k L R,
  csteps tm (3 * k) (StC, (rep [S1;S0;S0] k ++ L, S0, R)) =
  Some (StC, (L, S0, rep [S1;S1;S0] k ++ R)).
Proof. intros; apply token_sweep_back; assumption. Qed.

Lemma moving_sweep_turn : forall L,
  csteps tm 2 (StA, (L, S0, [])) = Some (StC, (L, S0, [S1])).
Proof. intros; apply token_sweep_turn; assumption. Qed.

Lemma moving_sweep_middle : forall k L,
  csteps tm (6*k+7) (StA, (L,S1,rep [S1;S0;S1] k)) =
  Some (StA, (S1::S0::S1::L,
      chd (rep [S1;S0;S1] k), ctl (rep [S1;S0;S1] k))).
Proof.
  intros k L. replace (6*k+7) with ((6*k+3)+4) by lia.
  rewrite csteps_add, moving_sweep_first_back, token_sweep_rotation.
  moving_compute.
Qed.

Lemma moving_sweep_second_back : forall k L,
  csteps tm (12*k+9) (StA, (L,S1,rep [S1;S0;S1] k)) =
  Some (StC, (S1::S0::S1::L,S0,rep [S1;S1;S0] k ++ [S1])).
Proof.
  intros k L. replace (12*k+9) with ((6*k+7)+(3*k+(2+3*k))) by lia.
  rewrite csteps_add, moving_sweep_middle, csteps_add.
  pose proof (moving_sweep_out k (S1::S0::S1::L) []) as E.
  rewrite app_nil_r in E. rewrite E. cbn [chd ctl].
  rewrite csteps_add, moving_sweep_turn. apply moving_sweep_back.
Qed.

Theorem moving_sweep : forall k L,
  csteps tm (12*k+12) (StA, (L,S1,rep [S1;S0;S1] k)) =
  Some (StC, (L,S1,rep [S1;S1;S0] (S k) ++ [S1])).
Proof.
  intros k L. replace (12*k+12) with ((12*k+9)+3) by lia.
  rewrite csteps_add, moving_sweep_second_back. cbn [rep app].
  moving_compute.
Qed.

Lemma moving_sweep_fire : forall k L t,
  t <> (StC,S1) ->
  exists j c,
    csteps tm j (StA, (L,S1,rep [S1;S0;S1] k)) = Some c /\
    cinstr c = t.
Proof.
  intros k L [q s] Ht. destruct q, s.
  - exists (3*k+1). eexists. split.
    + apply moving_sweep_first_out.
    + reflexivity.
  - exists 0, (StA,(L,S1,rep [S1;S0;S1] k)). split; reflexivity.
  - exists (3*k+2). eexists. split.
    + replace (3*k+2) with ((3*k+1)+1) by lia.
      rewrite csteps_add, moving_sweep_first_out. moving_compute.
    + reflexivity.
  - exists (6*k+6). eexists. split.
    + replace (6*k+6) with ((6*k+3)+3) by lia.
      rewrite csteps_add, moving_sweep_first_back, token_sweep_rotation.
      moving_compute.
    + reflexivity.
  - exists (6*k+3). eexists. split.
    + apply moving_sweep_first_back.
    + reflexivity.
  - exfalso. apply Ht. reflexivity.
  - exists (6*k+4). eexists. split.
    + replace (6*k+4) with ((6*k+3)+1) by lia.
      rewrite csteps_add, moving_sweep_first_back. moving_compute.
    + reflexivity.
  - exists (12*k+10). eexists. split.
    + replace (12*k+10) with ((12*k+9)+1) by lia.
      rewrite csteps_add, moving_sweep_second_back. moving_compute.
    + reflexivity.
Qed.

End MovingSweep.
