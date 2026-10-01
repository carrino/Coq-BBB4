(** * A token transducer for a counter next to a periodic bouncer.

    Tokens are read nearest first.  The final blank in [mt_tail] is
    explicit only to make the finite-list execution equations exact.
    Both carry entrances reach the same state and head symbol; their
    different return windows are part of the opaque opposite half-tape.
    This makes one recursive transducer sufficient for both ports.
    The carry is uniform in the opposite half-tape.  No arithmetic
    interpretation of the token word is needed by a lap closer. *)

From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement CTape.
Import ListNotations.

Inductive mt_digit : Set := MT0 | MT1 | MT2.

Definition mt_token (d : mt_digit) : list Sym :=
  match d with
  | MT0 => [S0; S0; S0]
  | MT1 => [S0; S0; S1]
  | MT2 => [S0; S1; S0]
  end.

Fixpoint mt_raw (w : list mt_digit) : list Sym :=
  match w with
  | [] => []
  | d :: t => mt_token d ++ mt_raw t
  end.

Definition mt_tail (w : list mt_digit) : list Sym :=
  mt_raw w ++ [S0; S1; S0].

Definition mt_encode (w : list mt_digit) : list Sym :=
  match w with [] => [] | _ :: _ => mt_tail w end.

Fixpoint mt_carry (w : list mt_digit) : list mt_digit :=
  match w with
  | [] => [MT1]
  | MT0 :: t => MT2 :: t
  | MT1 :: t => MT0 :: t
  | MT2 :: t => MT1 :: mt_carry t
  end.

Fixpoint mt_cdepth (w : list mt_digit) : nat :=
  match w with
  | [] => 1
  | MT0 :: _ | MT1 :: _ => 0
  | MT2 :: t => S (mt_cdepth t)
  end.

Definition mt_succ (w : list mt_digit) : list mt_digit :=
  match w with
  | [] => [MT1]
  | MT0 :: t => MT1 :: mt_carry t
  | MT1 :: t => MT2 :: t
  | MT2 :: t => MT0 :: mt_carry t
  end.

Definition mt_depth (w : list mt_digit) : nat :=
  match w with
  | [] => 1
  | MT1 :: _ => 0
  | MT0 :: t | MT2 :: t => S (mt_cdepth t)
  end.

Lemma mt_succ_head : forall w,
  exists Y, mt_encode (mt_succ w) = S0 :: Y.
Proof. intros [|d t]; [eexists; reflexivity|].
  destruct d; eexists; reflexivity. Qed.

Section TokenMachine.

Variable tm : TM.
Variable qa qb qc qd : St.
Hypothesis Ha0 : tm qa S0 = Some (mkTrans S0 DR qb).
Hypothesis Ha1 : tm qa S1 = Some (mkTrans S0 DR qa).
Hypothesis Hb0 : tm qb S0 = Some (mkTrans S1 DL qc).
Hypothesis Hb1 : tm qb S1 = Some (mkTrans S1 DR qa).
Hypothesis Hc0 : tm qc S0 = Some (mkTrans S0 DL qd).
Hypothesis Hc1 : tm qc S1 = Some (mkTrans S0 DL qc).
Hypothesis Hd0 : tm qd S0 = Some (mkTrans S1 DL qa).
Hypothesis Hd1 : tm qd S1 = Some (mkTrans S1 DL qb).

Ltac mt_steps :=
  cbn [Nat.add Nat.mul csteps cstep ctape_move chd ctl t_next t_dir t_write];
  repeat (first [rewrite Ha0 | rewrite Ha1 | rewrite Hb0 | rewrite Hb1 |
                 rewrite Hc0 | rewrite Hc1 | rewrite Hd0 | rewrite Hd1];
          cbn [Nat.add Nat.mul csteps cstep ctape_move chd ctl t_next t_dir t_write]);
  reflexivity.

Lemma mt_carry_enter : forall L R,
  csteps tm 3 (qb, (S0 :: S1 :: S0 :: L, S0, R)) =
  Some (qb, (L, S0, S1 :: S0 :: S1 :: R)).
Proof. intros; mt_steps. Qed.

Lemma mt_carry_return : forall L R,
  csteps tm 3 (qb, (L, S1, S1 :: S0 :: S1 :: R)) =
  Some (qb, (S0 :: S0 :: S1 :: L, S1, R)).
Proof. intros; mt_steps. Qed.

Lemma mt_carry_run : forall w R,
  csteps tm (6 + 6 * mt_cdepth w) (qb, (mt_tail w, S0, R)) =
  Some (qb, (mt_tail (mt_carry w), S1, R)).
Proof.
  induction w as [|d w IH]; intros R.
  - cbn [mt_cdepth mt_carry mt_tail mt_raw mt_token app]. mt_steps.
  - destruct d.
    + cbn [mt_cdepth mt_carry mt_tail mt_raw mt_token app]. mt_steps.
    + cbn [mt_cdepth mt_carry mt_tail mt_raw mt_token app]. mt_steps.
    + change (csteps tm (6 + 6 * S (mt_cdepth w))
        (qb, (S0 :: S1 :: S0 :: mt_tail w, S0, R)) =
        Some (qb, (S0 :: S0 :: S1 :: mt_tail (mt_carry w), S1, R))).
      replace (6 + 6 * S (mt_cdepth w))
        with (3 + ((6 + 6 * mt_cdepth w) + 3)) by lia.
      rewrite csteps_add, mt_carry_enter, csteps_add, IH.
      apply mt_carry_return.
Qed.

Lemma mt_zero_enter : forall L R,
  csteps tm 9 (qc, (S0 :: S0 :: S0 :: L, S1, R)) =
  Some (qb, (L, S0, S1 :: S0 :: S1 :: R)).
Proof. intros; mt_steps. Qed.

Lemma mt_two_enter : forall L R,
  csteps tm 3 (qc, (S0 :: S1 :: S0 :: L, S1, R)) =
  Some (qb, (L, S0, S1 :: S0 :: S0 :: R)).
Proof. intros; mt_steps. Qed.

Lemma mt_two_return : forall L R,
  csteps tm 9 (qb, (L, S1, S1 :: S0 :: S0 :: R)) =
  Some (qb, (S0 :: S0 :: S0 :: L, S1, R)).
Proof. intros; mt_steps. Qed.

(** The complete token phase.  The right half-tape has not been read.
    The successor is defined on every token word, which avoids a
    canonical-word side condition in the subsequent lap induction. *)
Lemma mt_token_phase : forall w R,
  csteps tm (12 + 6 * mt_depth w)
    (qc, (mt_encode w, S1, R)) =
  Some (qb, (mt_encode (mt_succ w), S1, R)).
Proof.
  intros [|d w] R.
  - cbn [mt_depth mt_encode mt_succ mt_tail mt_raw mt_token app]. mt_steps.
  - destruct d.
    + change (csteps tm (12 + 6 * S (mt_cdepth w))
        (qc, (S0 :: S0 :: S0 :: mt_tail w, S1, R)) =
        Some (qb, (S0 :: S0 :: S1 :: mt_tail (mt_carry w), S1, R))).
      replace (12 + 6 * S (mt_cdepth w))
        with (9 + ((6 + 6 * mt_cdepth w) + 3)) by lia.
      rewrite csteps_add, mt_zero_enter, csteps_add, mt_carry_run.
      apply mt_carry_return.
    + cbn [mt_depth mt_encode mt_succ mt_tail mt_raw mt_token app]. mt_steps.
    + change (csteps tm (12 + 6 * S (mt_cdepth w))
        (qc, (S0 :: S1 :: S0 :: mt_tail w, S1, R)) =
        Some (qb, (S0 :: S0 :: S0 :: mt_tail (mt_carry w), S1, R))).
      replace (12 + 6 * S (mt_cdepth w))
        with (3 + ((6 + 6 * mt_cdepth w) + 9)) by lia.
      rewrite csteps_add, mt_two_enter, csteps_add, mt_carry_run.
      apply mt_two_return.
Qed.

End TokenMachine.
