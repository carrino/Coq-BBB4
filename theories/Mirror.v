(** * Mirror: left/right symmetry.

    Reflecting a machine's move directions and reflecting the tape
    commute with stepping, and the start configuration is symmetric,
    so every quasihalting-level property transfers between a machine
    and its mirror.  Checkers can therefore be written one-sided
    (right-handed) and applied to left-moving behaviors through
    [mirror_tm] -- the BBB harness's `side L/R` certificates become a
    checker on [tm] or on [mirror_tm tm]. *)

From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement.
Import ListNotations.

Definition mirror_dir (d : Dir) : Dir :=
  match d with DL => DR | DR => DL end.

Definition mirror_tm (tm : TM) : TM :=
  fun q s => match tm q s with
             | None => None
             | Some tr => Some (mkTrans (t_write tr) (mirror_dir (t_dir tr))
                                        (t_next tr))
             end.

Definition mirror_tape (t : Tape) : Tape :=
  mkTape (t_right t) (t_head t) (t_left t).

Definition mirror_es (c : ExecState) : ExecState :=
  (fst c, mirror_tape (snd c)).

Lemma mirror_es_init : mirror_es InitES = InitES.
Proof. reflexivity. Qed.

Lemma mirror_step : forall tm c,
  step (mirror_tm tm) (mirror_es c) =
  match step tm c with
  | Some c' => Some (mirror_es c')
  | None => None
  end.
Proof.
  intros tm [q t]. unfold step, mirror_es, mirror_tm; simpl.
  destruct (tm q (t_head t)) as [tr|]; [|reflexivity].
  destruct (t_dir tr); reflexivity.
Qed.

Lemma mirror_stepn : forall tm n c,
  stepn (mirror_tm tm) n (mirror_es c) =
  match stepn tm n c with
  | Some c' => Some (mirror_es c')
  | None => None
  end.
Proof.
  induction n; intros.
  - reflexivity.
  - cbn [stepn]. rewrite mirror_step.
    destruct (step tm c); [apply IHn | reflexivity].
Qed.

Lemma mirror_stepn_init : forall tm n,
  stepn (mirror_tm tm) n InitES =
  match stepn tm n InitES with
  | Some c' => Some (mirror_es c')
  | None => None
  end.
Proof.
  intros. rewrite <- mirror_es_init at 1. apply mirror_stepn.
Qed.

Lemma mirror_visits : forall tm q n,
  VisitsAt (mirror_tm tm) q n <-> VisitsAt tm q n.
Proof.
  intros tm q n; unfold VisitsAt; split.
  - intros (c & Hc & Hq).
    rewrite mirror_stepn_init in Hc.
    destruct (stepn tm n InitES) as [c'|] eqn:E; [|discriminate].
    injection Hc as <-.
    exists c'. split; [reflexivity | exact Hq].
  - intros (c & Hc & Hq).
    exists (mirror_es c). split; [|exact Hq].
    rewrite mirror_stepn_init, Hc. reflexivity.
Qed.

Lemma mirror_nonhalt : forall tm, NonHalt (mirror_tm tm) -> NonHalt tm.
Proof.
  intros tm H n E. apply (H n).
  rewrite mirror_stepn_init, E. reflexivity.
Qed.

Lemma mirror_never_qh : forall tm,
  NeverQuasiHaltsSt (mirror_tm tm) -> NeverQuasiHaltsSt tm.
Proof.
  intros tm H q Hv N.
  assert (Hv' : Visited (mirror_tm tm) q).
  { destruct Hv as (n0 & Hv0). exists n0. apply mirror_visits. exact Hv0. }
  destruct (H q Hv' N) as (n & Hn & Hvis).
  exists n. split; [exact Hn | apply mirror_visits; exact Hvis].
Qed.

Lemma mirror_quiet_after : forall tm q s,
  QuietAfter (mirror_tm tm) q s -> QuietAfter tm q s.
Proof.
  intros tm q s [Hvis Hq].
  split.
  - apply mirror_visits. exact Hvis.
  - intros n Hn Hv. apply (Hq n Hn). apply mirror_visits. exact Hv.
Qed.

Lemma mirror_qh : forall tm,
  QuasiHaltsSt (mirror_tm tm) -> QuasiHaltsSt tm.
Proof.
  intros tm (q & (n0 & Hv) & N & HN).
  exists q. split.
  - exists n0. apply mirror_visits. exact Hv.
  - exists N. intros n Hn Hvis.
    apply (HN n Hn). apply mirror_visits. exact Hvis.
Qed.
