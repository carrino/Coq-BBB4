(** * Assembly: app-chain the NGramHist harvest per-file [Forall]s into one
    [Forall boarded] (route A of docs/NGHIST_WAVE5.md S5 -- NO census walk).

    Each [NGHStage/NGH_NN.v] proves [Forall NeverQuasiHaltsSt ngh_NN] and each
    [NGHWStage/NGHW_NN.v] proves [Forall iqh nghw_NN] (with
    [iqh tm := NonHalt tm /\ QHBound 2000 tm /\ QuasiHaltsSt tm]).  Both shapes
    weaken to the common [boarded] predicate -- a machine is off the deferred
    list if it is proven never-QH, or a bounded quasihalter -- and app-chain
    into one [Forall boarded boarded_all], entirely by kernel term composition.

    This composes wave-6 (NGH_00..04, NGHW_00..05) with the wave-7 oracle-drive
    boards (NGH_05.., NGHW_06..).  A closeout can further app-chain the
    wave-2/3/4 stage [Forall]s (on their branch) the same way and relate
    [boarded_all] to the frozen [D_census] list. *)

From Coq Require Import List.
From BBB4 Require Import BBB4_Statement.
From BBB4.Census Require Import TNF_QH.
From BBB4.Machines.NGHStage Require Import
  NGH_00 NGH_01 NGH_02 NGH_03 NGH_04
  NGH_05 NGH_06 NGH_07.
From BBB4.Machines.NGHWStage Require Import
  NGHW_00 NGHW_01 NGHW_02 NGHW_03 NGHW_04 NGHW_05.
Import ListNotations.

(** A machine is boarded (removable from [D_census]) if it never quasihalts,
    or it is a quasihalter with a certified last-visit bound. *)
Definition boarded (tm : TM) : Prop :=
  NeverQuasiHaltsSt tm
  \/ (NonHalt tm /\ QHBound 2000 tm /\ QuasiHaltsSt tm).

Lemma nqh_to_boarded : forall l,
  Forall NeverQuasiHaltsSt l -> Forall boarded l.
Proof.
  intros l H. eapply Forall_impl; [| exact H].
  intros a Ha. left. exact Ha.
Qed.

Lemma iqh_to_boarded : forall l,
  Forall (fun tm => NonHalt tm /\ QHBound 2000 tm /\ QuasiHaltsSt tm) l ->
  Forall boarded l.
Proof.
  intros l H. eapply Forall_impl; [| exact H].
  intros a Ha. right. exact Ha.
Qed.

(** The never-QH boards (wave-6 NGH_00..04 + wave-7 oracle-drive NGH_05..07). *)
Definition nqh_all : list TM :=
  ngh_00 ++ ngh_01 ++ ngh_02 ++ ngh_03 ++ ngh_04
  ++ ngh_05 ++ ngh_06 ++ ngh_07.

(** The R_QH boards (wave-6). *)
Definition qh_all : list TM :=
  nghw_00 ++ nghw_01 ++ nghw_02 ++ nghw_03 ++ nghw_04 ++ nghw_05.

Definition boarded_all : list TM := nqh_all ++ qh_all.

Lemma nqh_all_boarded : Forall boarded nqh_all.
Proof.
  unfold nqh_all.
  repeat (apply Forall_app; split);
    apply nqh_to_boarded;
    first [ exact ngh_00_nqh | exact ngh_01_nqh | exact ngh_02_nqh
          | exact ngh_03_nqh | exact ngh_04_nqh | exact ngh_05_nqh
          | exact ngh_06_nqh | exact ngh_07_nqh ].
Qed.

Lemma qh_all_boarded : Forall boarded qh_all.
Proof.
  unfold qh_all.
  repeat (apply Forall_app; split);
    apply iqh_to_boarded;
    first [ exact nghw_00_all | exact nghw_01_all | exact nghw_02_all
          | exact nghw_03_all | exact nghw_04_all | exact nghw_05_all ].
Qed.

Theorem boarded_all_boarded : Forall boarded boarded_all.
Proof.
  unfold boarded_all. apply Forall_app. split.
  - exact nqh_all_boarded.
  - exact qh_all_boarded.
Qed.
