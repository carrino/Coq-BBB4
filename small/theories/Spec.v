From Coq Require Import Arith Lia List.
From SmallBB Require Import Statement StatementTr Size Bounds.
Import ListNotations.

Definition AttainsSt tm B := exists q s, QuietAfter tm q s /\ S s = B.
Definition AttainsTr tm B := exists tg s, QuietAfterTr tm tg s /\ S s = B.
Definition BBBSt_is ns ms B :=
  (exists tm, Admissible ns ms tm /\ AttainsSt tm B) /\
  (forall tm B', Admissible ns ms tm -> AttainsSt tm B' -> B' <= B).
Definition BBBTr_is ns ms B :=
  (exists tm, Admissible ns ms tm /\ AttainsTr tm B) /\
  (forall tm B', Admissible ns ms tm -> AttainsTr tm B' -> B' <= B).

Theorem BBBSt_unique : forall ns ms B B',
  BBBSt_is ns ms B -> BBBSt_is ns ms B' -> B = B'.
Proof. intros ns ms B B' [(m & Hm & Ha) H] [(m' & Hm' & Ha') H'];
  specialize (H m' B' Hm' Ha'); specialize (H' m B Hm Ha); lia. Qed.
Theorem BBBTr_unique : forall ns ms B B',
  BBBTr_is ns ms B -> BBBTr_is ns ms B' -> B = B'.
Proof. intros ns ms B B' [(m & Hm & Ha) H] [(m' & Hm' & Ha') H'];
  specialize (H m' B' Hm' Ha'); specialize (H' m B Hm Ha); lia. Qed.

Definition BBB22_statement := BBBSt_is 2 2 6 /\ BBBTr_is 2 2 8.
Definition BBB32_statement := BBBSt_is 3 2 55 /\ BBBTr_is 3 2 55.
Definition BBB23_statement := BBBSt_is 2 3 59 /\ BBBTr_is 2 3 67.
