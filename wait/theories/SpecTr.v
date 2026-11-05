(** A fixed instruction is the beep target. Configuration B has already been
    observed after B transitions, so the inclusive window is [B,B+w]. *)
From Coq Require Import Arith Lia.
From SmallBB Require Import Statement StatementTr Size Bounds Spec.

Definition FutureBeepTr tm q B := exists t, B <= t /\ FiresAt tm q t.
Definition BeepWindowTr tm q B w := exists t, B <= t /\ t <= B+w /\ FiresAt tm q t.
Definition WaitBoundTr ns ms B w := forall tm, Admissible ns ms tm ->
 forall q, FutureBeepTr tm q B -> BeepWindowTr tm q B w.
Definition BBBWaitTr_is ns ms B w := BBBTr_is ns ms B /\ WaitBoundTr ns ms B w /\
 forall v, WaitBoundTr ns ms B v -> w <= v.

Theorem wait_tr_decides_future : forall ns ms B w, WaitBoundTr ns ms B w ->
 forall tm, Admissible ns ms tm -> forall q,
 FutureBeepTr tm q B <-> BeepWindowTr tm q B w.
Proof.
 intros ns ms B w H tm Had q;split;[apply H;exact Had|].
 intros(t&Ht&_&Hv);exists t;auto.
Qed.
Theorem wait_tr_silence_decision : forall ns ms B w, WaitBoundTr ns ms B w ->
 forall tm, Admissible ns ms tm -> forall q,
 (forall t,B<=t->t<=B+w->~FiresAt tm q t) <-> QuietFromTr tm q B.
Proof.
 intros ns ms B w H tm Had q;split.
 - intros Hnone t Ht Hv;destruct(H tm Had q (ex_intro _ t (conj Ht Hv)))as(k&Hk&Hkw&Hvk).
   exact(Hnone k Hk Hkw Hvk).
 - intros Hnone t Ht _;exact(Hnone t Ht).
Qed.
Theorem BBBWaitTr_unique : forall ns ms B w v,
 BBBWaitTr_is ns ms B w -> BBBWaitTr_is ns ms B v -> w=v.
Proof. intros ns ms B w v [_ [Hw Hminw]] [_ [Hv Hminv]];specialize(Hminw v Hv);specialize(Hminv w Hw);lia. Qed.
