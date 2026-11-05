(** A fixed state is the beep target. Configuration B has already been
    observed after B transitions, so the inclusive window is [B,B+w]. *)
From Coq Require Import Arith Lia.
From SmallBB Require Import Statement Size Bounds Spec.

Definition FutureBeep tm q B := exists t, B <= t /\ VisitsAt tm q t.
Definition BeepWindow tm q B w := exists t, B <= t /\ t <= B+w /\ VisitsAt tm q t.
Definition WaitBound ns ms B w := forall tm, Admissible ns ms tm ->
 forall q, FutureBeep tm q B -> BeepWindow tm q B w.
Definition BBBWait_is ns ms B w := BBBSt_is ns ms B /\ WaitBound ns ms B w /\
 forall v, WaitBound ns ms B v -> w <= v.

Theorem wait_decides_future : forall ns ms B w, WaitBound ns ms B w ->
 forall tm, Admissible ns ms tm -> forall q,
 FutureBeep tm q B <-> BeepWindow tm q B w.
Proof.
 intros ns ms B w H tm Had q;split;[apply H;exact Had|].
 intros(t&Ht&_&Hv);exists t;auto.
Qed.
Theorem wait_silence_decision : forall ns ms B w, WaitBound ns ms B w ->
 forall tm, Admissible ns ms tm -> forall q,
 (forall t,B<=t->t<=B+w->~VisitsAt tm q t) <-> QuietFrom tm q B.
Proof.
 intros ns ms B w H tm Had q;split.
 - intros Hnone t Ht Hv;destruct(H tm Had q (ex_intro _ t (conj Ht Hv)))as(k&Hk&Hkw&Hvk).
   exact(Hnone k Hk Hkw Hvk).
 - intros Hnone t Ht _;exact(Hnone t Ht).
Qed.
Theorem BBBWait_unique : forall ns ms B w v,
 BBBWait_is ns ms B w -> BBBWait_is ns ms B v -> w=v.
Proof. intros ns ms B w v [_ [Hw Hminw]] [_ [Hv Hminv]];specialize(Hminw v Hv);specialize(Hminv w Hw);lia. Qed.
