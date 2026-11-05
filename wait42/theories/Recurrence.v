From Coq Require Import Arith Lia.
From BBB4 Require Import BBB4_Statement BBBT4_Statement BBB4_Spec BBBT4_Spec.
From BBB4.Census Require Import TNF_QH.
From BBB4.CensusTr Require Import TNF_QHTr.
From BBBWait42 Require Import Spec.

Lemma visits_decidable : forall tm q t, {VisitsAt tm q t} + {~ VisitsAt tm q t}.
Proof.
 intros tm q t; destruct (stepn tm t InitES) as [c|] eqn:E.
 - destruct (st_eqb (fst c) q) eqn:Hq.
   + left; exists c; split; [exact E|apply st_eqb_spec; exact Hq].
   + right; intros (d&Ed&Hd); rewrite E in Ed; injection Ed as <-.
     assert (st_eqb (fst c) q = true) by (apply st_eqb_spec; exact Hd). congruence.
 - right; intros (d&Ed&_); rewrite E in Ed; discriminate.
Qed.
Lemma bounded_last_visit : forall tm q N,
  (exists t, t <= N /\ VisitsAt tm q t) ->
  exists s, s <= N /\ VisitsAt tm q s /\
    forall t, s < t -> t <= N -> ~ VisitsAt tm q t.
Proof.
  intros tm q N; induction N as [|N IH]; intros (t & Ht & Hv).
  - assert (t = 0) by lia; subst t.
    exists 0; repeat split; try assumption; try lia.
  - destruct (visits_decidable tm q (S N)) as [Hend|Hend].
    + exists (S N); repeat split; try assumption; try lia.
    + assert (HtN : t <= N).
      { destruct (le_lt_dec t N); [assumption|].
        assert (t = S N) by lia; subst t; contradiction. }
      destruct (IH (ex_intro _ t (conj HtN Hv))) as (s & Hs & Hvs & Hlast).
      exists s; repeat split; try assumption; try lia.
      intros u Hsu Hu.
      destruct (le_lt_dec u N) as [HuN|HuN].
      * exact (Hlast u Hsu HuN).
      * assert (u = S N) by lia; subst u; exact Hend.
Qed.

Lemma no_late_last_visit : forall tm B,
  QHBound B tm -> forall q s, B <= s -> ~ QuietAfter tm q s.
Proof.
  intros tm B Hbound q s Hs Hlast.
  specialize (Hbound q s Hlast); lia.
Qed.

Theorem late_beep_not_eventually_quiet : forall tm q B,
  QHBound B tm -> FutureBeep tm q B ->
  forall N, ~ QuietFrom tm q N.
Proof.
  intros tm q B Hbound (t & HBt & Hv) N Hquiet.
  assert (HtN : t <= N).
  { destruct (le_lt_dec t N); [assumption|].
    exfalso; exact (Hquiet t ltac:(lia) Hv). }
  destruct (bounded_last_visit tm q N (ex_intro _ t (conj HtN Hv)))
    as (s & Hs & Hvs & Hlast).
  assert (Hts : t <= s).
  { destruct (le_lt_dec t s); [assumption|].
    exfalso; exact (Hlast t ltac:(lia) HtN Hv). }
  apply (no_late_last_visit tm B Hbound q s ltac:(lia)).
  split; [exact Hvs|].
  intros u Hsu.
  destruct (le_lt_dec u N) as [HuN|HuN].
  - exact (Hlast u Hsu HuN).
  - exact (Hquiet u ltac:(lia)).
Qed.

Print Assumptions late_beep_not_eventually_quiet.

Theorem wait_decides_quasihalting : forall B w,
  BBB4_is B -> WaitBound B w -> forall tm,
  (QuasiHaltsSt tm <->
   exists q, (exists t, t < B /\ VisitsAt tm q t) /\
     (forall t, B <= t -> t <= B+w -> ~ VisitsAt tm q t)).
Proof.
  intros B w Hbbb Hwait tm.
  assert (Hbound : QHBound B tm).
  { intros q s Hlast.
    destruct Hbbb as [_ Hupper].
    apply (Hupper tm (S s)).
    exists q, s; split; [exact Hlast|reflexivity]. }
  split.
  - intros (q & (t & Hv) & N & Hquiet).
    exists q; split.
    + exists t; split; [|exact Hv].
      destruct (lt_dec t B) as [Ht|Ht]; [exact Ht|].
      exfalso.
      assert (Hfuture : FutureBeep tm q B).
      { exists t; split; [lia|exact Hv]. }
      exact (late_beep_not_eventually_quiet tm q B Hbound Hfuture N Hquiet).
    + intros u Hlo _ Hvu.
      apply (late_beep_not_eventually_quiet tm q B Hbound
        (ex_intro _ u (conj Hlo Hvu)) N Hquiet).
  - intros (q & (t & Ht & Hv) & Hwindow).
    exists q; split.
    + exists t; exact Hv.
    + exists B.
      apply (proj1 (wait_silence_decision B w Hwait tm q)).
      exact Hwindow.
Qed.

Print Assumptions wait_decides_quasihalting.

Lemma fires_decidable : forall tm q t, {FiresAt tm q t} + {~ FiresAt tm q t}.
Proof.
 intros tm q t; destruct (stepn tm t InitES) as [c|] eqn:E.
 - destruct (instr_eqb (instr_of c) q) eqn:Hq.
   + left; exists c; split; [exact E|apply instr_eqb_spec; exact Hq].
   + right; intros (d&Ed&Hd); rewrite E in Ed; injection Ed as <-.
     assert (instr_eqb (instr_of c) q = true) by (apply instr_eqb_spec; exact Hd). congruence.
 - right; intros (d&Ed&_); rewrite E in Ed; discriminate.
Qed.
Lemma bounded_last_fire : forall tm q N,
  (exists t, t <= N /\ FiresAt tm q t) ->
  exists s, s <= N /\ FiresAt tm q s /\
    forall t, s < t -> t <= N -> ~ FiresAt tm q t.
Proof.
  intros tm q N; induction N as [|N IH]; intros (t & Ht & Hv).
  - assert (t = 0) by lia; subst t.
    exists 0; repeat split; try assumption; try lia.
  - destruct (fires_decidable tm q (S N)) as [Hend|Hend].
    + exists (S N); repeat split; try assumption; try lia.
    + assert (HtN : t <= N).
      { destruct (le_lt_dec t N); [assumption|].
        assert (t = S N) by lia; subst t; contradiction. }
      destruct (IH (ex_intro _ t (conj HtN Hv))) as (s & Hs & Hvs & Hlast).
      exists s; repeat split; try assumption; try lia.
      intros u Hsu Hu.
      destruct (le_lt_dec u N) as [HuN|HuN].
      * exact (Hlast u Hsu HuN).
      * assert (u = S N) by lia; subst u; exact Hend.
Qed.

Lemma no_late_last_fire : forall tm B,
  QHBoundTr B tm -> forall q s, B <= s -> ~ QuietAfterTr tm q s.
Proof.
  intros tm B Hbound q s Hs Hlast.
  specialize (Hbound q s Hlast); lia.
Qed.

Theorem late_instruction_not_eventually_quiet : forall tm q B,
  QHBoundTr B tm -> FutureBeepTr tm q B ->
  forall N, ~ QuietFromTr tm q N.
Proof.
  intros tm q B Hbound (t & HBt & Hv) N Hquiet.
  assert (HtN : t <= N).
  { destruct (le_lt_dec t N); [assumption|].
    exfalso; exact (Hquiet t ltac:(lia) Hv). }
  destruct (bounded_last_fire tm q N (ex_intro _ t (conj HtN Hv)))
    as (s & Hs & Hvs & Hlast).
  assert (Hts : t <= s).
  { destruct (le_lt_dec t s); [assumption|].
    exfalso; exact (Hlast t ltac:(lia) HtN Hv). }
  apply (no_late_last_fire tm B Hbound q s ltac:(lia)).
  split; [exact Hvs|].
  intros u Hsu.
  destruct (le_lt_dec u N) as [HuN|HuN].
  - exact (Hlast u Hsu HuN).
  - exact (Hquiet u ltac:(lia)).
Qed.

Print Assumptions late_instruction_not_eventually_quiet.

Theorem wait_tr_decides_quasihalting : forall B w,
  BBBT4_is B -> WaitBoundTr B w -> forall tm,
  (QuasiHaltsTr tm <->
   exists q, (exists t, t < B /\ FiresAt tm q t) /\
     (forall t, B <= t -> t <= B+w -> ~ FiresAt tm q t)).
Proof.
  intros B w Hbbb Hwait tm.
  assert (Hbound : QHBoundTr B tm).
  { intros q s Hlast.
    destruct Hbbb as [_ Hupper].
    apply (Hupper tm (S s)).
    exists q, s; split; [exact Hlast|reflexivity]. }
  split.
  - intros (q & (t & Hv) & N & Hquiet).
    exists q; split.
    + exists t; split; [|exact Hv].
      destruct (lt_dec t B) as [Ht|Ht]; [exact Ht|].
      exfalso.
      assert (Hfuture : FutureBeepTr tm q B).
      { exists t; split; [lia|exact Hv]. }
      exact (late_instruction_not_eventually_quiet tm q B Hbound Hfuture N Hquiet).
    + intros u Hlo _ Hvu.
      apply (late_instruction_not_eventually_quiet tm q B Hbound
        (ex_intro _ u (conj Hlo Hvu)) N Hquiet).
  - intros (q & (t & Ht & Hv) & Hwindow).
    exists q; split.
    + exists t; exact Hv.
    + exists B.
      apply (proj1 (waitTr_silence_decision B w Hwait tm q)).
      exact Hwindow.
Qed.

Print Assumptions wait_tr_decides_quasihalting.
