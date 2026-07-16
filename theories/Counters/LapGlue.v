(** * LapGlue: monotone-counter laps imply never-quasihalting.

    The closer for the counter families (SCOPING section 5 phase 5):
    an anchor family [Cf : positive -> cconf] with

    - a bootstrap: the blank tape reaches (the denotation of) [Cf p0];
    - a lap: from every [Cf p] (p >= p0) the run reaches [Cf (succ p)]
      in at least one step, up to blank padding ([lift] equality);
    - visits: from every [Cf p], every state is reachable at some
      offset

    never quasihalts: the laps chain forever (the counter grows
    without bound), the global step index of the [k]-th anchor is at
    least [k], and each anchor launches a visit to every state --
    so every state is visited at unboundedly large indices, which is
    [NeverQuasiHaltsSt] verbatim (for visited AND unvisited states,
    hence a fortiori for the visited ones the definition ranges
    over).

    The lap premise is stated up to [lift] because an overflow lap
    (counter 2^j - 1 -> 2^j) leaves one freshly-blanked cell beyond
    the new working area: the reached configuration equals the next
    anchor only after stripping that trailing blank
    ([WTape.lift_app_blank]). *)

From Coq Require Import Arith Lia List PArith.
From BBB4 Require Import BBB4_Statement CTape.
Import ListNotations.

Section Glue.

Variable tm : TM.
Variable Cf : positive -> cconf.
Variable p0 : positive.

Hypothesis Hboot : exists t0, stepn tm t0 InitES = Some (lift (Cf p0)).
Hypothesis Hlap : forall p, (p0 <= p)%positive ->
  exists n c', csteps tm n (Cf p) = Some c' /\
               lift c' = lift (Cf (Pos.succ p)) /\ 0 < n.
Hypothesis Hvis : forall p q, (p0 <= p)%positive ->
  exists k c, csteps tm k (Cf p) = Some c /\ fst c = q.

(** The k-th anchor is reached at a global index of at least k. *)
Lemma glue_reach : forall k, exists T p, (p0 <= p)%positive /\ k <= T /\
  stepn tm T InitES = Some (lift (Cf p)).
Proof.
  induction k.
  - destruct Hboot as (t0 & H0).
    exists t0, p0. split; [apply Pos.le_refl|]. split; [lia | exact H0].
  - destruct IHk as (T & p & Hp & HT & Hstep).
    destruct (Hlap p Hp) as (n & c' & Hrun & Hlift & Hn).
    exists (T + n), (Pos.succ p).
    split.
    { eapply Pos.le_trans; [exact Hp|].
      apply Pos.lt_le_incl, Pos.lt_succ_diag_r. }
    split; [lia|].
    rewrite stepn_add, Hstep.
    rewrite (csteps_lift _ _ _ _ Hrun), Hlift.
    reflexivity.
Qed.

Theorem glue_neverqh : NeverQuasiHaltsSt tm.
Proof.
  intros q _ N.
  destruct (glue_reach N) as (T & p & Hp & HN & Hstep).
  destruct (Hvis p q Hp) as (k & c & Hc & Hqc).
  exists (T + k). split; [lia|].
  exists (lift c). split.
  - rewrite stepn_add, Hstep. apply csteps_lift; exact Hc.
  - rewrite lift_state. exact Hqc.
Qed.

End Glue.
