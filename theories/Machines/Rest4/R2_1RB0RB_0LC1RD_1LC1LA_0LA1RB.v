(** * 1RB0RB_0LC1RD_1LC1LA_0LA1RB -- never quasihalts.

    Row 2 of [docs/WAVE38_REST_FOUR.md] ("the phi row"): a Fibonacci
    counter whose tape stays [log_phi t] cells wide.  The [NGramHist]
    closure covers [StC] and nothing else, and [ReachStI] certifies
    nothing beyond [StC] either, so no checker route opens; the row goes
    out through its macro system and [LiveAll.neverqh_of_live4], exactly
    as the write-up's section 3 laid out.

    THE MACRO SYSTEM (section 3a, on [cconf]).  The orbit keeps the
    right half-tape a bare unary run followed by a blank, so every
    [StA] configuration is

      Cf l s R Z = (StA, (l, s, rep [S1] R ++ S0 :: Z))

    with [l] the left half-tape (nearest cell first) and [Z] a tail no
    rule ever reaches.  Six rules, each starting and ending in [StA]:

      (1) s=S0, R=0              -> (ctl l, chd l, 1)            3    steps
      (2) s=S1, R=0, l=0^j 1 l1  -> (ctl l1, chd l1, j+2)        j+4  steps
      (3) s=S0, R=2k+1           -> (1^(2k+1) ++ l, S1, 0)       2k+3 steps
      (4) s=S0, R=2k+2           -> (1^(2k+1) ++ l, S1, 1)       2k+5 steps
      (5) s=S1, R=2k+1           -> (1^(2k) ++ S0::l, S1, 0)     2k+3 steps
      (6) s=S1, R=2k+2           -> (1^(2k) ++ S0::l, S1, 1)     2k+5 steps

    Rule 2 is PARTIAL: it needs an [S1] in [l].  On an all-blank left
    half the machine sweeps left in [StC] for ever and only [StC]
    recurs -- a genuine quasihalt, so totality is a real obligation.

    THE INVARIANT (section 3c).  Every rule changes [ones l + sval s]
    by an EVEN amount: rule 1 moves the head cell into [s], rule 2
    consumes one [S1] from [l] and one from [s] (its output head cell
    moves the difference into [s] again), and rules 3-6 move the whole
    right-hand run onto [l] -- [2k+1] ones and a head bit, or [2k] ones
    and an unchanged head.  So the parity of [ones l + sval s] is a
    run invariant ([Ev], preserved by [g_step]).  A configuration where
    rule 2 is stuck has [ones l = 0] and [s = S1], i.e. parity ODD; the
    orbit boots into [Cf [] S0 1 []] at parity EVEN.  Hence the macro
    system is total on the orbit and never sticks.

    LIVENESS (section 3b).  [StB] is step 1 of every rule; [StA] is the
    macro boundary; [StD] is step 2 whenever [R >= 1], and both [R = 0]
    rules land at [R' >= 1]; [StC] is step 2 whenever [R = 0], rules
    3/5 land at [R' = 0], and rules 4/6 land at [R' = 1] from which
    rule 5 (k = 0) lands at [R'' = 0].  So every state is hit within
    three macro steps of any even-parity configuration, and
    [neverqh_of_live4] closes the row. *)

From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape BinVal.
From BBB4.Checkers Require Import LiveAll.
Import ListNotations.

Definition tm_1RB0RB_0LC1RD_1LC1LA_0LA1RB : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S0 DR StB)
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StD)
  | StC, S0 => Some (mkTrans S1 DL StC)
  | StC, S1 => Some (mkTrans S1 DL StA)
  | StD, S0 => Some (mkTrans S0 DL StA)
  | StD, S1 => Some (mkTrans S1 DR StB)
  end.

Local Notation tm := tm_1RB0RB_0LC1RD_1LC1LA_0LA1RB.

(** ** The shape and the six macro rules *)

Definition Cf (l : list Sym) (s : Sym) (R : nat) (Z : list Sym) : cconf :=
  (StA, (l, s, rep [S1] R ++ S0 :: Z)).

(** The rightward sweep of rules 3-6 crosses the unary run two cells
    per [StB]-[StD] pair, rewriting [1 1] to [1 1]. *)
Lemma unitBD : wsteps true true tm 2 (StB, ([], S1, [S1; S1]))
             = Some (StB, ([S1; S1], S1, [])).
Proof. reflexivity. Qed.

Lemma sweepBD : forall k L R,
  csteps tm (2 * k) (StB, (L, S1, rep [S1; S1] k ++ R))
  = Some (StB, (rep [S1; S1] k ++ L, S1, R)).
Proof. exact (cycR tm 2 StB S1 [S1; S1] [S1; S1] unitBD). Qed.

(** Rule 2's leftward sweep crosses the blank run in [StC], writing
    ones. *)
Lemma unitC : wsteps true true tm 1 (StC, ([S0], S0, []))
            = Some (StC, ([], S0, [S1])).
Proof. reflexivity. Qed.

Lemma sweepC : forall k L R,
  csteps tm (1 * k) (StC, (rep [S0] k ++ L, S0, R))
  = Some (StC, (L, S0, rep [S1] k ++ R)).
Proof. exact (cycL tm 1 StC S0 [S0] [] [S1] unitC). Qed.

Lemma r1 : forall l Z,
  csteps tm 3 (Cf l S0 0 Z) = Some (Cf (ctl l) (chd l) 1 Z).
Proof. intros. unfold Cf. reflexivity. Qed.

Lemma r2 : forall j l1 Z,
  csteps tm (4 + j) (Cf (rep [S0] j ++ S1 :: l1) S1 0 Z)
  = Some (Cf (ctl l1) (chd l1) (S (S j)) Z).
Proof.
  intros j l1 Z.
  replace (4 + j) with (2 + (1 * j + 2)) by lia.
  eapply csteps_chain
    with (c1 := (StC, (rep [S0] j ++ S1 :: l1, S0, S0 :: Z))).
  - unfold Cf. reflexivity.
  - eapply csteps_chain
      with (c1 := (StC, (S1 :: l1, S0, rep [S1] j ++ S0 :: Z))).
    + apply sweepC.
    + unfold Cf. reflexivity.
Qed.

Lemma r3 : forall l k Z,
  csteps tm (3 + 2 * k) (Cf l S0 (S (2 * k)) Z)
  = Some (Cf (rep [S1] (2 * k) ++ S1 :: l) S1 0 Z).
Proof.
  intros l k Z.
  replace (3 + 2 * k) with (1 + (2 * k + 2)) by lia.
  eapply csteps_chain
    with (c1 := (StB, (S1 :: l, S1, rep [S1] (2 * k) ++ S0 :: Z))).
  - unfold Cf. reflexivity.
  - eapply csteps_chain
      with (c1 := (StB, (rep [S1] (2 * k) ++ S1 :: l, S1, S0 :: Z))).
    + rewrite <- (rep_dbl S1 k). apply sweepBD.
    + unfold Cf. reflexivity.
Qed.

Lemma r4 : forall l k Z,
  csteps tm (5 + 2 * k) (Cf l S0 (S (S (2 * k))) Z)
  = Some (Cf (rep [S1] (2 * k) ++ S1 :: l) S1 1 Z).
Proof.
  intros l k Z.
  replace (5 + 2 * k) with (1 + (2 * k + 4)) by lia.
  eapply csteps_chain
    with (c1 := (StB, (S1 :: l, S1, rep [S1] (2 * k) ++ S1 :: S0 :: Z))).
  - unfold Cf. rewrite <- (rep_slide S1 (2 * k) (S0 :: Z)). reflexivity.
  - eapply csteps_chain
      with (c1 := (StB, (rep [S1] (2 * k) ++ S1 :: l, S1, S1 :: S0 :: Z))).
    + rewrite <- (rep_dbl S1 k). apply sweepBD.
    + unfold Cf. reflexivity.
Qed.

Lemma r5 : forall l k Z,
  csteps tm (3 + 2 * k) (Cf l S1 (S (2 * k)) Z)
  = Some (Cf (rep [S1] (2 * k) ++ S0 :: l) S1 0 Z).
Proof.
  intros l k Z.
  replace (3 + 2 * k) with (1 + (2 * k + 2)) by lia.
  eapply csteps_chain
    with (c1 := (StB, (S0 :: l, S1, rep [S1] (2 * k) ++ S0 :: Z))).
  - unfold Cf. reflexivity.
  - eapply csteps_chain
      with (c1 := (StB, (rep [S1] (2 * k) ++ S0 :: l, S1, S0 :: Z))).
    + rewrite <- (rep_dbl S1 k). apply sweepBD.
    + unfold Cf. reflexivity.
Qed.

Lemma r6 : forall l k Z,
  csteps tm (5 + 2 * k) (Cf l S1 (S (S (2 * k))) Z)
  = Some (Cf (rep [S1] (2 * k) ++ S0 :: l) S1 1 Z).
Proof.
  intros l k Z.
  replace (5 + 2 * k) with (1 + (2 * k + 4)) by lia.
  eapply csteps_chain
    with (c1 := (StB, (S0 :: l, S1, rep [S1] (2 * k) ++ S1 :: S0 :: Z))).
  - unfold Cf. rewrite <- (rep_slide S1 (2 * k) (S0 :: Z)). reflexivity.
  - eapply csteps_chain
      with (c1 := (StB, (rep [S1] (2 * k) ++ S0 :: l, S1, S1 :: S0 :: Z))).
    + rewrite <- (rep_dbl S1 k). apply sweepBD.
    + unfold Cf. reflexivity.
Qed.

(** ** The parity invariant *)

Fixpoint ones (l : list Sym) : nat :=
  match l with [] => 0 | x :: t => sval x + ones t end.

Lemma ones_chd_ctl : forall l, ones l = sval (chd l) + ones (ctl l).
Proof. destruct l; reflexivity. Qed.

Lemma ones_app : forall a b, ones (a ++ b) = ones a + ones b.
Proof.
  induction a as [|x a IH]; intro b; cbn [ones app]; [reflexivity|].
  rewrite IH. lia.
Qed.

Lemma ones_rep1 : forall k, ones (rep [S1] k) = k.
Proof.
  induction k as [|k IH]; cbn [rep]; [reflexivity|].
  cbn [app ones sval]. lia.
Qed.

Lemma ones_rep0 : forall k, ones (rep [S0] k) = 0.
Proof.
  induction k as [|k IH]; cbn [rep]; [reflexivity|].
  cbn [app ones sval]. lia.
Qed.

(** [ones l + sval s] stays even for ever; a stuck rule-2 configuration
    has it odd ([ones l = 0], [s = S1]), so it never occurs. *)
Definition Ev (l : list Sym) (s : Sym) : Prop := EvenN (ones l + sval s).

Lemma ev_boot : Ev [] S0.
Proof. exact evenN_0. Qed.

(** An odd-ones word contains an [S1]: the decomposition rule 2 needs. *)
Lemma split_first_one : forall l, ones l <> 0 ->
  exists j l1, l = rep [S0] j ++ S1 :: l1.
Proof.
  induction l as [|x t IH]; intro H.
  - cbn [ones] in H. congruence.
  - destruct x.
    + cbn [ones sval] in H.
      destruct (IH ltac:(lia)) as (j & l1 & ->).
      exists (S j), l1. reflexivity.
    + exists 0, t. reflexivity.
Qed.

Lemma nat_split2 : forall n, (exists k, n = 2 * k) \/ (exists k, n = S (2 * k)).
Proof.
  induction n as [|n IH].
  - left. exists 0. reflexivity.
  - destruct IH as [[k ->] | [k ->]].
    + right. exists k. reflexivity.
    + left. exists (S k). lia.
Qed.

(** ** One macro step: total on [Ev], and [Ev]-preserving *)

Lemma g_step : forall l s R Z, Ev l s ->
  exists n l' s' R', 1 <= n
    /\ csteps tm n (Cf l s R Z) = Some (Cf l' s' R' Z)
    /\ Ev l' s'.
Proof.
  intros l s R Z HE.
  destruct s.
  - (* s = S0 *)
    destruct R as [|R0].
    + (* rule 1 *)
      exists 3, (ctl l), (chd l), 1.
      split; [lia | split; [apply r1 |]].
      destruct HE as [j Hj]; cbn [sval] in Hj.
      pose proof (ones_chd_ctl l) as Hoc.
      exists j. lia.
    + destruct (nat_split2 R0) as [[k ->] | [k ->]].
      * (* rule 3 *)
        exists (3 + 2 * k), (rep [S1] (2 * k) ++ S1 :: l), S1, 0.
        split; [lia | split; [apply r3 |]].
        destruct HE as [j Hj]; cbn [sval] in Hj.
        exists (k + j + 1). rewrite ones_app, ones_rep1.
        cbn [ones sval]. lia.
      * (* rule 4 *)
        exists (5 + 2 * k), (rep [S1] (2 * k) ++ S1 :: l), S1, 1.
        split; [lia | split; [apply r4 |]].
        destruct HE as [j Hj]; cbn [sval] in Hj.
        exists (k + j + 1). rewrite ones_app, ones_rep1.
        cbn [ones sval]. lia.
  - (* s = S1 *)
    destruct R as [|R0].
    + (* rule 2; [Ev] supplies the [S1] the guard needs *)
      assert (Hne : ones l <> 0).
      { intro H0. apply evenN_1.
        unfold Ev in HE. rewrite H0 in HE. exact HE. }
      destruct (split_first_one l Hne) as (j & l1 & ->).
      exists (4 + j), (ctl l1), (chd l1), (S (S j)).
      split; [lia | split; [apply r2 |]].
      destruct HE as [i Hi].
      rewrite ones_app, ones_rep0 in Hi; cbn [ones sval] in Hi.
      pose proof (ones_chd_ctl l1) as Hoc.
      exists (i - 1). lia.
    + destruct (nat_split2 R0) as [[k ->] | [k ->]].
      * (* rule 5 *)
        exists (3 + 2 * k), (rep [S1] (2 * k) ++ S0 :: l), S1, 0.
        split; [lia | split; [apply r5 |]].
        destruct HE as [j Hj]; cbn [sval] in Hj.
        exists (k + j). rewrite ones_app, ones_rep1.
        cbn [ones sval]. lia.
      * (* rule 6 *)
        exists (5 + 2 * k), (rep [S1] (2 * k) ++ S0 :: l), S1, 1.
        split; [lia | split; [apply r6 |]].
        destruct HE as [j Hj]; cbn [sval] in Hj.
        exists (k + j). rewrite ones_app, ones_rep1.
        cbn [ones sval]. lia.
Qed.

(** ** Each state is hit within three macro steps *)

Definition Hit (q : St) (c : cconf) : Prop :=
  exists n cc, 1 <= n /\ csteps tm n c = Some cc /\ fst cc = q.

Lemma hit_pre : forall q n c c',
  csteps tm n c = Some c' -> Hit q c' -> Hit q c.
Proof.
  intros q n c c' H (n' & cc & H1 & H2 & H3).
  exists (n + n'), cc. split; [lia|].
  split; [rewrite csteps_add, H; exact H2 | exact H3].
Qed.

(** [StB] is step 1 of every rule: both [StA] arms move right into it. *)
Lemma hitB : forall l s R Z, Hit StB (Cf l s R Z).
Proof.
  intros l s R Z.
  destruct s.
  - exists 1, (StB, (S1 :: l, chd (rep [S1] R ++ S0 :: Z),
                     ctl (rep [S1] R ++ S0 :: Z))).
    split; [lia|]. split; [unfold Cf; reflexivity | reflexivity].
  - exists 1, (StB, (S0 :: l, chd (rep [S1] R ++ S0 :: Z),
                     ctl (rep [S1] R ++ S0 :: Z))).
    split; [lia|]. split; [unfold Cf; reflexivity | reflexivity].
Qed.

(** At [R = 0] the second step reads the blank and drops into [StC]. *)
Lemma hitC0 : forall l s Z, Hit StC (Cf l s 0 Z).
Proof.
  intros l s Z.
  destruct s.
  - exists 2, (StC, (l, S1, S0 :: Z)).
    split; [lia|]. split; [unfold Cf; reflexivity | reflexivity].
  - exists 2, (StC, (l, S0, S0 :: Z)).
    split; [lia|]. split; [unfold Cf; reflexivity | reflexivity].
Qed.

(** At [R >= 1] the second step reads a run cell and enters [StD]. *)
Lemma hitDpos : forall l s R0 Z, Hit StD (Cf l s (S R0) Z).
Proof.
  intros l s R0 Z.
  destruct s.
  - exists 2, (StD, (S1 :: S1 :: l, chd (rep [S1] R0 ++ S0 :: Z),
                     ctl (rep [S1] R0 ++ S0 :: Z))).
    split; [lia|]. split; [unfold Cf; reflexivity | reflexivity].
  - exists 2, (StD, (S1 :: S0 :: l, chd (rep [S1] R0 ++ S0 :: Z),
                     ctl (rep [S1] R0 ++ S0 :: Z))).
    split; [lia|]. split; [unfold Cf; reflexivity | reflexivity].
Qed.

Lemma hitA : forall l s R Z, Ev l s -> Hit StA (Cf l s R Z).
Proof.
  intros l s R Z HE.
  destruct (g_step l s R Z HE) as (n & l' & s' & R' & Hn & Hc & _).
  exists n, (Cf l' s' R' Z).
  split; [exact Hn | split; [exact Hc | reflexivity]].
Qed.

Lemma hitD : forall l s R Z, Ev l s -> Hit StD (Cf l s R Z).
Proof.
  intros l s R Z HE.
  destruct R as [|R0]; [|apply hitDpos].
  destruct s.
  - (* rule 1 lands at R' = 1 *)
    eapply hit_pre; [apply r1 | apply (hitDpos _ _ 0)].
  - (* rule 2 lands at R' = j + 2 *)
    assert (Hne : ones l <> 0).
    { intro H0. apply evenN_1.
      unfold Ev in HE. rewrite H0 in HE. exact HE. }
    destruct (split_first_one l Hne) as (j & l1 & ->).
    eapply hit_pre; [apply r2 | apply (hitDpos _ _ (S j))].
Qed.

Lemma hitC : forall l s R Z, Ev l s -> Hit StC (Cf l s R Z).
Proof.
  intros l s R Z _.
  destruct R as [|R0]; [apply hitC0|].
  destruct (nat_split2 R0) as [[k ->] | [k ->]].
  - (* R odd: rules 3/5 land at R' = 0 *)
    destruct s.
    + eapply hit_pre; [apply r3 | apply hitC0].
    + eapply hit_pre; [apply r5 | apply hitC0].
  - (* R even: rules 4/6 land at R' = 1, rule 5 (k = 0) at R'' = 0 *)
    destruct s.
    + eapply hit_pre; [apply r4 |].
      eapply hit_pre; [apply (r5 _ 0) | apply hitC0].
    + eapply hit_pre; [apply r6 |].
      eapply hit_pre; [apply (r5 _ 0) | apply hitC0].
Qed.

(** ** Liveness at arbitrarily large indices *)

Lemma live_gen : forall q,
  (forall l s R Z, Ev l s -> Hit q (Cf l s R Z)) ->
  forall N l s R Z, Ev l s ->
  exists m cc, N <= m /\ csteps tm m (Cf l s R Z) = Some cc /\ fst cc = q.
Proof.
  intros q Hhit.
  induction N as [|N IHN]; intros l s R Z HE.
  - destruct (Hhit l s R Z HE) as (n & cc & H1 & H2 & H3).
    exists n, cc. split; [lia | split; assumption].
  - destruct (g_step l s R Z HE) as (n & l' & s' & R' & Hn & Hstep & HE').
    destruct (IHN l' s' R' Z HE') as (m & cc & Hm & Hc & Hq).
    exists (n + m), cc. split; [lia|].
    split; [rewrite csteps_add, Hstep; exact Hc | exact Hq].
Qed.

Lemma boot : csteps tm 3 c0 = Some (Cf [] S0 1 []).
Proof. reflexivity. Qed.

Lemma live_st : forall q,
  (forall l s R Z, Ev l s -> Hit q (Cf l s R Z)) -> LiveSt tm q.
Proof.
  intros q Hhit N.
  destruct (live_gen q Hhit N [] S0 1 [] ev_boot) as (m & cc & Hm & Hc & Hq).
  exists (3 + m). split; [lia|].
  exists (lift cc). split.
  - rewrite <- lift_c0. apply csteps_lift.
    rewrite csteps_add, boot. exact Hc.
  - rewrite lift_state. exact Hq.
Qed.

Lemma liveStA_1RB0RB_0LC1RD_1LC1LA_0LA1RB : LiveSt tm StA.
Proof. exact (live_st StA hitA). Qed.

Lemma liveStB_1RB0RB_0LC1RD_1LC1LA_0LA1RB : LiveSt tm StB.
Proof. apply live_st. intros l s R Z _. apply hitB. Qed.

Lemma liveStC_1RB0RB_0LC1RD_1LC1LA_0LA1RB : LiveSt tm StC.
Proof. exact (live_st StC hitC). Qed.

Lemma liveStD_1RB0RB_0LC1RD_1LC1LA_0LA1RB : LiveSt tm StD.
Proof. exact (live_st StD hitD). Qed.

(** ** The theorem *)

Theorem nqh_1RB0RB_0LC1RD_1LC1LA_0LA1RB :
  NeverQuasiHaltsSt tm_1RB0RB_0LC1RD_1LC1LA_0LA1RB.
Proof.
  exact (neverqh_of_live4 tm
           liveStA_1RB0RB_0LC1RD_1LC1LA_0LA1RB
           liveStB_1RB0RB_0LC1RD_1LC1LA_0LA1RB
           liveStC_1RB0RB_0LC1RD_1LC1LA_0LA1RB
           liveStD_1RB0RB_0LC1RD_1LC1LA_0LA1RB).
Qed.

Theorem nonhalt_1RB0RB_0LC1RD_1LC1LA_0LA1RB :
  NonHalt tm_1RB0RB_0LC1RD_1LC1LA_0LA1RB.
Proof.
  exact (nonhalt_of_live tm StA liveStA_1RB0RB_0LC1RD_1LC1LA_0LA1RB).
Qed.
