(** * DRZ6_1RB0RD_1LB1LC_1RC0RA_0LB1RD: Drozd's sixth core row, boarded BY HAND.

    Machine `1RB0RD_1LB1LC_1RC0RA_0LB1RD` -- the LAST undecided (4,2) core
    row, filed `-` / `no-anchor` / `-` / `no overflow phase at K=6` in
    `tools/closeout/residue_map.tsv`.  The `no-anchor` verdict is a statement
    about `digit_words`, not about the tape: the row has an exact anchor, and
    a DENSE one.

    ** The reset family is not the anchor

    The family the row is usually described by is the reset family

      R k = (StC, ([], S0, rep [S1] k)),

    visited only at k = 2, 3 (mod 4), booting at R 2 after three steps, with
    half-laps  R(4i+2) -> R(4i+3)  in  2^(2i+3) - 1  and  R(4i+3) -> R(4i+6)
    in  48*4^i - 6i - 15  (`tools/counters/drz6lap.py`: 14 visits, 0
    non-unary, both closed forms exact on all 13 measured half-laps).  Both
    half-laps are EXPONENTIAL in i, so no `Checkers/LapDecider.v` arm reaches
    them -- arms are affine -- and `emit_lapcert.py`'s refusal was correct.

    But `Counters/LapGlueNeverIx.glue_neverqh_ix` takes an ARBITRARY index
    type, so the anchor family need not be the sparse one.  Measured over
    300,000 steps (`tools/counters/drz6land.py`), the configuration class

      E l = (StD, (l, S0, []))            -- state D reading blank

    recurs with a MAXIMUM GAP OF 56 over that window, and its right list is
    LITERALLY EMPTY at every one of 37,516 visits.  (The gap is not a
    constant -- it is `2z+4` in the leading zero-run `z` -- but it is the only
    class that is polynomial where the other seven are exponential.)

    Be precise about what that buys: it does NOT make the lap bounded.  The
    family below still has laps of 36, 198, 864, 3546, ... steps, containing
    5, 26, 110, 446, ... macro steps.  What `E` gives is a COORDINATE SYSTEM
    in which this row's macro system CLOSES -- three rules, closed form,
    generic context -- where the same system read at `StA` does not
    (`docs/WAVE38_REST_FOUR.md` SS4 got five rules and stopped on the sixth,
    the leftward sweep; at `E` that sweep is not a rule at all, it sits inside
    every macro step as one `WTape.cycL` over `rep [S0] z`).  The exponential
    then rides on an induction over three rules instead of on new mathematics
    per gap.

    ** The three rules

    With  l = rep [S0] z ++ S1 :: l2  head-outward, the `E`-to-`E` law is

      (i)   l2 = S1 :: X       E l -> E (rep [S1] z ++ S0::S0::X)        2z+4
      (ii)  chd l2 = S0, z>0   E l -> E (rep [S1] (z-1) ++ S0::S0::S1::ctl l2)
                                                                         2z+4
      (iii) chd l2 = S0, z=0   E l -> E (S0::S0::S1::S1:: ctl l2)          10

    -- three branches, checked against the raw simulator on all 37,515
    landmark transitions with ZERO mismatches, branch counts 37432 / 76 / 7
    (`tools/counters/drz6lem.py`).  Each rule is at most one leftward
    `WTape.cycL` sweep, one rightward `WTape.cycR` sweep and five single
    steps; (iii) is ten single steps and no sweep.

    THE OVERFLOW CASE has its own cost AND its own SHAPE here: rule (iii) is
    the only one that reads the cell PAST the head's run, and the
    unknown-context probe catches it -- run with an unknown right tail it
    aborts at step 5, where `A0 = 1RB` carries the head onto the cell past the
    run -- and `A0` is the transition no other branch uses (it fires 8 times
    in 300,000 steps).  So (iii) is stated with the
    EXPLICIT empty right list that the landmark always carries, while (i) and
    (ii) tolerate a generic tail.  That is a fourth outcome for
    `docs/LADDER_PLAN.md`'s overflow question (SS4y: its own cost; SS4z:
    shared; #126: its own plus a third branch; here: its own cost AND the
    only branch that is not tail-generic).

    ** The family

    Writing  G z = E (rep [S0] z ++ [S1]),  the anchor is

      Cf t = G (4t+1)

    and the lap  Cf t -> Cf (S t)  is six composed pieces, every one of them
    generic in its context -- there is NO invariant on the left word anywhere
    in this file:

      G(2b+1)      -> G(2b+2)          (ii) ; Zdown b
      G(4t+2)      -> Q (2t) 0         (ii) ; Zdown 2t
      Q (S m) j    -> Q m (S j)        (ii) ; Zdown m
      Q 0 j        -> K 0 j            (iii) ; (i) ; Zdown 1
      K s (S(S i)) -> K (S s) i        (ii) ; Zdown ; (i) ; Zdown
      K s 0         = G (4s+5)

    with  Q m j = E (rep [S0] (2m) ++ [S1;S0;S0;S1] ++ rep [S0;S1] j)  and
    K s i = E (rep [S0] (4s+5) ++ S1 :: rep [S0;S1] i).  `Zdown a` is the
    DESCENDING BINARY CASCADE -- an all-ones digit word of `a` two-cell digits
    counting down to zero -- and it is three lines,

      Zdown (S a) = Zdown a ; (i) at z = 2a ; Zdown a,

    because in `E`-coordinates a decrement IS rule (i).  This is the nesting
    `Counters/Bin3Lap.v` is the template for, and it is the ONLY induction in
    the row that is not linear.

    Boot: the blank tape reaches `Cf 1 = G 5` at step 36.  Liveness: all four
    states occur in every lap (0 of 6 measured full laps miss one), and from
    `Cf t` they are reached at offsets 0 / 1 / 4t+3 / 4t+5, so the closer is
    the plain never-quasihalting one and the theorem is `NeverQuasiHaltsSt`.

    Differentially validated against the raw simulator before any proof:
    every rule in single cells over an UNKNOWN context, aborting on the first
    unknown read (`tools/counters/drz6lem.py`), and every arrow of the chain
    above run on the real machine and compared cell for cell
    (`tools/counters/drz6chain.py`).
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)

From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlueNeverIx.
Import ListNotations.

Definition mk_drz6 (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).
Local Notation mk := mk_drz6.

Definition tm_1RB0RD_1LB1LC_1RC0RA_0LB1RD : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DR StD
  | StB, S0 => mk S1 DL StB | StB, S1 => mk S1 DL StC
  | StC, S0 => mk S1 DR StC | StC, S1 => mk S0 DR StA
  | StD, S0 => mk S0 DL StB | StD, S1 => mk S1 DR StD end.
Local Notation tm := tm_1RB0RD_1LB1LC_1RC0RA_0LB1RD.

(** The landmark: state D reading blank, right list literally empty. *)
Definition E_drz6 (l : list Sym) : cconf := (StD, (l, S0, [])).
Local Notation E := E_drz6.

(** ** Rep algebra

    Two cells of a digit peel off the OUTER end of a run, which is the end the
    cascade consumes.  Stated as an [app] rewrite so the context [X] stays
    untouched. *)

Lemma rep2_peel : forall (x : Sym) a X,
  rep [x] (2 * S a) ++ X = rep [x] (2 * a) ++ x :: x :: X.
Proof.
  intros x a X.
  replace (2 * S a) with (2 * a + 2) by lia.
  rewrite rep_add, <- app_assoc. reflexivity.
Qed.

Lemma rep1_peel : forall (x : Sym) a X,
  rep [x] (S a) ++ X = rep [x] a ++ x :: X.
Proof.
  intros x a X.
  replace (S a) with (a + 1) by lia.
  rewrite rep_add, <- app_assoc. reflexivity.
Qed.

Lemma rep_grow2 : forall (x : Sym) a X,
  rep [x] a ++ x :: x :: X = rep [x] (2 + a) ++ X.
Proof.
  intros x a X.
  replace (2 + a) with (a + 2) by lia.
  rewrite rep_add, <- app_assoc. reflexivity.
Qed.

Lemma rep01_cons : forall j,
  rep [S0; S1] (S j) = S0 :: S1 :: rep [S0; S1] j.
Proof. reflexivity. Qed.

(** ** The two sweeps

    Both are [WTape] repetition cycles over a one-cell unit. *)

Lemma sweepD : forall k L R,
  csteps tm k (StD, (L, S1, rep [S1] k ++ R))
  = Some (StD, (rep [S1] k ++ L, S1, R)).
Proof.
  intros k L R.
  assert (Hu : wsteps true true tm 1 (StD, ([], S1, [S1]))
               = Some (StD, ([S1], S1, []))) by reflexivity.
  pose proof (cycR tm 1 StD S1 [S1] [S1] Hu k L R) as H.
  rewrite Nat.mul_1_l in H. exact H.
Qed.

Lemma sweepB : forall k L R,
  csteps tm k (StB, (rep [S0] k ++ L, S0, R))
  = Some (StB, (L, S0, rep [S1] k ++ R)).
Proof.
  intros k L R.
  assert (Hu : wsteps true true tm 1 (StB, ([S0], S0, []))
               = Some (StB, ([], S0, [] ++ [S1]))) by reflexivity.
  pose proof (cycL tm 1 StB S0 [S0] [] [S1] Hu k L R) as H.
  rewrite Nat.mul_1_l in H. cbn [app] in H. exact H.
Qed.

(** ** The three single-cell rules

    Stated against the probe before being proved; see the header. *)

Lemma repS_cons : forall (x : Sym) n Y, rep [x] (S n) ++ Y = x :: (rep [x] n ++ Y).
Proof. reflexivity. Qed.

Ltac drz6_run :=
  cbn [csteps cstep ctape_move chd ctl E_drz6
       tm_1RB0RD_1LB1LC_1RC0RA_0LB1RD mk_drz6 t_next t_dir t_write].

(** (i) a digit that is set becomes clear, and the borrow below it refills. *)
Lemma rule_i : forall z X,
  csteps tm (2 * z + 4) (E (rep [S0] z ++ S1 :: S1 :: X))
  = Some (E (rep [S1] z ++ S0 :: S0 :: X)).
Proof.
  intros [|z] X.
  - reflexivity.
  - rewrite (repS_cons S0 z (S1 :: S1 :: X)), (repS_cons S1 z (S0 :: S0 :: X)).
    replace (2 * S z + 4) with (1 + (z + (4 + (z + 1)))) by lia.
    rewrite csteps_add; drz6_run.
    rewrite csteps_add, sweepB.
    rewrite csteps_add; drz6_run.
    rewrite csteps_add, sweepD.
    drz6_run. reflexivity.
Qed.

(** (ii) the borrow runs off the bottom of the word and re-seeds one digit. *)
Lemma rule_ii : forall z l2, chd l2 = S0 ->
  csteps tm (2 * z + 6) (E (rep [S0] (S z) ++ S1 :: l2))
  = Some (E (rep [S1] z ++ S0 :: S0 :: S1 :: ctl l2)).
Proof.
  intros z l2 Hl2.
  destruct l2 as [|a l3]; [ | cbn [chd] in Hl2; subst a ]; cbn [chd ctl];
    destruct z as [|z].
  1,3: reflexivity.
  all: rewrite (repS_cons S0 (S z)); rewrite (repS_cons S1 z);
       replace (2 * S z + 6) with (1 + (S z + (5 + (z + 1)))) by lia;
       rewrite csteps_add; drz6_run;
       rewrite csteps_add, sweepB;
       rewrite (repS_cons S1 z [S0]);
       rewrite csteps_add; drz6_run;
       rewrite csteps_add, sweepD;
       drz6_run; reflexivity.
Qed.

(** (iii) the borrow runs off the bottom with no run under it: the only
    branch that fires [A0 = 1RB], and the only one that reads the cell past
    the head, so it needs the landmark's LITERALLY EMPTY right list. *)
Lemma rule_iii : forall l2, chd l2 = S0 ->
  csteps tm 10 (E (S1 :: l2)) = Some (E (S0 :: S0 :: S1 :: S1 :: ctl l2)).
Proof.
  intros l2 Hl2.
  destruct l2 as [|a l3]; [ | cbn [chd] in Hl2; subst a ];
    cbn [chd ctl]; reflexivity.
Qed.

(** ** Reachability, existentially in the step count

    [glue_neverqh_ix]'s lap premise quantifies the step count away, so neither
    closed form of the header ever has to be written down. *)

Definition Rch (c c' : cconf) : Prop := exists n, csteps tm n c = Some c'.

Lemma Rch_refl : forall c, Rch c c.
Proof. intro c. exists 0. reflexivity. Qed.

Lemma Rch_of : forall n c c', csteps tm n c = Some c' -> Rch c c'.
Proof. intros n c c' H. exists n. exact H. Qed.

Lemma Rch_trans : forall a b c, Rch a b -> Rch b c -> Rch a c.
Proof.
  intros a b c (n1 & H1) (n2 & H2). exists (n1 + n2).
  exact (csteps_chain tm n1 n2 a b c H1 H2).
Qed.

Lemma rep_split : forall (x : Sym) a b Y,
  rep [x] (a + b) ++ Y = rep [x] a ++ rep [x] b ++ Y.
Proof. intros. rewrite rep_add, <- app_assoc. reflexivity. Qed.

(** Two freshly cleared cells join the run below them. *)
Lemma rep_absorb2 : forall (x : Sym) a b Y, b = a + 2 ->
  rep [x] a ++ x :: x :: Y = rep [x] b ++ Y.
Proof.
  intros x a b Y ->. rewrite (rep_split x a 2 Y). cbn [rep app]. reflexivity.
Qed.

(** ** The descending binary cascade

    An all-ones digit word of [a] two-cell digits counts down to zero.  In
    [E]-coordinates a decrement IS rule (i), so the doubling is three lines
    and the context [X] never moves. *)

Lemma Zdown : forall a X,
  Rch (E (rep [S1] (2 * a) ++ X)) (E (rep [S0] (2 * a) ++ X)).
Proof.
  induction a as [|a IH]; intro X.
  - apply Rch_refl.
  - rewrite (rep2_peel S1 a X), (rep2_peel S0 a X).
    eapply Rch_trans; [apply (IH (S1 :: S1 :: X)) |].
    eapply Rch_trans; [apply (Rch_of _ _ _ (rule_i (2 * a) X)) |].
    apply (IH (S0 :: S0 :: X)).
Qed.

(** The cascade at a count that is even for an arithmetic reason. *)
Lemma Zdown_at : forall n a X, n = 2 * a ->
  Rch (E (rep [S1] n ++ X)) (E (rep [S0] n ++ X)).
Proof. intros n a X ->. apply Zdown. Qed.

(** ** The three shapes of the lap *)

Definition G_drz6 (z : nat) : cconf := E (rep [S0] z ++ [S1]).
Definition Q_drz6 (m j : nat) : cconf :=
  E (rep [S0] (2 * m) ++ S1 :: S0 :: S0 :: S1 :: rep [S0; S1] j).
Definition K_drz6 (s i : nat) : cconf :=
  E (rep [S0] (4 * s + 5) ++ S1 :: rep [S0; S1] i).
Definition Cf_drz6 (t : nat) : cconf := G_drz6 (4 * t + 1).

Local Notation G := G_drz6.
Local Notation Q := Q_drz6.
Local Notation K := K_drz6.
Local Notation Cf := Cf_drz6.

(** The odd half-lap: one (ii) and one cascade.  This is the piece that
    carries the lap's POSITIVITY. *)
Lemma Godd : forall b, exists n, 0 < n /\
  csteps tm n (G (2 * b + 1)) = Some (G (2 * b + 2)).
Proof.
  intro b.
  assert (HG : G (2 * b + 2) = E (rep [S0] (2 * b) ++ [S0; S0; S1])).
  { unfold G_drz6. f_equal.
    rewrite (rep_split S0 (2 * b) 2 [S1]). cbn [rep app]. reflexivity. }
  rewrite HG.
  destruct (Zdown b [S0; S0; S1]) as (n2 & H2).
  exists (2 * (2 * b) + 6 + n2). split; [lia|].
  eapply csteps_chain; [| exact H2].
  unfold G_drz6. replace (2 * b + 1) with (S (2 * b)) by lia.
  pose proof (rule_ii (2 * b) [] eq_refl) as HR. cbn [ctl] in HR. exact HR.
Qed.

(** The even half-lap, in four pieces. *)

Lemma GtoQ : forall t, Rch (G (4 * t + 2)) (Q (2 * t) 0).
Proof.
  intro t.
  unfold G_drz6, Q_drz6.
  replace (4 * t + 2) with (S (4 * t + 1)) by lia.
  eapply Rch_trans.
  { apply (Rch_of _ _ _ (rule_ii (4 * t + 1) [] eq_refl)). }
  cbn [ctl].
  rewrite (rep_split S1 (4 * t) 1 (S0 :: S0 :: S1 :: nil)).
  cbn [rep app].
  replace (2 * (2 * t)) with (4 * t) by lia.
  cbn [rep app].
  apply (Zdown_at (4 * t) (2 * t) [S1; S0; S0; S1]). lia.
Qed.

Lemma Qstep : forall m j, Rch (Q (S m) j) (Q m (S j)).
Proof.
  intros m j.
  unfold Q_drz6.
  replace (2 * S m) with (S (2 * m + 1)) by lia.
  eapply Rch_trans.
  { apply (Rch_of _ _ _
      (rule_ii (2 * m + 1) (S0 :: S0 :: S1 :: rep [S0; S1] j) eq_refl)). }
  cbn [ctl].
  rewrite (rep_split S1 (2 * m) 1
             (S0 :: S0 :: S1 :: S0 :: S1 :: rep [S0; S1] j)).
  cbn [rep app].
  apply (Zdown_at (2 * m) m
           (S1 :: S0 :: S0 :: S1 :: S0 :: S1 :: rep [S0; S1] j)). lia.
Qed.

Lemma Qchain : forall m j, Rch (Q m j) (Q 0 (m + j)).
Proof.
  induction m as [|m IH]; intro j.
  - cbn [Nat.add]. apply Rch_refl.
  - eapply Rch_trans; [apply Qstep |].
    replace (S m + j) with (m + S j) by lia.
    apply IH.
Qed.

Lemma QtoK : forall j, Rch (Q 0 j) (K 0 j).
Proof.
  intro j.
  unfold Q_drz6, K_drz6.
  cbn [Nat.mul rep app].
  eapply Rch_trans.
  { apply (Rch_of _ _ _
      (rule_iii (S0 :: S0 :: S1 :: rep [S0; S1] j) eq_refl)). }
  cbn [ctl].
  eapply Rch_trans.
  { apply (Rch_of _ _ _ (rule_i 2 (S0 :: S1 :: rep [S0; S1] j))). }
  cbn [rep app].
  eapply Rch_trans.
  { apply (Zdown_at 2 1 (S0 :: S0 :: S0 :: S1 :: rep [S0; S1] j)). lia. }
  cbn [rep app]. apply Rch_refl.
Qed.

Lemma Kstep : forall s i, Rch (K s (S (S i))) (K (S s) i).
Proof.
  intros s i.
  unfold K_drz6.
  replace (4 * s + 5) with (S (4 * s + 4)) by lia.
  eapply Rch_trans.
  { apply (Rch_of _ _ _
      (rule_ii (4 * s + 4) (rep [S0; S1] (S (S i))) eq_refl)). }
  cbn [rep app ctl].
  eapply Rch_trans.
  { apply (Zdown_at (4 * s + 4) (2 * s + 2)
             (S0 :: S0 :: S1 :: S1 :: S0 :: S1 :: rep [S0; S1] i)); lia. }
  rewrite (rep_absorb2 S0 (4 * s + 4) (4 * s + 6)
             (S1 :: S1 :: S0 :: S1 :: rep [S0; S1] i) ltac:(lia)).
  eapply Rch_trans.
  { apply (Rch_of _ _ _
      (rule_i (4 * s + 6) (S0 :: S1 :: rep [S0; S1] i))). }
  eapply Rch_trans.
  { apply (Zdown_at (4 * s + 6) (2 * s + 3)
             (S0 :: S0 :: S0 :: S1 :: rep [S0; S1] i)); lia. }
  rewrite (rep_absorb2 S0 (4 * s + 6) (4 * s + 8)
             (S0 :: S1 :: rep [S0; S1] i) ltac:(lia)).
  replace (4 * S s + 5) with (S (4 * s + 8)) by lia.
  rewrite (rep1_peel S0 (4 * s + 8) (S1 :: rep [S0; S1] i)).
  apply Rch_refl.
Qed.

Lemma Kzero : forall s, K s 0 = G (4 * s + 5).
Proof. intro s. unfold K_drz6, G_drz6. cbn [rep app]. reflexivity. Qed.

Lemma Kchain : forall s i, Rch (K s (2 * i)) (K (s + i) 0).
Proof.
  intros s i. revert s.
  induction i as [|i IH]; intro s.
  - replace (s + 0) with s by lia. cbn [Nat.mul]. apply Rch_refl.
  - replace (2 * S i) with (S (S (2 * i))) by lia.
    eapply Rch_trans; [apply Kstep |].
    replace (s + S i) with (S s + i) by lia.
    apply IH.
Qed.

(** ** The lap

    [Cf t = G (4t+1)] and the two half-laps compose.  Positivity comes from
    [Godd]'s rule (ii), whose cost [2*(4t)+6] is never zero. *)

Lemma lap : forall t, exists n, 0 < n /\ csteps tm n (Cf t) = Some (Cf (S t)).
Proof.
  intro t.
  assert (HA : Cf t = G (2 * (2 * t) + 1)) by (unfold Cf_drz6; f_equal; lia).
  assert (HB : G (2 * (2 * t) + 2) = G (4 * t + 2)) by (f_equal; lia).
  assert (HC : K (0 + t) 0 = Cf (S t))
    by (rewrite Kzero; unfold Cf_drz6; f_equal; lia).
  assert (Hrest : Rch (G (4 * t + 2)) (Cf (S t))).
  { eapply Rch_trans; [apply GtoQ |].
    eapply Rch_trans; [apply (Qchain (2 * t) 0) |].
    replace (2 * t + 0) with (2 * t) by lia.
    eapply Rch_trans; [apply QtoK |].
    eapply Rch_trans; [apply (Kchain 0 t) |].
    rewrite HC. apply Rch_refl. }
  destruct (Godd (2 * t)) as (n1 & Hn1 & H1).
  destruct Hrest as (n2 & H2).
  exists (n1 + n2). split; [lia|].
  rewrite HA. eapply csteps_chain; [exact H1 |]. rewrite HB. exact H2.
Qed.

(** ** Bootstrap

    The blank tape reaches [Cf 1 = G 5 = (StD, ([S0;S0;S0;S0;S0;S1], S0, []))]
    at step 36 -- the first landmark of the family, with no offset. *)

Lemma boot : exists t0, stepn tm t0 InitES = Some (lift (Cf 1)).
Proof.
  exists 36.
  assert (H : csteps tm 36 c0 = Some (Cf 1)) by (vm_compute; reflexivity).
  rewrite <- lift_c0, (csteps_lift _ _ _ _ H). reflexivity.
Qed.

(** ** Liveness

    [glue_neverqh]'s [Hvis] premise, read off the head of the lap: from
    [Cf t] the four states occur at offsets 0, 1, 4t+3 and 4t+5 -- measured
    first, then proved (`tools/counters/drz6chain.py`). *)

Lemma vis_run : forall t,
  csteps tm 1 (Cf t) = Some (StB, (rep [S0] (4 * t) ++ [S1], S0, [S0]))
  /\ csteps tm (1 + (4 * t + 2)) (Cf t)
     = Some (StC, ([], S0, S1 :: S1 :: (rep [S1] (4 * t) ++ [S0])))
  /\ csteps tm (1 + (4 * t + 4)) (Cf t)
     = Some (StA, ([S0; S1], S1, rep [S1] (4 * t) ++ [S0])).
Proof.
  intro t.
  unfold Cf_drz6, G_drz6.
  replace (4 * t + 1) with (S (4 * t)) by lia.
  rewrite (repS_cons S0 (4 * t) [S1]).
  split; [drz6_run; reflexivity | split].
  - rewrite csteps_add; drz6_run.
    rewrite csteps_add, sweepB. drz6_run. reflexivity.
  - rewrite csteps_add; drz6_run.
    rewrite csteps_add, sweepB. drz6_run. reflexivity.
Qed.

Lemma vis : forall t q, exists k c, csteps tm k (Cf t) = Some c /\ fst c = q.
Proof.
  intros t q. destruct (vis_run t) as (H1 & H2 & H3). destruct q.
  - exists (1 + (4 * t + 4)). eexists. split; [exact H3 | reflexivity].
  - exists 1. eexists. split; [exact H1 | reflexivity].
  - exists (1 + (4 * t + 2)). eexists. split; [exact H2 | reflexivity].
  - exists 0. eexists. split; reflexivity.
Qed.

(** ** The theorem *)

Theorem nqh_1RB0RD_1LB1LC_1RC0RA_0LB1RD : NeverQuasiHaltsSt tm.
Proof.
  apply (glue_neverqh_ix tm nat S Cf 1).
  - exact boot.
  - intro t. destruct (lap t) as (n & Hn & H).
    exists n, (Cf (S t)). split; [exact H | split; [reflexivity | exact Hn]].
  - exact vis.
Qed.

Theorem nonhalt_1RB0RD_1LB1LC_1RC0RA_0LB1RD : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_1RB0RD_1LB1LC_1RC0RA_0LB1RD. Qed.
