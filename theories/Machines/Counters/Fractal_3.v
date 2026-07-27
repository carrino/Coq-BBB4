(** * Fractal_3: the fractal machine #3, 1RB0LA_1LC0RD_0LB1LA_0RB1LA.

    The second of the two BBB `fractal` holdouts.  Like [Fractal_5] it
    has no upstream proof to port, and like [Fractal_5] it turns out to
    be a BINARY COUNTER WHOSE DIGITS ARE BLOCKS -- here two cells per
    digit instead of one.

    THE ANCHOR.  Blank-tape right-records occur at

      A(k) = (StB, (0^(2^k) ++ 1^(2^k), 0, []))       (left list, nearest first)

    i.e. the tape reads [1^(2^k) 0^(2^k)] with the head one cell past
    the last blank, at global step (9, 31, 111, 403, 1479, ...).  The
    lap A(k) -> A(k+1) costs [3*4^k + 4*3^k - 2^k] steps.  The [3^k]
    term is what rules out every affine certificate in the repo, and it
    is why [LapGlue]'s [exists n] lap obligation is the only shape this
    machine can meet.

    WHAT THE MACHINE IS DOING.  With the head at a blank in state [B],
    the left half-tape is always

      0^(2z+2) ++ 1 1 ++ b_0^2 ++ b_1^4 ++ .. ++ b_{j-1}^(2^j)

    with [b_{j-1}..b_0] the binary digits of [z]: digit [i] occupies
    [2^(i+1)] cells.  One macro-step increments the counter and eats
    exactly two blanks on the right.  A carry of length [2m] cells
    costs [Theta(m^2) + Theta(3^log m)] and is the machine one level
    down -- the fractal.

    THE PROOF mirrors [Fractal_5] exactly.  Straight-line gadgets
    ([phLD] the left drift, [turnA] the left turnaround, [g1] the
    one-digit bump, [phBRun]/[phBSkip] the right sweeps, [close3] the
    period closer, [inc3_1] the carry-free increment), then a two-way
    mutual recursion closed by one induction on the level:

      SW3n e : run the counter through a full period
      INC3n e : one carry of full period length

    where [SW3n (e + S (S e))] is built from [SW3n e] (twice),
    [inc3_1] and [INC3n e], and [INC3n e] is built from the gadgets and
    [SW3n e].  Every dependency is one level down, so a single
    [induction] discharges both.

    Differentially validated against a plain simulator for every level
    up to 2^6 and for random left/right frames.

    Axiom footprint: [functional_extensionality_dep] only (inherited
    from [CTape]; this file adds none). *)

From Coq Require Import Arith Lia List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB0LA_1LC0RD_0LB1LA_0RB1LA *)
Definition tm_f3 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DL StA
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S0 DR StD
  | StC, S0 => mk S0 DL StB | StC, S1 => mk S1 DL StA
  | StD, S0 => mk S0 DR StB | StD, S1 => mk S1 DL StA
  end.

(** ** Reachability up to an unnamed step count *)

Definition Reach (c c' : cconf) : Prop :=
  exists n, csteps tm_f3 n c = Some c'.

Lemma Reach_refl : forall c, Reach c c.
Proof. intro c. exists 0. reflexivity. Qed.

Lemma Reach_of : forall n c c', csteps tm_f3 n c = Some c' -> Reach c c'.
Proof. intros n c c' H. exists n. exact H. Qed.

Lemma Reach_trans : forall a b c, Reach a b -> Reach b c -> Reach a c.
Proof.
  intros a b c (n1 & H1) (n2 & H2).
  exists (n1 + n2). eapply csteps_chain; eassumption.
Qed.

(** ** List algebra *)

Lemma rep_split : forall (x : Sym) i j X,
  rep [x] (i + j) ++ X = rep [x] i ++ rep [x] j ++ X.
Proof. intros. rewrite rep_add, <- app_assoc. reflexivity. Qed.

Lemma rep2S : forall (x : Sym) k X,
  rep [x] (2 * S k) ++ X = x :: x :: rep [x] (2 * k) ++ X.
Proof. intros. replace (2 * S k) with (S (S (2 * k))) by lia. reflexivity. Qed.

Lemma repS1 : forall (x : Sym) k X, rep [x] (k + 1) ++ X = x :: rep [x] k ++ X.
Proof. intros. replace (k + 1) with (S k) by lia. reflexivity. Qed.

Lemma rep_join : forall (x : Sym) i j X,
  rep [x] i ++ rep [x] j ++ X = rep [x] (i + j) ++ X.
Proof. intros. rewrite <- rep_split. reflexivity. Qed.

Lemma rep0_comm2 : forall k X, rep [S0] k ++ [S0; S0] ++ X = rep [S0] (k + 2) ++ X.
Proof. intros. rewrite rep_add, <- app_assoc. reflexivity. Qed.

(** ** The translated cycles *)

(** [LD]: the left drift.  [B] writes its 1, [C] steps past one more
    blank and hands straight back to [B] -- the head walks left two
    cells per unit and lays down a [0 1] pair behind it. *)
Lemma uLD : wsteps true true tm_f3 2 (StB, ([S0; S0], S0, []))
            = Some (StB, ([], S0, [S0; S1])).
Proof. reflexivity. Qed.

Lemma phLD : forall k L R,
  csteps tm_f3 (2 * k) (StB, (rep [S0] (2 * k) ++ L, S0, R))
  = Some (StB, (L, S0, rep [S0; S1] k ++ R)).
Proof.
  intros k L R.
  pose proof (cycL tm_f3 2 StB S0 [S0; S0] [] [S0; S1] uLD k L R) as H.
  cbn [app] in H. rewrite (rep_dbl S0 k) in H. exact H.
Qed.

(** [A] erasing a run of ones leftward. *)
Lemma uA1 : wsteps true true tm_f3 1 (StA, ([S1], S1, []))
            = Some (StA, ([], S1, [S0])).
Proof. reflexivity. Qed.

Lemma phA1 : forall k L R,
  csteps tm_f3 k (StA, (rep [S1] k ++ L, S1, R))
  = Some (StA, (L, S1, rep [S0] k ++ R)).
Proof.
  intros k L R.
  pose proof (cycL tm_f3 1 StA S1 [S1] [] [S0] uA1 k L R) as H.
  rewrite Nat.mul_1_l in H. cbn [app] in H. exact H.
Qed.

(** [BRun]: rightward, [B] on a 1 eats the next 1 and re-lays it on the
    left ([B1 -> D1 -> A0 -> B]). *)
Lemma uBRun : wsteps true true tm_f3 3 (StB, ([], S1, [S1]))
              = Some (StB, ([S1], S1, [])).
Proof. reflexivity. Qed.

Lemma phBRun : forall k L R,
  csteps tm_f3 (3 * k) (StB, (L, S1, rep [S1] k ++ R))
  = Some (StB, (rep [S1] k ++ L, S1, R)).
Proof. intros. exact (cycR tm_f3 3 StB S1 [S1] [S1] uBRun k L R). Qed.

(** [BSkip]: rightward, [B] on a 1 followed by a blank walks two cells
    and leaves two blanks ([B1 -> D0 -> B]). *)
Lemma uBSkip : wsteps true true tm_f3 2 (StB, ([], S1, [S0; S1]))
               = Some (StB, ([S0; S0], S1, [])).
Proof. reflexivity. Qed.

Lemma phBSkip : forall k L R,
  csteps tm_f3 (2 * k) (StB, (L, S1, rep [S0; S1] k ++ R))
  = Some (StB, (rep [S0] (2 * k) ++ L, S1, R)).
Proof.
  intros k L R.
  pose proof (cycR tm_f3 2 StB S1 [S0; S1] [S0; S0] uBSkip k L R) as H.
  rewrite (rep_dbl S0 k) in H. exact H.
Qed.

(** ** The straight-line gadgets *)

(** [turnA]: the left turnaround.  A run of [a+2] ones is met; its top
    1 is kept, the other [a+1] erased, and the machine turns on the
    blank beyond, leaving [0^a 1 1] behind on the right. *)
Lemma uBCA : wsteps true true tm_f3 2 (StB, ([S1; S1], S0, []))
             = Some (StA, ([], S1, [S1; S1])).
Proof. reflexivity. Qed.

Lemma uAB : wsteps true true tm_f3 2 (StA, ([S0], S1, []))
            = Some (StB, ([S1], S0, [])).
Proof. reflexivity. Qed.

Lemma turnA : forall a L R,
  csteps tm_f3 (a + 4)
    (StB, (rep [S1] (S (S a)) ++ [S0] ++ L, S0, R))
  = Some (StB, ([S1] ++ L, S0, rep [S0] a ++ [S1; S1] ++ R)).
Proof.
  intros a L R.
  replace (a + 4) with (2 + (a + 2)) by lia.
  eapply csteps_chain.
  { exact (wsteps_frame tm_f3 2 StB [S1; S1] S0 [] StA [] S1 [S1; S1]
             (rep [S1] a ++ [S0] ++ L) R uBCA). }
  eapply csteps_chain. { apply phA1. }
  exact (wsteps_frame tm_f3 2 StA [S0] S1 [] StB [S1] S0 []
           L (rep [S0] a ++ [S1; S1] ++ R) uAB).
Qed.

(** [g1]: the one-digit bump -- the counter's lowest digit goes from
    [0 0] to [1 1] while two blanks are eaten on the right. *)
Lemma g1 : wsteps true true tm_f3 8 (StB, ([S1; S0], S0, [S0; S0]))
           = Some (StB, ([S0; S0; S1; S1], S0, [])).
Proof. reflexivity. Qed.

(** [head3]: the turn that opens a rightward sweep -- three steps onto
    the marker pair, then three [BRun]s. *)
Lemma head3 : forall M Rr,
  csteps tm_f3 12 (StB, ([S1; S0] ++ M, S0, [S1; S1] ++ Rr))
  = Some (StB, (rep [S1] 4 ++ M, S1, Rr)).
Proof.
  intros M Rr.
  replace 12 with (3 + 3 * 3) by lia.
  eapply csteps_chain
    with (c1 := (StB, ([S1] ++ M, S1, [S1; S1; S1] ++ Rr))).
  { reflexivity. }
  exact (phBRun 3 ([S1] ++ M) Rr).
Qed.

(** [fin3]: the tail of a period -- skip [k] laid pairs, then step out
    over the two blanks the increment consumes. *)
Lemma fin3 : forall k L R,
  csteps tm_f3 (2 * k + 2)
    (StB, (L, S1, rep [S0; S1] k ++ [S0; S0] ++ R))
  = Some (StB, (rep [S0] (2 * k + 2) ++ L, S0, R)).
Proof.
  intros k L R.
  eapply csteps_chain. { apply phBSkip. }
  replace (2 * k + 2) with (S (S (2 * k))) by lia.
  reflexivity.
Qed.

(** [inc3_1]: the counter increment with NO carry. *)
Lemma inc3_1 : forall z H R,
  csteps tm_f3 (4 * S z + 18)
    (StB, (rep [S0] (2 * S z) ++ [S1; S1; S0; S0] ++ H, S0, [S0; S0] ++ R))
  = Some (StB, (rep [S0] (2 * S (S z)) ++ rep [S1] 4 ++ H, S0, R)).
Proof.
  intros z H R.
  replace (4 * S z + 18) with (2 * S z + (4 + (12 + (2 * S z + 2)))) by lia.
  eapply csteps_chain.
  { exact (phLD (S z) ([S1; S1; S0; S0] ++ H) ([S0; S0] ++ R)). }
  eapply csteps_chain.
  { exact (turnA 0 ([S0] ++ H) (rep [S0; S1] (S z) ++ [S0; S0] ++ R)). }
  eapply csteps_chain.
  { exact (head3 H (rep [S0; S1] (S z) ++ [S0; S0] ++ R)). }
  pose proof (fin3 (S z) (rep [S1] 4 ++ H) R) as HF.
  replace (2 * S (S z)) with (2 * S z + 2) by lia.
  exact HF.
Qed.

(** [close3]: the closer of one full counter period. *)
Lemma close3 : forall e z H R,
  Reach (StB, (rep [S0] (2 * S e) ++ [S1; S1; S0; S0] ++ rep [S1] (2 * e) ++ H,
               S0, [S1; S1] ++ rep [S0; S1] (S z) ++ [S0; S0] ++ R))
        (StB, (rep [S0] (2 * S (S z)) ++ [S1; S1] ++ rep [S0] (2 * S e)
                 ++ rep [S1] (2 * S (S e)) ++ H, S0, R)).
Proof.
  intros e z H R.
  eapply Reach_trans.
  { eapply Reach_of.
    exact (phLD (S e) ([S1; S1; S0; S0] ++ rep [S1] (2 * e) ++ H)
             ([S1; S1] ++ rep [S0; S1] (S z) ++ [S0; S0] ++ R)). }
  eapply Reach_trans.
  { eapply Reach_of.
    exact (turnA 0 ([S0] ++ rep [S1] (2 * e) ++ H)
             (rep [S0; S1] (S e) ++ [S1; S1] ++ rep [S0; S1] (S z)
                ++ [S0; S0] ++ R)). }
  eapply Reach_trans.
  { eapply Reach_of.
    exact (head3 (rep [S1] (2 * e) ++ H)
             (rep [S0; S1] (S e) ++ [S1; S1] ++ rep [S0; S1] (S z)
                ++ [S0; S0] ++ R)). }
  eapply Reach_trans.
  { eapply Reach_of.
    exact (phBSkip (S e) (rep [S1] 4 ++ rep [S1] (2 * e) ++ H)
             ([S1; S1] ++ rep [S0; S1] (S z) ++ [S0; S0] ++ R)). }
  eapply Reach_trans.
  { eapply Reach_of.
    exact (phBRun 2 (rep [S0] (2 * S e) ++ rep [S1] 4 ++ rep [S1] (2 * e) ++ H)
             (rep [S0; S1] (S z) ++ [S0; S0] ++ R)). }
  eapply Reach_of.
  rewrite (rep_join S1 4 (2 * e) H).
  replace (4 + 2 * e) with (2 * S (S e)) by lia.
  pose proof (fin3 (S z)
                (rep [S1] 2 ++ rep [S0] (2 * S e) ++ rep [S1] (2 * S (S e)) ++ H)
                R) as HF.
  replace (2 * S (S z)) with (2 * S z + 2) by lia.
  exact HF.
Qed.

(** ** The two mutually recursive summaries *)

(** [SW3n e]: run the level-[e] counter through a whole period. *)
Definition SW3n (e : nat) : Prop := forall z0 H Rx,
  Reach (StB, (rep [S0] (2 * S z0) ++ [S1; S1] ++ rep [S0] (2 * S e) ++ H,
               S0, rep [S0] (2 * e) ++ Rx))
        (StB, (rep [S0] (2 * S (z0 + e)) ++ [S1; S1; S0; S0]
                 ++ rep [S1] (2 * e) ++ H, S0, Rx)).

(** [INC3n e]: one increment whose carry runs the full period. *)
Definition INC3n (e : nat) : Prop := forall z H R,
  Reach (StB, (rep [S0] (2 * S z) ++ rep [S1] (2 * S (S e))
                 ++ rep [S0] (2 * S (S e)) ++ H, S0, [S0; S0] ++ R))
        (StB, (rep [S0] (2 * S (S z)) ++ [S1; S1] ++ rep [S0] (2 * S e)
                 ++ rep [S1] (2 * S (S e)) ++ H, S0, R)).

Lemma INC_of_SW : forall e, SW3n e -> INC3n e.
Proof.
  intros e HSW z H R.
  (* peel the drift *)
  eapply Reach_trans.
  { eapply Reach_of.
    exact (phLD (S z) (rep [S1] (2 * S (S e)) ++ rep [S0] (2 * S (S e)) ++ H)
             ([S0; S0] ++ R)). }
  (* turn around on the full run of ones *)
  eapply Reach_trans.
  { eapply Reach_of.
    assert (E1 : rep [S1] (2 * S (S e)) ++ rep [S0] (2 * S (S e)) ++ H
                 = rep [S1] (S (S (2 * S e))) ++ [S0]
                     ++ (rep [S0] (2 * S e + 1) ++ H)).
    { replace (2 * S (S e)) with (S (S (2 * S e))) by lia.
      replace (2 * S e + 1) with (S (2 * S e)) by lia. reflexivity. }
    rewrite E1.
    exact (turnA (2 * S e) (rep [S0] (2 * S e + 1) ++ H)
             (rep [S0; S1] (S z) ++ [S0; S0] ++ R)). }
  (* bump the lowest digit *)
  eapply Reach_trans.
  { eapply Reach_of.
    rewrite (repS1 S0 (2 * S e) H).
    rewrite (rep2S S0 e
               ([S1; S1] ++ rep [S0; S1] (S z) ++ [S0; S0] ++ R)).
    exact (wsteps_frame tm_f3 8 StB [S1; S0] S0 [S0; S0]
             StB [S0; S0; S1; S1] S0 []
             (rep [S0] (2 * S e) ++ H)
             (rep [S0] (2 * e) ++ [S1; S1] ++ rep [S0; S1] (S z)
                ++ [S0; S0] ++ R) g1). }
  (* the level-e period, then its closer *)
  eapply Reach_trans.
  { exact (HSW 0 H ([S1; S1] ++ rep [S0; S1] (S z) ++ [S0; S0] ++ R)). }
  exact (close3 e z H R).
Qed.

Lemma SW3n_0 : SW3n 0.
Proof.
  intros z0 H Rx. rewrite Nat.add_0_r. apply Reach_refl.
Qed.

Lemma SW3n_S : forall e, SW3n e -> INC3n e -> SW3n (e + S (S e)).
Proof.
  intros e HSW HINC z0 H Rx.
  replace (2 * S (e + S (S e))) with (2 * S e + 2 * S (S e)) by lia.
  replace (2 * (e + S (S e))) with (2 * e + 2 * S (S e)) by lia.
  replace (z0 + (e + S (S e))) with (S (S (z0 + e)) + e) by lia.
  rewrite (rep_split S0 (2 * S e) (2 * S (S e)) H),
          (rep_split S0 (2 * e) (2 * S (S e)) Rx),
          (rep_split S1 (2 * e) (2 * S (S e)) H).
  (* 1. the low half of the period *)
  eapply Reach_trans.
  { exact (HSW z0 (rep [S0] (2 * S (S e)) ++ H)
             (rep [S0] (2 * S (S e)) ++ Rx)). }
  (* 2. the carry-free increment filling the low half *)
  eapply Reach_trans.
  { eapply Reach_of.
    rewrite (rep2S S0 (S e) Rx).
    exact (inc3_1 (z0 + e)
             (rep [S1] (2 * e) ++ rep [S0] (2 * S (S e)) ++ H)
             (rep [S0] (2 * S e) ++ Rx)). }
  (* 3. the full-length carry *)
  eapply Reach_trans.
  { rewrite (rep_join S1 4 (2 * e) (rep [S0] (2 * S (S e)) ++ H)).
    replace (4 + 2 * e) with (2 * S (S e)) by lia.
    rewrite (rep2S S0 e Rx).
    exact (HINC (S (z0 + e)) H (rep [S0] (2 * e) ++ Rx)). }
  (* 4. the high half of the period *)
  eapply Reach_trans.
  { exact (HSW (S (S (z0 + e))) (rep [S1] (2 * S (S e)) ++ H) Rx). }
  apply Reach_refl.
Qed.

(** ** Level arithmetic and the induction *)

Definition ee (t : nat) : nat := 2 ^ (S t) - 2.

Lemma ee_0 : ee 0 = 0.
Proof. reflexivity. Qed.

Lemma ee_rec : forall t, ee (S t) = ee t + S (S (ee t)).
Proof.
  intro t. unfold ee.
  rewrite (Nat.pow_succ_r 2 (S t)) by lia.
  assert (H2 : 2 <= 2 ^ (S t)).
  { rewrite Nat.pow_succ_r by lia. pose proof (Nat.pow_nonzero 2 t). lia. }
  lia.
Qed.

Lemma SW3n_all : forall t, SW3n (ee t).
Proof.
  induction t.
  - rewrite ee_0. exact SW3n_0.
  - rewrite ee_rec. apply SW3n_S; [exact IHt | apply INC_of_SW, IHt].
Qed.

Lemma INC3n_all : forall t, INC3n (ee t).
Proof. intro t. apply INC_of_SW, SW3n_all. Qed.

(** ** The anchor and its lap *)

(** [anch3 f] denotes the tape [1^(2f+4) 0^(2f+4)] with the head one
    past the last blank -- the blank-tape right-record. *)
Definition anch3 (f : nat) : cconf :=
  (StB, (rep [S0] (2 * S (S f)) ++ rep [S1] (2 * S (S f))
           ++ rep [S0] (2 * S (S f)), S0, rep [S0] (2 * S (S f)))).

Lemma lap_gen : forall f L R, SW3n f -> INC3n f ->
  exists n, 0 < n /\
    csteps tm_f3 n
      (StB, (rep [S0] (2 * S (S f)) ++ rep [S1] (2 * S (S f))
               ++ rep [S0] (2 * S (S f)) ++ L, S0, rep [S0] (2 * S (S f)) ++ R))
    = Some (StB, (rep [S0] (2 * S (S (f + S (S f))))
                    ++ rep [S1] (2 * S (S (f + S (S f)))) ++ L, S0, R)).
Proof.
  intros f L R HSW HINC.
  (* 1. the full-length carry that lifts the anchor into counter form *)
  assert (H1 : Reach
    (StB, (rep [S0] (2 * S (S f)) ++ rep [S1] (2 * S (S f))
             ++ rep [S0] (2 * S (S f)) ++ L, S0, rep [S0] (2 * S (S f)) ++ R))
    (StB, (rep [S0] (2 * S (S (S f))) ++ [S1; S1] ++ rep [S0] (2 * S f)
             ++ rep [S1] (2 * S (S f)) ++ L, S0, rep [S0] (2 * S f) ++ R))).
  { pose proof (HINC (S f) L (rep [S0] (2 * S f) ++ R)) as HH.
    rewrite (rep2S S0 (S f) R). exact HH. }
  (* 2. a whole period of the level-f counter *)
  assert (H2 : Reach
    (StB, (rep [S0] (2 * S (S (S f))) ++ [S1; S1] ++ rep [S0] (2 * S f)
             ++ rep [S1] (2 * S (S f)) ++ L, S0, rep [S0] (2 * S f) ++ R))
    (StB, (rep [S0] (2 * S (S (S f) + f)) ++ [S1; S1; S0; S0]
             ++ rep [S1] (2 * f) ++ rep [S1] (2 * S (S f)) ++ L,
           S0, [S0; S0] ++ R))).
  { pose proof (HSW (S (S f)) (rep [S1] (2 * S (S f)) ++ L) ([S0; S0] ++ R))
      as HH.
    rewrite (rep0_comm2 (2 * f) R) in HH.
    replace (2 * f + 2) with (2 * S f) in HH by lia.
    exact HH. }
  destruct H1 as (n1 & E1). destruct H2 as (n2 & E2).
  pose proof (inc3_1 (S (S f) + f)
                (rep [S1] (2 * f) ++ rep [S1] (2 * S (S f)) ++ L) R) as E3.
  assert (Eones : rep [S1] 4 ++ rep [S1] (2 * f) ++ rep [S1] (2 * S (S f)) ++ L
                  = rep [S1] (2 * S (S (f + S (S f)))) ++ L).
  { rewrite (rep_join S1 (2 * f) (2 * S (S f)) L).
    rewrite (rep_join S1 4 (2 * f + 2 * S (S f)) L).
    f_equal. f_equal. lia. }
  rewrite Eones in E3.
  replace (2 * S (S (S (S f) + f))) with (2 * S (S (f + S (S f)))) in E3 by lia.
  exists (n1 + (n2 + (4 * S (S (S f) + f) + 18))).
  split; [lia|].
  eapply csteps_chain; [exact E1|].
  eapply csteps_chain; [exact E2|].
  exact E3.
Qed.

(** ** Bootstrap, visits, and the closer *)

Definition Cf (p : positive) : cconf := anch3 (ee (Pos.to_nat p - 1)).

Lemma Cf_succ : forall p, Cf (Pos.succ p) = anch3 (ee (Pos.to_nat p)).
Proof.
  intro p. unfold Cf. rewrite Pos2Nat.inj_succ. f_equal. f_equal. lia.
Qed.

Lemma lift_side_blanks : forall l k, lift_side (l ++ rep [S0] k) = lift_side l.
Proof.
  intros l k; revert l; induction k as [|k IH]; intro l.
  - cbn [rep]. rewrite app_nil_r. reflexivity.
  - cbn [rep app].
    replace (l ++ S0 :: rep [S0] k) with ((l ++ [S0]) ++ rep [S0] k)
      by (rewrite <- app_assoc; reflexivity).
    rewrite IH. apply lift_side_app_blank.
Qed.

Lemma lift_blanks : forall q l h r j k,
  lift (q, (l ++ rep [S0] j, h, r ++ rep [S0] k)) = lift (q, (l, h, r)).
Proof.
  intros. unfold lift, lift_tape; cbn [fst snd].
  rewrite !lift_side_blanks. reflexivity.
Qed.

Lemma boot_f3 : exists t0, stepn tm_f3 t0 InitES = Some (lift (Cf 1)).
Proof.
  exists 31.
  assert (H : match csteps tm_f3 31 c0 with
              | Some c => ceqb c (Cf 1)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm_f3 31 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
  f_equal. apply ceqb_lift. exact H.
Qed.

Lemma lap_f3 : forall p, (1 <= p)%positive ->
  exists n c', csteps tm_f3 n (Cf p) = Some c' /\
               lift c' = lift (Cf (Pos.succ p)) /\ 0 < n.
Proof.
  intros p _.
  assert (Ht : Pos.to_nat p = S (Pos.to_nat p - 1)).
  { pose proof (Pos2Nat.is_pos p). lia. }
  set (t := Pos.to_nat p - 1).
  destruct (lap_gen (ee t) [] [] (SW3n_all t) (INC3n_all t)) as (n & Hn & E).
  rewrite !app_nil_r in E.
  exists n. eexists. split; [|split; [|exact Hn]].
  - unfold Cf, anch3. fold t. exact E.
  - rewrite Cf_succ, Ht. fold t. rewrite <- ee_rec.
    unfold anch3. rewrite app_assoc. symmetry.
    exact (lift_blanks StB
             (rep [S0] (2 * S (S (ee (S t)))) ++ rep [S1] (2 * S (S (ee (S t)))))
             S0 [] (2 * S (S (ee (S t)))) (2 * S (S (ee (S t))))).
Qed.

Lemma vis_f3 : forall p q, (1 <= p)%positive ->
  exists k c, csteps tm_f3 k (Cf p) = Some c /\ fst c = q.
Proof.
  intros p q _.
  unfold Cf, anch3.
  set (f := ee (Pos.to_nat p - 1)).
  destruct q.
  - (* StA: drift left onto the ones, then C hands to A *)
    exists (2 * S (S f) + 2). eexists. split.
    + eapply csteps_chain.
      { exact (phLD (S (S f))
                 (rep [S1] (2 * S (S f)) ++ rep [S0] (2 * S (S f)))
                 (rep [S0] (2 * S (S f)))). }
      rewrite (rep2S S1 (S f)).
      exact (wsteps_frame tm_f3 2 StB [S1; S1] S0 [] StA [] S1 [S1; S1]
               (rep [S1] (2 * S f) ++ rep [S0] (2 * S (S f)))
               (rep [S0; S1] (S (S f)) ++ rep [S0] (2 * S (S f))) uBCA).
    + reflexivity.
  - (* StB: the anchor itself *)
    exists 0. eexists. split; reflexivity.
  - (* StC: one step *)
    exists 1. eexists. split; reflexivity.
  - (* StD: drift, turn around, then the bump's fourth step *)
    exists (2 * S (S f) + ((2 * S f + 4) + 4)). eexists. split.
    + eapply csteps_chain.
      { exact (phLD (S (S f))
                 (rep [S1] (2 * S (S f)) ++ rep [S0] (2 * S (S f)))
                 (rep [S0] (2 * S (S f)))). }
      eapply csteps_chain.
      { assert (E : rep [S1] (2 * S (S f)) ++ rep [S0] (2 * S (S f))
                    = rep [S1] (S (S (2 * S f))) ++ [S0] ++ rep [S0] (S (2 * S f))).
        { replace (2 * S (S f)) with (S (S (2 * S f))) by lia. reflexivity. }
        rewrite E.
        exact (turnA (2 * S f) (rep [S0] (S (2 * S f)))
                 (rep [S0; S1] (S (S f)) ++ rep [S0] (2 * S (S f)))). }
      assert (E2 : rep [S0] (2 * S f) ++ [S1; S1] ++ rep [S0; S1] (S (S f))
                     ++ rep [S0] (2 * S (S f))
                   = [S0; S0] ++ (rep [S0] (2 * f) ++ [S1; S1]
                       ++ rep [S0; S1] (S (S f)) ++ rep [S0] (2 * S (S f)))).
      { rewrite (rep2S S0 f). reflexivity. }
      rewrite E2.
      exact (wsteps_frame tm_f3 4 StB [S1; S0] S0 [S0; S0]
               StD [S0; S1] S1 [S0; S0]
               (rep [S0] (2 * S f))
               (rep [S0] (2 * f) ++ [S1; S1] ++ rep [S0; S1] (S (S f))
                  ++ rep [S0] (2 * S (S f)))
               (eq_refl : wsteps true true tm_f3 4 (StB, ([S1; S0], S0, [S0; S0]))
                          = Some (StD, ([S0; S1], S1, [S0; S0])))).
    + reflexivity.
Qed.

(** #3 never quasihalts: bbchallenge 1RB0LA_1LC0RD_0LB1LA_0RB1LA. *)
Theorem nqh_1RB0LA_1LC0RD_0LB1LA_0RB1LA : NeverQuasiHaltsSt tm_f3.
Proof.
  apply (glue_neverqh tm_f3 Cf 1).
  - exact boot_f3.
  - exact lap_f3.
  - exact vis_f3.
Qed.

Theorem tm_f3_nonhalt : NonHalt tm_f3.
Proof. apply never_qh_nonhalt, nqh_1RB0LA_1LC0RD_0LB1LA_0RB1LA. Qed.
