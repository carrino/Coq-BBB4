(** * Fractal_5: the fractal machine #5, 1RB0LA_1LC1RD_0LC1LA_0RD0RB.

    One of the two BBB `fractal` holdouts, and the one for which the
    BBB harness has NO proof to port: its own soundness note says the
    "for all j" closure "evidences but does not by itself mechanise
    the all-j induction".  This file mechanises it.

    THE ANCHOR.  Blank-tape right-records occur at

      A(k) = (StB, (0^(2^k-1) ++ 1^(2^k), 0, []))      (left list, nearest first)

    i.e. the tape reads [1^(2^k) 0^(2^k)] with the head on the last
    blank, at global step [2*4^k - 2^k].  The lap A(k) -> A(k+1) costs
    [6*4^k - 2^k] steps, so it is Theta(4^k) and no affine certificate
    can carry it; [LapGlue] only ever asks for [exists n], which is all
    a fractal lap can give.

    WHAT THE MACHINE IS DOING.  Written out with the head at a blank in
    state [B], the left half-tape during a lap is always

      0^z ++ W(z)      with   W(z) = 1 ++ b_0^1 ++ b_1^2 ++ .. ++ b_{j-1}^{2^(j-1)}

    where [b_{j-1}..b_0] are the binary digits of [z].  That is: the
    left tape is a BINARY COUNTER whose digit [i] is stored as a block
    of [2^i] cells, and one macro-step of the machine increments it
    while consuming exactly one blank from the right.  A carry of
    length [m = 2^i] costs [Theta(m^2)] and is itself the whole
    machine one level down -- that is the fractal.

    THE PROOF.  Three straight-line gadgets ([inc1], [turnl], [close],
    each an exact step count), then a three-way mutual recursion closed
    by a single induction on the level [t]:

      SW  t : run the counter through a full period, z0 -> z0+2^(t+1)-2
      INC t : one carry of length 2^(t+1)
      E2  t : the two-parameter rewriting rule the carry unfolds into

    with [SW (S t)] built from [SW t] (twice), [inc1] and [INC t], and
    [INC t] built from [turnl] and [E2 t], and [E2 t] from [SW t] and
    [close].  Every dependency is at level [<= t], so one [induction t]
    discharges all three.  [E2] carries a free parameter [b] that never
    appears in its own hypotheses -- the same device that makes the
    corresponding busycoq [FractalType0] arguments go through.

    The step counts are recorded in the gadget lemmas but deliberately
    NOT propagated: [Reach] is [exists n, csteps .. = Some ..], so the
    exponential cost of a lap lives inside an existential and is never
    written down.  Differentially validated against a plain simulator
    for every level up to 2^7 and for random left/right frames.

    Axiom footprint: [functional_extensionality_dep] only (inherited
    from [CTape]; this file adds none). *)

From Coq Require Import Arith Lia List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB0LA_1LC1RD_0LC1LA_0RD0RB *)
Definition tm_f5 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DL StA
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DR StD
  | StC, S0 => mk S0 DL StC | StC, S1 => mk S1 DL StA
  | StD, S0 => mk S0 DR StD | StD, S1 => mk S0 DR StB
  end.

(** ** Reachability up to an unnamed step count *)

Definition Reach (c c' : cconf) : Prop :=
  exists n, csteps tm_f5 n c = Some c'.

Lemma Reach_refl : forall c, Reach c c.
Proof. intro c. exists 0. reflexivity. Qed.

Lemma Reach_of : forall n c c', csteps tm_f5 n c = Some c' -> Reach c c'.
Proof. intros n c c' H. exists n. exact H. Qed.

Lemma Reach_trans : forall a b c, Reach a b -> Reach b c -> Reach a c.
Proof.
  intros a b c (n1 & H1) (n2 & H2).
  exists (n1 + n2). eapply csteps_chain; eassumption.
Qed.

(** ** The three translated cycles

    [C] walking left over blanks, [D] walking right over blanks, and
    [A] erasing a run of ones leftward.  Each is one [wsteps] unit fed
    to [cycL] / [cycR]. *)

Lemma uC0 : wsteps true true tm_f5 1 (StC, ([S0], S0, []))
            = Some (StC, ([], S0, [S0])).
Proof. reflexivity. Qed.

Lemma phC0 : forall k L R,
  csteps tm_f5 k (StC, (rep [S0] k ++ L, S0, R))
  = Some (StC, (L, S0, rep [S0] k ++ R)).
Proof.
  intros k L R.
  pose proof (cycL tm_f5 1 StC S0 [S0] [] [S0] uC0 k L R) as H.
  rewrite Nat.mul_1_l in H. cbn [app] in H. exact H.
Qed.

Lemma uD0 : wsteps true true tm_f5 1 (StD, ([], S0, [S0]))
            = Some (StD, ([S0], S0, [])).
Proof. reflexivity. Qed.

Lemma phD0 : forall k L R,
  csteps tm_f5 k (StD, (L, S0, rep [S0] k ++ R))
  = Some (StD, (rep [S0] k ++ L, S0, R)).
Proof.
  intros k L R.
  pose proof (cycR tm_f5 1 StD S0 [S0] [S0] uD0 k L R) as H.
  rewrite Nat.mul_1_l in H. exact H.
Qed.

Lemma uA1 : wsteps true true tm_f5 1 (StA, ([S1], S1, []))
            = Some (StA, ([], S1, [S0])).
Proof. reflexivity. Qed.

Lemma phA1 : forall k L R,
  csteps tm_f5 k (StA, (rep [S1] k ++ L, S1, R))
  = Some (StA, (L, S1, rep [S0] k ++ R)).
Proof.
  intros k L R.
  pose proof (cycL tm_f5 1 StA S1 [S1] [] [S0] uA1 k L R) as H.
  rewrite Nat.mul_1_l in H. cbn [app] in H. exact H.
Qed.

(** ** The straight-line gadgets *)

(** [bounceZ]: from the head blank, [B] writes its 1 and [C] walks left
    across [z] blanks onto the first 1. *)
Lemma bounceZ : forall z Lx R,
  csteps tm_f5 (S z) (StB, (rep [S0] z ++ [S1] ++ Lx, S0, R))
  = Some (StC, (Lx, S1, rep [S0] z ++ [S1] ++ R)).
Proof.
  destruct z as [|z]; intros Lx R.
  - reflexivity.
  - replace (S (S z)) with (1 + (z + 1)) by lia.
    eapply csteps_chain
      with (c1 := (StC, (rep [S0] z ++ [S1] ++ Lx, S0, [S1] ++ R))).
    { reflexivity. }
    eapply csteps_chain
      with (c1 := (StC, ([S1] ++ Lx, S0, rep [S0] z ++ [S1] ++ R))).
    { apply phC0. }
    reflexivity.
Qed.

(** [brd]: [B] on a 1 hands to [D], which walks right across [z] blanks
    onto the next 1. *)
Lemma brd : forall z L R,
  csteps tm_f5 (S z) (StB, (L, S1, rep [S0] z ++ [S1] ++ R))
  = Some (StD, (rep [S0] z ++ [S1] ++ L, S1, R)).
Proof.
  destruct z as [|z]; intros L R.
  - reflexivity.
  - replace (S (S z)) with (1 + (z + 1)) by lia.
    eapply csteps_chain
      with (c1 := (StD, ([S1] ++ L, S0, rep [S0] z ++ [S1] ++ R))).
    { reflexivity. }
    eapply csteps_chain
      with (c1 := (StD, (rep [S0] z ++ [S1] ++ L, S0, [S1] ++ R))).
    { apply phD0. }
    reflexivity.
Qed.

(** [brdx]: [brd], then [D] erases that 1 and hands back to [B]. *)
Lemma brdx : forall z L R,
  csteps tm_f5 (S (S z)) (StB, (L, S1, rep [S0] z ++ [S1] ++ R))
  = Some (StB, (rep [S0] (S z) ++ [S1] ++ L, chd R, ctl R)).
Proof.
  intros z L R.
  replace (S (S z)) with (S z + 1) by lia.
  eapply csteps_chain. { apply brd. }
  reflexivity.
Qed.

(** [uCA]: [C] on the 1 hands to [A], which finds a blank and turns. *)
Lemma uCA : wsteps true true tm_f5 2 (StC, ([S0], S1, []))
            = Some (StB, ([S1], S1, [])).
Proof. reflexivity. Qed.

(** [uAB]: [A] erases the last 1 of a run and turns on the blank. *)
Lemma uAB : wsteps true true tm_f5 2 (StA, ([S0], S1, []))
            = Some (StB, ([S1], S0, [])).
Proof. reflexivity. Qed.

(** [turnbase]: the left turnaround when the 1-run has length one. *)
Lemma turnbase : forall z Lx R,
  csteps tm_f5 (S (S (S z))) (StB, (rep [S0] z ++ [S1; S0] ++ Lx, S0, R))
  = Some (StB, ([S1] ++ Lx, S1, rep [S0] z ++ [S1] ++ R)).
Proof.
  intros z Lx R.
  replace (S (S (S z))) with (S z + 2) by lia.
  eapply csteps_chain. { apply (bounceZ z ([S0] ++ Lx) R). }
  exact (wsteps_frame tm_f5 2 StC [S0] S1 [] StB [S1] S1 []
           Lx (rep [S0] z ++ [S1] ++ R) uCA).
Qed.

(** [inc1]: the counter increment with NO carry -- digit 0 flips from
    0 to 1, one blank is eaten on the right. *)
Lemma inc1 : forall z H R,
  csteps tm_f5 (2 * z + 5) (StB, (rep [S0] z ++ [S1; S0] ++ H, S0, S0 :: R))
  = Some (StB, (rep [S0] (S z) ++ [S1; S1] ++ H, S0, R)).
Proof.
  intros z H R.
  replace (2 * z + 5) with (S (S (S z)) + S (S z)) by lia.
  eapply csteps_chain. { apply turnbase. }
  exact (brdx z ([S1] ++ H) (S0 :: R)).
Qed.

(** [turnl]: the general left turnaround.  [b] blanks are crossed, a
    run of [a+2] ones is met, its top 1 is kept and the other [a+1]
    erased, and the machine turns on the blank beyond. *)
Lemma turnl : forall a b L R,
  csteps tm_f5 (a + b + 4)
    (StB, (rep [S0] b ++ rep [S1] (S (S a)) ++ [S0] ++ L, S0, R))
  = Some (StB, ([S1] ++ L, S0,
                rep [S0] a ++ [S1] ++ rep [S0] b ++ [S1] ++ R)).
Proof.
  intros a b L R.
  replace (a + b + 4) with (S b + (1 + (a + 2))) by lia.
  eapply csteps_chain.
  { apply (bounceZ b (rep [S1] (S a) ++ [S0] ++ L) R). }
  eapply csteps_chain
    with (c1 := (StA, (rep [S1] a ++ [S0] ++ L, S1,
                       [S1] ++ rep [S0] b ++ [S1] ++ R))).
  { exact (wsteps_frame tm_f5 1 StC [S1] S1 [] StA [] S1 [S1]
             (rep [S1] a ++ [S0] ++ L) (rep [S0] b ++ [S1] ++ R)
             (eq_refl : wsteps true true tm_f5 1 (StC, ([S1], S1, []))
                        = Some (StA, ([], S1, [S1])))). }
  eapply csteps_chain. { apply phA1. }
  exact (wsteps_frame tm_f5 2 StA [S0] S1 [] StB [S1] S0 []
           L (rep [S0] a ++ [S1] ++ rep [S0] b ++ [S1] ++ R) uAB).
Qed.

(** [close]: the closing gadget of one full counter period -- the
    machine folds the [1 0 1^e] top of the counter into a solid [1^(e+2)]
    and steps out over the two markers on the right. *)
Lemma close : forall e b H R,
  csteps tm_f5 (2 * e + b + 7)
    (StB, (rep [S0] e ++ [S1; S0] ++ rep [S1] e ++ H, S0,
           [S1] ++ rep [S0] b ++ [S1; S0] ++ R))
  = Some (StB, (rep [S0] (S b) ++ [S1] ++ rep [S0] (S e)
                  ++ rep [S1] (S (S e)) ++ H, S0, R)).
Proof.
  intros e b H R.
  replace (2 * e + b + 7) with (S (S (S e)) + (S (S e) + S (S b))) by lia.
  eapply csteps_chain. { apply (turnbase e (rep [S1] e ++ H)). }
  eapply csteps_chain.
  { exact (brdx e ([S1] ++ rep [S1] e ++ H)
             ([S1] ++ rep [S0] b ++ [S1; S0] ++ R)). }
  exact (brdx b (rep [S0] (S e) ++ [S1; S1] ++ rep [S1] e ++ H) (S0 :: R)).
Qed.

(** ** List algebra used by the recursion *)

Lemma rep_split : forall (x : Sym) i j X,
  rep [x] (i + j) ++ X = rep [x] i ++ rep [x] j ++ X.
Proof. intros. rewrite rep_add, <- app_assoc. reflexivity. Qed.

Lemma rep0_cons : forall e X, rep [S0] (S e) ++ X = rep [S0] e ++ S0 :: X.
Proof. intros. cbn [rep app]. apply rep_slide. Qed.

(** ** The three mutually recursive summaries

    All three are indexed by [e], the counter's period minus two; the
    level-[t] instance is [e = 2^(t+1) - 2].  Writing them in [e]
    rather than in [2^(t+1)] keeps every list index in the shape
    [S e] / [S (S e)], which [csteps] reduces on its own. *)

(** [SWn e]: run the counter through a whole period.  The left tape
    enters as [0^z0 1 0^(e+1)] (counter value 0) and leaves as
    [0^(z0+e) 1 0 1^e] (counter value [e]), eating exactly [e] blanks
    from the right.  [H] and [Rx] are arbitrary frames. *)
Definition SWn (e : nat) : Prop := forall z0 H Rx,
  Reach (StB, (rep [S0] z0 ++ [S1] ++ rep [S0] (S e) ++ H,
               S0, rep [S0] e ++ Rx))
        (StB, (rep [S0] (z0 + e) ++ [S1; S0] ++ rep [S1] e ++ H,
               S0, Rx)).

(** [E2n e]: the two-parameter rewriting rule the recursion turns on.
    [b] is free -- it never constrains the hypothesis -- and that is
    what lets one level's leftovers be threaded into the next. *)
Definition E2n (e : nat) : Prop := forall a b L R, S e <= a ->
  Reach (StB, ([S1] ++ rep [S0] a ++ L, S0,
               rep [S0] e ++ [S1] ++ rep [S0] b ++ [S1; S0] ++ R))
        (StB, (rep [S0] (S b) ++ [S1] ++ rep [S0] (S e)
                 ++ rep [S1] (S (S e)) ++ rep [S0] (a - S e) ++ L,
               S0, R)).

(** [INCn e]: one increment whose carry runs the full period length
    [e+2] -- the block [1^(e+2) 0^(e+2)] becomes [1 0^(e+1) 1^(e+2)]. *)
Definition INCn (e : nat) : Prop := forall z H R,
  Reach (StB, (rep [S0] z ++ rep [S1] (S (S e)) ++ rep [S0] (S (S e)) ++ H,
               S0, S0 :: R))
        (StB, (rep [S0] (S z) ++ [S1] ++ rep [S0] (S e)
                 ++ rep [S1] (S (S e)) ++ H, S0, R)).

Lemma E2_of_SW : forall e, SWn e -> E2n e.
Proof.
  intros e HSW a b L R Ha.
  replace a with (S e + (a - S e)) at 1 by lia.
  rewrite rep_split.
  eapply Reach_trans.
  { exact (HSW 0 (rep [S0] (a - S e) ++ L)
             ([S1] ++ rep [S0] b ++ [S1; S0] ++ R)). }
  eapply Reach_of.
  exact (close e b (rep [S0] (a - S e) ++ L) R).
Qed.

Lemma INC_of_E2 : forall e, E2n e -> INCn e.
Proof.
  intros e HE2 z H R.
  eapply Reach_trans.
  { eapply Reach_of.
    exact (turnl e z (rep [S0] (S e) ++ H) (S0 :: R)). }
  pose proof (HE2 (S e) z H R (le_n _)) as HH.
  rewrite Nat.sub_diag in HH. exact HH.
Qed.

Lemma SWn_0 : SWn 0.
Proof.
  intros z0 H Rx. rewrite Nat.add_0_r. apply Reach_refl.
Qed.

Lemma SWn_S : forall e, SWn e -> INCn e -> SWn (e + S (S e)).
Proof.
  intros e HSW HINC z0 H Rx.
  replace (S (e + S (S e))) with (S e + S (S e)) by lia.
  replace (z0 + (e + S (S e))) with (S (S (z0 + e)) + e) by lia.
  rewrite (rep_split S0 (S e) (S (S e)) H),
          (rep_split S0 e (S (S e)) Rx),
          (rep_split S1 e (S (S e)) H).
  eapply Reach_trans.
  { exact (HSW z0 (rep [S0] (S (S e)) ++ H) (rep [S0] (S (S e)) ++ Rx)). }
  eapply Reach_trans.
  { eapply Reach_of.
    exact (inc1 (z0 + e) (rep [S1] e ++ rep [S0] (S (S e)) ++ H)
             (rep [S0] (S e) ++ Rx)). }
  eapply Reach_trans.
  { exact (HINC (S (z0 + e)) H (rep [S0] e ++ Rx)). }
  exact (HSW (S (S (z0 + e))) (rep [S1] (S (S e)) ++ H) Rx).
Qed.

(** ** Level arithmetic and the induction *)

Definition ee (t : nat) : nat := 2 ^ (S t) - 2.

Lemma ee_0 : ee 0 = 0.
Proof. reflexivity. Qed.

Lemma ee_rec : forall t, ee (S t) = ee t + S (S (ee t)).
Proof.
  intro t. unfold ee.
  rewrite (Nat.pow_succ_r 2 (S t)) by lia.
  pose proof (Nat.pow_nonzero 2 (S t)) as Hnz.
  assert (H2 : 2 <= 2 ^ (S t)).
  { rewrite Nat.pow_succ_r by lia. pose proof (Nat.pow_nonzero 2 t). lia. }
  lia.
Qed.

Lemma SWn_all : forall t, SWn (ee t).
Proof.
  induction t.
  - rewrite ee_0. exact SWn_0.
  - rewrite ee_rec.
    apply SWn_S; [exact IHt | apply INC_of_E2, E2_of_SW, IHt].
Qed.

Lemma INCn_all : forall t, INCn (ee t).
Proof. intro t. apply INC_of_E2, E2_of_SW, SWn_all. Qed.

(** ** The anchor and its lap *)

(** [anch e] denotes the tape [1^(e+2) 0^(e+2)] with the head on the
    last blank -- the blank-tape right-record at level [t] when
    [e = ee t], reached at global step [2*4^t - 2^t]. *)
Definition anch (e : nat) : cconf :=
  (StB, (rep [S0] (S e) ++ rep [S1] (S (S e)) ++ rep [S0] (S (S e)),
         S0, rep [S0] (S (S e)))).

Lemma lap_gen : forall e L R, SWn e -> INCn e ->
  exists n, 0 < n /\
    csteps tm_f5 n
      (StB, (rep [S0] (S e) ++ rep [S1] (S (S e)) ++ rep [S0] (S (S e)) ++ L,
             S0, rep [S0] (S (S e)) ++ R))
    = Some (StB, (rep [S0] (S (e + S (S e)))
                    ++ rep [S1] (S (S (e + S (S e)))) ++ L, S0, R)).
Proof.
  intros e L R HSW HINC.
  destruct (HINC (S e) L (rep [S0] (S e) ++ R)) as (n1 & E1).
  assert (Hmid : Reach
    (StB, (rep [S0] (S (S e)) ++ [S1] ++ rep [S0] (S e)
             ++ rep [S1] (S (S e)) ++ L, S0, rep [S0] (S e) ++ R))
    (StB, (rep [S0] (S (S e) + e) ++ [S1; S0] ++ rep [S1] e
             ++ rep [S1] (S (S e)) ++ L, S0, S0 :: R))).
  { rewrite (rep0_cons e R).
    exact (HSW (S (S e)) (rep [S1] (S (S e)) ++ L) (S0 :: R)). }
  destruct Hmid as (n2 & E2).
  exists (n1 + (n2 + (2 * (S (S e) + e) + 5))).
  split; [lia|].
  eapply csteps_chain; [exact E1|].
  eapply csteps_chain; [exact E2|].
  rewrite (inc1 (S (S e) + e) (rep [S1] e ++ rep [S1] (S (S e)) ++ L) R).
  assert (Eo : rep [S1] (S (S (e + S (S e)))) ++ L
               = [S1; S1] ++ rep [S1] e ++ rep [S1] (S (S e)) ++ L).
  { replace (S (S (e + S (S e)))) with (2 + (e + S (S e))) by lia.
    rewrite rep_split. cbn [rep app]. do 2 f_equal.
    rewrite rep_split. reflexivity. }
  rewrite Eo.
  replace (S (S (S e) + e)) with (S (e + S (S e))) by lia.
  reflexivity.
Qed.

(** ** Bootstrap, visits, and the closer *)

Definition Cf (p : positive) : cconf := anch (ee (Pos.to_nat p - 1)).

Lemma Cf_succ : forall p, Cf (Pos.succ p) = anch (ee (Pos.to_nat p)).
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

Lemma boot_f5 : exists t0, stepn tm_f5 t0 InitES = Some (lift (Cf 1)).
Proof.
  exists 6.
  assert (H : match csteps tm_f5 6 c0 with
              | Some c => ceqb c (Cf 1)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm_f5 6 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
  f_equal. apply ceqb_lift. exact H.
Qed.

Lemma lap_f5 : forall p, (1 <= p)%positive ->
  exists n c', csteps tm_f5 n (Cf p) = Some c' /\
               lift c' = lift (Cf (Pos.succ p)) /\ 0 < n.
Proof.
  intros p _.
  assert (Ht : Pos.to_nat p = S (Pos.to_nat p - 1)).
  { pose proof (Pos2Nat.is_pos p). lia. }
  set (t := Pos.to_nat p - 1).
  destruct (lap_gen (ee t) [] [] (SWn_all t) (INCn_all t)) as (n & Hn & E).
  rewrite !app_nil_r in E.
  exists n. eexists. split; [|split; [|exact Hn]].
  - unfold Cf, anch. fold t. exact E.
  - rewrite Cf_succ, Ht. fold t. rewrite <- ee_rec.
    unfold anch. rewrite app_assoc. symmetry.
    exact (lift_blanks StB
             (rep [S0] (S (ee (S t))) ++ rep [S1] (S (S (ee (S t)))))
             S0 [] (S (S (ee (S t)))) (S (S (ee (S t))))).
Qed.

Lemma vis_f5 : forall p q, (1 <= p)%positive ->
  exists k c, csteps tm_f5 k (Cf p) = Some c /\ fst c = q.
Proof.
  intros p q _.
  unfold Cf, anch.
  set (e := ee (Pos.to_nat p - 1)).
  destruct q.
  - (* StA: bounce left onto the top 1, then C hands to A *)
    exists (S (S e) + 1). eexists. split.
    + eapply csteps_chain.
      { exact (bounceZ (S e) (rep [S1] (S e) ++ rep [S0] (S (S e)))
                 (rep [S0] (S (S e)))). }
      reflexivity.
    + reflexivity.
  - (* StB: the anchor itself *)
    exists 0. eexists. split; reflexivity.
  - (* StC: one step *)
    exists 1. eexists. split; reflexivity.
  - (* StD: turn left, turn again on the lone 1, then B hands to D *)
    exists ((e + S e + 4) + (3 + 1)). eexists. split.
    + eapply csteps_chain.
      { exact (turnl e (S e) (rep [S0] (S e)) (rep [S0] (S (S e)))). }
      eapply csteps_chain.
      { exact (turnbase 0 (rep [S0] e)
                 (rep [S0] e ++ [S1] ++ rep [S0] (S e) ++ [S1]
                    ++ rep [S0] (S (S e)))). }
      reflexivity.
    + reflexivity.
Qed.

(** #5 never quasihalts: bbchallenge 1RB0LA_1LC1RD_0LC1LA_0RD0RB. *)
Theorem nqh_1RB0LA_1LC1RD_0LC1LA_0RD0RB : NeverQuasiHaltsSt tm_f5.
Proof.
  apply (glue_neverqh tm_f5 Cf 1).
  - exact boot_f5.
  - exact lap_f5.
  - exact vis_f5.
Qed.

Theorem tm_f5_nonhalt : NonHalt tm_f5.
Proof. apply never_qh_nonhalt, nqh_1RB0LA_1LC1RD_0LC1LA_0RD0RB. Qed.
