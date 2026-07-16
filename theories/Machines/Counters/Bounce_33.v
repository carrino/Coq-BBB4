(** * Bounce_33: the bounce_counter machine #33, 1RB1LD_1RC0RB_1LA1RB_0LD0LA.

    Second machine of the BBB harness's [bounce_counter] family
    (certificate results/counter33.cert).  The macro anchor is

      D(k) = 1^m 0^(2k),  m = 2^k + 1,  head on the last 0, StB.

    Same architecture as #8 (Bounce_8) at the opposite sweep parity:
    stable sweep-configs keep the digit word behind a 11 separator
    over a (10)-comb,

      Sc a w = 0 (1 0)^a 11 Dw(w) 11,  head on the leading 0, StA,

    the STABLE->MID sweep carries the digit increment (zeroing run
    over the set pairs, 4-step flip, walk back over the zeros) and
    the MID->STABLE sweep re-creates the separator two cells further
    out.  One double-sweep is the same cell-uniform binary increment
    Sc a (1^j 0 x) -> Sc (a+1) (0^j 1 x), composed by
    MeasureGlue.mrun with the measure cval and the conservation law
    S(fst x) + cval (snd x) = 2*2^t - 1.  Validated differentially
    for k = 2..8 -- 254 double-sweeps -- by tools/counters/lap33.py. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MeasureGlue ILCounter
  ExpCounter BounceCounter.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB1LD_1RC0RB_1LA1RB_0LD0LA *)
Definition tm_33 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DL StD
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S0 DR StB
  | StC, S0 => mk S1 DL StA | StC, S1 => mk S1 DR StB
  | StD, S0 => mk S0 DL StD | StD, S1 => mk S0 DL StA
  end.

(** Macro anchor: with t = to_nat p, D(t+1) = 1^(2*2^t+1) 0^(2t+2). *)
Definition Cc (p : positive) : cconf :=
  (StB, (rep [S0] (2 * Pos.to_nat p + 1)
           ++ rep [S1] (2 * 2 ^ Pos.to_nat p + 1), S0, [])).

(** Stable sweep-config (micro anchor). *)
Definition Sc (a : nat) (w : list bool) : cconf :=
  (StA, ([], S0, S0 :: rep [S1; S0] a ++ S1 :: S1 :: Dw w ++ [S1; S1])).

(** ** The unit runs *)

(** U1: sweep prologue at the left edge. *)
Lemma U1 : wsteps true true tm_33 3 (StA, ([], S0, [S0; S1; S0]))
           = Some (StB, ([S1; S1; S1], S0, [])).
Proof. reflexivity. Qed.

(** UC: the collapse crossing (2 steps per comb unit). *)
Lemma UC : wsteps true true tm_33 2 (StB, ([], S0, [S1; S0]))
           = Some (StB, ([S1; S1], S0, [])).
Proof. reflexivity. Qed.

(** UJ2: enter the separator. *)
Lemma UJ2 : wsteps true true tm_33 2 (StB, ([], S0, [S1; S1]))
            = Some (StB, ([S1; S1], S1, [])).
Proof. reflexivity. Qed.

(** UBr: the zeroing run across set digit cells (1 step/cell). *)
Lemma UBr : wsteps true true tm_33 1 (StB, ([], S1, [S1]))
            = Some (StB, ([S0], S1, [])).
Proof. reflexivity. Qed.

(** UT2: flip the stop digit. *)
Lemma UT2 : wsteps true true tm_33 4 (StB, ([], S1, [S0; S0]))
            = Some (StD, ([], S0, [S1; S1])).
Proof. reflexivity. Qed.

(** UD0: the walk back across the zeroed cells (1 step/cell). *)
Lemma UD0 : wsteps true true tm_33 1 (StD, ([S0], S0, []))
            = Some (StD, ([], S0, [S0])).
Proof. reflexivity. Qed.

(** UJ3: land on the solid block. *)
Lemma UJ3 : wsteps true true tm_33 2 (StD, ([S1; S1], S0, []))
            = Some (StA, ([], S1, [S0; S0])).
Proof. reflexivity. Qed.

(** UJ: the junction into the spread. *)
Lemma UJ : wsteps true true tm_33 1 (StA, ([S1], S1, []))
           = Some (StD, ([], S1, [S1])).
Proof. reflexivity. Qed.

(** USp: the spread crossing (2 steps per pair). *)
Lemma USp : wsteps true true tm_33 2 (StD, ([S1; S1], S1, []))
            = Some (StD, ([], S1, [S1; S0])).
Proof. reflexivity. Qed.

(** UE: the left-edge exit of a sweep. *)
Lemma UE : wsteps false true tm_33 1 (StD, ([], S1, []))
           = Some (StA, ([], S0, [S0])).
Proof. reflexivity. Qed.

(** UT1: the mid->stable turnaround, re-creating the separator. *)
Lemma UT1 : wsteps true true tm_33 3 (StB, ([S1], S0, [S0]))
            = Some (StD, ([], S1, [S1; S1])).
Proof. reflexivity. Qed.

(** UT0: the boot-in turnaround at the macro anchor. *)
Lemma UT0 : wsteps true false tm_33 3 (StB, ([S0], S0, []))
            = Some (StD, ([], S0, [S1; S1])).
Proof. reflexivity. Qed.

(** UJ0: step off the zeros onto the solid block. *)
Lemma UJ0 : wsteps true true tm_33 1 (StD, ([S1], S0, []))
            = Some (StD, ([], S1, [S0])).
Proof. reflexivity. Qed.

(** UTD: the terminal step onto the next macro anchor. *)
Lemma UTD : wsteps true false tm_33 1 (StB, ([], S1, []))
            = Some (StB, ([S0], S0, [])).
Proof. reflexivity. Qed.

(** Visit witnesses: C after 1 step, A after 2 (D is UT0's exit). *)
Lemma UV1 : wsteps true false tm_33 1 (StB, ([S0], S0, []))
            = Some (StC, ([S1; S0], S0, [])).
Proof. reflexivity. Qed.

Lemma UV2 : wsteps true false tm_33 2 (StB, ([S0], S0, []))
            = Some (StA, ([S0], S1, [S1])).
Proof. reflexivity. Qed.

(** ** Transported phases *)

Lemma phU1 : forall L R,
  csteps tm_33 3 (StA, (L, S0, S0 :: S1 :: S0 :: R))
  = Some (StB, (S1 :: S1 :: S1 :: L, S0, R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U1). Qed.

Lemma phUC : forall k L R,
  csteps tm_33 (2 * k) (StB, (L, S0, rep [S1; S0] k ++ R))
  = Some (StB, (rep [S1; S1] k ++ L, S0, R)).
Proof. intros. exact (cycR _ _ _ _ _ _ UC k L R). Qed.

Lemma phUJ2 : forall L R,
  csteps tm_33 2 (StB, (L, S0, S1 :: S1 :: R))
  = Some (StB, (S1 :: S1 :: L, S1, R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R UJ2). Qed.

Lemma phUBr : forall k L R,
  csteps tm_33 k (StB, (L, S1, rep [S1] k ++ R))
  = Some (StB, (rep [S0] k ++ L, S1, R)).
Proof.
  intros.
  pose proof (cycR _ _ _ _ _ _ UBr k L R) as H.
  rewrite Nat.mul_1_l in H.
  exact H.
Qed.

Lemma phUT2 : forall L R,
  csteps tm_33 4 (StB, (L, S1, S0 :: S0 :: R))
  = Some (StD, (L, S0, S1 :: S1 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R UT2). Qed.

Lemma phUD0 : forall k L R,
  csteps tm_33 k (StD, (rep [S0] k ++ L, S0, R))
  = Some (StD, (L, S0, rep [S0] k ++ R)).
Proof.
  intros.
  pose proof (cycL _ _ _ _ _ _ _ UD0 k L R) as H.
  rewrite Nat.mul_1_l in H; cbn [app] in H.
  exact H.
Qed.

Lemma phUJ3 : forall L R,
  csteps tm_33 2 (StD, (S1 :: S1 :: L, S0, R))
  = Some (StA, (L, S1, S0 :: S0 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R UJ3). Qed.

Lemma phUJ : forall L R,
  csteps tm_33 1 (StA, (S1 :: L, S1, R))
  = Some (StD, (L, S1, S1 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R UJ). Qed.

Lemma phUSp : forall k L R,
  csteps tm_33 (2 * k) (StD, (rep [S1; S1] k ++ L, S1, R))
  = Some (StD, (L, S1, rep [S1; S0] k ++ R)).
Proof.
  intros.
  pose proof (cycL _ _ _ _ _ _ _ USp k L R) as H; cbn [app] in H.
  exact H.
Qed.

Lemma phUE : forall R,
  csteps tm_33 1 (StD, ([], S1, R))
  = Some (StA, ([], S0, S0 :: R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R UE). Qed.

Lemma phUT1 : forall L R,
  csteps tm_33 3 (StB, (S1 :: L, S0, S0 :: R))
  = Some (StD, (L, S1, S1 :: S1 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R UT1). Qed.

Lemma phUT0 : forall L,
  csteps tm_33 3 (StB, (S0 :: L, S0, []))
  = Some (StD, (L, S0, [S1; S1])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L UT0). Qed.

Lemma phUJ0 : forall L R,
  csteps tm_33 1 (StD, (S1 :: L, S0, R))
  = Some (StD, (L, S1, S0 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R UJ0). Qed.

Lemma phUTD : forall L,
  csteps tm_33 1 (StB, (L, S1, []))
  = Some (StB, (S0 :: L, S0, [])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L UTD). Qed.

Lemma phUV1 : forall L,
  csteps tm_33 1 (StB, (S0 :: L, S0, []))
  = Some (StC, (S1 :: S0 :: L, S0, [])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L UV1). Qed.

Lemma phUV2 : forall L,
  csteps tm_33 2 (StB, (S0 :: L, S0, []))
  = Some (StA, (S0 :: L, S1, [S1])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L UV2). Qed.

(** ** The sweeps (uniform in the word suffix) *)

(** Sweep A: stable to mid -- the digit increment. *)
Lemma sweepA_33 : forall a o Y, exists n,
  csteps tm_33 n
    (StA, ([], S0, S0 :: rep [S1; S0] (S a) ++
                     S1 :: S1 :: rep [S1] o ++ S0 :: S0 :: Y))
  = Some (StA, ([], S0, S0 :: rep [S1; S0] (S a) ++
                          S1 :: S0 :: S0 :: rep [S0] o ++ S1 :: S1 :: Y))
  /\ 0 < n.
Proof.
  intros a o Y.
  change (S0 :: rep [S1; S0] (S a) ++
            S1 :: S1 :: rep [S1] o ++ S0 :: S0 :: Y)
    with (S0 :: S1 :: S0 :: rep [S1; S0] a ++
            S1 :: S1 :: rep [S1] o ++ S0 :: S0 :: Y).
  eexists. split.
  - eapply csteps_chain. { apply phU1. }
    eapply csteps_chain. { apply phUC. }
    eapply csteps_chain. { apply phUJ2. }
    eapply csteps_chain. { apply phUBr. }
    eapply csteps_chain. { apply phUT2. }
    eapply csteps_chain. { apply phUD0. }
    eapply csteps_chain. { apply phUJ3. }
    rewrite (ones_fold3 a).
    eapply csteps_chain. { apply phUJ. }
    replace (S (S (2 * a))) with (2 * S a) by lia.
    rewrite <- rep_dbl.
    rewrite <- (app_nil_r (rep [S1; S1] (S a))).
    eapply csteps_chain. { apply phUSp. }
    apply phUE.
  - lia.
Qed.

(** Sweep B: mid to stable -- re-create the separator. *)
Lemma sweepB_33 : forall a o Y, exists n,
  csteps tm_33 n
    (StA, ([], S0, S0 :: rep [S1; S0] (S a) ++
                     S1 :: S0 :: S0 :: rep [S0] o ++ S1 :: S1 :: Y))
  = Some (StA, ([], S0, S0 :: rep [S1; S0] (S (S a)) ++
                          S1 :: S1 :: rep [S0] o ++ S1 :: S1 :: Y))
  /\ 0 < n.
Proof.
  intros a o Y.
  change (S0 :: rep [S1; S0] (S a) ++
            S1 :: S0 :: S0 :: rep [S0] o ++ S1 :: S1 :: Y)
    with (S0 :: S1 :: S0 :: rep [S1; S0] a ++
            S1 :: S0 :: S0 :: rep [S0] o ++ S1 :: S1 :: Y).
  rewrite (pair_fold S1 S0 a).
  eexists. split.
  - eapply csteps_chain. { apply phU1. }
    eapply csteps_chain. { apply phUC. }
    rewrite (ones_fold3 (S a)).
    change (rep [S1] (S (S (S (2 * S a)))))
      with (S1 :: rep [S1] (S (S (2 * S a)))).
    eapply csteps_chain. { apply phUT1. }
    replace (S (S (2 * S a))) with (2 * S (S a)) by lia.
    rewrite <- rep_dbl.
    rewrite <- (app_nil_r (rep [S1; S1] (S (S a)))).
    eapply csteps_chain. { apply phUSp. }
    apply phUE.
  - lia.
Qed.

(** ** The double-sweep: a cell-uniform binary increment *)

Lemma dlap_33 : forall a j x, exists n,
  csteps tm_33 n (Sc (S a) (repeat true j ++ false :: x))
  = Some (Sc (S (S a)) (repeat false j ++ true :: x)) /\ 0 < n.
Proof.
  intros a j x.
  unfold Sc.
  rewrite !Dw_app, Dw_true, Dw_false.
  cbn [Dw].
  rewrite <- !app_assoc, !rep_dbl.
  destruct (sweepA_33 a (2 * j) (Dw x ++ [S1; S1])) as (n1 & H1 & Hn1).
  destruct (sweepB_33 a (2 * j) (Dw x ++ [S1; S1])) as (n2 & H2 & Hn2).
  exists (n1 + n2). split; [|lia].
  eapply csteps_chain; [exact H1|].
  exact H2.
Qed.

(** ** The terminal settle from the all-ones word *)

Lemma term_33 : forall a nb, exists n,
  csteps tm_33 n (Sc (S a) (repeat true nb))
  = Some (StB, (rep [S0] (S (S (S (2 * nb))))
                  ++ rep [S1] (S (S (S (S (S (2 * a)))))), S0, []))
  /\ 0 < n.
Proof.
  intros a nb.
  unfold Sc.
  rewrite Dw_true, rep_dbl.
  rewrite rep1_fold, rep1_fold, app_nil_r.
  change (S0 :: rep [S1; S0] (S a) ++
            S1 :: S1 :: rep [S1] (S (S (2 * nb))))
    with (S0 :: S1 :: S0 :: rep [S1; S0] a ++
            S1 :: S1 :: rep [S1] (S (S (2 * nb)))).
  eexists. split.
  - eapply csteps_chain. { apply phU1. }
    eapply csteps_chain. { apply phUC. }
    eapply csteps_chain. { apply phUJ2. }
    rewrite <- (app_nil_r (rep [S1] (S (S (2 * nb))))).
    eapply csteps_chain. { apply phUBr. }
    rewrite (ones_fold3 a).
    apply phUTD.
  - lia.
Qed.

(** ** The abstract recurrence and its invariant *)

Definition bstep (x : nat * list bool) : option (nat * list bool) :=
  match bview (snd x) with
  | (j, Some tl) => Some (S (fst x), repeat false j ++ true :: tl)
  | (_, None) => None
  end.

Definition bmu (x : nat * list bool) : nat := cval (snd x).

Definition Scx (x : nat * list bool) : cconf := Sc (S (fst x)) (snd x).

(** ** The macro lap *)

Lemma lap_33 : forall p,
  exists n c', csteps tm_33 n (Cc p) = Some c' /\
               lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p.
  set (t := Pos.to_nat p).
  assert (Hpos : 1 <= t) by apply Pos2Nat.is_pos.
  assert (Hpow : 2 <= 2 ^ t).
  { change 2 with (2 ^ 1) at 1. apply Nat.pow_le_mono_r; lia. }
  destruct (2 ^ t) as [|[|P']] eqn:EP; [lia | lia |].
  (* the boot-in half sweep + one mid->stable sweep *)
  assert (Hboot : exists n0,
    csteps tm_33 n0 (Cc p) = Some (Scx (S P', repeat false t)) /\ 0 < n0).
  { unfold Cc; fold t. rewrite EP.
    replace (2 * t + 1) with (S (2 * t)) by lia.
    replace (2 * S (S P') + 1) with (S (2 * S (S P'))) by lia.
    change (rep [S0] (S (2 * t)) ++ rep [S1] (S (2 * S (S P'))))
      with (S0 :: rep [S0] (2 * t) ++ S1 :: rep [S1] (2 * S (S P'))).
    rewrite <- (rep_dbl S1 (S (S P'))).
    destruct (sweepB_33 P' (2 * t) []) as (n2 & H2 & Hn2).
    rewrite (pair_fold S1 S0 (S P')) in H2.
    eexists. split.
    - eapply csteps_chain. { apply phUT0. }
      eapply csteps_chain. { apply phUD0. }
      eapply csteps_chain. { apply phUJ0. }
      rewrite <- (app_nil_r (rep [S1; S1] (S (S P')))).
      eapply csteps_chain. { apply phUSp. }
      eapply csteps_chain. { apply phUE. }
      unfold Scx, Sc; cbn [fst snd].
      rewrite Dw_false, rep_dbl.
      exact H2.
    - lia. }
  destruct Hboot as (n0 & Hb & Hn0).
  (* the measured composition over the double-sweeps *)
  assert (Hrun : exists n c',
    csteps tm_33 n (Scx (S P', repeat false t)) = Some c' /\
    lift c' = lift (Cc (Pos.succ p)) /\ 0 < n).
  { apply (mrun tm_33 _ bstep bmu
             (fun x => S (fst x) + cval (snd x) = 2 * 2 ^ t - 1 /\
                       length (snd x) = t)
             Scx (Cc (Pos.succ p))).
    - (* Hstep: one double-sweep *)
      intros [a w] [a' w'] [Hsum Hlen] Hst.
      unfold bstep in Hst; cbn [fst snd] in *.
      destruct (bview w) as [j [tl|]] eqn:Ebv; [|discriminate].
      injection Hst as <- <-.
      pose proof (bview_some w j tl Ebv) as Hw.
      pose proof (cval_step j tl) as Hcv.
      split; [|split].
      + cbn [fst snd]. split.
        * rewrite Hw in Hsum. lia.
        * rewrite Hw in Hlen. rewrite <- len_step in Hlen. lia.
      + unfold bmu; cbn [snd]. rewrite Hw. lia.
      + unfold Scx; cbn [fst snd]. rewrite Hw.
        destruct (dlap_33 a j tl) as (n & Hrun & Hn).
        eauto.
    - (* Hterm: the settle *)
      intros [a w] [Hsum Hlen] Hst.
      unfold bstep in Hst; cbn [fst snd] in *.
      destruct (bview w) as [nb [tl|]] eqn:Ebv; [discriminate|].
      pose proof (bview_none w nb Ebv) as Hw.
      rewrite Hw in Hsum, Hlen |- *.
      rewrite repeat_length in Hlen. subst nb.
      rewrite cval_true in Hsum.
      unfold Scx; cbn [fst snd].
      destruct (term_33 a t) as (n & Hrun & Hn).
      exists n. eexists. split; [exact Hrun|]. split; [|exact Hn].
      unfold Cc.
      rewrite Pos2Nat.inj_succ; fold t.
      rewrite Nat.pow_succ_r'.
      rewrite EP.
      replace (2 * S t + 1) with (S (S (S (2 * t)))) by lia.
      replace (2 * (2 * S (S P')) + 1)
        with (S (S (S (S (S (2 * a)))))) by lia.
      reflexivity.
    - (* the initial state satisfies the invariant *)
      cbn [fst snd]. split; [|apply repeat_length].
      pose proof (cval_false t) as Hcf. lia. }
  destruct Hrun as (n1 & c' & Hr & Hl & Hn1).
  exists (n0 + n1), c'.
  split; [|split; [exact Hl | lia]].
  eapply csteps_chain; eauto.
Qed.

(** ** Bootstrap, visits, and the theorem *)

Lemma boot_33 : exists t0, stepn tm_33 t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 33.
  assert (H : match csteps tm_33 33 c0 with
              | Some c => ceqb c (Cc 1)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm_33 33 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
  f_equal. apply ceqb_lift. exact H.
Qed.

Lemma vis_33 : forall p q,
  exists k c, csteps tm_33 k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q.
  unfold Cc.
  replace (2 * Pos.to_nat p + 1) with (S (2 * Pos.to_nat p)) by lia.
  destruct q.
  - exists 2. eexists. split; [apply phUV2 | reflexivity].
  - exists 0. eexists. split; reflexivity.
  - exists 1. eexists. split; [apply phUV1 | reflexivity].
  - exists 3. eexists. split; [apply phUT0 | reflexivity].
Qed.

(** #33 never quasihalts: bbchallenge 1RB1LD_1RC0RB_1LA1RB_0LD0LA. *)
Theorem nqh_1RB1LD_1RC0RB_1LA1RB_0LD0LA : NeverQuasiHaltsSt tm_33.
Proof.
  apply (glue_neverqh tm_33 Cc 1).
  - exact boot_33.
  - intros p _. apply lap_33.
  - intros p q _. apply vis_33.
Qed.

Theorem tm_33_nonhalt : NonHalt tm_33.
Proof. apply never_qh_nonhalt, nqh_1RB1LD_1RC0RB_1LA1RB_0LD0LA. Qed.
