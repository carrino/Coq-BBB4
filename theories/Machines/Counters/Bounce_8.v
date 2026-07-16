(** * Bounce_8: the bounce_counter machine #8, 1RB0LC_1LC0RB_1RD1LA_0LA1RB.

    First machine of the BBB harness's [bounce_counter] family
    (certificate results/counter8.cert; the QUAD geometric-rollover
    class).  The macro anchor is

      D(k) = 1^m 0^(2k+1),  m = 2^k - 1,  head on the last 0, StB.

    One macro lap D(k) -> D(k+1) is NOT a single parametric run: it
    chains 2^(k-1)-1 double-sweeps of a nested working-area binary
    counter.  Stable sweep-configs are

      Sc a w = (0 1)^(a+1) 00 Dw(w) 11,  head on the first cell, StA,

    with w the digit word (00/11 pairs).  One double-sweep is the
    CELL-UNIFORM binary increment  Sc a (1^j 0 x) -> Sc (a+1) (0^j 1 x)
    -- the C verifier's interior/overflow split is pure decode (the
    flipped top digit merges with the accumulator as cells), so no
    case analysis survives at the cell level.  Each sweep is a
    collapse crossing (4-step cycle), a bounded turnaround, and a
    spread crossing (2-step cycle) back to the left edge.

    The macro lap composes: a boot-in half sweep, MeasureGlue.mrun
    over the increment recurrence (measure = cval, the complement
    value of the word, decrementing by exactly 1 per double-sweep,
    with the conservation law  S(fst x) + cval (snd x) = 2*2^t - 2
    as the invariant), and a terminal settle from the all-ones word.
    LapGlue.glue_neverqh then closes never-quasihalting over the
    macro family.  Everything validated differentially for
    k = 2..9 -- 510 double-sweeps -- by tools/counters/lap8.py. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MeasureGlue ILCounter
  ExpCounter BounceCounter.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB0LC_1LC0RB_1RD1LA_0LA1RB *)
Definition tm_8 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DL StC
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S0 DR StB
  | StC, S0 => mk S1 DR StD | StC, S1 => mk S1 DL StA
  | StD, S0 => mk S0 DL StA | StD, S1 => mk S1 DR StB
  end.

(** Macro anchor: with t = to_nat p, D(t+1) = 1^(2*2^t-1) 0^(2t+3). *)
Definition Cc (p : positive) : cconf :=
  (StB, (rep [S0] (2 * Pos.to_nat p + 2)
           ++ rep [S1] (2 * 2 ^ Pos.to_nat p - 1), S0, [])).

(** Stable sweep-config (micro anchor). *)
Definition Sc (a : nat) (w : list bool) : cconf :=
  (StA, ([], S0, S1 :: rep [S0; S1] a ++ S0 :: S0 :: Dw w ++ [S1; S1])).

(** ** The unit runs *)

(** U1: sweep prologue at the left edge. *)
Lemma U1 : wsteps true true tm_8 5 (StA, ([], S0, [S1; S0; S1]))
           = Some (StB, ([S1; S1; S1], S1, [])).
Proof. reflexivity. Qed.

(** UC: the collapse crossing (4 steps per comb unit). *)
Lemma UC : wsteps true true tm_8 4 (StB, ([], S1, [S0; S1]))
           = Some (StB, ([S1; S1], S1, [])).
Proof. reflexivity. Qed.

(** UT1: the turnaround, flipping a 00 pair to 11. *)
Lemma UT1 : wsteps true true tm_8 6 (StB, ([], S1, [S0; S0]))
            = Some (StA, ([], S1, [S1; S1])).
Proof. reflexivity. Qed.

(** UBr: the zeroing run across set digit cells (1 step/cell). *)
Lemma UBr : wsteps true true tm_8 1 (StB, ([], S1, [S1]))
            = Some (StB, ([S0], S1, [])).
Proof. reflexivity. Qed.

(** UZ: the walk back across the zeroed cells (3 steps/cell). *)
Lemma UZ : wsteps true true tm_8 3 (StA, ([S0], S1, []))
           = Some (StA, ([], S1, [S0])).
Proof. reflexivity. Qed.

(** USp: the spread crossing (2 steps per pair). *)
Lemma USp : wsteps true true tm_8 2 (StA, ([S1; S1], S1, []))
            = Some (StA, ([], S1, [S1; S0])).
Proof. reflexivity. Qed.

(** UE: the left-edge exit of a sweep. *)
Lemma UE : wsteps false true tm_8 2 (StA, ([S1], S1, []))
           = Some (StA, ([], S0, [S1; S0])).
Proof. reflexivity. Qed.

(** UT0: the boot-in turnaround at the macro anchor. *)
Lemma UT0 : wsteps true false tm_8 5 (StB, ([S0], S0, []))
            = Some (StA, ([], S1, [S1; S1])).
Proof. reflexivity. Qed.

(** UTD: the terminal step onto the next macro anchor. *)
Lemma UTD : wsteps true false tm_8 1 (StB, ([], S1, []))
            = Some (StB, ([S0], S0, [])).
Proof. reflexivity. Qed.

(** Visit witnesses: C after 1 step, D after 2 (A is UT0's exit). *)
Lemma UV1 : wsteps true false tm_8 1 (StB, ([S0], S0, []))
            = Some (StC, ([], S0, [S1])).
Proof. reflexivity. Qed.

Lemma UV2 : wsteps true false tm_8 2 (StB, ([S0], S0, []))
            = Some (StD, ([S1], S1, [])).
Proof. reflexivity. Qed.

(** ** Transported phases *)

Lemma phU1 : forall L R,
  csteps tm_8 5 (StA, (L, S0, S1 :: S0 :: S1 :: R))
  = Some (StB, (S1 :: S1 :: S1 :: L, S1, R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U1). Qed.

Lemma phUC : forall k L R,
  csteps tm_8 (4 * k) (StB, (L, S1, rep [S0; S1] k ++ R))
  = Some (StB, (rep [S1; S1] k ++ L, S1, R)).
Proof. intros. exact (cycR _ _ _ _ _ _ UC k L R). Qed.

Lemma phUT1 : forall L R,
  csteps tm_8 6 (StB, (L, S1, S0 :: S0 :: R))
  = Some (StA, (L, S1, S1 :: S1 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R UT1). Qed.

Lemma phUBr : forall k L R,
  csteps tm_8 k (StB, (L, S1, rep [S1] k ++ R))
  = Some (StB, (rep [S0] k ++ L, S1, R)).
Proof.
  intros.
  pose proof (cycR _ _ _ _ _ _ UBr k L R) as H.
  rewrite Nat.mul_1_l in H.
  exact H.
Qed.

Lemma phUZ : forall k L R,
  csteps tm_8 (3 * k) (StA, (rep [S0] k ++ L, S1, R))
  = Some (StA, (L, S1, rep [S0] k ++ R)).
Proof.
  intros.
  pose proof (cycL _ _ _ _ _ _ _ UZ k L R) as H; cbn [app] in H.
  exact H.
Qed.

Lemma phUSp : forall k L R,
  csteps tm_8 (2 * k) (StA, (rep [S1; S1] k ++ L, S1, R))
  = Some (StA, (L, S1, rep [S1; S0] k ++ R)).
Proof.
  intros.
  pose proof (cycL _ _ _ _ _ _ _ USp k L R) as H; cbn [app] in H.
  exact H.
Qed.

Lemma phUE : forall R,
  csteps tm_8 2 (StA, ([S1], S1, R))
  = Some (StA, ([], S0, S1 :: S0 :: R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R UE). Qed.

Lemma phUT0 : forall L,
  csteps tm_8 5 (StB, (S0 :: L, S0, []))
  = Some (StA, (L, S1, [S1; S1])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L UT0). Qed.

Lemma phUTD : forall L,
  csteps tm_8 1 (StB, (L, S1, []))
  = Some (StB, (S0 :: L, S0, [])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L UTD). Qed.

Lemma phUV1 : forall L,
  csteps tm_8 1 (StB, (S0 :: L, S0, []))
  = Some (StC, (L, S0, [S1])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L UV1). Qed.

Lemma phUV2 : forall L,
  csteps tm_8 2 (StB, (S0 :: L, S0, []))
  = Some (StD, (S1 :: L, S1, [])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L UV2). Qed.

(** ** The sweeps (uniform in the word suffix) *)

(** Sweep A: stable to mid -- flip the separator, one comb unit out. *)
Lemma sweepA_8 : forall a Y, exists n,
  csteps tm_8 n
    (StA, ([], S0, S1 :: rep [S0; S1] (S a) ++ S0 :: S0 :: Y))
  = Some (StA, ([], S0, S1 :: S0 :: rep [S1; S0] (S a) ++ S1 :: S1 :: Y))
  /\ 0 < n.
Proof.
  intros a Y.
  eexists. split.
  - eapply csteps_chain. { apply phU1. }
    eapply csteps_chain. { apply phUC. }
    eapply csteps_chain. { apply phUT1. }
    rewrite (pair_fold S1 S1 a).
    eapply csteps_chain. { apply phUSp. }
    apply phUE.
  - lia.
Qed.

(** Sweep B: mid to stable -- carry through the block, flip the stop
    pair, walk back, one more comb unit. *)
Lemma sweepB_8 : forall a o Y, exists n,
  csteps tm_8 n
    (StA, ([], S0, S1 :: S0 :: rep [S1; S0] (S a) ++
                     S1 :: rep [S1] o ++ S0 :: S0 :: Y))
  = Some (StA, ([], S0, S1 :: rep [S0; S1] (S (S a)) ++
                          S0 :: rep [S0] o ++ S1 :: S1 :: Y))
  /\ 0 < n.
Proof.
  intros a o Y.
  rewrite <- (comb_rot0 S0 S1 (S (S a))).
  rewrite (comb_rot1 S0 S1 (S a)).
  change (S1 :: rep [S0; S1] (S (S a)) ++ rep [S1] o ++ S0 :: S0 :: Y)
    with (S1 :: S0 :: S1 :: rep [S0; S1] (S a) ++ rep [S1] o ++ S0 :: S0 :: Y).
  eexists. split.
  - eapply csteps_chain. { apply phU1. }
    eapply csteps_chain. { apply phUC. }
    eapply csteps_chain. { apply phUBr. }
    eapply csteps_chain. { apply phUT1. }
    eapply csteps_chain. { apply phUZ. }
    rewrite (pair_fold S1 S1 (S a)).
    eapply csteps_chain. { apply phUSp. }
    apply phUE.
  - lia.
Qed.

(** ** The double-sweep: a cell-uniform binary increment *)

Lemma dlap_8 : forall a j x, exists n,
  csteps tm_8 n (Sc (S a) (repeat true j ++ false :: x))
  = Some (Sc (S (S a)) (repeat false j ++ true :: x)) /\ 0 < n.
Proof.
  intros a j x.
  unfold Sc.
  rewrite !Dw_app, Dw_true, Dw_false.
  cbn [Dw].
  rewrite <- !app_assoc, !rep_dbl.
  destruct (sweepA_8 a (rep [S1] (2 * j) ++ S0 :: S0 :: Dw x ++ [S1; S1]))
    as (n1 & H1 & Hn1).
  destruct (sweepB_8 a (S (2 * j)) (Dw x ++ [S1; S1]))
    as (n2 & H2 & Hn2).
  exists (n1 + n2). split; [|lia].
  eapply csteps_chain; [exact H1|].
  exact H2.
Qed.

(** ** The terminal settle from the all-ones word *)

Lemma term_8 : forall a nb, exists n,
  csteps tm_8 n (Sc (S a) (repeat true nb))
  = Some (StB, (rep [S0] (S (S (S (S (2 * nb)))))
                  ++ rep [S1] (S (S (S (2 * S a)))), S0, []))
  /\ 0 < n.
Proof.
  intros a nb.
  unfold Sc.
  rewrite Dw_true, rep_dbl, <- ones_fold3.
  rewrite rep1_fold, rep1_fold, app_nil_r.
  destruct (sweepA_8 a (rep [S1] (S (S (2 * nb)))))
    as (n1 & H1 & Hn1).
  rewrite (comb_rot1 S0 S1 (S a)) in H1.
  eexists. split.
  - eapply csteps_chain. { exact H1. }
    change (S1 :: rep [S0; S1] (S (S a)) ++ S1 :: rep [S1] (S (S (2 * nb))))
      with (S1 :: S0 :: S1 :: rep [S0; S1] (S a) ++
              S1 :: rep [S1] (S (S (2 * nb)))).
    eapply csteps_chain. { apply phU1. }
    eapply csteps_chain. { apply phUC. }
    change (S1 :: rep [S1] (S (S (2 * nb))))
      with (rep [S1] (S (S (S (2 * nb))))).
    rewrite <- (app_nil_r (rep [S1] (S (S (S (2 * nb)))))).
    eapply csteps_chain. { apply phUBr. }
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

Lemma lap_8 : forall p,
  exists n c', csteps tm_8 n (Cc p) = Some c' /\
               lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p.
  set (t := Pos.to_nat p).
  assert (Hpos : 1 <= t) by apply Pos2Nat.is_pos.
  assert (Hpow : 2 <= 2 ^ t).
  { change 2 with (2 ^ 1) at 1. apply Nat.pow_le_mono_r; lia. }
  destruct (2 ^ t) as [|[|P']] eqn:EP; [lia | lia |].
  (* the boot-in half sweep, D(t+1) -> Sc (S P') 0^t *)
  assert (Hboot : exists n0,
    csteps tm_8 n0 (Cc p) = Some (Scx (P', repeat false t)) /\ 0 < n0).
  { unfold Cc; fold t. rewrite EP.
    replace (2 * t + 2) with (S (S (2 * t))) by lia.
    replace (2 * S (S P') - 1) with (S (2 * S P')) by lia.
    rewrite solid_split.
    change (rep [S0] (S (S (2 * t))) ++ rep [S1; S1] (S P') ++ [S1])
      with (S0 :: rep [S0] (S (2 * t)) ++ rep [S1; S1] (S P') ++ [S1]).
    eexists. split.
    - eapply csteps_chain. { apply phUT0. }
      eapply csteps_chain. { apply phUZ. }
      eapply csteps_chain. { apply phUSp. }
      unfold Scx, Sc; cbn [fst snd].
      rewrite Dw_false, rep_dbl.
      rewrite <- (comb_rot0 S0 S1 (S P')).
      apply phUE.
    - lia. }
  destruct Hboot as (n0 & Hb & Hn0).
  (* the measured composition over the double-sweeps *)
  assert (Hrun : exists n c',
    csteps tm_8 n (Scx (P', repeat false t)) = Some c' /\
    lift c' = lift (Cc (Pos.succ p)) /\ 0 < n).
  { apply (mrun tm_8 _ bstep bmu
             (fun x => S (fst x) + cval (snd x) = 2 * 2 ^ t - 2 /\
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
      + cbn [fst snd]. split; [|rewrite Hw in Hlen; rewrite <- len_step in Hlen; lia].
        rewrite Hw in Hsum. lia.
      + unfold bmu; cbn [snd]. rewrite Hw. lia.
      + unfold Scx; cbn [fst snd]. rewrite Hw.
        destruct (dlap_8 a j tl) as (n & Hrun & Hn).
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
      destruct (term_8 a t) as (n & Hrun & Hn).
      exists n. eexists. split; [exact Hrun|]. split; [|exact Hn].
      unfold Cc.
      rewrite Pos2Nat.inj_succ; fold t.
      rewrite Nat.pow_succ_r'.
      rewrite EP.
      replace (2 * S t + 2) with (S (S (S (S (2 * t))))) by lia.
      replace (2 * (2 * S (S P')) - 1) with (S (S (S (2 * S a)))) by lia.
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

Lemma boot_8 : exists t0, stepn tm_8 t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 34.
  assert (H : match csteps tm_8 34 c0 with
              | Some c => ceqb c (Cc 1)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm_8 34 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
  f_equal. apply ceqb_lift. exact H.
Qed.

Lemma vis_8 : forall p q,
  exists k c, csteps tm_8 k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q.
  unfold Cc.
  replace (2 * Pos.to_nat p + 2) with (S (S (2 * Pos.to_nat p))) by lia.
  destruct q.
  - exists 5. eexists. split; [apply phUT0 | reflexivity].
  - exists 0. eexists. split; reflexivity.
  - exists 1. eexists. split; [apply phUV1 | reflexivity].
  - exists 2. eexists. split; [apply phUV2 | reflexivity].
Qed.

(** #8 never quasihalts: bbchallenge 1RB0LC_1LC0RB_1RD1LA_0LA1RB. *)
Theorem nqh_1RB0LC_1LC0RB_1RD1LA_0LA1RB : NeverQuasiHaltsSt tm_8.
Proof.
  apply (glue_neverqh tm_8 Cc 1).
  - exact boot_8.
  - intros p _. apply lap_8.
  - intros p q _. apply vis_8.
Qed.

Theorem tm_8_nonhalt : NonHalt tm_8.
Proof. apply never_qh_nonhalt, nqh_1RB0LC_1LC0RB_1RD1LA_0LA1RB. Qed.
