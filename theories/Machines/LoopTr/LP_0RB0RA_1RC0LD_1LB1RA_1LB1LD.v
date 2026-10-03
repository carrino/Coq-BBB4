(** * LP_0RB0RA_1RC0LD_1LB1RA_1LB1LD (SCOPING_INSTR 7.4.LE10)

    A mirror counter with an offset and a two-bit top.  [A [1]] sits at
    the junction [JL] between a left string of 2-cell digits ([00] / [11],
    count [n], then the marker [11]) and a right string of 5-cell digits
    ([10111] / [10101], count [n + 1] mod [2^mR]).  Bits [mR] and [mR+1] of
    the right count are held by the tail [T0]..[T3], and the right carry
    into it ([top0]..[top3]) steps [T0 -> T1 -> T2 -> T3 -> 10111 T0].
    The left carry [armL] walks [D] left over the [11]s, turns at the first
    [00], and sweeps [A] back, restoring the junction.  So one lap is four
    [mirror_inc] runs ([iter]) and four top steps.  The last increment
    carries the left counter onto blank tape, where the blank acts as the
    digit [00] and the marker becomes a digit.  The lap ends at the same
    anchor with both widths one larger ([fin], [lap_g]).

    Hand-stated, kernel-checked.  Axiom footprint: [functional_extensionality_dep]. *)
From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr LoopMirrorTr.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.

Definition tm_0RB0RA_1RC0LD_1LB1RA_1LB1LD : TM := fun q s => match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB) | StA, S1 => Some (mkTrans S0 DR StA)
  | StB, S0 => Some (mkTrans S1 DR StC) | StB, S1 => Some (mkTrans S0 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StB) | StC, S1 => Some (mkTrans S1 DR StA)
  | StD, S0 => Some (mkTrans S1 DL StB) | StD, S1 => Some (mkTrans S1 DL StD)
  end.
Local Notation tm := (tm_wrap_trs tm_0RB0RA_1RC0LD_1LB1RA_1LB1LD []).
Local Notation ZL := [S0; S0].
Local Notation OL := [S1; S1].
Local Notation Zp := [S1; S0; S1; S1; S1].
Local Notation Op := [S1; S0; S1; S0; S1].
Local Notation W := [S1; S1; S0; S1; S1].
Local Notation JL := [S1; S1; S0; S1; S1; S1; S1].
Local Notation JM := [S1; S1; S1; S0; S1; S1; S1].
Local Notation T0 := [S1; S0; S1; S0; S1].
Local Notation T1 := [S1; S0; S1; S1; S0; S1; S0; S1].
Local Notation T2 := [S1; S0; S1; S0; S0; S1; S0; S1].
Local Notation T3 := [S1; S0; S1; S0; S1; S1; S0; S1].

Definition mk1 (Lc Rc : list Sym) : cconf := cR StA (JL ++ Lc) Rc.
Definition mk2 (Lc Rc : list Sym) : cconf := cL StD (JL ++ Lc) Rc.

Lemma aO : forall n L R, Reach0 tm (cR StA L (rep Op n ++ R)) (cR StA (rep W n ++ L) R).
Proof. apply sweepR. intros L R. rr 9. r0. Qed.

Lemma dW : forall n L R, Reach0 tm (cL StD (rep W n ++ L) R) (cL StD L (rep Zp n ++ R)).
Proof. apply sweepL. intros L R. rr 5. r0. Qed.

Lemma dO : forall n L R, Reach0 tm (cL StD (rep OL n ++ L) R) (cL StD L (rep OL n ++ R)).
Proof. apply sweepL. intros L R. rr 2. r0. Qed.

Lemma aOL : forall n L R, Reach0 tm (cR StA L (rep OL n ++ R)) (cR StA (rep ZL n ++ L) R).
Proof. apply sweepR. intros L R. rr 2. r0. Qed.

Lemma armR : forall k r Lc R',
  Reach1 tm (mk1 Lc (bcells Zp Op (repeat true k ++ false :: r) ++ R'))
            (mk2 Lc (bcells Zp Op (repeat false k ++ true :: r) ++ R')).
Proof.
  intros k r Lc R'. rewrite bcells_tt, bcells_ff, bcells_f, bcells_t, <- !app_assoc. unfold mk1, mk2.
  eapply reach01; [apply aO|]. rr 11.
  change (StD, (ctl (rep W k ++ JL ++ Lc), chd (rep W k ++ JL ++ Lc), Op ++ bcells Zp Op r ++ R'))
    with (cL StD (rep W k ++ JL ++ Lc) (Op ++ bcells Zp Op r ++ R')).
  rt (dW k (JL ++ Lc) (Op ++ bcells Zp Op r ++ R')). r0.
Qed.

Lemma armL : forall k r L' Rc,
  Reach0 tm (mk2 (bcells ZL OL (repeat true k ++ false :: r) ++ L') Rc)
            (mk1 (bcells ZL OL (repeat false k ++ true :: r) ++ L') Rc).
Proof.
  intros k r L' Rc. rewrite bcells_tt, bcells_ff, bcells_f, bcells_t, <- !app_assoc. unfold mk1, mk2.
  set (X := bcells ZL OL r ++ L').
  rr 7.
  change (StD, (ctl (rep OL k ++ ZL ++ X), chd (rep OL k ++ ZL ++ X), JM ++ Rc))
    with (cL StD (rep OL k ++ ZL ++ X) (JM ++ Rc)).
  rt (dO k (ZL ++ X) (JM ++ Rc)). unfold cL; cbn [chd ctl app]. rr 3.
  change (StA, (S1 :: S1 :: X, chd (rep OL k ++ JM ++ Rc), ctl (rep OL k ++ JM ++ Rc)))
    with (cR StA (OL ++ X) (rep OL k ++ JM ++ Rc)).
  rt (aOL k (OL ++ X) (JM ++ Rc)). rr 25. rfix.
Qed.

Definition mc (mL mR nl nr : nat) (Tj : list Sym) : cconf :=
  mk1 (bcells ZL OL (nb mL nl) ++ OL) (bcells Zp Op (nb mR nr) ++ Tj).

Lemma inc : forall mL mR nl nr Tj, S nl < 2 ^ mL -> S nr < 2 ^ mR ->
  Reach0 tm (mc mL mR nl nr Tj) (mc mL mR (S nl) (S nr) Tj).
Proof.
  intros mL mR nl nr Tj Hl Hr. unfold mc. rewrite (nb_succ mL nl Hl), (nb_succ mR nr Hr).
  apply (mirror_inc tm mk1 mk2 ZL OL Zp Op (fun k r Lc R0 => reach1_0 _ _ _ (armR k r Lc R0)) armL);
    apply nb_split; assumption.
Qed.

Lemma iter : forall d mL mR nl nr Tj, nl + d < 2 ^ mL -> nr + d < 2 ^ mR ->
  Reach0 tm (mc mL mR nl nr Tj) (mc mL mR (nl + d) (nr + d) Tj).
Proof.
  induction d as [|d IH]; intros mL mR nl nr Tj Hl Hr.
  - rewrite !Nat.add_0_r. r0.
  - eapply reach0_trans; [apply inc; lia|].
    replace (nl + S d) with (S nl + d) by lia. replace (nr + S d) with (S nr + d) by lia.
    apply IH; lia.
Qed.

Lemma top : forall Tj Tj', (forall k Lc, Reach0 tm (mk1 Lc (rep Op k ++ Tj)) (mk2 Lc (rep Zp k ++ Tj'))) ->
  forall mL mR nl, S nl < 2 ^ mL ->
  Reach0 tm (mc mL mR nl (2 ^ mR - 1) Tj) (mk1 (bcells ZL OL (nb mL (S nl)) ++ OL) (rep Zp mR ++ Tj')).
Proof.
  intros Tj Tj' Ht mL mR nl Hl. unfold mc. rewrite nb_full, bcells_alltrue, (nb_succ mL nl Hl).
  destruct (nb_split mL nl ltac:(lia)) as (k & r & ->). rewrite binc_int.
  eapply reach0_trans; [apply Ht|]. apply armL.
Qed.

Lemma top0 : forall k Lc, Reach0 tm (mk1 Lc (rep Op k ++ T0)) (mk2 Lc (rep Zp k ++ T1)).
Proof.
  intros k Lc. unfold mk1, mk2. rt (aO k (JL ++ Lc) T0). rr 19.
  change (StD, (ctl (rep W k ++ JL ++ Lc), chd (rep W k ++ JL ++ Lc), T1))
    with (cL StD (rep W k ++ JL ++ Lc) T1).
  rt (dW k (JL ++ Lc) T1). r0.
Qed.

Lemma top1 : forall k Lc, Reach0 tm (mk1 Lc (rep Op k ++ T1)) (mk2 Lc (rep Zp k ++ T2)).
Proof.
  intros k Lc. unfold mk1, mk2. rt (aO k (JL ++ Lc) T1). rr 11.
  change (StD, (ctl (rep W k ++ JL ++ Lc), chd (rep W k ++ JL ++ Lc), T2))
    with (cL StD (rep W k ++ JL ++ Lc) T2).
  rt (dW k (JL ++ Lc) T2). r0.
Qed.

Lemma top2 : forall k Lc, Reach0 tm (mk1 Lc (rep Op k ++ T2)) (mk2 Lc (rep Zp k ++ T3)).
Proof.
  intros k Lc. unfold mk1, mk2. rt (aO k (JL ++ Lc) T2). rr 13.
  change (StD, (ctl (rep W k ++ JL ++ Lc), chd (rep W k ++ JL ++ Lc), T3))
    with (cL StD (rep W k ++ JL ++ Lc) T3).
  rt (dW k (JL ++ Lc) T3). r0.
Qed.

Lemma top3 : forall k Lc, Reach0 tm (mk1 Lc (rep Op k ++ T3)) (mk2 Lc (rep Zp k ++ Zp ++ T0)).
Proof.
  intros k Lc. unfold mk1, mk2. rt (aO k (JL ++ Lc) T3). rr 27.
  change (StD, (ctl (rep W k ++ JL ++ Lc), chd (rep W k ++ JL ++ Lc), Zp ++ T0))
    with (cL StD (rep W k ++ JL ++ Lc) (Zp ++ T0)).
  rt (dW k (JL ++ Lc) (Zp ++ T0)). r0.
Qed.

Lemma zero_r : forall mR Tj, rep Zp mR ++ Tj = bcells Zp Op (nb mR 0) ++ Tj.
Proof. intros. rewrite nb_zero, bcells_allfalse. reflexivity. Qed.

Lemma fin : forall mL mR,
  Reach1 tm (mk1 (rep OL mL ++ OL) (rep Zp mR ++ Zp ++ T0)) (mc (S mL) (S mR) 0 1 T0).
Proof.
  intros mL mR. unfold mc. rewrite nb_one, nb_zero, bcells_t, !bcells_allfalse, rep_snoc.
  pose proof (armR 0 (repeat false mR) (rep OL mL ++ OL) T0) as H.
  cbn [repeat app] in H. rewrite bcells_f, bcells_t, bcells_allfalse in H.
  eapply reach10; [exact H|].
  pose proof (armL (S mL) [] [] (Op ++ rep Zp mR ++ T0)) as H'.
  rewrite bcells_tt, bcells_ff, bcells_f, bcells_t in H'. cbn [bcells flat_map] in H'.
  rewrite !app_nil_r in H'.
  eapply reach0_lift_l; [|rewrite <- app_assoc; exact H'].
  unfold mk2, cL. rewrite rep_S_r, <- !app_assoc. cbn [app chd ctl].
  change [S1; S1; S0; S0] with (OL ++ rep [S0] 2). rewrite (app_assoc (rep OL mL) OL).
  rewrite !app_comm_cons. symmetry. apply lift_padL.
Qed.

Lemma lap_g : forall mR, 1 <= mR -> Reach1 tm (mc (S (S mR)) mR 0 1 T0) (mc (S (S (S mR))) (S mR) 0 1 T0).
Proof.
  intros mR Hm.
  assert (E : 2 ^ S (S mR) = 4 * 2 ^ mR) by (rewrite !pow2_S; lia).
  assert (H2 : 2 <= 2 ^ mR) by (destruct mR as [|m]; [lia|]; rewrite pow2_S; pose proof (Nat.pow_nonzero 2 m ltac:(lia)); lia).
  eapply reach01.
  { replace (2 ^ mR - 2) with (0 + (2 ^ mR - 2)) by lia. apply (iter (2 ^ mR - 2) _ _ 0 1); lia. }
  replace (1 + (2 ^ mR - 2)) with (2 ^ mR - 1) by lia.
  eapply reach01; [apply (top _ _ top0); lia|]. rewrite zero_r.
  eapply reach01; [apply (iter (2 ^ mR - 1)); lia|]. rewrite Nat.add_0_l.
  eapply reach01; [apply (top _ _ top1); lia|]. rewrite zero_r.
  eapply reach01; [apply (iter (2 ^ mR - 1)); lia|]. rewrite Nat.add_0_l.
  eapply reach01; [apply (top _ _ top2); lia|]. rewrite zero_r.
  eapply reach01; [apply (iter (2 ^ mR - 1)); lia|]. rewrite Nat.add_0_l.
  eapply reach01; [apply (top _ _ top3); lia|].
  replace (S (S (S (S (2 ^ mR - 2) + (2 ^ mR - 1)) + (2 ^ mR - 1)) + (2 ^ mR - 1)))
    with (2 ^ S (S mR) - 1) by lia.
  rewrite nb_full, bcells_alltrue. apply fin.
Qed.

Definition Cf (i : nat) : cconf := mc (S (S (S i))) (S i) 0 1 T0.

Lemma lap : forall i, Reach1 tm (Cf i) (Cf (S i)).
Proof. intros i. apply lap_g. lia. Qed.

Lemma p0 : forall i, Reach0 tm (Cf i) (mc (S (S (S i))) (S i) (2 ^ S i - 2) (2 ^ S i - 1) T0).
Proof.
  intros i. assert (H2 : 2 <= 2 ^ S i) by (rewrite pow2_S; pose proof (Nat.pow_nonzero 2 i ltac:(lia)); lia).
  assert (E : 2 ^ S (S (S i)) = 4 * 2 ^ S i) by (rewrite !pow2_S; lia).
  unfold Cf. replace (2 ^ S i - 2) with (0 + (2 ^ S i - 2)) by lia.
  replace (2 ^ S i - 1) with (1 + (2 ^ S i - 2)) by lia. apply iter; lia.
Qed.

Lemma cf_eq : forall i, Cf (S i) = mk1 (rep ZL (S (S (S (S i)))) ++ OL) (Op ++ Zp ++ rep Zp i ++ T0).
Proof.
  intros i. unfold Cf, mc. rewrite nb_zero, bcells_allfalse, nb_one, bcells_t, bcells_allfalse.
  cbn [rep]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma fires : forall t, ~ In t [] -> forall i, Fires tm (Cf i) t.
Proof.
  intros [q s] _ [|i].
  - unfold Cf, mc, mk1, cR. cbn. destruct q, s; fire_find.
  - destruct q, s;
    first [ rewrite cf_eq; unfold mk1; fire_find
          | eapply fire_back; [apply p0|]; unfold mc; rewrite nb_full, bcells_alltrue; unfold mk1;
            eapply fire_back; [apply aO|]; fire_find ].
Qed.

Theorem nqhtr_0RB0RA_1RC0LD_1LB1RA_1LB1LD : NeverQuasiHaltsTr tm_0RB0RA_1RC0LD_1LB1RA_1LB1LD.
Proof.
  apply (boardS_neverqhtr _ [] Cf lap fires 432).
  apply boot_ok. vm_compute. reflexivity.
Qed.
