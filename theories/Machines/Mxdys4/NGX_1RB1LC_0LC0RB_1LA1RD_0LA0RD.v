(** * 1RB1LC_0LC0RB_1LA1RD_0LA0RD -- never quasihalts.

    Row 1 of the four handed over in [docs/WAVE36_MXDYS_FOUR.md].  The
    [NGramHist] closure discharges the liveness of [StA], [StB] and [StC];
    it cannot discharge [StD] at any rung, and neither can anything else in
    the [ReachSt] tier -- [StD] recurs on a [Theta(2^width)] schedule while
    every measure in that tier is linear in the tape (section 3 of the
    write-up).  So [StD] is proved here by hand, off the machine's macro
    system.

    THE MACRO SYSTEM (section 2a, restated on [cconf]).  The orbit keeps
    the right half-tape a bare unary run followed by a blank, so every
    [StA] configuration is

      Cf l s R Z = (StA, (l, s, rep [S1] R ++ S0 :: Z))

    with [l] the left half-tape (nearest cell first, so [length l] is the
    head position and [last l] the frame's cell 0) and [Z] a tail no rule
    ever reaches.  Four rules, each starting and ending in [StA]:

      (1) s=S0, R=k+2       -> (0^k ++ S1::l, S0, 1)        k+5 steps
      (2) s=S0, R<=1        -> (l, S1, R)                   4   steps
      (4) s=S1, l=S0::l1    -> (ctl l1, chd l1, R+2)        2   steps
      (5) s=S1, l=S1::L     -> (0^R ++ S1::L, S0, 0)        R+4 steps

    [StD] fires exactly at rule 5 and at rule 2 with R=0, and at no other
    point of any rule.

    THE ARGUMENT (section 4).  With [bval] the left half-tape read as a
    binary number (nearest cell least significant) put

      mu l s R = 2^R * (2 * bval l + sval s + 1)      Wd l R = |l| + 1 + R

    Rules 1, 2 and 4 each strictly increase [mu] and preserve [Wd], and
    [mu <= 2^Wd] always, so no run of 1/2/4 alone is infinite.  The one
    way out is that rule 4 at [l = []] or [l = [S0]] WIDENS the frame --
    which is exactly the parity lock of section 4: with [length l] odd and
    [last l = S1], [length l = 1] forces [l = [S1]], which is rule 5's
    guard and not rule 4's.  Rules 1, 2 and 4 preserve that invariant
    ([IO]), so from an [IO] configuration rule 5 is forced.

    Rule 5 leaves [IO] (it sets [R := 0]), landing in the even-parity
    companion [IE], from which an induction on [length l] returns to [IO]
    -- through the widening state [IZ] ([l = []]) when it must.  The
    disjunction [G = IO \/ IE \/ IZ] is closed under one macro rule, and
    [StD] is hit from every member of it, which is exactly what
    [NGramHistExt.ngramhist_check_neverqh_lex_ext_sound] asks for. *)

From Coq Require Import Arith Lia Bool List Wf_nat ZArith
                        FunctionalExtensionality.
From BBB4 Require Import BBB4_Statement CTape PosEnc PattCount Closure.
From BBB4.Counters Require Import WTape BinVal.
From BBB4.Checkers Require Import Cycle ExactClosure NGram NGramHist
                                  ClosureExt NGramHistExt.
Import ListNotations.

Definition tm_1RB1LC_0LC0RB_1LA1RD_0LA0RD : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StC)
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StB)
  | StC, S0 => Some (mkTrans S1 DL StA)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S0 DL StA)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Local Notation tm := tm_1RB1LC_0LC0RB_1LA1RD_0LA0RD.

(** ** The shape, and the four macro rules *)

Definition Cf (l : list Sym) (s : Sym) (R : nat) (Z : list Sym) : cconf :=
  (StA, (l, s, rep [S1] R ++ S0 :: Z)).

(** One rightward step of the [StB] sweep (rule 1) and of the [StD] sweep
    (rule 5): both cross a [S1] writing a [S0], so both are [cycR] at the
    same unit. *)
Lemma unitB : wsteps true true tm 1 (StB, ([], S1, [S1]))
            = Some (StB, ([S0], S1, [])).
Proof. reflexivity. Qed.

Lemma unitD : wsteps true true tm 1 (StD, ([], S1, [S1]))
            = Some (StD, ([S0], S1, [])).
Proof. reflexivity. Qed.

Lemma sweepB : forall k L R,
  csteps tm (1 * k) (StB, (L, S1, rep [S1] k ++ R))
  = Some (StB, (rep [S0] k ++ L, S1, R)).
Proof. exact (cycR tm 1 StB S1 [S1] [S0] unitB). Qed.

Lemma sweepD : forall k L R,
  csteps tm (1 * k) (StD, (L, S1, rep [S1] k ++ R))
  = Some (StD, (rep [S0] k ++ L, S1, R)).
Proof. exact (cycR tm 1 StD S1 [S1] [S0] unitD). Qed.

Lemma r1 : forall l k Z,
  csteps tm (5 + k) (Cf l S0 (S (S k)) Z)
  = Some (Cf (rep [S0] k ++ S1 :: l) S0 1 Z).
Proof.
  intros l k Z.
  replace (5 + k) with (1 + (1 * S k + 3)) by lia.
  eapply csteps_chain
    with (c1 := (StB, (S1 :: l, S1, rep [S1] (S k) ++ S0 :: Z))).
  - unfold Cf. reflexivity.
  - eapply csteps_chain
      with (c1 := (StB, (rep [S0] (S k) ++ S1 :: l, S1, S0 :: Z))).
    + apply sweepB.
    + unfold Cf. reflexivity.
Qed.

Lemma r2a : forall l Z, csteps tm 4 (Cf l S0 0 Z) = Some (Cf l S1 0 Z).
Proof. intros. unfold Cf. reflexivity. Qed.

Lemma r2b : forall l Z, csteps tm 4 (Cf l S0 1 Z) = Some (Cf l S1 1 Z).
Proof. intros. unfold Cf. reflexivity. Qed.

Lemma r4 : forall l1 R Z,
  csteps tm 2 (Cf (S0 :: l1) S1 R Z)
  = Some (Cf (ctl l1) (chd l1) (S (S R)) Z).
Proof. intros. unfold Cf. reflexivity. Qed.

Lemma r4nil : forall R Z,
  csteps tm 2 (Cf [] S1 R Z) = Some (Cf [] S0 (S (S R)) Z).
Proof. intros. unfold Cf. reflexivity. Qed.

Lemma r5 : forall L R Z,
  csteps tm (4 + R) (Cf (S1 :: L) S1 R Z)
  = Some (Cf (rep [S0] R ++ S1 :: L) S0 0 Z).
Proof.
  intros L R Z.
  replace (4 + R) with (2 + (1 * R + 2)) by lia.
  eapply csteps_chain
    with (c1 := (StD, (S1 :: L, S1, rep [S1] R ++ S0 :: Z))).
  - unfold Cf. reflexivity.
  - eapply csteps_chain
      with (c1 := (StD, (rep [S0] R ++ S1 :: L, S1, S0 :: Z))).
    + apply sweepD.
    + unfold Cf. reflexivity.
Qed.

(** ** [StD] is hit *)

Definition HitD (c : cconf) : Prop :=
  exists n cc, 1 <= n /\ csteps tm n c = Some cc /\ fst cc = StD.

Lemma hitD_pre : forall n c c', csteps tm n c = Some c' -> HitD c' -> HitD c.
Proof.
  intros n c c' H (n' & cc & H1 & H2 & H3).
  exists (n + n'), cc. split; [lia|].
  split; [rewrite csteps_add, H; exact H2 | exact H3].
Qed.

(** Rule 5 passes through [StD] on its second step. *)
Lemma hitD_r5 : forall L R Z, HitD (Cf (S1 :: L) S1 R Z).
Proof.
  intros L R Z.
  exists 2, (StD, (S1 :: L, S1, rep [S1] R ++ S0 :: Z)).
  split; [lia|]. split; [unfold Cf; reflexivity | reflexivity].
Qed.

(** Rule 2 at [R = 0] passes through [StD] on its third step. *)
Lemma hitD_r2a : forall l Z, HitD (Cf l S0 0 Z).
Proof.
  intros l Z. exists 3, (StD, (S1 :: l, S0, Z)).
  split; [lia|]. split; [unfold Cf; reflexivity | reflexivity].
Qed.

(** ** The measure and the invariants *)

Definition Wd (l : list Sym) (R : nat) : nat := length l + 1 + R.
Definition mu (l : list Sym) (s : Sym) (R : nat) : nat :=
  2 ^ R * (2 * bval l + sval s + 1).

Lemma mu_bound : forall l s R, mu l s R <= 2 ^ (Wd l R).
Proof.
  intros l s R. unfold mu, Wd.
  rewrite Nat.pow_add_r, Nat.pow_add_r. cbn [Nat.pow].
  pose proof (bval_lt l) as Hb. pose proof (sval_le s) as Hs.
  set (L := 2 ^ length l) in *. set (P := 2 ^ R) in *.
  nia.
Qed.

Definition IO (l : list Sym) (R : nat) : Prop :=
  OddN (length l) /\ OddN R /\ last l S0 = S1.
Definition IE (l : list Sym) (R : nat) : Prop :=
  EvenN (length l) /\ EvenN R /\ last l S0 = S1.
Definition IZ (l : list Sym) (R : nat) : Prop := l = [] /\ EvenN R.
Definition G (l : list Sym) (R : nat) : Prop := IO l R \/ IE l R \/ IZ l R.

(** The three [mu] deltas, exact. *)
Lemma mu_r1 : forall l k,
  mu (rep [S0] k ++ S1 :: l) S0 1 = mu l S0 (S (S k)) + 2.
Proof.
  intros l k. unfold mu. rewrite bval_rep0_app. cbn [bval sval].
  replace (2 ^ S (S k)) with (4 * 2 ^ k) by (cbn [Nat.pow]; lia).
  replace (2 ^ 1) with 2 by reflexivity.
  set (P := 2 ^ k). set (b := bval l). nia.
Qed.

Lemma mu_r2 : forall l R, mu l S1 R = mu l S0 R + 2 ^ R.
Proof.
  intros l R. unfold mu. cbn [sval].
  set (P := 2 ^ R). set (b := bval l). nia.
Qed.

Lemma mu_r4 : forall b l2 R,
  mu l2 b (S (S R)) = mu (S0 :: b :: l2) S1 R + 2 ^ R * 2.
Proof.
  intros b l2 R. destruct b; unfold mu; cbn [bval sval];
    replace (2 ^ S (S R)) with (4 * 2 ^ R) by (cbn [Nat.pow]; lia);
    set (P := 2 ^ R); set (v := bval l2); nia.
Qed.

(** [Wd] is preserved by rules 1, 2 and 4. *)
Lemma wd_r1 : forall l k, Wd (rep [S0] k ++ S1 :: l) 1 = Wd l (S (S k)).
Proof.
  intros l k. unfold Wd. rewrite app_length, length_rep1. cbn [length]. lia.
Qed.

Lemma wd_r4 : forall b l2 R, Wd l2 (S (S R)) = Wd (S0 :: b :: l2) R.
Proof. intros. unfold Wd. cbn [length]. lia. Qed.

(** [last] under rules 1, 4 and 5. *)
Lemma last_r1 : forall l k, last l S0 = S1 ->
  last (rep [S0] k ++ S1 :: l) S0 = S1.
Proof.
  intros l k H. rewrite last_app_cons.
  destruct l as [|x l]; [discriminate | rewrite last_cons_ne by discriminate].
  exact H.
Qed.

Lemma last_r1_nil : forall k, last (rep [S0] k ++ [S1]) S0 = S1.
Proof. intro k. rewrite last_app_cons. reflexivity. Qed.

Lemma last_r4 : forall b l2, l2 <> [] ->
  last (S0 :: b :: l2) S0 = last l2 S0.
Proof.
  intros b l2 H.
  rewrite last_cons_ne by discriminate.
  rewrite last_cons_ne by exact H. reflexivity.
Qed.

Lemma last_r5 : forall L R, last (rep [S0] R ++ S1 :: L) S0 = last (S1 :: L) S0.
Proof. intros. apply last_app_cons. Qed.

(** ** Hitting [StD] from the odd-parity invariant *)

Lemma hitD_IO : forall F l s R Z,
  2 ^ (Wd l R) - mu l s R <= F -> IO l R -> HitD (Cf l s R Z).
Proof.
  intro F. induction F as [F IH] using (well_founded_induction lt_wf).
  intros l s R Z Hpot (Hlo & Hro & Hlast).
  pose proof (mu_bound l s R) as Hmb.
  destruct s.
  - (* s = S0: R is odd, so R = 1 or R = k+2 with k odd *)
    destruct R as [|R0]; [destruct (oddN_0 Hro)|].
    destruct R0 as [|k].
    + (* rule 2 at R = 1 *)
      eapply hitD_pre; [ apply (r2b l Z) | ].
      pose proof (mu_r2 l 1) as Hd.
      replace (2 ^ 1) with 2 in Hd by reflexivity.
      pose proof (mu_bound l S1 1) as Hmb'.
      apply (IH (2 ^ (Wd l 1) - mu l S1 1)); [ lia | lia | ].
      split; [exact Hlo | split; [exact Hro | exact Hlast]].
    + (* rule 1 at R = k+2 *)
      eapply hitD_pre; [ apply (r1 l k Z) | ].
      pose proof (mu_r1 l k) as Hd.
      pose proof (wd_r1 l k) as Hw.
      pose proof (mu_bound (rep [S0] k ++ S1 :: l) S0 1) as Hmb'.
      rewrite Hw in Hmb'.
      apply (IH (2 ^ (Wd l (S (S k))) - mu (rep [S0] k ++ S1 :: l) S0 1));
        [ lia | rewrite Hw; lia | ].
      split; [| split].
      * rewrite app_length, length_rep1. cbn [length].
        apply oddN_SS_inv in Hro.
        destruct Hro as [j Hj]; destruct Hlo as [i Hi];
          exists (i + j + 1); lia.
      * apply oddN_1.
      * apply last_r1; exact Hlast.
  - (* s = S1 *)
    destruct l as [|x l1]; [cbn in Hlast; discriminate|].
    destruct x.
    + (* rule 4 *)
      destruct l1 as [|b l2]; [cbn in Hlast; discriminate|].
      assert (Hl2 : l2 <> []).
      { destruct l2 as [|z l2]; [|discriminate].
        cbn [length] in Hlo; destruct Hlo as [j Hj]; lia. }
      eapply hitD_pre; [ apply (r4 (b :: l2) R Z) | ].
      cbn [ctl chd].
      pose proof (mu_r4 b l2 R) as Hd.
      pose proof (wd_r4 b l2 R) as Hw.
      pose proof (mu_bound l2 b (S (S R))) as Hmb'.
      pose proof (Nat.pow_nonzero 2 R ltac:(lia)) as Hp.
      rewrite Hw in Hmb'.
      apply (IH (2 ^ (Wd (S0 :: b :: l2) R) - mu l2 b (S (S R))));
        [ lia | rewrite Hw; lia | ].
      cbn [length] in Hlo.
      split; [| split].
      * destruct Hlo as [j Hj]; exists (j - 1); lia.
      * apply oddN_SS_intro; exact Hro.
      * rewrite <- (last_r4 b l2 Hl2). exact Hlast.
    + (* rule 5: [StD] on the spot *)
      apply hitD_r5.
Qed.

(** ** Hitting [StD] from the widening state and the even-parity invariant *)

Lemma hitD_IZ0 : forall R Z, EvenN R -> HitD (Cf [] S0 R Z).
Proof.
  intros R Z HR. destruct R as [|R0].
  - apply hitD_r2a.
  - destruct R0 as [|k]; [destruct (evenN_1 HR)|].
    eapply hitD_pre; [ apply (r1 [] k Z) | ].
    apply (hitD_IO (2 ^ (Wd (rep [S0] k ++ [S1]) 1)
                    - mu (rep [S0] k ++ [S1]) S0 1)); [ lia | ].
    split; [| split].
    + rewrite app_length, length_rep1. cbn [length].
      apply evenN_SS_inv in HR. destruct HR as [j Hj]; exists j; lia.
    + apply oddN_1.
    + apply last_r1_nil.
Qed.

Lemma hitD_IZ : forall s R Z, EvenN R -> HitD (Cf [] s R Z).
Proof.
  intros s R Z HR. destruct s.
  - apply hitD_IZ0; exact HR.
  - eapply hitD_pre; [ apply (r4nil R Z) | ].
    apply hitD_IZ0. apply evenN_SS_intro; exact HR.
Qed.

Lemma hitD_IE : forall F l s R Z,
  length l <= F -> IE l R -> HitD (Cf l s R Z).
Proof.
  intro F. induction F as [F IH] using (well_founded_induction lt_wf).
  intros l s R Z Hlen (Hle & Hre & Hlast).
  destruct s.
  - (* s = S0 *)
    destruct R as [|R0].
    + apply hitD_r2a.
    + destruct R0 as [|k]; [destruct (evenN_1 Hre)|].
      eapply hitD_pre; [ apply (r1 l k Z) | ].
      apply (hitD_IO (2 ^ (Wd (rep [S0] k ++ S1 :: l) 1)
                      - mu (rep [S0] k ++ S1 :: l) S0 1)); [ lia | ].
      split; [| split].
      * rewrite app_length, length_rep1. cbn [length].
        apply evenN_SS_inv in Hre.
        destruct Hre as [j Hj]; destruct Hle as [i Hi]; exists (i + j); lia.
      * apply oddN_1.
      * apply last_r1; exact Hlast.
  - (* s = S1 *)
    destruct l as [|x l1]; [cbn in Hlast; discriminate|].
    destruct x.
    + (* rule 4 *)
      destruct l1 as [|b l2]; [cbn in Hlast; discriminate|].
      eapply hitD_pre; [ apply (r4 (b :: l2) R Z) | ].
      cbn [ctl chd].
      destruct l2 as [|z l2].
      * (* l = [S0; b], and [last] forces b = S1: the widening state *)
        apply hitD_IZ. apply evenN_SS_intro; exact Hre.
      * cbn [length] in Hlen, Hle.
        apply (IH (length (z :: l2))); [ cbn [length]; lia
                                       | cbn [length]; lia | ].
        split; [| split].
        -- destruct Hle as [j Hj]; cbn [length]; exists (j - 1); lia.
        -- apply evenN_SS_intro; exact Hre.
        -- rewrite <- (last_r4 b (z :: l2) ltac:(discriminate)). exact Hlast.
    + apply hitD_r5.
Qed.

Lemma hitD_G : forall l s R Z, G l R -> HitD (Cf l s R Z).
Proof.
  intros l s R Z [Hio | [Hie | [-> Hz]]].
  - apply (hitD_IO (2 ^ (Wd l R) - mu l s R)); [lia | exact Hio].
  - apply (hitD_IE (length l)); [lia | exact Hie].
  - apply hitD_IZ; exact Hz.
Qed.

(** ** [G] is closed under one macro rule *)

Lemma g_step : forall l s R Z, G l R ->
  exists n l' s' R', 1 <= n
    /\ csteps tm n (Cf l s R Z) = Some (Cf l' s' R' Z)
    /\ G l' R'.
Proof.
  intros l s R Z HG.
  destruct s.
  - (* s = S0 *)
    destruct R as [|R0].
    + (* rule 2 at R = 0 *)
      exists 4, l, S1, 0. split; [lia | split; [apply r2a |]].
      destruct HG as [(H1 & H2 & H3) | [H | H]].
      * destruct (oddN_0 H2).
      * right; left; exact H.
      * right; right; exact H.
    + destruct R0 as [|k].
      * (* rule 2 at R = 1 *)
        exists 4, l, S1, 1. split; [lia | split; [apply r2b |]].
        destruct HG as [H | [(H1 & H2 & H3) | (H1 & H2)]].
        -- left; exact H.
        -- destruct (evenN_1 H2).
        -- destruct (evenN_1 H2).
      * (* rule 1 *)
        exists (5 + k), (rep [S0] k ++ S1 :: l), S0, 1.
        split; [lia | split; [apply r1 |]].
        left. split; [| split].
        -- rewrite app_length, length_rep1. cbn [length].
           destruct HG as [(H1 & H2 & H3) | [(H1 & H2 & H3) | (Hnil & H2)]].
           ++ apply oddN_SS_inv in H2.
              destruct H1 as [i Hi]; destruct H2 as [j Hj];
                exists (i + j + 1); lia.
           ++ apply evenN_SS_inv in H2.
              destruct H1 as [i Hi]; destruct H2 as [j Hj]; exists (i + j); lia.
           ++ subst l. apply evenN_SS_inv in H2.
              destruct H2 as [j Hj]; cbn [length]; exists j; lia.
        -- apply oddN_1.
        -- destruct HG as [(H1 & H2 & H3) | [(H1 & H2 & H3) | (Hnil & H2)]].
           ++ apply last_r1; exact H3.
           ++ apply last_r1; exact H3.
           ++ subst l. apply last_r1_nil.
  - (* s = S1 *)
    destruct l as [|x l1].
    + (* the widening state *)
      exists 2, (@nil Sym), S0, (S (S R)).
      split; [lia | split; [apply r4nil |]].
      right; right. split; [reflexivity|].
      destruct HG as [(H1 & H2 & H3) | [(H1 & H2 & H3) | (H1 & H2)]].
      * cbn in H3. discriminate.
      * cbn in H3. discriminate.
      * apply evenN_SS_intro; exact H2.
    + destruct x.
      * (* rule 4 *)
        destruct HG as [(H1 & H2 & H3) | [(H1 & H2 & H3) | (H1 & H2)]];
          [ | | discriminate ].
        -- (* odd: l1 = b :: l2 with l2 <> [] *)
           destruct l1 as [|b l2]; [cbn in H3; discriminate|].
           assert (Hl2 : l2 <> []).
           { destruct l2 as [|z l2]; [|discriminate].
             cbn [length] in H1; destruct H1 as [j Hj]; lia. }
           exists 2, l2, b, (S (S R)).
           split; [lia|].
           split; [ exact (r4 (b :: l2) R Z) |].
           cbn [length] in H1.
           left. split; [| split].
           ++ destruct H1 as [j Hj]; exists (j - 1); lia.
           ++ apply oddN_SS_intro; exact H2.
           ++ rewrite <- (last_r4 b l2 Hl2). exact H3.
        -- (* even: l1 = b :: l2, and l2 may be empty (widening next) *)
           destruct l1 as [|b l2]; [cbn in H3; discriminate|].
           exists 2, l2, b, (S (S R)).
           split; [lia|].
           split; [ exact (r4 (b :: l2) R Z) |].
           destruct l2 as [|z l2].
           ++ right; right. split; [reflexivity | apply evenN_SS_intro; exact H2].
           ++ cbn [length] in H1.
              right; left. split; [| split].
              ** destruct H1 as [j Hj]; cbn [length]; exists (j - 1); lia.
              ** apply evenN_SS_intro; exact H2.
              ** rewrite <- (last_r4 b (z :: l2) ltac:(discriminate)). exact H3.
      * (* rule 5 *)
        exists (4 + R), (rep [S0] R ++ S1 :: l1), S0, 0.
        split; [lia | split; [apply r5 |]].
        destruct HG as [(H1 & H2 & H3) | [(H1 & H2 & H3) | (H1 & H2)]];
          [ | | discriminate ].
        -- cbn [length] in H1.
           right; left. split; [| split].
           ++ rewrite app_length, length_rep1. cbn [length].
              destruct H1 as [i Hi]; destruct H2 as [j Hj];
                exists (i + j + 1); lia.
           ++ apply evenN_0.
           ++ rewrite last_r5. exact H3.
        -- cbn [length] in H1.
           right; left. split; [| split].
           ++ rewrite app_length, length_rep1. cbn [length].
              destruct H1 as [i Hi]; destruct H2 as [j Hj]; exists (i + j); lia.
           ++ apply evenN_0.
           ++ rewrite last_r5. exact H3.
Qed.

(** ** [StD] at arbitrarily large indices *)

Lemma live_D : forall N l s R Z, G l R ->
  exists m cc, N <= m /\ csteps tm m (Cf l s R Z) = Some cc /\ fst cc = StD.
Proof.
  induction N as [|N IHN]; intros l s R Z HG.
  - destruct (hitD_G l s R Z HG) as (n & cc & H1 & H2 & H3).
    exists n, cc. split; [lia | split; assumption].
  - destruct (g_step l s R Z HG) as (n & l' & s' & R' & Hn & Hstep & HG').
    destruct (IHN l' s' R' Z HG') as (m & cc & Hm & Hc & Hq).
    exists (n + m), cc. split; [lia|].
    split; [rewrite csteps_add, Hstep; exact Hc | exact Hq].
Qed.

Lemma boot : csteps tm 4 c0 = Some (Cf [] S1 0 []).
Proof. reflexivity. Qed.

Lemma recurD_1RB1LC_0LC0RB_1LA1RD_0LA0RD :
  forall N, exists m, N <= m /\ VisitsAt tm StD m.
Proof.
  intro N.
  destruct (live_D N [] S1 0 []) as (m & cc & Hm & Hc & Hq).
  - right; right. split; [reflexivity | apply evenN_0].
  - exists (4 + m). split; [lia|].
    exists (lift cc). split.
    + rewrite <- lift_c0. apply csteps_lift.
      rewrite csteps_add, boot. exact Hc.
    + rewrite lift_state. exact Hq.
Qed.

(* --- generated below by tools/mxdys4/emit_ngx.py --- *)

(** The [NGramHist] closure at k=3 n=2 t=200 fuel=40000 (134
    contexts).  It discharges the liveness of every state but [StD];
    [StD] is [recurD_1RB1LC_0LC0RB_1LA1RD_0LA0RD] above. *)

Definition lset_1RB1LC_0LC0RB_1LA1RD_0LA0RD : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S1);(StA,S1);(StA,S0)]);(S0,[(StB,S1);(StC,S0);(StB,S1)])];
   [(S0,[(StB,S1);(StA,S1);(StC,S1)]);(S0,[(StB,S1);(StC,S0)])];
   [(S0,[(StB,S1);(StA,S1);(StC,S1)]);(S0,[(StB,S1);(StC,S0);(StD,S1)])];
   [(S0,[(StB,S1);(StC,S0)]);(S1,[(StA,S0)])];
   [(S0,[(StB,S1);(StC,S0);(StB,S1)]);(S0,[(StB,S1);(StA,S1);(StA,S0)])];
   [(S0,[(StB,S1);(StC,S0);(StB,S1)]);(S1,[(StA,S0);(StB,S1);(StA,S1)])];
   [(S0,[(StB,S1);(StC,S0);(StB,S1)]);(S1,[(StA,S0);(StB,S1);(StC,S0)])];
   [(S0,[(StB,S1);(StC,S0);(StD,S1)]);(S0,[(StB,S1);(StA,S1);(StC,S1)])];
   [(S0,[(StB,S1);(StC,S0);(StD,S1)]);(S1,[(StA,S0);(StD,S1);(StC,S0)])];
   [(S0,[(StD,S1);(StA,S1);(StA,S0)]);(S0,[(StD,S1);(StC,S0);(StB,S1)])];
   [(S0,[(StD,S1);(StA,S1);(StA,S0)]);(S1,[(StC,S1);(StA,S0)])];
   [(S0,[(StD,S1);(StA,S1);(StA,S0)]);(S1,[(StC,S1);(StA,S0);(StD,S1)])];
   [(S0,[(StD,S1);(StC,S0);(StB,S1)]);(S0,[(StD,S1);(StA,S1);(StA,S0)])];
   [(S1,[(StA,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StB,S1);(StA,S1)]);(S0,[(StB,S1);(StC,S0);(StB,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StC,S0)]);(S0,[(StB,S1);(StA,S1);(StC,S1)])];
   [(S1,[(StA,S0);(StB,S1);(StC,S0)]);(S1,[(StA,S0)])];
   [(S1,[(StA,S0);(StB,S1);(StC,S0)]);(S1,[(StA,S0);(StD,S1);(StC,S0)])];
   [(S1,[(StA,S0);(StD,S1);(StC,S0)]);(S0,[(StD,S1);(StA,S1);(StA,S0)])];
   [(S1,[(StC,S1);(StA,S0)]);(S0,[])];
   [(S1,[(StC,S1);(StA,S0);(StD,S1)]);(S0,[(StD,S1);(StA,S1);(StA,S0)])]].

Definition rset_1RB1LC_0LC0RB_1LA1RD_0LA0RD : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StB,S0);(StB,S0);(StB,S0)]);(S0,[])];
   [(S0,[(StB,S0);(StB,S0);(StD,S0)]);(S0,[])];
   [(S0,[(StB,S0);(StD,S0);(StB,S0)]);(S0,[])];
   [(S0,[(StD,S0);(StB,S0);(StD,S0)]);(S0,[])];
   [(S1,[(StA,S1);(StA,S0);(StB,S1)]);(S1,[(StC,S0);(StB,S1);(StC,S0)])];
   [(S1,[(StA,S1);(StC,S1);(StA,S0)]);(S0,[(StD,S0);(StB,S0);(StD,S0)])];
   [(S1,[(StA,S1);(StC,S1);(StA,S0)]);(S1,[(StC,S0);(StD,S1);(StA,S1)])];
   [(S1,[(StC,S0);(StB,S1);(StC,S0)]);(S0,[(StB,S0);(StB,S0);(StB,S0)])];
   [(S1,[(StC,S0);(StB,S1);(StC,S0)]);(S0,[(StB,S0);(StB,S0);(StD,S0)])];
   [(S1,[(StC,S0);(StB,S1);(StC,S0)]);(S1,[(StA,S1);(StA,S0);(StB,S1)])];
   [(S1,[(StC,S0);(StD,S1);(StA,S1)]);(S1,[(StA,S1);(StC,S1);(StA,S0)])]].

Definition cert_1RB1LC_0LC0RB_1LA1RD_0LA0RD (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MRight 136 [(349266307306706025533357%positive,2);(354653312770783559112911%positive,2);(336234238813184571824335%positive,2);(78895917781545217242%positive,0);(308187077366205869%positive,2);(317344772890660996733133%positive,2);(329197582829504480893658%positive,2);(354653312770783810377935%positive,2);(329197582841405560925613%positive,2);(336234238813184823089359%positive,2);(78859884035801165229%positive,2);(19284603889458075%positive,0);(336234238813150211037389%positive,2);(329197582846353637592493%positive,2);(21019216850244600680365%positive,2);(354653312788534657898701%positive,2);(19314805998172601%positive,1);(75920907054240042701%positive,2);(5329380909918915834%positive,2);(79438584687486635725%positive,2);(19284569277413785%positive,1);(4928741447072296367%positive,2);(19284603638192539%positive,1);(78895912867180916622%positive,1);(79438601536643337933%positive,2);(329197582841406103694765%positive,2);(317344772881705990969551%positive,2);(78859884036343934381%positive,2);(5411580089973823695%positive,2);(19293558643956633%positive,1);(349266307336908749754285%positive,2);(329197582849673374019470%positive,2);(336234238822139577587917%positive,2);(19284603638200731%positive,1);(19284569277405593%positive,1);(19284603273943481%positive,2);(79436349736181258970%positive,0);(317344772881671630182605%positive,2);(329197582841439921713038%positive,2);(354653312770749198325965%positive,2);(329197582849673374018991%positive,2);(317344772899457089755341%positive,2);(1285928057892103474605%positive,2);(1252842953803565%positive,2);(329197582841406103706330%positive,2);(329197582841439921712559%positive,2);(4930993246885982094%positive,1);(336307469594925681020154%positive,2);(310298139691539162%positive,0);(5131644738779679994%positive,2);(78895917780896796077%positive,2);(76647285098766%positive,2);(5082493696146%positive,2);(79436353055917682095%positive,2);(78895900932388515034%positive,0);(329197582846353637595866%positive,2);(79436344822465375663%positive,2);(336307469594925065523117%positive,2);(19302354736978329%positive,1);(354653312779738564876493%positive,2);(21829144207230910681005%positive,2);(20574848926282682281870%positive,2);(80370503618256530650%positive,2);(329197582829504480890285%positive,2);(329197582829505129311450%positive,2);(1285928057892103477978%positive,2);(349266307306706389765370%positive,2);(336234238830935670610125%positive,2);(78895921100633223054%positive,1);(329197582846354286013658%positive,2);(20574848926282682281391%positive,2);(78859892303614258607%positive,2);(310972035320142849969869%positive,2);(19394183486574285%positive,2);(78859884036343945946%positive,0);(1205849488701881%positive,1);(4964770244091260335%positive,2);(4842296949576521935%positive,2);(78859884035801176794%positive,0);(317344772881706242234575%positive,2);(336307469625127789744045%positive,2);(5130527325728233679%positive,2);(329197582841405560937178%positive,2);(1301118386210605%positive,2);(310972035303293693267661%positive,2);(79436332887024556762%positive,0);(349266307306706641030394%positive,2);(79436344788104588717%positive,2);(336307469594925429755130%positive,2);(19261692335451354%positive,0);(78895900931740093869%positive,2);(78859884070161952175%positive,2)] [349266307306706025533357%positive;354653312770783559112911%positive;336234238813184571824335%positive;78895917781545217242%positive;308187077366205869%positive;317344772890660996733133%positive;329197582829504480893658%positive;354653312770783810377935%positive;329197582841405560925613%positive;336234238813184823089359%positive;78859884035801165229%positive;19284603889458075%positive;336234238813150211037389%positive;329197582846353637592493%positive;21019216850244600680365%positive;354653312788534657898701%positive;19314805998172601%positive;75920907054240042701%positive;5329380909918915834%positive;79438584687486635725%positive;19284569277413785%positive;4928741447072296367%positive;19284603638192539%positive;79438601536643337933%positive;78895912867180916622%positive;329197582841406103694765%positive;317344772881705990969551%positive;78859884036343934381%positive;5411580089973823695%positive;19293558643956633%positive;349266307336908749754285%positive;329197582849673374019470%positive;336234238822139577587917%positive;19284603638200731%positive;19284569277405593%positive;19284603273943481%positive;79436349736181258970%positive;317344772881671630182605%positive;329197582841439921713038%positive;354653312770749198325965%positive;329197582849673374018991%positive;317344772899457089755341%positive;1285928057892103474605%positive;1252842953803565%positive;329197582841406103706330%positive;329197582841439921712559%positive;4930993246885982094%positive;336307469594925681020154%positive;310298139691539162%positive;5131644738779679994%positive;78895917780896796077%positive;76647285098766%positive;5082493696146%positive;79436353055917682095%positive;78895900932388515034%positive;329197582846353637595866%positive;79436344822465375663%positive;336307469594925065523117%positive;19302354736978329%positive;354653312779738564876493%positive;21829144207230910681005%positive;20574848926282682281870%positive;80370503618256530650%positive;329197582829504480890285%positive;329197582829505129311450%positive;1285928057892103477978%positive;349266307306706389765370%positive;336234238830935670610125%positive;78895921100633223054%positive;20574848926282682281391%positive;329197582846354286013658%positive;78859892303614258607%positive;310972035320142849969869%positive;19394183486574285%positive;78859884036343945946%positive;1205849488701881%positive;4964770244091260335%positive;4842296949576521935%positive;78859884035801176794%positive;317344772881706242234575%positive;336307469625127789744045%positive;5130527325728233679%positive;329197582841405560937178%positive;1301118386210605%positive;310972035303293693267661%positive;349266307306706641030394%positive;79436332887024556762%positive;79436344788104588717%positive;336307469594925429755130%positive;19261692335451354%positive;78895900931740093869%positive;78859884070161952175%positive]]
  | StB => [HMeas MLeft 136 [(354653312770783559112911%positive,0);(317344772881671630163160%positive,136);(336234238813184571824335%positive,0);(78895917781545217242%positive,136);(310972035315228485704440%positive,136);(318525940963175341456088%positive,136);(338223755623345548%positive,136);(329197582829504480893658%positive,136);(4928882184560663288%positive,0);(354653312770783810377935%positive,0);(320657957857996172%positive,136);(78862144103427955448%positive,0);(336234238813184823089359%positive,0);(318525940993378065677016%positive,136);(310972035323461938018540%positive,136);(19284603889458075%positive,0);(5329380909918915834%positive,136);(354653312770783194852748%positive,136);(354653889231535498296024%positive,136);(317344772890660996713688%positive,136);(4928741447072296367%positive,0);(4964910981579634924%positive,136);(354653312788534657895820%positive,136);(19284603638192539%positive,0);(78895912867180916622%positive,136);(317344772881705990969551%positive,0);(22165868077532752739032%positive,136);(5411580089973823695%positive,0);(354653312788534657879256%positive,136);(329197582849673374019470%positive,136);(19284603638200731%positive,0);(79436349736181258970%positive,136);(329197582841439921713038%positive,136);(18985625563198168%positive,136);(79438604855731386604%positive,136);(329197582849673374018991%positive,0);(354653889261738222516952%positive,136);(354653312770749198323084%positive,136);(329197582841406103706330%positive,136);(329197582841439921712559%positive,0);(4930993246885982094%positive,136);(336307469594925681020154%positive,136);(317344772899457089752460%positive,136);(310298139691539162%positive,136);(5131644738779679994%positive,136);(76647285098766%positive,136);(5082493696146%positive,136);(79436353055917682095%positive,0);(78895900932388515034%positive,136);(354653312800985919073676%positive,136);(354653312770749198306520%positive,136);(336234238843386931785100%positive,136);(329197582846353637595866%positive,136);(79438596622279080172%positive,136);(79436344822465375663%positive,0);(20574848926282682281870%positive,136);(80370503618256530650%positive,136);(354653312779738564873612%positive,136);(329197582829505129311450%positive,136);(19907871310760242936536%positive,136);(1285928057892103477978%positive,136);(349266307306706389765370%positive,136);(1158461106196716%positive,136);(78895921100633223054%positive,136);(21139019086197464%positive,136);(317344772881671630179724%positive,136);(329197582846354286013658%positive,136);(19435752205894467549420%positive,136);(20574848926282682281391%positive,0);(78859892303614258607%positive,0);(336234238813184207564172%positive,136);(17676679312%positive,136);(19435752205894467541752%positive,136);(78859884036343945946%positive,136);(78862135869975649016%positive,0);(310972035315228485712108%positive,136);(4964770244091260335%positive,0);(4842296949576521935%positive,0);(22165832048735733755276%positive,136);(21014639926385797049740%positive,136);(78859884035801176794%positive,136);(317344772881706242234575%positive,0);(5130527325728233679%positive,0);(317344772890660996730252%positive,136);(329197582841405560937178%positive,136);(310972035323461938010872%positive,136);(79436332887024556762%positive,136);(349266307306706641030394%positive,136);(354653312779738564857048%positive,136);(336307469594925429755130%positive,136);(19261692335451354%positive,136);(317344772899457089735896%positive,136);(78859884070161952175%positive,0)] [354653312770783559112911%positive;317344772881671630163160%positive;336234238813184571824335%positive;78895917781545217242%positive;310972035315228485704440%positive;318525940963175341456088%positive;338223755623345548%positive;329197582829504480893658%positive;4928882184560663288%positive;354653312770783810377935%positive;320657957857996172%positive;78862144103427955448%positive;336234238813184823089359%positive;318525940993378065677016%positive;310972035323461938018540%positive;19284603889458075%positive;5329380909918915834%positive;354653312770783194852748%positive;354653889231535498296024%positive;317344772890660996713688%positive;4928741447072296367%positive;4964910981579634924%positive;354653312788534657895820%positive;19284603638192539%positive;78895912867180916622%positive;317344772881705990969551%positive;22165868077532752739032%positive;5411580089973823695%positive;354653312788534657879256%positive;329197582849673374019470%positive;19284603638200731%positive;79436349736181258970%positive;329197582841439921713038%positive;18985625563198168%positive;79438604855731386604%positive;329197582849673374018991%positive;354653889261738222516952%positive;354653312770749198323084%positive;329197582841406103706330%positive;329197582841439921712559%positive;4930993246885982094%positive;336307469594925681020154%positive;317344772899457089752460%positive;310298139691539162%positive;5131644738779679994%positive;76647285098766%positive;5082493696146%positive;79436353055917682095%positive;78895900932388515034%positive;354653312800985919073676%positive;354653312770749198306520%positive;336234238843386931785100%positive;329197582846353637595866%positive;79438596622279080172%positive;79436344822465375663%positive;20574848926282682281870%positive;80370503618256530650%positive;354653312779738564873612%positive;329197582829505129311450%positive;19907871310760242936536%positive;1285928057892103477978%positive;349266307306706389765370%positive;1158461106196716%positive;78895921100633223054%positive;21139019086197464%positive;317344772881671630179724%positive;329197582846354286013658%positive;19435752205894467549420%positive;20574848926282682281391%positive;78859892303614258607%positive;17676679312%positive;336234238813184207564172%positive;19435752205894467541752%positive;78859884036343945946%positive;78862135869975649016%positive;310972035315228485712108%positive;4964770244091260335%positive;4842296949576521935%positive;22165832048735733755276%positive;21014639926385797049740%positive;78859884035801176794%positive;317344772881706242234575%positive;5130527325728233679%positive;317344772890660996730252%positive;329197582841405560937178%positive;310972035323461938010872%positive;79436332887024556762%positive;349266307306706641030394%positive;354653312779738564857048%positive;336307469594925429755130%positive;19261692335451354%positive;317344772899457089735896%positive;78859884070161952175%positive]; HMeas MRight 136 [(354653312770783559112911%positive,276);(317344772881671630163160%positive,139);(336234238813184571824335%positive,276);(78895917781545217242%positive,276);(310972035315228485704440%positive,0);(318525940963175341456088%positive,139);(338223755623345548%positive,276);(329197582829504480893658%positive,139);(4928882184560663288%positive,274);(354653312770783810377935%positive,276);(320657957857996172%positive,276);(78862144103427955448%positive,274);(336234238813184823089359%positive,276);(318525940993378065677016%positive,139);(310972035323461938018540%positive,276);(19284603889458075%positive,275);(5329380909918915834%positive,139);(354653312770783194852748%positive,276);(354653889231535498296024%positive,2);(317344772890660996713688%positive,139);(4928741447072296367%positive,276);(4964910981579634924%positive,274);(354653312788534657895820%positive,276);(19284603638192539%positive,275);(78895912867180916622%positive,276);(317344772881705990969551%positive,276);(22165868077532752739032%positive,2);(5411580089973823695%positive,276);(354653312788534657879256%positive,2);(329197582849673374019470%positive,276);(19284603638200731%positive,275);(79436349736181258970%positive,276);(329197582841439921713038%positive,276);(18985625563198168%positive,139);(79438604855731386604%positive,274);(329197582849673374018991%positive,276);(354653889261738222516952%positive,2);(354653312770749198323084%positive,276);(329197582841406103706330%positive,139);(329197582841439921712559%positive,276);(4930993246885982094%positive,276);(336307469594925681020154%positive,137);(317344772899457089752460%positive,276);(310298139691539162%positive,276);(5131644738779679994%positive,137);(76647285098766%positive,276);(5082493696146%positive,139);(79436353055917682095%positive,276);(78895900932388515034%positive,276);(354653312800985919073676%positive,276);(354653312770749198306520%positive,2);(336234238843386931785100%positive,276);(329197582846353637595866%positive,139);(79438596622279080172%positive,274);(79436344822465375663%positive,276);(20574848926282682281870%positive,276);(80370503618256530650%positive,139);(354653312779738564873612%positive,276);(329197582829505129311450%positive,139);(19907871310760242936536%positive,139);(1285928057892103477978%positive,139);(349266307306706389765370%positive,139);(1158461106196716%positive,276);(78895921100633223054%positive,276);(21139019086197464%positive,2);(317344772881671630179724%positive,276);(329197582846354286013658%positive,139);(19435752205894467549420%positive,276);(20574848926282682281391%positive,276);(78859892303614258607%positive,276);(336234238813184207564172%positive,276);(17676679312%positive,2);(19435752205894467541752%positive,0);(78859884036343945946%positive,276);(78862135869975649016%positive,274);(310972035315228485712108%positive,276);(4964770244091260335%positive,276);(4842296949576521935%positive,276);(22165832048735733755276%positive,276);(21014639926385797049740%positive,276);(78859884035801176794%positive,276);(317344772881706242234575%positive,276);(5130527325728233679%positive,276);(317344772890660996730252%positive,276);(329197582841405560937178%positive,139);(310972035323461938010872%positive,0);(79436332887024556762%positive,276);(349266307306706641030394%positive,139);(354653312779738564857048%positive,2);(336307469594925429755130%positive,137);(19261692335451354%positive,276);(317344772899457089735896%positive,139);(78859884070161952175%positive,276)] [354653312770783559112911%positive;317344772881671630163160%positive;336234238813184571824335%positive;78895917781545217242%positive;310972035315228485704440%positive;318525940963175341456088%positive;338223755623345548%positive;329197582829504480893658%positive;4928882184560663288%positive;354653312770783810377935%positive;320657957857996172%positive;78862144103427955448%positive;336234238813184823089359%positive;318525940993378065677016%positive;310972035323461938018540%positive;19284603889458075%positive;5329380909918915834%positive;354653312770783194852748%positive;354653889231535498296024%positive;317344772890660996713688%positive;4928741447072296367%positive;4964910981579634924%positive;354653312788534657895820%positive;19284603638192539%positive;78895912867180916622%positive;317344772881705990969551%positive;22165868077532752739032%positive;5411580089973823695%positive;354653312788534657879256%positive;329197582849673374019470%positive;19284603638200731%positive;79436349736181258970%positive;329197582841439921713038%positive;18985625563198168%positive;79438604855731386604%positive;329197582849673374018991%positive;354653889261738222516952%positive;354653312770749198323084%positive;329197582841406103706330%positive;329197582841439921712559%positive;4930993246885982094%positive;336307469594925681020154%positive;317344772899457089752460%positive;310298139691539162%positive;5131644738779679994%positive;76647285098766%positive;5082493696146%positive;79436353055917682095%positive;78895900932388515034%positive;354653312800985919073676%positive;354653312770749198306520%positive;336234238843386931785100%positive;329197582846353637595866%positive;79438596622279080172%positive;79436344822465375663%positive;20574848926282682281870%positive;80370503618256530650%positive;354653312779738564873612%positive;329197582829505129311450%positive;19907871310760242936536%positive;1285928057892103477978%positive;349266307306706389765370%positive;1158461106196716%positive;78895921100633223054%positive;21139019086197464%positive;317344772881671630179724%positive;329197582846354286013658%positive;19435752205894467549420%positive;20574848926282682281391%positive;78859892303614258607%positive;17676679312%positive;336234238813184207564172%positive;19435752205894467541752%positive;78859884036343945946%positive;78862135869975649016%positive;310972035315228485712108%positive;4964770244091260335%positive;4842296949576521935%positive;22165832048735733755276%positive;21014639926385797049740%positive;78859884035801176794%positive;317344772881706242234575%positive;5130527325728233679%positive;317344772890660996730252%positive;329197582841405560937178%positive;310972035323461938010872%positive;79436332887024556762%positive;349266307306706641030394%positive;354653312779738564857048%positive;336307469594925429755130%positive;19261692335451354%positive;317344772899457089735896%positive;78859884070161952175%positive]]
  | StC => [HMeas MRight 136 [(349266307306706025533357%positive,3);(354653312770783559112911%positive,3);(317344772881671630163160%positive,3);(336234238813184571824335%positive,3);(310972035315228485704440%positive,3);(308187077366205869%positive,3);(318525940963175341456088%positive,3);(317344772890660996733133%positive,3);(338223755623345548%positive,3);(4928882184560663288%positive,1);(354653312770783810377935%positive,3);(320657957857996172%positive,3);(329197582841405560925613%positive,3);(78862144103427955448%positive,1);(336234238813184823089359%positive,3);(318525940993378065677016%positive,3);(310972035323461938018540%positive,3);(78859884035801165229%positive,3);(19284603889458075%positive,3);(336234238813150211037389%positive,3);(329197582846353637592493%positive,3);(21019216850244600680365%positive,3);(354653312788534657898701%positive,3);(19314805998172601%positive,2);(75920907054240042701%positive,3);(79438584687486635725%positive,3);(354653312770783194852748%positive,3);(354653889231535498296024%positive,3);(19284569277413785%positive,2);(317344772890660996713688%positive,3);(4928741447072296367%positive,3);(4964910981579634924%positive,2);(354653312788534657895820%positive,3);(19284603638192539%positive,2);(79438601536643337933%positive,3);(329197582841406103694765%positive,3);(317344772881705990969551%positive,3);(78859884036343934381%positive,3);(22165868077532752739032%positive,3);(5411580089973823695%positive,3);(19293558643956633%positive,2);(354653312788534657879256%positive,3);(349266307336908749754285%positive,3);(336234238822139577587917%positive,3);(19284603638200731%positive,2);(19284569277405593%positive,2);(19284603273943481%positive,0);(317344772881671630182605%positive,3);(354653312770749198325965%positive,3);(18985625563198168%positive,3);(79438604855731386604%positive,2);(329197582849673374018991%positive,3);(317344772899457089755341%positive,3);(354653889261738222516952%positive,3);(354653312770749198323084%positive,3);(1285928057892103474605%positive,3);(1252842953803565%positive,3);(329197582841439921712559%positive,3);(317344772899457089752460%positive,3);(78895917780896796077%positive,3);(79436353055917682095%positive,3);(354653312800985919073676%positive,3);(354653312770749198306520%positive,3);(336234238843386931785100%positive,3);(79438596622279080172%positive,2);(79436344822465375663%positive,3);(336307469594925065523117%positive,3);(19302354736978329%positive,2);(354653312779738564876493%positive,3);(21829144207230910681005%positive,3);(329197582829504480890285%positive,3);(354653312779738564873612%positive,3);(19907871310760242936536%positive,3);(336234238830935670610125%positive,3);(1158461106196716%positive,3);(21139019086197464%positive,3);(317344772881671630179724%positive,3);(19435752205894467549420%positive,3);(20574848926282682281391%positive,3);(78859892303614258607%positive,3);(310972035320142849969869%positive,3);(336234238813184207564172%positive,3);(17676679312%positive,3);(19394183486574285%positive,3);(19435752205894467541752%positive,3);(78862135869975649016%positive,1);(1205849488701881%positive,2);(310972035315228485712108%positive,3);(4964770244091260335%positive,3);(4842296949576521935%positive,3);(22165832048735733755276%positive,3);(21014639926385797049740%positive,3);(317344772881706242234575%positive,3);(336307469625127789744045%positive,3);(5130527325728233679%positive,3);(317344772890660996730252%positive,3);(1301118386210605%positive,3);(310972035303293693267661%positive,3);(310972035323461938010872%positive,3);(79436344788104588717%positive,3);(354653312779738564857048%positive,3);(317344772899457089735896%positive,3);(78895900931740093869%positive,3);(78859884070161952175%positive,3)] [349266307306706025533357%positive;354653312770783559112911%positive;317344772881671630163160%positive;336234238813184571824335%positive;310972035315228485704440%positive;308187077366205869%positive;318525940963175341456088%positive;317344772890660996733133%positive;338223755623345548%positive;4928882184560663288%positive;354653312770783810377935%positive;320657957857996172%positive;329197582841405560925613%positive;78862144103427955448%positive;336234238813184823089359%positive;318525940993378065677016%positive;310972035323461938018540%positive;78859884035801165229%positive;19284603889458075%positive;336234238813150211037389%positive;329197582846353637592493%positive;21019216850244600680365%positive;354653312788534657898701%positive;19314805998172601%positive;75920907054240042701%positive;79438584687486635725%positive;354653312770783194852748%positive;354653889231535498296024%positive;19284569277413785%positive;317344772890660996713688%positive;4928741447072296367%positive;4964910981579634924%positive;354653312788534657895820%positive;19284603638192539%positive;79438601536643337933%positive;329197582841406103694765%positive;317344772881705990969551%positive;78859884036343934381%positive;22165868077532752739032%positive;5411580089973823695%positive;19293558643956633%positive;354653312788534657879256%positive;349266307336908749754285%positive;336234238822139577587917%positive;19284603638200731%positive;19284569277405593%positive;19284603273943481%positive;317344772881671630182605%positive;354653312770749198325965%positive;18985625563198168%positive;79438604855731386604%positive;329197582849673374018991%positive;317344772899457089755341%positive;354653889261738222516952%positive;354653312770749198323084%positive;1285928057892103474605%positive;1252842953803565%positive;329197582841439921712559%positive;317344772899457089752460%positive;78895917780896796077%positive;79436353055917682095%positive;354653312800985919073676%positive;354653312770749198306520%positive;336234238843386931785100%positive;79438596622279080172%positive;79436344822465375663%positive;336307469594925065523117%positive;19302354736978329%positive;354653312779738564876493%positive;21829144207230910681005%positive;329197582829504480890285%positive;354653312779738564873612%positive;19907871310760242936536%positive;336234238830935670610125%positive;1158461106196716%positive;19435752205894467549420%positive;21139019086197464%positive;317344772881671630179724%positive;20574848926282682281391%positive;78859892303614258607%positive;310972035320142849969869%positive;336234238813184207564172%positive;17676679312%positive;19394183486574285%positive;19435752205894467541752%positive;78862135869975649016%positive;1205849488701881%positive;310972035315228485712108%positive;4964770244091260335%positive;4842296949576521935%positive;22165832048735733755276%positive;21014639926385797049740%positive;317344772881706242234575%positive;336307469625127789744045%positive;5130527325728233679%positive;317344772890660996730252%positive;1301118386210605%positive;310972035303293693267661%positive;310972035323461938010872%positive;79436344788104588717%positive;354653312779738564857048%positive;317344772899457089735896%positive;78895900931740093869%positive;78859884070161952175%positive]]
  | StD => []
  end.

Theorem nqh_1RB1LC_0LC0RB_1LA1RD_0LA0RD : NeverQuasiHaltsSt tm_1RB1LC_0LC0RB_1LA1RD_0LA0RD.
Proof.
  apply (ngramhist_check_neverqh_lex_ext_sound tm_1RB1LC_0LC0RB_1LA1RD_0LA0RD 3 2 200 40000
           lset_1RB1LC_0LC0RB_1LA1RD_0LA0RD rset_1RB1LC_0LC0RB_1LA1RD_0LA0RD cert_1RB1LC_0LC0RB_1LA1RD_0LA0RD StD recurD_1RB1LC_0LC0RB_1LA1RD_0LA0RD).
  vm_compute. reflexivity.
Qed.
