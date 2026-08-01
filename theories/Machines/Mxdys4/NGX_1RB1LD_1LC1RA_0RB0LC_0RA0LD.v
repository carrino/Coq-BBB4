(** * 1RB1LD_1LC1RA_0RB0LC_0RA0LD -- never quasihalts.

    Row 4 of the four handed over in [docs/WAVE36_MXDYS_FOUR.md], and the
    same story as row 1 with the two half-tapes exchanged: the [NGramHist]
    closure discharges [StA], [StB] and [StC], and [StD] -- which recurs on
    a [Theta(2^width)] schedule -- is proved live here by hand.  (The two
    rows are NOT related by [mirror_tm] under any state bijection, so
    nothing transports; only the reading does.)

    THE MACRO SYSTEM (section 2b, restated on [cconf]).  The orbit keeps
    the LEFT half-tape a bare unary run followed by a blank, so every
    [StA] configuration is

      Cf p s r Y = (StA, (rep [S1] p ++ S0 :: Y, s, r))

    with [p] the run length, [r] the (arbitrary) right half-tape carrying
    the counter and [Y] a tail no rule ever reaches.  Five rules:

      (1)  s=S0, r=S1::r1     -> (p+2, chd r1, ctl r1)        2      steps
      (2)  s=S0, chd r=S0, p>0-> (1, S0, 0^(p-1) ++ S1::ctl r) p+7    steps
      (2') s=S0, chd r=S0, p=0-> (1, S1, ctl r)               7      steps
      (3)  s=S1, p>0          -> (0, S0, 0^(p-1) ++ S1::r)    p+2    steps
      (3') s=S1, p=0          -> (0, S1, r)                   2      steps

    [StD] is entered by rules 3 and 3' on their FIRST step and by nothing
    else, so the liveness of [StD] is exactly "the head reads [S1] in state
    [StA] infinitely often".

    THE ARGUMENT.  With [bval] the right half-tape read as a binary number
    (nearest cell least significant) put

      mu p s r = 2^p * (2 * bval r + sval s + 1)      Wd p r = p + 1 + |r|

    Rules 1 and 2 -- the only [StD]-free ones -- strictly increase [mu] and
    preserve [Wd], and [mu <= 2^Wd] always.  [Wd] grows only where the head
    walks onto FRESH blank tape, i.e. at [r = [S1]] (rule 1) or [r = []]
    (rule 2), and the parity invariant [O] ([p] odd, [|r|] even,
    [last r = S1]) rules both out: [last r = S1] forces [r <> []], and with
    [|r|] even and [chd r = S1] the case [r = [S1]] cannot occur.

    Rule 3 leaves [O] (it sets [p := 0]), landing in the companion [E]
    ([p] even, [|r|] odd), from which an induction on [|r|] returns to [O]
    -- through the two blank-tape states [Z0]/[Z1] ([r = []]) when it must.
    The four-way disjunction [G] is closed under one macro rule and [StD]
    is hit from every member of it. *)

From Coq Require Import Arith Lia Bool List Wf_nat ZArith
                        FunctionalExtensionality.
From BBB4 Require Import BBB4_Statement CTape PosEnc PattCount Closure.
From BBB4.Counters Require Import WTape BinVal.
From BBB4.Checkers Require Import Cycle ExactClosure NGram NGramHist
                                  ClosureExt NGramHistExt.
Import ListNotations.

Definition tm_1RB1LD_1LC1RA_0RB0LC_0RA0LD : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S0 DR StB)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S0 DR StA)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Local Notation tm := tm_1RB1LD_1LC1RA_0RB0LC_0RA0LD.

(** ** The shape, and the five macro rules *)

Definition Cf (p : nat) (s : Sym) (r : list Sym) (Y : list Sym) : cconf :=
  (StA, (rep [S1] p ++ S0 :: Y, s, r)).

(** One leftward step of the [StD] sweep (rule 3) and of the [StC] sweep
    (rule 2): both cross a [S1] writing a [S0], so both are [cycL] at the
    same unit. *)
Lemma unitD : wsteps true true tm 1 (StD, ([S1], S1, []))
            = Some (StD, ([], S1, [] ++ [S0])).
Proof. reflexivity. Qed.

Lemma unitC : wsteps true true tm 1 (StC, ([S1], S1, []))
            = Some (StC, ([], S1, [] ++ [S0])).
Proof. reflexivity. Qed.

Lemma sweepD : forall k L R,
  csteps tm (1 * k) (StD, (rep [S1] k ++ L, S1, R))
  = Some (StD, (L, S1, rep [S0] k ++ R)).
Proof. intros k L R. exact (cycL tm 1 StD S1 [S1] [] [S0] unitD k L R). Qed.

Lemma sweepC : forall k L R,
  csteps tm (1 * k) (StC, (rep [S1] k ++ L, S1, R))
  = Some (StC, (L, S1, rep [S0] k ++ R)).
Proof. intros k L R. exact (cycL tm 1 StC S1 [S1] [] [S0] unitC k L R). Qed.

Lemma r1 : forall p c r2 Y,
  csteps tm 2 (Cf p S0 (S1 :: c :: r2) Y) = Some (Cf (S (S p)) c r2 Y).
Proof. intros. unfold Cf. reflexivity. Qed.

Lemma r1nil : forall p Y,
  csteps tm 2 (Cf p S0 [S1] Y) = Some (Cf (S (S p)) S0 [] Y).
Proof. intros. unfold Cf. reflexivity. Qed.

Lemma r2 : forall m r1 Y,
  csteps tm (8 + m) (Cf (S m) S0 (S0 :: r1) Y)
  = Some (Cf 1 S0 (rep [S0] m ++ S1 :: r1) Y).
Proof.
  intros m r1 Y.
  replace (8 + m) with (2 + (1 * S m + 5)) by lia.
  eapply csteps_chain
    with (c1 := (StC, (rep [S1] (S m) ++ S0 :: Y, S1, S1 :: r1))).
  - unfold Cf. reflexivity.
  - eapply csteps_chain
      with (c1 := (StC, (S0 :: Y, S1, rep [S0] (S m) ++ S1 :: r1))).
    + apply sweepC.
    + unfold Cf. reflexivity.
Qed.

Lemma r2nil : forall m Y,
  csteps tm (8 + m) (Cf (S m) S0 [] Y)
  = Some (Cf 1 S0 (rep [S0] m ++ [S1]) Y).
Proof.
  intros m Y.
  replace (8 + m) with (2 + (1 * S m + 5)) by lia.
  eapply csteps_chain
    with (c1 := (StC, (rep [S1] (S m) ++ S0 :: Y, S1, [S1]))).
  - unfold Cf. reflexivity.
  - eapply csteps_chain
      with (c1 := (StC, (S0 :: Y, S1, rep [S0] (S m) ++ [S1]))).
    + apply sweepC.
    + unfold Cf. reflexivity.
Qed.

Lemma r2p : forall r1 Y,
  csteps tm 7 (Cf 0 S0 (S0 :: r1) Y) = Some (Cf 1 S1 r1 Y).
Proof. intros. unfold Cf. reflexivity. Qed.

Lemma r2pnil : forall Y, csteps tm 7 (Cf 0 S0 [] Y) = Some (Cf 1 S1 [] Y).
Proof. intros. unfold Cf. reflexivity. Qed.

Lemma r3 : forall m r Y,
  csteps tm (3 + m) (Cf (S m) S1 r Y)
  = Some (Cf 0 S0 (rep [S0] m ++ S1 :: r) Y).
Proof.
  intros m r Y.
  replace (3 + m) with (1 + (1 * m + 2)) by lia.
  eapply csteps_chain
    with (c1 := (StD, (rep [S1] m ++ S0 :: Y, S1, S1 :: r))).
  - unfold Cf. reflexivity.
  - eapply csteps_chain
      with (c1 := (StD, (S0 :: Y, S1, rep [S0] m ++ S1 :: r))).
    + apply sweepD.
    + unfold Cf. reflexivity.
Qed.

Lemma r3p : forall r Y, csteps tm 2 (Cf 0 S1 r Y) = Some (Cf 0 S1 r Y).
Proof. intros. unfold Cf. reflexivity. Qed.

(** ** [StD] is hit *)

Definition HitD (c : cconf) : Prop :=
  exists n cc, 1 <= n /\ csteps tm n c = Some cc /\ fst cc = StD.

Lemma hitD_pre : forall n c c', csteps tm n c = Some c' -> HitD c' -> HitD c.
Proof.
  intros n c c' H (n' & cc & H1 & H2 & H3).
  exists (n + n'), cc. split; [lia|].
  split; [rewrite csteps_add, H; exact H2 | exact H3].
Qed.

(** Reading [S1] in [StA] enters [StD] on the spot -- this is the whole
    liveness obligation, and rules 3 / 3' are its only occurrences. *)
Lemma hitD_s1 : forall p r Y, HitD (Cf p S1 r Y).
Proof.
  intros p r Y.
  exists 1, (StD, (ctl (rep [S1] p ++ S0 :: Y),
                   chd (rep [S1] p ++ S0 :: Y), S1 :: r)).
  split; [lia|]. split; [unfold Cf; reflexivity | reflexivity].
Qed.

(** ** The measure and the invariants *)

Definition Wd (p : nat) (r : list Sym) : nat := p + 1 + length r.
Definition mu (p : nat) (s : Sym) (r : list Sym) : nat :=
  2 ^ p * (2 * bval r + sval s + 1).

Lemma mu_bound : forall p s r, mu p s r <= 2 ^ (Wd p r).
Proof.
  intros p s r. unfold mu, Wd.
  rewrite Nat.pow_add_r, Nat.pow_add_r. cbn [Nat.pow].
  pose proof (bval_lt r) as Hb. pose proof (sval_le s) as Hs.
  set (L := 2 ^ length r) in *. set (P := 2 ^ p) in *.
  nia.
Qed.

Definition IO (p : nat) (r : list Sym) : Prop :=
  OddN p /\ EvenN (length r) /\ last r S0 = S1.
Definition IE (p : nat) (r : list Sym) : Prop :=
  EvenN p /\ OddN (length r) /\ last r S0 = S1.
Definition G (p : nat) (s : Sym) (r : list Sym) : Prop :=
  IO p r \/ IE p r \/ (r = [] /\ EvenN p /\ s = S0)
                   \/ (r = [] /\ OddN p /\ s = S1).

Lemma mu_r1 : forall p c r2,
  mu (S (S p)) c r2 = mu p S0 (S1 :: c :: r2) + 2 ^ p.
Proof.
  intros p c r2. destruct c; unfold mu; cbn [bval sval];
    replace (2 ^ S (S p)) with (4 * 2 ^ p) by (cbn [Nat.pow]; lia);
    set (P := 2 ^ p); set (v := bval r2); nia.
Qed.

Lemma mu_r2 : forall m r1,
  mu 1 S0 (rep [S0] m ++ S1 :: r1) = mu (S m) S0 (S0 :: r1) + (2 ^ m * 2 + 2).
Proof.
  intros m r1. unfold mu. rewrite bval_rep0_app. cbn [bval sval].
  replace (2 ^ S m) with (2 * 2 ^ m) by (cbn [Nat.pow]; lia).
  replace (2 ^ 1) with 2 by reflexivity.
  set (P := 2 ^ m). set (w := bval r1). nia.
Qed.

Lemma wd_r1 : forall p c r2, Wd (S (S p)) r2 = Wd p (S1 :: c :: r2).
Proof. intros. unfold Wd. cbn [length]. lia. Qed.

Lemma wd_r2 : forall m r1,
  Wd 1 (rep [S0] m ++ S1 :: r1) = Wd (S m) (S0 :: r1).
Proof.
  intros. unfold Wd. rewrite app_length, length_rep1. cbn [length]. lia.
Qed.

Lemma last_r2 : forall m r1, last (rep [S0] m ++ S1 :: r1) S0 = last (S1 :: r1) S0.
Proof. intros. apply last_app_cons. Qed.

Lemma last_hd2 : forall c r2, r2 <> [] ->
  last (S1 :: c :: r2) S0 = last r2 S0.
Proof.
  intros c r2 H.
  rewrite last_cons_ne by discriminate.
  rewrite last_cons_ne by exact H. reflexivity.
Qed.

(** ** Hitting [StD] from the odd-parity invariant *)

Lemma hitD_IO : forall F p s r Y,
  2 ^ (Wd p r) - mu p s r <= F -> IO p r -> HitD (Cf p s r Y).
Proof.
  intro F. induction F as [F IH] using (well_founded_induction lt_wf).
  intros p s r Y Hpot (Hpo & Hre & Hlast).
  destruct s; [| apply hitD_s1 ].
  pose proof (mu_bound p S0 r) as Hmb.
  destruct r as [|c r1]; [cbn in Hlast; discriminate|].
  destruct c.
  - (* chd r = S0: rule 2, and [p] is odd so [p = S m] *)
    destruct p as [|m]; [destruct (oddN_0 Hpo)|].
    assert (Hr1 : r1 <> []).
    { destruct r1 as [|d r2]; [|discriminate].
      cbn in Hlast. discriminate. }
    eapply hitD_pre; [ apply (r2 m r1 Y) | ].
    pose proof (mu_r2 m r1) as Hd.
    pose proof (wd_r2 m r1) as Hw.
    pose proof (mu_bound 1 S0 (rep [S0] m ++ S1 :: r1)) as Hmb'.
    pose proof (Nat.pow_nonzero 2 m ltac:(lia)) as Hp.
    rewrite Hw in Hmb'.
    apply (IH (2 ^ (Wd (S m) (S0 :: r1))
               - mu 1 S0 (rep [S0] m ++ S1 :: r1)));
      [ lia | rewrite Hw; lia | ].
    cbn [length] in Hre.
    split; [| split].
    + apply oddN_1.
    + rewrite app_length, length_rep1. cbn [length].
      destruct Hpo as [i Hi]; destruct Hre as [j Hj]; exists (i + j); lia.
    + rewrite last_r2.
      rewrite last_cons_ne by exact Hr1.
      rewrite <- (last_cons_ne S0 r1 S0 Hr1). exact Hlast.
  - (* chd r = S1: rule 1 *)
    destruct r1 as [|d r2].
    + (* r = [S1], excluded: [|r|] is even *)
      cbn [length] in Hre. destruct Hre as [j Hj]; lia.
    + destruct d.
      * (* the next head symbol is S0: stay in [IO] *)
        assert (Hr2 : r2 <> []).
        { destruct r2 as [|e r2]; [|discriminate].
          cbn in Hlast. discriminate. }
        eapply hitD_pre; [ apply (r1 p S0 r2 Y) | ].
        pose proof (mu_r1 p S0 r2) as Hd.
        pose proof (wd_r1 p S0 r2) as Hw.
        pose proof (mu_bound (S (S p)) S0 r2) as Hmb'.
        pose proof (Nat.pow_nonzero 2 p ltac:(lia)) as Hp.
        rewrite Hw in Hmb'.
        apply (IH (2 ^ (Wd p (S1 :: S0 :: r2)) - mu (S (S p)) S0 r2));
          [ lia | rewrite Hw; lia | ].
        cbn [length] in Hre.
        split; [| split].
        -- apply oddN_SS_intro; exact Hpo.
        -- destruct Hre as [j Hj]; exists (j - 1); lia.
        -- rewrite <- (last_hd2 S0 r2 Hr2). exact Hlast.
      * (* the next head symbol is S1: [StD] one macro rule on *)
        eapply hitD_pre; [ apply (r1 p S1 r2 Y) | ]. apply hitD_s1.
Qed.

(** ** The blank-tape states and the even-parity invariant *)

Lemma hitD_Z0 : forall p Y, EvenN p -> HitD (Cf p S0 [] Y).
Proof.
  intros p Y HP. destruct p as [|m].
  - eapply hitD_pre; [ apply (r2pnil Y) | ]. apply hitD_s1.
  - eapply hitD_pre; [ apply (r2nil m Y) | ].
    apply (hitD_IO (2 ^ (Wd 1 (rep [S0] m ++ [S1]))
                    - mu 1 S0 (rep [S0] m ++ [S1]))); [ lia | ].
    split; [| split].
    + apply oddN_1.
    + rewrite app_length, length_rep1. cbn [length].
      destruct HP as [j Hj]; exists j; lia.
    + rewrite last_r2. reflexivity.
Qed.

Lemma hitD_IE : forall F p s r Y,
  length r <= F -> IE p r -> HitD (Cf p s r Y).
Proof.
  intro F. induction F as [F IH] using (well_founded_induction lt_wf).
  intros p s r Y Hlen (Hpe & Hro & Hlast).
  destruct s; [| apply hitD_s1 ].
  destruct r as [|c r1]; [cbn in Hlast; discriminate|].
  destruct c.
  - (* chd r = S0 *)
    assert (Hr1 : r1 <> []).
    { destruct r1 as [|d r2]; [|discriminate].
      cbn in Hlast. discriminate. }
    destruct p as [|m].
    + (* rule 2' *)
      eapply hitD_pre; [ apply (r2p r1 Y) | ]. apply hitD_s1.
    + (* rule 2 *)
      eapply hitD_pre; [ apply (r2 m r1 Y) | ].
      apply (hitD_IO (2 ^ (Wd 1 (rep [S0] m ++ S1 :: r1))
                      - mu 1 S0 (rep [S0] m ++ S1 :: r1))); [ lia | ].
      cbn [length] in Hro.
      split; [| split].
      * apply oddN_1.
      * rewrite app_length, length_rep1. cbn [length].
        destruct Hpe as [i Hi]; destruct Hro as [j Hj]; exists (i + j); lia.
      * rewrite last_r2. rewrite last_cons_ne by exact Hr1.
        rewrite <- (last_cons_ne S0 r1 S0 Hr1). exact Hlast.
  - (* chd r = S1: rule 1 *)
    destruct r1 as [|d r2].
    + (* r = [S1]: the head walks onto fresh blank tape *)
      eapply hitD_pre; [ apply (r1nil p Y) | ].
      apply hitD_Z0. apply evenN_SS_intro; exact Hpe.
    + destruct d.
      * (* stay in [IE], with [|r|] two shorter *)
        assert (Hr2 : r2 <> []).
        { destruct r2 as [|e r2]; [|discriminate].
          cbn in Hlast. discriminate. }
        eapply hitD_pre; [ apply (r1 p S0 r2 Y) | ].
        cbn [length] in Hlen, Hro.
        apply (IH (length r2)); [ lia | lia | ].
        split; [| split].
        -- apply evenN_SS_intro; exact Hpe.
        -- destruct Hro as [j Hj]; exists (j - 1); lia.
        -- rewrite <- (last_hd2 S0 r2 Hr2). exact Hlast.
      * eapply hitD_pre; [ apply (r1 p S1 r2 Y) | ]. apply hitD_s1.
Qed.

Lemma hitD_G : forall p s r Y, G p s r -> HitD (Cf p s r Y).
Proof.
  intros p s r Y [Hio | [Hie | [(-> & Hz & ->) | (-> & Hz & ->)]]].
  - apply (hitD_IO (2 ^ (Wd p r) - mu p s r)); [lia | exact Hio].
  - apply (hitD_IE (length r)); [lia | exact Hie].
  - apply hitD_Z0; exact Hz.
  - apply hitD_s1.
Qed.

(** ** [G] is closed under one macro rule *)

Lemma g_step : forall p s r Y, G p s r ->
  exists n p' s' r', 1 <= n
    /\ csteps tm n (Cf p s r Y) = Some (Cf p' s' r' Y)
    /\ G p' s' r'.
Proof.
  intros p s r Y HG.
  destruct s.
  - (* s = S0: rules 1, 2, 2' *)
    destruct r as [|c r1].
    + (* r = [] *)
      assert (Hpe : EvenN p).
      { destruct HG as [(H1 & H2 & H3) | [(H1 & H2 & H3) | [(H1 & H2 & H3)
                                                           | (H1 & H2 & H3)]]];
          [ cbn in H3; discriminate | cbn in H3; discriminate
          | exact H2 | discriminate ]. }
      destruct p as [|m].
      * exists 7, 1, S1, (@nil Sym).
        split; [lia | split; [apply r2pnil |]].
        right; right; right. split; [reflexivity | split; [apply oddN_1 | reflexivity]].
      * exists (8 + m), 1, S0, (rep [S0] m ++ [S1]).
        split; [lia | split; [apply r2nil |]].
        left. split; [| split].
        -- apply oddN_1.
        -- rewrite app_length, length_rep1. cbn [length].
           destruct Hpe as [j Hj]; exists j; lia.
        -- rewrite last_r2. reflexivity.
    + destruct c.
      * (* chd r = S0: rule 2 or 2' *)
        assert (Hr1 : r1 <> [] /\ last r1 S0 = S1 /\ ~ (S0 :: r1 = [])).
        { destruct HG as [(H1 & H2 & H3) | [(H1 & H2 & H3) | [(H1 & H2 & H3)
                                                             | (H1 & H2 & H3)]]];
            [ | | discriminate | discriminate ];
            (assert (Hne : r1 <> []) by
               (destruct r1 as [|d r2]; [cbn in H3; discriminate | discriminate]));
            (split; [exact Hne | split;
               [ rewrite <- (last_cons_ne S0 r1 S0 Hne); exact H3
               | discriminate ]]). }
        destruct Hr1 as (Hne & Hlr1 & _).
        destruct p as [|m].
        -- (* rule 2' *)
           exists 7, 1, S1, r1.
           split; [lia | split; [apply r2p |]].
           left. split; [| split].
           ++ apply oddN_1.
           ++ destruct HG as [(H1 & H2 & H3) | [(H1 & H2 & H3) | [(H1 & H2 & H3)
                                                                 | (H1 & H2 & H3)]]];
                [ destruct (oddN_0 H1) | | discriminate | discriminate ].
              cbn [length] in H2. destruct H2 as [j Hj]; exists j; lia.
           ++ exact Hlr1.
        -- (* rule 2 *)
           exists (8 + m), 1, S0, (rep [S0] m ++ S1 :: r1).
           split; [lia | split; [apply r2 |]].
           left. split; [| split].
           ++ apply oddN_1.
           ++ rewrite app_length, length_rep1. cbn [length].
              destruct HG as [(H1 & H2 & H3) | [(H1 & H2 & H3) | [(H1 & H2 & H3)
                                                                 | (H1 & H2 & H3)]]];
                [ | | discriminate | discriminate ];
                cbn [length] in H2.
              ** destruct H1 as [i Hi]; destruct H2 as [j Hj];
                   exists (i + j); lia.
              ** destruct H1 as [i Hi]; destruct H2 as [j Hj];
                   exists (i + j); lia.
           ++ rewrite last_r2. rewrite last_cons_ne by exact Hne. exact Hlr1.
      * (* chd r = S1: rule 1 *)
        destruct r1 as [|d r2].
        -- (* r = [S1] *)
           exists 2, (S (S p)), S0, (@nil Sym).
           split; [lia | split; [apply r1nil |]].
           destruct HG as [(H1 & H2 & H3) | [(H1 & H2 & H3) | [(H1 & H2 & H3)
                                                              | (H1 & H2 & H3)]]];
             [ | | discriminate | discriminate ].
           ++ (* [IO] with |r| = 1: impossible *)
              cbn [length] in H2. destruct H2 as [j Hj]; lia.
           ++ right; right; left.
              split; [reflexivity | split; [apply evenN_SS_intro; exact H1
                                           | reflexivity]].
        -- exists 2, (S (S p)), d, r2.
           split; [lia | split; [apply r1 |]].
           destruct HG as [(H1 & H2 & H3) | [(H1 & H2 & H3) | [(H1 & H2 & H3)
                                                              | (H1 & H2 & H3)]]];
             [ | | discriminate | discriminate ].
           ++ (* [IO] *)
              destruct r2 as [|e r2].
              ** (* r = [S1; d] with last = d, so d = S1 and r2 = [] *)
                 cbn in H3. subst d.
                 right; right; right.
                 split; [reflexivity | split; [apply oddN_SS_intro; exact H1
                                              | reflexivity]].
              ** left. cbn [length] in H2. split; [| split].
                 --- apply oddN_SS_intro; exact H1.
                 --- destruct H2 as [j Hj]; cbn [length]; exists (j - 1); lia.
                 --- rewrite <- (last_hd2 d (e :: r2) ltac:(discriminate)).
                     exact H3.
           ++ (* [IE] *)
              assert (Hr2 : r2 <> []).
              { destruct r2 as [|e r2]; [|discriminate].
                cbn [length] in H2. destruct H2 as [j Hj]; lia. }
              right; left. cbn [length] in H2. split; [| split].
              ** apply evenN_SS_intro; exact H1.
              ** destruct H2 as [j Hj]; exists (j - 1); lia.
              ** rewrite <- (last_hd2 d r2 Hr2). exact H3.
  - (* s = S1: rules 3, 3' *)
    destruct p as [|m].
    + exists 2, 0, S1, r. split; [lia | split; [apply r3p |]].
      destruct HG as [(H1 & H2 & H3) | [(H1 & H2 & H3) | [(H1 & H2 & H3)
                                                         | (H1 & H2 & H3)]]].
      * destruct (oddN_0 H1).
      * right; left. split; [exact H1 | split; [exact H2 | exact H3]].
      * discriminate.
      * destruct (oddN_0 H2).
    + exists (3 + m), 0, S0, (rep [S0] m ++ S1 :: r).
      split; [lia | split; [apply r3 |]].
      right; left. split; [apply evenN_0 | split].
      * rewrite app_length, length_rep1. cbn [length].
        destruct HG as [(H1 & H2 & H3) | [(H1 & H2 & H3) | [(H1 & H2 & H3)
                                                           | (H1 & H2 & H3)]]].
        -- destruct H1 as [i Hi]; destruct H2 as [j Hj]; exists (i + j); lia.
        -- destruct H1 as [i Hi]; destruct H2 as [j Hj]; exists (i + j); lia.
        -- discriminate.
        -- subst r. destruct H2 as [i Hi]; cbn [length]; exists i; lia.
      * rewrite last_r2.
        destruct HG as [(H1 & H2 & H3) | [(H1 & H2 & H3) | [(H1 & H2 & H3)
                                                           | (H1 & H2 & H3)]]].
        -- rewrite last_cons_ne by (apply last_nonnil; exact H3). exact H3.
        -- rewrite last_cons_ne by (apply last_nonnil; exact H3). exact H3.
        -- discriminate.
        -- subst r. reflexivity.
Qed.

(** ** [StD] at arbitrarily large indices *)

Lemma live_D : forall N p s r Y, G p s r ->
  exists m cc, N <= m /\ csteps tm m (Cf p s r Y) = Some cc /\ fst cc = StD.
Proof.
  induction N as [|N IHN]; intros p s r Y HG.
  - destruct (hitD_G p s r Y HG) as (n & cc & H1 & H2 & H3).
    exists n, cc. split; [lia | split; assumption].
  - destruct (g_step p s r Y HG) as (n & p' & s' & r' & Hn & Hstep & HG').
    destruct (IHN p' s' r' Y HG') as (m & cc & Hm & Hc & Hq).
    exists (n + m), cc. split; [lia|].
    split; [rewrite csteps_add, Hstep; exact Hc | exact Hq].
Qed.

Lemma boot : csteps tm 7 c0 = Some (Cf 1 S1 [] []).
Proof. reflexivity. Qed.

Lemma recurD_1RB1LD_1LC1RA_0RB0LC_0RA0LD :
  forall N, exists m, N <= m /\ VisitsAt tm StD m.
Proof.
  intro N.
  destruct (live_D N 1 S1 [] []) as (m & cc & Hm & Hc & Hq).
  - right; right; right.
    split; [reflexivity | split; [apply oddN_1 | reflexivity]].
  - exists (7 + m). split; [lia|].
    exists (lift cc). split.
    + rewrite <- lift_c0. apply csteps_lift.
      rewrite csteps_add, boot. exact Hc.
    + rewrite lift_state. exact Hq.
Qed.

(* --- generated below by tools/mxdys4/emit_ngx.py --- *)

(** The [NGramHist] closure at k=3 n=2 t=200 fuel=40000 (131
    contexts).  It discharges the liveness of every state but [StD];
    [StD] is [recurD_1RB1LD_1LC1RA_0RB0LC_0RA0LD] above. *)

Definition lset_1RB1LD_1LC1RA_0RB0LC_0RA0LD : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0);(StC,S0)]);(S0,[])];
   [(S0,[(StC,S0);(StC,S0);(StD,S0)]);(S0,[])];
   [(S0,[(StD,S0);(StC,S0);(StC,S0)]);(S0,[])];
   [(S1,[(StA,S0);(StC,S1);(StA,S0)]);(S1,[(StB,S1);(StB,S0);(StC,S1)])];
   [(S1,[(StA,S0);(StD,S1);(StB,S1)]);(S0,[(StD,S0);(StC,S0);(StC,S0)])];
   [(S1,[(StA,S0);(StD,S1);(StB,S1)]);(S1,[(StB,S1);(StA,S1);(StB,S0)])];
   [(S1,[(StB,S1);(StA,S1);(StB,S0)]);(S1,[(StA,S0);(StD,S1);(StB,S1)])];
   [(S1,[(StB,S1);(StB,S0);(StC,S1)]);(S0,[(StC,S0);(StC,S0);(StC,S0)])];
   [(S1,[(StB,S1);(StB,S0);(StC,S1)]);(S0,[(StC,S0);(StC,S0);(StD,S0)])];
   [(S1,[(StB,S1);(StB,S0);(StC,S1)]);(S1,[(StA,S0);(StC,S1);(StA,S0)])]].

Definition rset_1RB1LD_1LC1RA_0RB0LC_0RA0LD : hgset :=
  [[(S0,[]);(S0,[])];
   [(S0,[(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0);(StC,S1)]);(S0,[(StC,S1);(StB,S1);(StB,S0)])];
   [(S0,[(StC,S1);(StA,S0);(StC,S1)]);(S1,[(StB,S0);(StC,S1);(StA,S0)])];
   [(S0,[(StC,S1);(StA,S0);(StC,S1)]);(S1,[(StB,S0);(StC,S1);(StB,S1)])];
   [(S0,[(StC,S1);(StA,S0);(StD,S1)]);(S0,[(StC,S1);(StB,S1);(StA,S1)])];
   [(S0,[(StC,S1);(StA,S0);(StD,S1)]);(S1,[(StB,S0);(StD,S1);(StA,S0)])];
   [(S0,[(StC,S1);(StB,S1);(StA,S1)]);(S0,[(StC,S1);(StA,S0)])];
   [(S0,[(StC,S1);(StB,S1);(StA,S1)]);(S0,[(StC,S1);(StA,S0);(StD,S1)])];
   [(S0,[(StC,S1);(StB,S1);(StB,S0)]);(S0,[(StC,S1);(StA,S0);(StC,S1)])];
   [(S0,[(StD,S1);(StA,S0);(StC,S1)]);(S0,[(StD,S1);(StB,S1);(StB,S0)])];
   [(S0,[(StD,S1);(StB,S1);(StB,S0)]);(S0,[(StD,S1);(StA,S0);(StC,S1)])];
   [(S0,[(StD,S1);(StB,S1);(StB,S0)]);(S1,[(StA,S1);(StB,S0)])];
   [(S0,[(StD,S1);(StB,S1);(StB,S0)]);(S1,[(StA,S1);(StB,S0);(StD,S1)])];
   [(S1,[(StA,S1);(StB,S0)]);(S0,[])];
   [(S1,[(StA,S1);(StB,S0);(StD,S1)]);(S0,[(StD,S1);(StB,S1);(StB,S0)])];
   [(S1,[(StB,S0)]);(S0,[])];
   [(S1,[(StB,S0);(StC,S1);(StA,S0)]);(S0,[(StC,S1);(StB,S1);(StA,S1)])];
   [(S1,[(StB,S0);(StC,S1);(StA,S0)]);(S1,[(StB,S0)])];
   [(S1,[(StB,S0);(StC,S1);(StA,S0)]);(S1,[(StB,S0);(StD,S1);(StA,S0)])];
   [(S1,[(StB,S0);(StC,S1);(StB,S1)]);(S0,[(StC,S1);(StA,S0);(StC,S1)])];
   [(S1,[(StB,S0);(StD,S1);(StA,S0)]);(S0,[(StD,S1);(StB,S1);(StB,S0)])]].

Definition cert_1RB1LD_1LC1RA_0RB0LC_0RA0LD (q:St) : list hcomp :=
  match q with
  | StA => [HMeas MLeft 133 [(78107515931703208415%positive,4);(19430436796872067604366%positive,4);(374132791642827860676239%positive,4);(18564009276549818%positive,3);(21705766042417834%positive,3);(1204617590238990%positive,4);(348224062901400688877198%positive,4);(20755771571121066%positive,1);(348225977771286298303710%positive,4);(1250030242562831244942%positive,4);(364199219947010574454415%positive,4);(19274058645663977%positive,4);(1250030234836185079438%positive,4);(319928688423644802017759%positive,4);(19955305423206423137935%positive,4);(373607923014930016964253%positive,4);(19430436799707297052905%positive,4);(319926775519703747492073%positive,4);(78107122925024147689%positive,2);(78126909968641105118%positive,4);(19955305419413880535501%positive,4);(78107122925016276878%positive,4);(358085474265663185316318%positive,4);(348225977767476662312158%positive,4);(78107589942713870815%positive,4);(374132791630703167999631%positive,4);(19430436799706625937053%positive,4);(91212871825351839389%positive,0);(374132791634637271562701%positive,4);(18395396209%positive,4);(18563895141149610%positive,1);(364162325345087941185166%positive,4);(311450478578336005054094%positive,4);(311452393460346307157214%positive,4);(20755885706521274%positive,3);(78098508457570557597%positive,0);(4743758979712514281%positive,2);(75893996439972683241%positive,2);(310861809436966733159913%positive,4);(4743758979838316189%positive,0);(373607923012095458631566%positive,4);(87423211486041169565%positive,0);(364163490932966500011662%positive,4);(319891490661047558695390%positive,4);(1250030246960877756046%positive,4);(310861809436966733176477%positive,4);(364162325332963248508558%positive,4);(87423211486041172446%positive,4);(374132791638429814165135%positive,4);(19955305423223516522745%positive,4);(310861809436966733179358%positive,4);(4932455855062215135%positive,4);(364199219954737220619919%positive,4);(364199219954754314009037%positive,4);(78098508457570541033%positive,2);(78098508457704778206%positive,4);(319926775516868518043534%positive,4);(19955305423223516527053%positive,4);(364199219950944678013177%positive,4);(364163490920841807335054%positive,4);(21705835516865194%positive,1);(75893996440106920414%positive,4);(319926775519703076376221%positive,4);(21707965132778155%positive,3);(319891490661047558692509%positive,4);(364199219959135267131023%positive,4);(78098508457570560478%positive,4);(374132791634637271558393%positive,4);(364199219954754314004729%positive,4);(364162325340689894674062%positive,4);(19955305427604469649039%positive,4);(78107122925149949597%positive,0);(21707965132782251%positive,3);(91212871825226037481%positive,2);(87423211486175390174%positive,4);(87423211486041153001%positive,2);(91212871825218166670%positive,4);(358085474265663185296873%positive,4);(75893996439972702686%positive,4);(348224062897002642366094%positive,4);(319928385275094884641247%positive,4);(348224062889275996200590%positive,4);(78126906159005113566%positive,4);(358085474265663185313437%positive,4);(364163490928568453500558%positive,4);(374132791638446907549945%positive,4);(22300052144339627%positive,3);(311450478590460697730702%positive,4);(1205560728646093%positive,4);(19955305419413880531193%positive,4);(78107515931837426143%positive,4);(364199219950944678017485%positive,4);(19955305415479776972431%positive,4);(311452393456536671165662%positive,4);(374132791638446907554253%positive,4);(4743758979704643470%positive,4);(308384937659535005%positive,4);(311450478586062651219598%positive,4);(21705766042413738%positive,3);(319891490661047558675945%positive,4);(373607923014930688080105%positive,4);(75893996439972699805%positive,0)] [78107515931703208415%positive;19430436796872067604366%positive;374132791642827860676239%positive;18564009276549818%positive;21705766042417834%positive;1204617590238990%positive;348224062901400688877198%positive;20755771571121066%positive;348225977771286298303710%positive;1250030242562831244942%positive;364199219947010574454415%positive;19274058645663977%positive;1250030234836185079438%positive;319928688423644802017759%positive;19955305423206423137935%positive;373607923014930016964253%positive;19430436799707297052905%positive;319926775519703747492073%positive;78107122925024147689%positive;78126909968641105118%positive;19955305419413880535501%positive;78107122925016276878%positive;358085474265663185316318%positive;348225977767476662312158%positive;78107589942713870815%positive;374132791630703167999631%positive;19430436799706625937053%positive;91212871825351839389%positive;374132791634637271562701%positive;18395396209%positive;18563895141149610%positive;364162325345087941185166%positive;311450478578336005054094%positive;311452393460346307157214%positive;20755885706521274%positive;78098508457570557597%positive;4743758979712514281%positive;75893996439972683241%positive;310861809436966733159913%positive;4743758979838316189%positive;373607923012095458631566%positive;87423211486041169565%positive;364163490932966500011662%positive;319891490661047558695390%positive;1250030246960877756046%positive;310861809436966733176477%positive;364162325332963248508558%positive;87423211486041172446%positive;374132791638429814165135%positive;19955305423223516522745%positive;310861809436966733179358%positive;4932455855062215135%positive;364199219954737220619919%positive;364199219954754314009037%positive;78098508457570541033%positive;78098508457704778206%positive;319926775516868518043534%positive;19955305423223516527053%positive;364199219950944678013177%positive;364163490920841807335054%positive;21705835516865194%positive;75893996440106920414%positive;319926775519703076376221%positive;21707965132778155%positive;319891490661047558692509%positive;364199219959135267131023%positive;78098508457570560478%positive;374132791634637271558393%positive;364199219954754314004729%positive;364162325340689894674062%positive;19955305427604469649039%positive;78107122925149949597%positive;21707965132782251%positive;91212871825226037481%positive;87423211486175390174%positive;87423211486041153001%positive;91212871825218166670%positive;358085474265663185296873%positive;75893996439972702686%positive;348224062897002642366094%positive;319928385275094884641247%positive;348224062889275996200590%positive;78126906159005113566%positive;358085474265663185313437%positive;364163490928568453500558%positive;374132791638446907549945%positive;22300052144339627%positive;311450478590460697730702%positive;1205560728646093%positive;19955305419413880531193%positive;78107515931837426143%positive;364199219950944678017485%positive;19955305415479776972431%positive;311452393456536671165662%positive;374132791638446907554253%positive;4743758979704643470%positive;308384937659535005%positive;311450478586062651219598%positive;21705766042413738%positive;319891490661047558675945%positive;373607923014930688080105%positive;75893996439972699805%positive]]
  | StB => [HMeas MLeft 133 [(364162325340689894697192%positive,2);(78107515931703208415%positive,2);(19430436796872067604366%positive,2);(374132791642827860676239%positive,2);(78107515931703713272%positive,0);(18564009276549818%positive,1);(21705766042417834%positive,1);(1204617590238990%positive,2);(348224062901400688877198%positive,2);(319928688420810243644920%positive,2);(20755771571121066%positive,2);(348225977771286298303710%positive,2);(1250030242562831244942%positive,2);(364199219947010574454415%positive,2);(1250030234836185079438%positive,2);(319928688423644802017759%positive,2);(19955305423206423137935%positive,2);(19955305427604469649308%positive,2);(78126909968641105118%positive,2);(348224062897002642368744%positive,2);(78107122925016276878%positive,2);(358085474265663185316318%positive,2);(311450478578336005056744%positive,2);(348225977767476662312158%positive,2);(78107589942713870815%positive,2);(374132791630703167999631%positive,2);(364162325332963248531688%positive,2);(18563895141149610%positive,2);(364162325345087941185166%positive,2);(311450478578336005054094%positive,2);(311452393460346307157214%positive,2);(20755885706521274%positive,1);(1250030234836185082088%positive,2);(78126914349594267112%positive,2);(364199219947010574454684%positive,2);(373607923012095458631566%positive,2);(348225977763542558789096%positive,2);(4713696782064%positive,2);(364163490920841807358184%positive,2);(364163490932966500011662%positive,2);(319891490661047558695390%positive,2);(1250030246960877756046%positive,2);(311452393464727260319208%positive,2);(4932453020503842296%positive,2);(364162325332963248508558%positive,2);(87423211486041172446%positive,2);(374132791638429814165135%positive,2);(310861809436966733179358%positive,2);(348225977775667251465704%positive,2);(4932455855062215135%positive,2);(364199219954737220619919%positive,2);(78098508457704778206%positive,2);(1250030242562831247592%positive,2);(319926775516868518043534%positive,2);(364163490920841807335054%positive,2);(21705835516865194%positive,2);(75893996440106920414%positive,2);(21707965132778155%positive,1);(19955305415479776972700%positive,2);(75332177948444%positive,2);(364163490928568453523688%positive,2);(364199219959135267131023%positive,2);(78098508457570560478%positive,2);(364162325340689894674062%positive,2);(374132791630703167999900%positive,2);(19955305427604469649039%positive,2);(21707965132782251%positive,1);(87423211486175390174%positive,2);(91212871825218166670%positive,2);(75893996439972702686%positive,2);(348224062897002642366094%positive,2);(319928385275094884641247%positive,2);(348224062889275996200590%positive,2);(78126902224901590504%positive,2);(78126906159005113566%positive,2);(374132791642827860676508%positive,2);(364163490928568453500558%positive,2);(22300052144339627%positive,1);(364199219959135267131292%positive,2);(311450478590460697730702%positive,2);(311450478586062651222248%positive,2);(78107515931837426143%positive,2);(19955305415479776972431%positive,2);(311452393452602567642600%positive,2);(311452393456536671165662%positive,2);(78107589942580157944%positive,0);(4743758979704643470%positive,2);(348224062889275996203240%positive,2);(311450478586062651219598%positive,2);(21705766042413738%positive,1);(319928385272260326268408%positive,2)] [364162325340689894697192%positive;78107515931703208415%positive;19430436796872067604366%positive;374132791642827860676239%positive;78107515931703713272%positive;18564009276549818%positive;21705766042417834%positive;1204617590238990%positive;348224062901400688877198%positive;319928688420810243644920%positive;20755771571121066%positive;348225977771286298303710%positive;1250030242562831244942%positive;364199219947010574454415%positive;1250030234836185079438%positive;319928688423644802017759%positive;19955305423206423137935%positive;19955305427604469649308%positive;78126909968641105118%positive;348224062897002642368744%positive;78107122925016276878%positive;358085474265663185316318%positive;311450478578336005056744%positive;348225977767476662312158%positive;78107589942713870815%positive;374132791630703167999631%positive;364162325332963248531688%positive;18563895141149610%positive;364162325345087941185166%positive;311450478578336005054094%positive;311452393460346307157214%positive;20755885706521274%positive;1250030234836185082088%positive;78126914349594267112%positive;364199219947010574454684%positive;373607923012095458631566%positive;348225977763542558789096%positive;4713696782064%positive;364163490920841807358184%positive;364163490932966500011662%positive;319891490661047558695390%positive;1250030246960877756046%positive;311452393464727260319208%positive;4932453020503842296%positive;364162325332963248508558%positive;87423211486041172446%positive;374132791638429814165135%positive;348225977775667251465704%positive;310861809436966733179358%positive;4932455855062215135%positive;364199219954737220619919%positive;78098508457704778206%positive;1250030242562831247592%positive;319926775516868518043534%positive;364163490920841807335054%positive;21705835516865194%positive;75893996440106920414%positive;21707965132778155%positive;19955305415479776972700%positive;75332177948444%positive;364163490928568453523688%positive;364199219959135267131023%positive;78098508457570560478%positive;364162325340689894674062%positive;374132791630703167999900%positive;19955305427604469649039%positive;21707965132782251%positive;87423211486175390174%positive;91212871825218166670%positive;75893996439972702686%positive;348224062897002642366094%positive;319928385275094884641247%positive;348224062889275996200590%positive;78126902224901590504%positive;78126906159005113566%positive;374132791642827860676508%positive;364163490928568453500558%positive;22300052144339627%positive;364199219959135267131292%positive;311450478590460697730702%positive;311450478586062651222248%positive;78107515931837426143%positive;19955305415479776972431%positive;311452393452602567642600%positive;311452393456536671165662%positive;78107589942580157944%positive;4743758979704643470%positive;348224062889275996203240%positive;311450478586062651219598%positive;21705766042413738%positive;319928385272260326268408%positive]]
  | StC => [HMeas MRight 133 [(364162325340689894697192%positive,133);(78107515931703208415%positive,0);(374132791642827860676239%positive,0);(78107515931703713272%positive,0);(319928688420810243644920%positive,133);(364199219947010574454415%positive,0);(19274058645663977%positive,133);(319928688423644802017759%positive,0);(19955305423206423137935%positive,0);(19955305427604469649308%positive,133);(373607923014930016964253%positive,133);(19430436799707297052905%positive,133);(319926775519703747492073%positive,133);(78107122925024147689%positive,133);(19955305419413880535501%positive,133);(348224062897002642368744%positive,133);(311450478578336005056744%positive,133);(78107589942713870815%positive,0);(374132791630703167999631%positive,0);(19430436799706625937053%positive,133);(91212871825351839389%positive,133);(374132791634637271562701%positive,133);(18395396209%positive,133);(364162325332963248531688%positive,133);(1250030234836185082088%positive,133);(78126914349594267112%positive,133);(364199219947010574454684%positive,133);(78098508457570557597%positive,133);(4743758979712514281%positive,133);(75893996439972683241%positive,133);(310861809436966733159913%positive,133);(4743758979838316189%positive,133);(87423211486041169565%positive,133);(348225977763542558789096%positive,133);(4713696782064%positive,133);(364163490920841807358184%positive,133);(310861809436966733176477%positive,133);(311452393464727260319208%positive,133);(4932453020503842296%positive,133);(374132791638429814165135%positive,0);(19955305423223516522745%positive,0);(348225977775667251465704%positive,133);(4932455855062215135%positive,0);(364199219954737220619919%positive,0);(364199219954754314009037%positive,133);(78098508457570541033%positive,133);(1250030242562831247592%positive,133);(19955305423223516527053%positive,133);(364199219950944678013177%positive,133);(319926775519703076376221%positive,133);(21707965132778155%positive,0);(19955305415479776972700%positive,133);(319891490661047558692509%positive,133);(75332177948444%positive,133);(364163490928568453523688%positive,133);(364199219959135267131023%positive,0);(374132791634637271558393%positive,133);(364199219954754314004729%positive,0);(374132791630703167999900%positive,133);(19955305427604469649039%positive,0);(78107122925149949597%positive,133);(21707965132782251%positive,0);(91212871825226037481%positive,133);(87423211486041153001%positive,133);(358085474265663185296873%positive,133);(319928385275094884641247%positive,0);(78126902224901590504%positive,133);(374132791642827860676508%positive,133);(358085474265663185313437%positive,133);(374132791638446907549945%positive,0);(22300052144339627%positive,0);(364199219959135267131292%positive,133);(1205560728646093%positive,133);(19955305419413880531193%positive,133);(311450478586062651222248%positive,133);(78107515931837426143%positive,0);(364199219950944678017485%positive,133);(19955305415479776972431%positive,0);(311452393452602567642600%positive,133);(374132791638446907554253%positive,133);(78107589942580157944%positive,0);(308384937659535005%positive,133);(348224062889275996203240%positive,133);(319891490661047558675945%positive,133);(373607923014930688080105%positive,133);(319928385272260326268408%positive,133);(75893996439972699805%positive,133)] [364162325340689894697192%positive;78107515931703208415%positive;374132791642827860676239%positive;78107515931703713272%positive;319928688420810243644920%positive;364199219947010574454415%positive;19274058645663977%positive;319928688423644802017759%positive;19955305423206423137935%positive;19955305427604469649308%positive;373607923014930016964253%positive;19430436799707297052905%positive;319926775519703747492073%positive;19955305419413880535501%positive;78107122925024147689%positive;348224062897002642368744%positive;311450478578336005056744%positive;78107589942713870815%positive;374132791630703167999631%positive;19430436799706625937053%positive;91212871825351839389%positive;374132791634637271562701%positive;18395396209%positive;364162325332963248531688%positive;1250030234836185082088%positive;78126914349594267112%positive;364199219947010574454684%positive;78098508457570557597%positive;4743758979712514281%positive;75893996439972683241%positive;310861809436966733159913%positive;4743758979838316189%positive;87423211486041169565%positive;348225977763542558789096%positive;4713696782064%positive;364163490920841807358184%positive;310861809436966733176477%positive;311452393464727260319208%positive;4932453020503842296%positive;374132791638429814165135%positive;19955305423223516522745%positive;348225977775667251465704%positive;4932455855062215135%positive;364199219954737220619919%positive;364199219954754314009037%positive;78098508457570541033%positive;1250030242562831247592%positive;19955305423223516527053%positive;364199219950944678013177%positive;319926775519703076376221%positive;21707965132778155%positive;19955305415479776972700%positive;319891490661047558692509%positive;75332177948444%positive;364163490928568453523688%positive;364199219959135267131023%positive;374132791634637271558393%positive;364199219954754314004729%positive;374132791630703167999900%positive;19955305427604469649039%positive;78107122925149949597%positive;21707965132782251%positive;91212871825226037481%positive;87423211486041153001%positive;358085474265663185296873%positive;319928385275094884641247%positive;78126902224901590504%positive;374132791642827860676508%positive;358085474265663185313437%positive;374132791638446907549945%positive;22300052144339627%positive;364199219959135267131292%positive;1205560728646093%positive;19955305419413880531193%positive;311450478586062651222248%positive;78107515931837426143%positive;364199219950944678017485%positive;19955305415479776972431%positive;311452393452602567642600%positive;374132791638446907554253%positive;78107589942580157944%positive;308384937659535005%positive;348224062889275996203240%positive;319891490661047558675945%positive;373607923014930688080105%positive;319928385272260326268408%positive;75893996439972699805%positive]; HMeas MLeft 133 [(364162325340689894697192%positive,270);(78107515931703208415%positive,404);(374132791642827860676239%positive,404);(78107515931703713272%positive,402);(319928688420810243644920%positive,134);(364199219947010574454415%positive,404);(19274058645663977%positive,136);(319928688423644802017759%positive,404);(19955305423206423137935%positive,404);(19955305427604469649308%positive,404);(373607923014930016964253%positive,404);(19430436799707297052905%positive,136);(319926775519703747492073%positive,136);(78107122925024147689%positive,404);(19955305419413880535501%positive,404);(348224062897002642368744%positive,270);(311450478578336005056744%positive,270);(78107589942713870815%positive,404);(374132791630703167999631%positive,404);(19430436799706625937053%positive,404);(91212871825351839389%positive,404);(374132791634637271562701%positive,404);(18395396209%positive,136);(364162325332963248531688%positive,270);(1250030234836185082088%positive,270);(78126914349594267112%positive,270);(364199219947010574454684%positive,404);(78098508457570557597%positive,404);(4743758979712514281%positive,404);(75893996439972683241%positive,404);(310861809436966733159913%positive,136);(4743758979838316189%positive,404);(87423211486041169565%positive,404);(348225977763542558789096%positive,270);(4713696782064%positive,270);(364163490920841807358184%positive,270);(310861809436966733176477%positive,404);(311452393464727260319208%positive,270);(4932453020503842296%positive,134);(374132791638429814165135%positive,404);(19955305423223516522745%positive,268);(348225977775667251465704%positive,270);(4932455855062215135%positive,404);(364199219954737220619919%positive,404);(364199219954754314009037%positive,268);(78098508457570541033%positive,404);(1250030242562831247592%positive,270);(19955305423223516527053%positive,268);(364199219950944678013177%positive,0);(319926775519703076376221%positive,404);(21707965132778155%positive,403);(19955305415479776972700%positive,404);(319891490661047558692509%positive,404);(75332177948444%positive,404);(364163490928568453523688%positive,270);(364199219959135267131023%positive,404);(374132791634637271558393%positive,0);(364199219954754314004729%positive,268);(374132791630703167999900%positive,404);(19955305427604469649039%positive,404);(78107122925149949597%positive,404);(21707965132782251%positive,403);(91212871825226037481%positive,404);(87423211486041153001%positive,404);(358085474265663185296873%positive,136);(319928385275094884641247%positive,404);(78126902224901590504%positive,270);(374132791642827860676508%positive,404);(358085474265663185313437%positive,404);(374132791638446907549945%positive,268);(22300052144339627%positive,403);(364199219959135267131292%positive,404);(1205560728646093%positive,404);(19955305419413880531193%positive,0);(311450478586062651222248%positive,270);(78107515931837426143%positive,404);(364199219950944678017485%positive,404);(19955305415479776972431%positive,404);(311452393452602567642600%positive,270);(374132791638446907554253%positive,268);(78107589942580157944%positive,402);(308384937659535005%positive,404);(348224062889275996203240%positive,270);(319891490661047558675945%positive,136);(373607923014930688080105%positive,136);(319928385272260326268408%positive,134);(75893996439972699805%positive,404)] [364162325340689894697192%positive;78107515931703208415%positive;374132791642827860676239%positive;78107515931703713272%positive;319928688420810243644920%positive;364199219947010574454415%positive;19274058645663977%positive;319928688423644802017759%positive;19955305423206423137935%positive;19955305427604469649308%positive;373607923014930016964253%positive;19430436799707297052905%positive;319926775519703747492073%positive;19955305419413880535501%positive;78107122925024147689%positive;348224062897002642368744%positive;311450478578336005056744%positive;78107589942713870815%positive;374132791630703167999631%positive;19430436799706625937053%positive;91212871825351839389%positive;374132791634637271562701%positive;18395396209%positive;364162325332963248531688%positive;1250030234836185082088%positive;78126914349594267112%positive;364199219947010574454684%positive;78098508457570557597%positive;4743758979712514281%positive;75893996439972683241%positive;310861809436966733159913%positive;4743758979838316189%positive;87423211486041169565%positive;348225977763542558789096%positive;4713696782064%positive;364163490920841807358184%positive;310861809436966733176477%positive;311452393464727260319208%positive;4932453020503842296%positive;374132791638429814165135%positive;19955305423223516522745%positive;348225977775667251465704%positive;4932455855062215135%positive;364199219954737220619919%positive;364199219954754314009037%positive;78098508457570541033%positive;1250030242562831247592%positive;19955305423223516527053%positive;364199219950944678013177%positive;319926775519703076376221%positive;21707965132778155%positive;19955305415479776972700%positive;319891490661047558692509%positive;75332177948444%positive;364163490928568453523688%positive;364199219959135267131023%positive;374132791634637271558393%positive;364199219954754314004729%positive;374132791630703167999900%positive;19955305427604469649039%positive;78107122925149949597%positive;21707965132782251%positive;91212871825226037481%positive;87423211486041153001%positive;358085474265663185296873%positive;319928385275094884641247%positive;78126902224901590504%positive;374132791642827860676508%positive;358085474265663185313437%positive;374132791638446907549945%positive;22300052144339627%positive;364199219959135267131292%positive;1205560728646093%positive;19955305419413880531193%positive;311450478586062651222248%positive;78107515931837426143%positive;364199219950944678017485%positive;19955305415479776972431%positive;311452393452602567642600%positive;374132791638446907554253%positive;78107589942580157944%positive;308384937659535005%positive;348224062889275996203240%positive;319891490661047558675945%positive;373607923014930688080105%positive;319928385272260326268408%positive;75893996439972699805%positive]]
  | StD => []
  end.

Theorem nqh_1RB1LD_1LC1RA_0RB0LC_0RA0LD : NeverQuasiHaltsSt tm_1RB1LD_1LC1RA_0RB0LC_0RA0LD.
Proof.
  apply (ngramhist_check_neverqh_lex_ext_sound tm_1RB1LD_1LC1RA_0RB0LC_0RA0LD 3 2 200 40000
           lset_1RB1LD_1LC1RA_0RB0LC_0RA0LD rset_1RB1LD_1LC1RA_0RB0LC_0RA0LD cert_1RB1LD_1LC1RA_0RB0LC_0RA0LD StD recurD_1RB1LD_1LC1RA_0RB0LC_0RA0LD).
  vm_compute. reflexivity.
Qed.
