(** * ReachSt: liveness of one state by UNIFORM REACHABILITY.

    The residue's hard half is LIVENESS -- "state [q] is visited infinitely
    often" ([docs/WHY_NO_HAMMER.md]).  Every lossy closure engine in the tree
    attacks it the same way: take the [q]-avoiding subgraph of a FINITE
    abstraction and show it has no infinite path.  On a counter that always
    fails, because the finite window admits the spurious abstract path "stay
    in the low bits forever" -- the carry is an unbounded wait.

    This file takes the same idea EXACTLY, but on the machine itself instead
    of on an abstraction:

      [ReachSt tm q]:  from EVERY configuration, [tm] reaches state [q].

    That is precisely "the [q]-avoiding sub-machine terminates", with no
    window and no merging, so the spurious path has nowhere to live.  It is
    stronger than what liveness needs and it implies it outright
    ([reach_st_recurs]): a machine all of whose transitions are defined and
    which reaches [q] from anywhere visits [q] at unboundedly large indices.

    The point is that the [q]-avoiding sub-machine can be DRAMATICALLY
    simpler than the machine.  For the [1RB0LD] family the full machine is a
    nested counter -- the residue's largest open item -- while the
    [StC]-avoiding sub-machine is

        A0 -> 1RB   A1 -> 0LD   B1 -> 1RA   D0 -> 0R{A,B}   D1 -> 1LD

    a plain binary counter running DOWN, and termination only needs a
    decreasing measure, not an exact lap.  The measure is

        mu (l, h, r) = 2 ^ |l| * (h + 2 * val r)

    -- the tape read from the head RIGHTWARD as a binary number, weighted by
    ABSOLUTE position ([2 ^ |l|] is the head cell's absolute weight, [l]
    being the left half-tape).  Every branch drops it by an exact power of
    two ([right_drop], [mb_leftS_drop], [ma_leftS_drop], [ma_left0_drop]),
    so a plain induction on [mu] closes it.

    The left half-tape is carried in the DECOMPOSED form
    [rep S1 k ++ S0 :: l2] -- a run of [k] ones, then a blank, then anything.
    That is not a normalisation trick: it says the list REPRESENTATION
    reaches past the leftmost 1, so the leftward sweep stops inside it and no
    blank cell is materialised.  Materialising one shifts the frame and
    DOUBLES [mu], and the measure would not decrease.  It costs nothing,
    because trailing blanks are invisible to [lift] ([lift_pad]): any
    configuration pads into the form, and every branch preserves it.

    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)

From Coq Require Import Arith Lia Bool List FunctionalExtensionality.
From BBB4 Require Import BBB4_Statement CTape.
Import ListNotations.

(** ** Uniform reachability and what it buys *)

(** From every finite-support configuration, [tm] reaches state [q]. *)
Definition ReachSt (tm : TM) (q : St) : Prop :=
  forall cc : cconf, exists k c', stepn tm k (lift cc) = Some c' /\ fst c' = q.

Definition Total (tm : TM) : Prop := forall q s, tm q s <> None.

Lemma total_cstep : forall tm, Total tm -> forall cc, exists cc', cstep tm cc = Some cc'.
Proof.
  intros tm HT [q [[l h] r]]. unfold cstep.
  destruct (tm q h) as [tr|] eqn:E; [eauto | exfalso; exact (HT q h E)].
Qed.

Lemma reach_st_far : forall tm q, Total tm -> ReachSt tm q ->
  forall N, exists n c, N <= n /\ stepn tm n InitES = Some c /\ fst c = q.
Proof.
  intros tm q HT HR N. induction N as [|N IH].
  - destruct (HR c0) as (k & c & Hk & Hq).
    rewrite lift_c0 in Hk. exists k, c. split; [lia | auto].
  - destruct IH as (n & c & Hn & Hc & Hq).
    destruct (stepn_csteps tm n c Hc) as (cc & _ & Hlift).
    destruct (total_cstep tm HT cc) as (cc1 & H1).
    destruct (HR cc1) as (k & c' & Hk & Hq').
    exists (n + 1 + k), c'. split; [lia | split; [| exact Hq']].
    rewrite stepn_add, stepn_add, Hc.
    cbn [stepn]. rewrite <- Hlift.
    rewrite (cstep_lift tm cc cc1 H1). cbn [stepn]. exact Hk.
Qed.

(** The liveness obligation of [NeverQuasiHaltsSt], discharged for [q]. *)
Theorem reach_st_recurs : forall tm q, Total tm -> ReachSt tm q ->
  forall N, exists n, N <= n /\ VisitsAt tm q n.
Proof.
  intros tm q HT HR N.
  destruct (reach_st_far tm q HT HR N) as (n & c & Hn & Hc & Hq).
  exists n. split; [exact Hn|]. exists c. split; assumption.
Qed.

(** ** Blank padding is invisible to [lift] *)

Lemma nthb_pad : forall l n, nthb (l ++ [S0]) n = nthb l n.
Proof.
  induction l as [|x l IH]; intros n.
  - destruct n as [|n]; [reflexivity|]. destruct n; reflexivity.
  - destruct n as [|n]; [reflexivity|]. apply IH.
Qed.

Lemma lift_pad : forall q l h r, lift (q, (l ++ [S0], h, r)) = lift (q, (l, h, r)).
Proof.
  intros. unfold lift, lift_tape, lift_side; cbn [fst snd].
  do 2 f_equal.
  apply functional_extensionality; intro n. apply nthb_pad.
Qed.

(** ** The measure *)

Definition sval (s : Sym) : nat := match s with S0 => 0 | S1 => 1 end.

Fixpoint val (r : list Sym) : nat :=
  match r with [] => 0 | s :: t => sval s + 2 * val t end.

Definition mu (l : list Sym) (h : Sym) (r : list Sym) : nat :=
  2 ^ (length l) * (sval h + 2 * val r).

Lemma val_chd_ctl : forall r, val r = sval (chd r) + 2 * val (ctl r).
Proof. destruct r; reflexivity. Qed.

Lemma pow2_pos : forall n, 0 < 2 ^ n.
Proof. induction n as [|n IH]; cbn [Nat.pow]; lia. Qed.

(** ** Runs of [S1] *)

Fixpoint runlen (l : list Sym) : nat :=
  match l with S1 :: t => S (runlen t) | _ => 0 end.

Fixpoint rep (s : Sym) (n : nat) : list Sym :=
  match n with 0 => [] | S m => s :: rep s m end.

Lemma rep_length : forall s n, length (rep s n) = n.
Proof. induction n; cbn; auto. Qed.

Lemma rep_app_cons : forall s n r, rep s n ++ s :: r = rep s (S n) ++ r.
Proof.
  induction n as [|n IH]; intros r; cbn [rep app]; [reflexivity|].
  f_equal. apply IH.
Qed.

Lemma runlen_rep : forall j l2, runlen (rep S1 j ++ S0 :: l2) = j.
Proof.
  induction j as [|j IH]; intros l2; cbn [rep app runlen]; [reflexivity|].
  f_equal. apply IH.
Qed.

Lemma skipn_rep : forall j l2, skipn (S j) (rep S1 j ++ S0 :: l2) = l2.
Proof.
  induction j as [|j IH]; intros l2; cbn [rep app skipn]; [reflexivity|].
  apply IH.
Qed.

Lemma length_rep_app : forall j l2,
  length (rep S1 j ++ S0 :: l2) = j + S (length l2).
Proof.
  intros. rewrite app_length, rep_length. reflexivity.
Qed.

Lemma val_rep1_app : forall j r, val (rep S1 j ++ r) + 1 = 2 ^ j * (val r + 1).
Proof.
  induction j as [|j IH]; intros r; cbn [rep app val]; [cbn; lia|].
  specialize (IH r). cbn [sval Nat.pow]. lia.
Qed.

(** Any left half-tape carrying a blank is in decomposed form. *)
Lemma left_decomp : forall l, In S0 l ->
  exists k l2, l = rep S1 k ++ S0 :: l2.
Proof.
  induction l as [|[|] l IH]; intros H.
  - destruct H.
  - exists 0, l. reflexivity.
  - destruct H as [H|H]; [discriminate H|].
    destruct (IH H) as (k & l2 & Hk).
    exists (S k), l2. cbn [rep app]. f_equal. exact Hk.
Qed.

Local Ltac cru :=
  cbn [csteps cstep ctape_move chd ctl rep app t_dir t_write t_next];
  try unfold ctape, cconf in *.

Local Ltac cru1 :=
  cbn [cstep ctape_move chd ctl rep app t_dir t_write t_next];
  try unfold ctape, cconf in *.

(** ** The leftward [StD] sweep

    [D1 -> 1LD] walks left over the leading [S1]-run, writing it back
    unchanged, and stops on the first blank. *)

Lemma dsweep : forall tm, tm StD S1 = Some (mkTrans S1 DL StD) ->
  forall l r,
    csteps tm (S (runlen l)) (StD, (l, S1, r))
    = Some (StD, (skipn (S (runlen l)) l, S0, rep S1 (S (runlen l)) ++ r)).
Proof.
  intros tm HD1. induction l as [|[|] l IH]; intros r.
  - cbn [runlen csteps cstep]. rewrite HD1. reflexivity.
  - cbn [runlen csteps cstep]. rewrite HD1. reflexivity.
  - cbn [runlen].
    replace (S (S (runlen l))) with (1 + S (runlen l)) by lia.
    rewrite csteps_add, csteps_1. cbn [cstep]. rewrite HD1.
    cbn [ctape_move ctl chd t_dir t_write t_next]. try unfold ctape, cconf in *.
    rewrite (IH (S1 :: r)), (rep_app_cons S1 (S (runlen l)) r).
    cbn [skipn]. reflexivity.
Qed.

(** ** The right branch, shared by both flavours

    [A] on a blank whose right neighbour is a 1 walks two cells right: the
    head's absolute weight quadruples and the suffix loses its low 1. *)

Section RightBranch.

  Variable tm : TM.
  Hypothesis HA0 : tm StA S0 = Some (mkTrans S1 DR StB).
  Hypothesis HB1 : tm StB S1 = Some (mkTrans S1 DR StA).

  Lemma right_step : forall l r, chd r = S1 ->
    csteps tm 2 (StA, (l, S0, r))
    = Some (StA, (S1 :: S1 :: l, chd (ctl r), ctl (ctl r))).
  Proof.
    intros l r Er. cru. rewrite HA0. cru. rewrite Er. cru. rewrite HB1. cru.
    reflexivity.
  Qed.

End RightBranch.

Lemma right_drop : forall l r, chd r = S1 ->
  mu (S1 :: S1 :: l) (chd (ctl r)) (ctl (ctl r)) + 2 ^ (S (length l))
  = mu l S0 r.
Proof.
  intros l r Er. unfold mu. cbn [length sval].
  rewrite <- (val_chd_ctl (ctl r)).
  assert (Hr : val r = 1 + 2 * val (ctl r))
    by (rewrite (val_chd_ctl r), Er; reflexivity).
  rewrite Hr. cbn [Nat.pow]. lia.
Qed.

(** The decomposed form is closed under the right branch. *)
Lemma rep_two : forall k l2,
  S1 :: S1 :: (rep S1 k ++ S0 :: l2) = rep S1 (S (S k)) ++ S0 :: l2.
Proof. reflexivity. Qed.

(** ** Flavour B: [D0 -> 0RB] *)

Section MB.

  Variable tm : TM.
  Hypothesis HA0 : tm StA S0 = Some (mkTrans S1 DR StB).
  Hypothesis HA1 : tm StA S1 = Some (mkTrans S0 DL StD).
  Hypothesis HB1 : tm StB S1 = Some (mkTrans S1 DR StA).
  Hypothesis HD0 : tm StD S0 = Some (mkTrans S0 DR StB).
  Hypothesis HD1 : tm StD S1 = Some (mkTrans S1 DL StD).
  Variable wB : Sym.
  Variable dB : Dir.
  Hypothesis HB0 : tm StB S0 = Some (mkTrans wB dB StC).

  Local Notation Hits cc :=
    (exists k cc', csteps tm k cc = Some cc' /\ fst cc' = StC).

  (** [A] on a blank whose right neighbour is blank: [B] meets the blank. *)
  Lemma mb_right0 : forall l r, chd r = S0 -> Hits (StA, (l, S0, r)).
  Proof.
    intros l r Er. exists 2. cru. rewrite HA0. cru. rewrite Er. cru.
    rewrite HB0. cru. eexists. split; reflexivity.
  Qed.

  (** The run is empty: [A] turns left onto a blank, [B] meets a blank. *)
  Lemma mb_left0 : forall l2 r, Hits (StA, (S0 :: l2, S1, r)).
  Proof.
    intros l2 r. exists 3. cru. rewrite HA1. cru. rewrite HD0. cru.
    rewrite HB0. cru. eexists. split; reflexivity.
  Qed.

  (** A real run: sweep left over it, then come back past the blank. *)
  Lemma mb_leftS : forall j l2 r,
    csteps tm (4 + j) (StA, (rep S1 (S j) ++ S0 :: l2, S1, r))
    = Some (StA, (S1 :: S0 :: l2,
                  chd (rep S1 j ++ S0 :: r), ctl (rep S1 j ++ S0 :: r))).
  Proof.
    intros j l2 r.
    replace (4 + j) with (1 + (S j + 2)) by lia.
    rewrite csteps_add, csteps_1. cru1. rewrite HA1. cru1.
    rewrite csteps_add.
    replace (S j) with (S (runlen (rep S1 j ++ S0 :: l2)))
      by (rewrite runlen_rep; reflexivity).
    rewrite (dsweep tm HD1 (rep S1 j ++ S0 :: l2) (S0 :: r)).
    rewrite runlen_rep, skipn_rep.
    cru. rewrite HD0. cru. rewrite HB1. cru. reflexivity.
  Qed.

  Lemma mb_leftS_drop : forall j l2 r,
    mu (S1 :: S0 :: l2) (chd (rep S1 j ++ S0 :: r)) (ctl (rep S1 j ++ S0 :: r))
    + 2 ^ (S (S (length l2)))
    = mu (rep S1 (S j) ++ S0 :: l2) S1 r.
  Proof.
    intros j l2 r. unfold mu.
    rewrite <- (val_chd_ctl (rep S1 j ++ S0 :: r)).
    rewrite length_rep_app. cbn [length sval].
    pose proof (val_rep1_app j (S0 :: r)) as HX. cbn [val sval] in HX.
    replace (S j + S (length l2)) with (S (S (length l2)) + j) by lia.
    rewrite Nat.pow_add_r. cbn [Nat.pow]. nia.
  Qed.

  Lemma mb_reachC_A : forall n k l2 h r,
    mu (rep S1 k ++ S0 :: l2) h r < n -> Hits (StA, (rep S1 k ++ S0 :: l2, h, r)).
  Proof.
    induction n as [|n IH]; intros k l2 h r Hmu; [lia|].
    destruct h as [|].
    - destruct (chd r) as [|] eqn:Er.
      + apply (mb_right0 _ r Er).
      + pose proof (right_drop (rep S1 k ++ S0 :: l2) r Er) as Hdec.
        pose proof (pow2_pos (S (length (rep S1 k ++ S0 :: l2)))).
        destruct (IH (S (S k)) l2 (chd (ctl r)) (ctl (ctl r))
                    ltac:(cbn [rep app]; lia)) as (m & cc' & Hm & Hq).
        exists (2 + m), cc'. split; [| exact Hq].
        rewrite csteps_add, (right_step tm HA0 HB1 _ r Er). exact Hm.
    - destruct k as [|j].
      + cbn [rep app]. apply mb_left0.
      + pose proof (mb_leftS_drop j l2 r) as Hdec.
        pose proof (pow2_pos (S (S (length l2)))).
        destruct (IH 1 l2 (chd (rep S1 j ++ S0 :: r)) (ctl (rep S1 j ++ S0 :: r))
                    ltac:(cbn [rep app]; lia)) as (m & cc' & Hm & Hq).
        exists (4 + j + m), cc'. split; [| exact Hq].
        rewrite csteps_add, (mb_leftS j l2 r). cbn [rep app] in Hm. exact Hm.
  Qed.

  Lemma mb_reachC_any : forall q k l2 h r, Hits (q, (rep S1 k ++ S0 :: l2, h, r)).
  Proof.
    intros q k l2 h r. destruct q.
    - apply (mb_reachC_A (S (mu (rep S1 k ++ S0 :: l2) h r)) k l2 h r ltac:(lia)).
    - destruct h.
      + exists 1. cru. rewrite HB0. cru. eexists. split; reflexivity.
      + destruct (mb_reachC_A (S (mu (rep S1 (S k) ++ S0 :: l2) (chd r) (ctl r)))
                    (S k) l2 (chd r) (ctl r) ltac:(lia)) as (m & cc' & Hm & Hq).
        exists (1 + m), cc'. split; [| exact Hq].
        rewrite csteps_add, csteps_1. cru1. rewrite HB1. cru1.
        cbn [rep app] in Hm. exact Hm.
    - exists 0. eexists. split; reflexivity.
    - destruct h.
      + destruct (chd r) eqn:Er.
        * exists 2. cru. rewrite HD0. cru. rewrite Er. cru. rewrite HB0. cru.
          eexists. split; reflexivity.
        * destruct (mb_reachC_A
                      (S (mu (rep S1 1 ++ S0 :: (rep S1 k ++ S0 :: l2))
                             (chd (ctl r)) (ctl (ctl r))))
                      1 (rep S1 k ++ S0 :: l2) (chd (ctl r)) (ctl (ctl r))
                      ltac:(lia)) as (m & cc' & Hm & Hq).
          exists (2 + m), cc'. split; [| exact Hq].
          rewrite csteps_add. cru. rewrite HD0. cru. rewrite Er. cru.
          rewrite HB1. cru. cbn [rep app] in Hm. exact Hm.
      + assert (Hs : csteps tm (S k + 2) (StD, (rep S1 k ++ S0 :: l2, S1, r))
                     = Some (StA, (S1 :: S0 :: l2,
                                   chd (rep S1 k ++ r), ctl (rep S1 k ++ r)))).
        { rewrite csteps_add.
          replace (S k) with (S (runlen (rep S1 k ++ S0 :: l2)))
            by (rewrite runlen_rep; reflexivity).
          rewrite (dsweep tm HD1 (rep S1 k ++ S0 :: l2) r).
          rewrite runlen_rep, skipn_rep.
          cru. rewrite HD0. cru. rewrite HB1. cru. reflexivity. }
        destruct (mb_reachC_A
                    (S (mu (rep S1 1 ++ S0 :: l2)
                           (chd (rep S1 k ++ r)) (ctl (rep S1 k ++ r))))
                    1 l2 (chd (rep S1 k ++ r)) (ctl (rep S1 k ++ r))
                    ltac:(lia)) as (m & cc' & Hm & Hq).
        exists (S k + 2 + m), cc'. split; [| exact Hq].
        rewrite csteps_add, Hs. cbn [rep app] in Hm. exact Hm.
  Qed.

  Theorem mb_ReachSt : ReachSt tm StC.
  Proof.
    intros [q [[l h] r]]. try unfold ctape, cconf in *.
    assert (Hin : In S0 (l ++ [S0]))
      by (apply in_or_app; right; left; reflexivity).
    destruct (left_decomp (l ++ [S0]) Hin) as (k & l2 & Hd).
    destruct (mb_reachC_any q k l2 h r) as (m & cc' & Hm & Hq).
    exists m, (lift cc'). split; [| rewrite lift_state; exact Hq].
    rewrite <- (lift_pad q l h r), Hd. apply csteps_lift. exact Hm.
  Qed.

End MB.

(** ** Flavour A: [D0 -> 0RA]

    The left branch lands in [StA] one cell earlier, so an empty run does not
    reach [StC] on the spot; the measure simply drops again. *)

Section MA.

  Variable tm : TM.
  Hypothesis HA0 : tm StA S0 = Some (mkTrans S1 DR StB).
  Hypothesis HA1 : tm StA S1 = Some (mkTrans S0 DL StD).
  Hypothesis HB1 : tm StB S1 = Some (mkTrans S1 DR StA).
  Hypothesis HD0 : tm StD S0 = Some (mkTrans S0 DR StA).
  Hypothesis HD1 : tm StD S1 = Some (mkTrans S1 DL StD).
  Variable wB : Sym.
  Variable dB : Dir.
  Hypothesis HB0 : tm StB S0 = Some (mkTrans wB dB StC).

  Local Notation Hits cc :=
    (exists k cc', csteps tm k cc = Some cc' /\ fst cc' = StC).

  Lemma ma_right0 : forall l r, chd r = S0 -> Hits (StA, (l, S0, r)).
  Proof.
    intros l r Er. exists 2. cru. rewrite HA0. cru. rewrite Er. cru.
    rewrite HB0. cru. eexists. split; reflexivity.
  Qed.

  Lemma ma_left0 : forall l2 r,
    csteps tm 2 (StA, (S0 :: l2, S1, r)) = Some (StA, (S0 :: l2, S0, r)).
  Proof.
    intros l2 r. cru. rewrite HA1. cru. rewrite HD0. cru. reflexivity.
  Qed.

  Lemma ma_left0_drop : forall l2 r,
    mu (S0 :: l2) S0 r + 2 ^ (S (length l2)) = mu (S0 :: l2) S1 r.
  Proof. intros. unfold mu. cbn [length sval]. lia. Qed.

  Lemma ma_leftS : forall j l2 r,
    csteps tm (3 + j) (StA, (rep S1 (S j) ++ S0 :: l2, S1, r))
    = Some (StA, (S0 :: l2, S1, rep S1 j ++ S0 :: r)).
  Proof.
    intros j l2 r.
    replace (3 + j) with (1 + (S j + 1)) by lia.
    rewrite csteps_add, csteps_1. cru1. rewrite HA1. cru1.
    rewrite csteps_add.
    replace (S j) with (S (runlen (rep S1 j ++ S0 :: l2)))
      by (rewrite runlen_rep; reflexivity).
    rewrite (dsweep tm HD1 (rep S1 j ++ S0 :: l2) (S0 :: r)).
    rewrite runlen_rep, skipn_rep, csteps_1.
    cru1. rewrite HD0. cru1. reflexivity.
  Qed.

  Lemma ma_leftS_drop : forall j l2 r,
    mu (S0 :: l2) S1 (rep S1 j ++ S0 :: r) + 2 ^ (S (length l2))
    = mu (rep S1 (S j) ++ S0 :: l2) S1 r.
  Proof.
    intros j l2 r. unfold mu.
    rewrite length_rep_app. cbn [length sval].
    pose proof (val_rep1_app j (S0 :: r)) as HX. cbn [val sval] in HX.
    replace (S j + S (length l2)) with (S (length l2) + S j) by lia.
    rewrite Nat.pow_add_r. cbn [Nat.pow]. nia.
  Qed.

  Lemma ma_reachC_A : forall n k l2 h r,
    mu (rep S1 k ++ S0 :: l2) h r < n -> Hits (StA, (rep S1 k ++ S0 :: l2, h, r)).
  Proof.
    induction n as [|n IH]; intros k l2 h r Hmu; [lia|].
    destruct h as [|].
    - destruct (chd r) as [|] eqn:Er.
      + apply (ma_right0 _ r Er).
      + pose proof (right_drop (rep S1 k ++ S0 :: l2) r Er) as Hdec.
        pose proof (pow2_pos (S (length (rep S1 k ++ S0 :: l2)))).
        destruct (IH (S (S k)) l2 (chd (ctl r)) (ctl (ctl r))
                    ltac:(cbn [rep app]; lia)) as (m & cc' & Hm & Hq).
        exists (2 + m), cc'. split; [| exact Hq].
        rewrite csteps_add, (right_step tm HA0 HB1 _ r Er). exact Hm.
    - destruct k as [|j].
      + cbn [rep app] in *.
        pose proof (ma_left0_drop l2 r) as Hdec.
        pose proof (pow2_pos (S (length l2))).
        destruct (IH 0 l2 S0 r ltac:(cbn [rep app]; lia)) as (m & cc' & Hm & Hq).
        exists (2 + m), cc'. split; [| exact Hq].
        rewrite csteps_add, (ma_left0 l2 r). cbn [rep app] in Hm. exact Hm.
      + pose proof (ma_leftS_drop j l2 r) as Hdec.
        pose proof (pow2_pos (S (length l2))).
        destruct (IH 0 l2 S1 (rep S1 j ++ S0 :: r) ltac:(cbn [rep app]; lia))
          as (m & cc' & Hm & Hq).
        exists (3 + j + m), cc'. split; [| exact Hq].
        rewrite csteps_add, (ma_leftS j l2 r). cbn [rep app] in Hm. exact Hm.
  Qed.

  Lemma ma_reachC_any : forall q k l2 h r, Hits (q, (rep S1 k ++ S0 :: l2, h, r)).
  Proof.
    intros q k l2 h r. destruct q.
    - apply (ma_reachC_A (S (mu (rep S1 k ++ S0 :: l2) h r)) k l2 h r ltac:(lia)).
    - destruct h.
      + exists 1. cru. rewrite HB0. cru. eexists. split; reflexivity.
      + destruct (ma_reachC_A (S (mu (rep S1 (S k) ++ S0 :: l2) (chd r) (ctl r)))
                    (S k) l2 (chd r) (ctl r) ltac:(lia)) as (m & cc' & Hm & Hq).
        exists (1 + m), cc'. split; [| exact Hq].
        rewrite csteps_add, csteps_1. cru1. rewrite HB1. cru1.
        cbn [rep app] in Hm. exact Hm.
    - exists 0. eexists. split; reflexivity.
    - destruct h.
      + destruct (ma_reachC_A
                    (S (mu (rep S1 0 ++ S0 :: (rep S1 k ++ S0 :: l2))
                           (chd r) (ctl r)))
                    0 (rep S1 k ++ S0 :: l2) (chd r) (ctl r) ltac:(lia))
          as (m & cc' & Hm & Hq).
        exists (1 + m), cc'. split; [| exact Hq].
        rewrite csteps_add, csteps_1. cru1. rewrite HD0. cru1.
        cbn [rep app] in Hm. exact Hm.
      + assert (Hs : csteps tm (S k + 1) (StD, (rep S1 k ++ S0 :: l2, S1, r))
                     = Some (StA, (S0 :: l2, S1, rep S1 k ++ r))).
        { rewrite csteps_add.
          replace (S k) with (S (runlen (rep S1 k ++ S0 :: l2)))
            by (rewrite runlen_rep; reflexivity).
          rewrite (dsweep tm HD1 (rep S1 k ++ S0 :: l2) r).
          rewrite runlen_rep, skipn_rep.
          cru. rewrite HD0. cru. reflexivity. }
        destruct (ma_reachC_A
                    (S (mu (rep S1 0 ++ S0 :: l2) S1 (rep S1 k ++ r)))
                    0 l2 S1 (rep S1 k ++ r)
                    ltac:(lia)) as (m & cc' & Hm & Hq).
        exists (S k + 1 + m), cc'. split; [| exact Hq].
        rewrite csteps_add, Hs. cbn [rep app] in Hm. exact Hm.
  Qed.

  Theorem ma_ReachSt : ReachSt tm StC.
  Proof.
    intros [q [[l h] r]]. try unfold ctape, cconf in *.
    assert (Hin : In S0 (l ++ [S0]))
      by (apply in_or_app; right; left; reflexivity).
    destruct (left_decomp (l ++ [S0]) Hin) as (k & l2 & Hd).
    destruct (ma_reachC_any q k l2 h r) as (m & cc' & Hm & Hq).
    exists m, (lift cc'). split; [| rewrite lift_state; exact Hq].
    rewrite <- (lift_pad q l h r), Hd. apply csteps_lift. exact Hm.
  Qed.

End MA.
