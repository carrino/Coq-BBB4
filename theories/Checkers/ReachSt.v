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
    simpler than the machine.  Where the full machine is a nested counter --
    the residue's largest open item -- the [qC]-avoiding sub-machine is one of
    only FOUR tables across the whole open core.  Two of them are

        qA 0 -> 1R qB   qA 1 -> 0L qD   qB 1 -> 1R qA
        qD 0 -> 0R qB   qD 1 -> 1L qD          (flavour B, section [MB])
        qD 0 -> 0R qA   qD 1 -> 1L qD          (flavour A, section [MA])

    a plain binary counter running DOWN, and termination only needs a
    decreasing measure, not an exact lap.  The other two are the PAIR
    counters of sections [MC] and [MD], whose block grows and whose measure
    is a different one; their headers state them.  The four roles
    [qA qB qC qD] are SECTION VARIABLES, not [StA..StD]: the sub-machine is
    what matters, so any relabelling of it is the same theorem, and together
    with [Mirror.mirror_visits] that is where most of the boarded rows come
    from.  The measure for [MA]/[MB] is

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

Lemma dsweep : forall tm qD, tm qD S1 = Some (mkTrans S1 DL qD) ->
  forall l r,
    csteps tm (S (runlen l)) (qD, (l, S1, r))
    = Some (qD, (skipn (S (runlen l)) l, S0, rep S1 (S (runlen l)) ++ r)).
Proof.
  intros tm qD HD1. induction l as [|[|] l IH]; intros r.
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
  Variable qA qB : St.
  Hypothesis HA0 : tm qA S0 = Some (mkTrans S1 DR qB).
  Hypothesis HB1 : tm qB S1 = Some (mkTrans S1 DR qA).

  Lemma right_step : forall l r, chd r = S1 ->
    csteps tm 2 (qA, (l, S0, r))
    = Some (qA, (S1 :: S1 :: l, chd (ctl r), ctl (ctl r))).
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
  Variable qA qB qC qD : St.
  Hypothesis Hst : forall q, q = qA \/ q = qB \/ q = qC \/ q = qD.
  Hypothesis HA0 : tm qA S0 = Some (mkTrans S1 DR qB).
  Hypothesis HA1 : tm qA S1 = Some (mkTrans S0 DL qD).
  Hypothesis HB1 : tm qB S1 = Some (mkTrans S1 DR qA).
  Hypothesis HD0 : tm qD S0 = Some (mkTrans S0 DR qB).
  Hypothesis HD1 : tm qD S1 = Some (mkTrans S1 DL qD).
  Variable wB : Sym.
  Variable dB : Dir.
  Hypothesis HB0 : tm qB S0 = Some (mkTrans wB dB qC).

  Local Notation Hits cc :=
    (exists k cc', csteps tm k cc = Some cc' /\ fst cc' = qC).

  (** [A] on a blank whose right neighbour is blank: [B] meets the blank. *)
  Lemma mb_right0 : forall l r, chd r = S0 -> Hits (qA, (l, S0, r)).
  Proof.
    intros l r Er. exists 2. cru. rewrite HA0. cru. rewrite Er. cru.
    rewrite HB0. cru. eexists. split; reflexivity.
  Qed.

  (** The run is empty: [A] turns left onto a blank, [B] meets a blank. *)
  Lemma mb_left0 : forall l2 r, Hits (qA, (S0 :: l2, S1, r)).
  Proof.
    intros l2 r. exists 3. cru. rewrite HA1. cru. rewrite HD0. cru.
    rewrite HB0. cru. eexists. split; reflexivity.
  Qed.

  (** A real run: sweep left over it, then come back past the blank. *)
  Lemma mb_leftS : forall j l2 r,
    csteps tm (4 + j) (qA, (rep S1 (S j) ++ S0 :: l2, S1, r))
    = Some (qA, (S1 :: S0 :: l2,
                  chd (rep S1 j ++ S0 :: r), ctl (rep S1 j ++ S0 :: r))).
  Proof.
    intros j l2 r.
    replace (4 + j) with (1 + (S j + 2)) by lia.
    rewrite csteps_add, csteps_1. cru1. rewrite HA1. cru1.
    rewrite csteps_add.
    replace (S j) with (S (runlen (rep S1 j ++ S0 :: l2)))
      by (rewrite runlen_rep; reflexivity).
    rewrite (dsweep tm qD HD1 (rep S1 j ++ S0 :: l2) (S0 :: r)).
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
    mu (rep S1 k ++ S0 :: l2) h r < n -> Hits (qA, (rep S1 k ++ S0 :: l2, h, r)).
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
        rewrite csteps_add, (right_step tm qA qB HA0 HB1 _ r Er). exact Hm.
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
    intros q k l2 h r. destruct (Hst q) as [E|[E|[E|E]]]; subst q.
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
      + assert (Hs : csteps tm (S k + 2) (qD, (rep S1 k ++ S0 :: l2, S1, r))
                     = Some (qA, (S1 :: S0 :: l2,
                                   chd (rep S1 k ++ r), ctl (rep S1 k ++ r)))).
        { rewrite csteps_add.
          replace (S k) with (S (runlen (rep S1 k ++ S0 :: l2)))
            by (rewrite runlen_rep; reflexivity).
          rewrite (dsweep tm qD HD1 (rep S1 k ++ S0 :: l2) r).
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

  Theorem mb_ReachSt : ReachSt tm qC.
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
  Variable qA qB qC qD : St.
  Hypothesis Hst : forall q, q = qA \/ q = qB \/ q = qC \/ q = qD.
  Hypothesis HA0 : tm qA S0 = Some (mkTrans S1 DR qB).
  Hypothesis HA1 : tm qA S1 = Some (mkTrans S0 DL qD).
  Hypothesis HB1 : tm qB S1 = Some (mkTrans S1 DR qA).
  Hypothesis HD0 : tm qD S0 = Some (mkTrans S0 DR qA).
  Hypothesis HD1 : tm qD S1 = Some (mkTrans S1 DL qD).
  Variable wB : Sym.
  Variable dB : Dir.
  Hypothesis HB0 : tm qB S0 = Some (mkTrans wB dB qC).

  Local Notation Hits cc :=
    (exists k cc', csteps tm k cc = Some cc' /\ fst cc' = qC).

  Lemma ma_right0 : forall l r, chd r = S0 -> Hits (qA, (l, S0, r)).
  Proof.
    intros l r Er. exists 2. cru. rewrite HA0. cru. rewrite Er. cru.
    rewrite HB0. cru. eexists. split; reflexivity.
  Qed.

  Lemma ma_left0 : forall l2 r,
    csteps tm 2 (qA, (S0 :: l2, S1, r)) = Some (qA, (S0 :: l2, S0, r)).
  Proof.
    intros l2 r. cru. rewrite HA1. cru. rewrite HD0. cru. reflexivity.
  Qed.

  Lemma ma_left0_drop : forall l2 r,
    mu (S0 :: l2) S0 r + 2 ^ (S (length l2)) = mu (S0 :: l2) S1 r.
  Proof. intros. unfold mu. cbn [length sval]. lia. Qed.

  Lemma ma_leftS : forall j l2 r,
    csteps tm (3 + j) (qA, (rep S1 (S j) ++ S0 :: l2, S1, r))
    = Some (qA, (S0 :: l2, S1, rep S1 j ++ S0 :: r)).
  Proof.
    intros j l2 r.
    replace (3 + j) with (1 + (S j + 1)) by lia.
    rewrite csteps_add, csteps_1. cru1. rewrite HA1. cru1.
    rewrite csteps_add.
    replace (S j) with (S (runlen (rep S1 j ++ S0 :: l2)))
      by (rewrite runlen_rep; reflexivity).
    rewrite (dsweep tm qD HD1 (rep S1 j ++ S0 :: l2) (S0 :: r)).
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
    mu (rep S1 k ++ S0 :: l2) h r < n -> Hits (qA, (rep S1 k ++ S0 :: l2, h, r)).
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
        rewrite csteps_add, (right_step tm qA qB HA0 HB1 _ r Er). exact Hm.
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
    intros q k l2 h r. destruct (Hst q) as [E|[E|[E|E]]]; subst q.
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
      + assert (Hs : csteps tm (S k + 1) (qD, (rep S1 k ++ S0 :: l2, S1, r))
                     = Some (qA, (S0 :: l2, S1, rep S1 k ++ r))).
        { rewrite csteps_add.
          replace (S k) with (S (runlen (rep S1 k ++ S0 :: l2)))
            by (rewrite runlen_rep; reflexivity).
          rewrite (dsweep tm qD HD1 (rep S1 k ++ S0 :: l2) r).
          rewrite runlen_rep, skipn_rep.
          cru. rewrite HD0. cru. reflexivity. }
        destruct (ma_reachC_A
                    (S (mu (rep S1 0 ++ S0 :: l2) S1 (rep S1 k ++ r)))
                    0 l2 S1 (rep S1 k ++ r)
                    ltac:(lia)) as (m & cc' & Hm & Hq).
        exists (S k + 1 + m), cc'. split; [| exact Hq].
        rewrite csteps_add, Hs. cbn [rep app] in Hm. exact Hm.
  Qed.

  Theorem ma_ReachSt : ReachSt tm qC.
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
(** ** Flavour C: the block GROWS, and the measure is a PAIR counter

    The two flavours above are binary counters running DOWN, and the tape
    read rightward from the head as a binary number is a decreasing measure.
    This third flavour is the one [docs/REACHST_TIER.md] section 4 flagged as
    wanting its own measure, and it does: the [qA]/[qD] alternation walks
    LEFT turning a run [1^k] into [1010...] while the rightward [qB] sweep
    appends one 1, so the block GROWS and [mu] does not decrease.

    What is really running is a binary counter in a PAIR encoding.  Read the
    tape rightward from the head two cells at a time,

        X = (1,1)    Y = (0,1)    Z = (1,0)    O = (0,0)

    and one round of the machine is exactly

        X^j (0,b) R   |-->   X Y^(j-1) (1,b) R

    -- a little-endian increment on the leading [{X,Y}] block, with [Z] the
    terminator that stops the machine (it is reached exactly when the head's
    1-run has ODD length, and then [qA] meets a blank and steps to [qC]).
    So the measure is the binary number whose [i]th bit says "pair [i] is not
    an X", taken over the leading [{X,Y}] block AND its terminator:

        mu2 w = sum_{i <= q} [w(2i) = 0] * 2^i,   q = min { i | w(2i+1) = 0 }

    ([mu2] below computes it by the recursion [mu2 (a :: b :: t) = [a=0] +
    2 * mu2 t] when [b = 1], and [[a=0]] when [b = 0]).  Every round drops it
    by exactly 2 ([mc_drop]), and [mu2 = 0] is exactly the halting case, so
    the induction is on [mu2] and nothing else.

    Unlike the two flavours above the round CONSUMES a blank from the right
    list, so the decomposed form has to be restored every round.  That is why
    reaching [qC] is stated here on the LIFTED configuration ([Hits]):
    trailing blanks are invisible to [lift] ([lift_pad_r]), so the form is
    free to restore, which it would not be on the raw [cconf]. *)

Definition zval (s : Sym) : nat := match s with S0 => 1 | S1 => 0 end.

Fixpoint mu2 (w : list Sym) : nat :=
  match w with
  | [] => 1
  | a :: w' =>
      zval a + match w' with
               | S1 :: t => 2 * mu2 t
               | _ => 0
               end
  end.

Lemma mu2_blank_one : forall r, mu2 (S0 :: r) = 1 + mu2 (S1 :: r).
Proof. intros [|[|] t]; reflexivity. Qed.

(** An [X] pair at the head: the counter shifts. *)
Lemma mu2_cons11 : forall w, mu2 (S1 :: S1 :: w) = 2 * mu2 w.
Proof. reflexivity. Qed.

Lemma mu2_pad_len : forall n w, length w <= n -> mu2 (w ++ [S0]) = mu2 w.
Proof.
  induction n as [|n IH]; intros [|a [|b w]] Hl; cbn [length] in Hl;
    try reflexivity; try lia.
  cbn [app]. destruct b as [|]; [reflexivity|].
  cbn [mu2]. rewrite (IH w ltac:(lia)). reflexivity.
Qed.

Lemma mu2_pad : forall w, mu2 (w ++ [S0]) = mu2 w.
Proof. intro w. apply (mu2_pad_len (length w) w). lia. Qed.

(** [rep2 t] is the [t]-fold [Y] block [(0,1)^t] the round leaves behind. *)
Fixpoint rep2 (t : nat) : list Sym :=
  match t with 0 => [] | S t' => S0 :: S1 :: rep2 t' end.

Lemma rep2_app_cons : forall t r, rep2 t ++ S0 :: S1 :: r = rep2 (S t) ++ r.
Proof.
  induction t as [|t IH]; intros r; cbn [rep2 app]; [reflexivity|].
  do 2 f_equal. apply IH.
Qed.

Lemma mu2_rep2 : forall t r, mu2 (rep2 t ++ r) = 2 ^ t * mu2 r + (2 ^ t - 1).
Proof.
  induction t as [|t IH]; intros r; cbn [rep2 app]; [cbn; lia|].
  cbn [mu2 zval]. rewrite IH.
  pose proof (pow2_pos t). cbn [Nat.pow]. nia.
Qed.

Lemma mu2_rep1 : forall k r, mu2 (rep S1 (2 * k) ++ r) = 2 ^ k * mu2 r.
Proof.
  induction k as [|k IH]; intros r; [cbn; lia|].
  replace (2 * S k) with (S (S (2 * k))) by lia.
  cbn [rep app mu2 zval]. rewrite IH. cbn [Nat.pow]. nia.
Qed.

Lemma nat_pair : forall n, exists k, n = 2 * k \/ n = S (2 * k).
Proof.
  induction n as [|n (k & [H|H])].
  - exists 0. left. reflexivity.
  - exists k. right. lia.
  - exists (S k). left. lia.
Qed.

(** Blank padding is invisible to [lift] on the RIGHT list too. *)
Lemma lift_pad_r : forall q l h r, lift (q, (l, h, r ++ [S0])) = lift (q, (l, h, r)).
Proof.
  intros. unfold lift, lift_tape, lift_side; cbn [fst snd].
  do 2 f_equal.
  apply functional_extensionality; intro n. apply nthb_pad.
Qed.

Section MC.

  Variable tm : TM.
  Variable qA qB qC qD : St.
  Hypothesis Hst : forall q, q = qA \/ q = qB \/ q = qC \/ q = qD.
  Variable wA : Sym.
  Variable dA : Dir.
  Hypothesis HA0 : tm qA S0 = Some (mkTrans wA dA qC).
  Hypothesis HA1 : tm qA S1 = Some (mkTrans S0 DL qD).
  Hypothesis HB0 : tm qB S0 = Some (mkTrans S1 DL qD).
  Hypothesis HB1 : tm qB S1 = Some (mkTrans S1 DR qB).
  Hypothesis HD0 : tm qD S0 = Some (mkTrans S0 DR qB).
  Hypothesis HD1 : tm qD S1 = Some (mkTrans S1 DL qA).

  Local Notation Hits cc :=
    (exists k c', stepn tm k (lift cc) = Some c' /\ fst c' = qC).

  Lemma mc_here : forall ct, Hits (qC, ct).
  Proof.
    intro ct. exists 0, (lift (qC, ct)).
    split; [reflexivity | apply lift_state].
  Qed.

  Lemma mc_after : forall k cc cc', csteps tm k cc = Some cc' -> Hits cc' -> Hits cc.
  Proof.
    intros k cc cc' Hk (m & c & Hm & Hq).
    exists (k + m), c. split; [| exact Hq].
    rewrite stepn_add, (csteps_lift tm k cc cc' Hk). exact Hm.
  Qed.

  (** *** The three blocks of a round *)

  (** The rightward [qB] sweep: over the run of [m] ones the head walks to
      the blank, fills it, and turns left onto the run's last cell. *)
  Lemma mc_sweep : forall m l r,
    csteps tm (S (S m)) (qB, (l, S1, rep S1 m ++ S0 :: r))
    = Some (qD, (rep S1 m ++ l, S1, S1 :: r)).
  Proof.
    induction m as [|m IH]; intros l r.
    - cru. rewrite HB1. cru. rewrite HB0. cru. reflexivity.
    - cbn [rep app].
      replace (S (S (S m))) with (1 + S (S m)) by lia.
      rewrite csteps_add, csteps_1. cru1. rewrite HB1. cru1.
      rewrite (IH (S1 :: l) r), (rep_app_cons S1 m l). reflexivity.
  Qed.

  (** The leftward alternation, two cells at a time: [qD] keeps its cell,
      [qA] erases the next one.  A [(1,1)] pair on the left becomes a
      [(0,1)] pair on the right -- an X turning into a Y. *)
  Lemma mc_peel : forall t l r,
    csteps tm (2 * t) (qD, (rep S1 (2 * t) ++ l, S1, r))
    = Some (qD, (l, S1, rep2 t ++ r)).
  Proof.
    induction t as [|t IH]; intros l r; [reflexivity|].
    replace (rep S1 (2 * S t) ++ l) with (S1 :: S1 :: (rep S1 (2 * t) ++ l))
      by (replace (2 * S t) with (S (S (2 * t))) by lia; reflexivity).
    replace (2 * S t) with (1 + (1 + 2 * t)) by lia.
    rewrite csteps_add, csteps_1. cru1. rewrite HD1. cru1.
    rewrite csteps_add, csteps_1. cru1. rewrite HA1. cru1.
    rewrite (IH l (S0 :: S1 :: r)), rep2_app_cons. reflexivity.
  Qed.

  (** The walk meets a blank at an ODD offset: [qA] reads it and steps to
      [qC].  This is the whole halting case. *)
  Lemma mc_hit : forall l r, Hits (qD, (S0 :: l, S1, r)).
  Proof.
    intros l r.
    apply (mc_after 2 _ (qC, ctape_move dA wA (l, S0, S1 :: r))).
    - cru. rewrite HD1. cru1. rewrite HA0. cru1. reflexivity.
    - apply mc_here.
  Qed.

  (** The walk meets a blank at an EVEN offset: [qD] reads it, turns, and
      after the two-step refill the head is back on the barrier's right
      neighbour in [qB] -- the next restart. *)
  Lemma mc_turn : forall l r,
    csteps tm 5 (qD, (S1 :: S0 :: l, S1, r)) = Some (qB, (S0 :: l, S1, S1 :: r)).
  Proof.
    intros l r.
    cru. rewrite HD1. cru1. rewrite HA1. cru1. rewrite HD0. cru1.
    rewrite HB0. cru1. rewrite HD0. cru1. reflexivity.
  Qed.

  (** *** One round, and the induction on [mu2] *)

  (** The round's exact measure law: the leading [X^(k+1)] block collapses
      to [X Y^k] and the terminator pair gains its 1. *)
  Lemma mc_drop : forall k r1,
    mu2 (S1 :: S1 :: rep2 k ++ S1 :: r1) + 2
    = mu2 (S1 :: rep S1 (S (2 * k)) ++ S0 :: r1).
  Proof.
    intros k r1.
    replace (S1 :: rep S1 (S (2 * k)) ++ S0 :: r1)
      with (rep S1 (2 * S k) ++ S0 :: r1)
      by (replace (2 * S k) with (S (S (2 * k))) by lia; reflexivity).
    rewrite mu2_cons11, mu2_rep2, mu2_rep1, mu2_blank_one.
    pose proof (pow2_pos k). cbn [Nat.pow]. nia.
  Qed.

  (** From a restart configuration -- [qB] on a 1 whose left neighbour is the
      barrier blank -- the machine reaches [qC].  Induction on [mu2]. *)
  Lemma mc_restart : forall n l2 r, mu2 (S1 :: r) < n -> Hits (qB, (S0 :: l2, S1, r)).
  Proof.
    induction n as [|n IH]; intros l2 r Hmu; [lia|].
    rewrite <- (lift_pad_r qB (S0 :: l2) S1 r).
    assert (Hmu' : mu2 (S1 :: (r ++ [S0])) < S n).
    { replace (S1 :: (r ++ [S0])) with ((S1 :: r) ++ [S0]) by reflexivity.
      rewrite mu2_pad. exact Hmu. }
    assert (Hin : In S0 (r ++ [S0]))
      by (apply in_or_app; right; left; reflexivity).
    destruct (left_decomp (r ++ [S0]) Hin) as (m & r1 & Hd).
    rewrite Hd in Hmu' |- *.
    destruct (nat_pair m) as (k & [Hk|Hk]); subst m.
    - (* even run: the walk ends on a blank at an odd offset *)
      apply (mc_after (S (S (2 * k))) _ (qD, (rep S1 (2 * k) ++ S0 :: l2, S1, S1 :: r1)));
        [apply mc_sweep|].
      apply (mc_after (2 * k) _ (qD, (S0 :: l2, S1, rep2 k ++ S1 :: r1)));
        [apply mc_peel|].
      apply mc_hit.
    - (* odd run: the walk turns, and the round has dropped [mu2] by 2 *)
      apply (mc_after (S (S (S (2 * k)))) _
               (qD, (rep S1 (S (2 * k)) ++ S0 :: l2, S1, S1 :: r1)));
        [apply mc_sweep|].
      replace (rep S1 (S (2 * k)) ++ S0 :: l2)
        with (rep S1 (2 * k) ++ S1 :: S0 :: l2)
        by (rewrite rep_app_cons; reflexivity).
      apply (mc_after (2 * k) _ (qD, (S1 :: S0 :: l2, S1, rep2 k ++ S1 :: r1)));
        [apply mc_peel|].
      apply (mc_after 5 _ (qB, (S0 :: l2, S1, S1 :: rep2 k ++ S1 :: r1)));
        [apply mc_turn|].
      apply IH.
      pose proof (mc_drop k r1) as Hdrop. lia.
  Qed.

  (** *** From anywhere *)

  (** [qD] on a 1: pad the left list, peel, and land on one of the two
      endpoints. *)
  Lemma mc_qD1 : forall l r, Hits (qD, (l, S1, r)).
  Proof.
    intros l r.
    rewrite <- (lift_pad qD l S1 r).
    assert (Hin : In S0 (l ++ [S0]))
      by (apply in_or_app; right; left; reflexivity).
    destruct (left_decomp (l ++ [S0]) Hin) as (n & l2 & Hd). rewrite Hd.
    destruct (nat_pair n) as (k & [Hk|Hk]); subst n.
    - apply (mc_after (2 * k) _ (qD, (S0 :: l2, S1, rep2 k ++ r)));
        [apply mc_peel | apply mc_hit].
    - replace (rep S1 (S (2 * k)) ++ S0 :: l2)
        with (rep S1 (2 * k) ++ S1 :: S0 :: l2)
        by (rewrite rep_app_cons; reflexivity).
      apply (mc_after (2 * k) _ (qD, (S1 :: S0 :: l2, S1, rep2 k ++ r)));
        [apply mc_peel|].
      apply (mc_after 5 _ (qB, (S0 :: l2, S1, S1 :: rep2 k ++ r)));
        [apply mc_turn|].
      apply (mc_restart (S (mu2 (S1 :: S1 :: rep2 k ++ r)))). lia.
  Qed.

  (** [qB] on a 1: pad the right list and sweep. *)
  Lemma mc_qB1 : forall l r, Hits (qB, (l, S1, r)).
  Proof.
    intros l r.
    rewrite <- (lift_pad_r qB l S1 r).
    assert (Hin : In S0 (r ++ [S0]))
      by (apply in_or_app; right; left; reflexivity).
    destruct (left_decomp (r ++ [S0]) Hin) as (m & r1 & Hd). rewrite Hd.
    apply (mc_after (S (S m)) _ (qD, (rep S1 m ++ l, S1, S1 :: r1)));
      [apply mc_sweep | apply mc_qD1].
  Qed.

  (** [qD] on a blank: turn right, and refill if the cell there is blank
      too. *)
  Lemma mc_qD0 : forall l r, Hits (qD, (l, S0, r)).
  Proof.
    intros l r. destruct r as [|[|] r'].
    - apply (mc_after 3 _ (qB, (S0 :: l, S1, []))).
      + cru. rewrite HD0. cru1. rewrite HB0. cru1. rewrite HD0. cru1. reflexivity.
      + apply mc_qB1.
    - apply (mc_after 3 _ (qB, (S0 :: l, S1, r'))).
      + cru. rewrite HD0. cru1. rewrite HB0. cru1. rewrite HD0. cru1. reflexivity.
      + apply mc_qB1.
    - apply (mc_after 1 _ (qB, (S0 :: l, S1, r'))).
      + cru. rewrite HD0. cru1. reflexivity.
      + apply mc_qB1.
  Qed.

  Lemma mc_qD : forall l h r, Hits (qD, (l, h, r)).
  Proof. intros l [|] r; [apply mc_qD0 | apply mc_qD1]. Qed.

  Lemma mc_qB : forall l h r, Hits (qB, (l, h, r)).
  Proof.
    intros l [|] r; [| apply mc_qB1].
    apply (mc_after 1 _ (qD, (ctl l, chd l, S1 :: r))).
    - cru. rewrite HB0. cru1. reflexivity.
    - apply mc_qD.
  Qed.

  Lemma mc_qA : forall l h r, Hits (qA, (l, h, r)).
  Proof.
    intros l [|] r.
    - apply (mc_after 1 _ (qC, ctape_move dA wA (l, S0, r)));
        [cru; rewrite HA0; cru1; reflexivity | apply mc_here].
    - apply (mc_after 1 _ (qD, (ctl l, chd l, S0 :: r)));
        [cru; rewrite HA1; cru1; reflexivity | apply mc_qD].
  Qed.

  Theorem mc_ReachSt : ReachSt tm qC.
  Proof.
    intros [q [[l h] r]]. try unfold ctape, cconf in *.
    destruct (Hst q) as [E|[E|[E|E]]]; subst q.
    - apply mc_qA.
    - apply mc_qB.
    - apply mc_here.
    - apply mc_qD.
  Qed.

End MC.
(** ** Flavour D: the same shape as C, with the two blank branches swapped

    [mc] and [md] are the same five arrows apart from which of the two
    leftward roles meets the blank and stops.  In [mc] the ERASER's blank is
    the gate into [qC] and the WRITER's blank turns the machine round; in
    [md] it is the other way about.  That one swap changes the round from an
    increment to a DECREMENT.  In the same pair alphabet

        X = (1,1)    Y = (0,1)    Z = (1,0)    O = (0,0)

    a round is exactly

        X^j Z R   |-->   Z^j X R

    -- borrow-propagation.  So reading [Z] as the bit 1 over the leading
    [{X,Z}] block, little-endian,

        nu2 w = sum_{i < p} [w(2i+1) = 0] * 2^i,   p = min { i | w(2i) = 0 }

    drops by exactly ONE per round ([md_drop]), and [nu2 = 0] -- the block is
    all X -- is exactly the halting case, where the WRITER walks onto the
    barrier blank and steps to [qC]. *)

Fixpoint nu2 (w : list Sym) : nat :=
  match w with
  | [] => 0
  | S0 :: _ => 0
  | S1 :: w' =>
      match w' with
      | S1 :: t => 2 * nu2 t
      | S0 :: t => 1 + 2 * nu2 t
      | [] => 1
      end
  end.

Lemma nu2_pad_len : forall n w, length w <= n -> nu2 (w ++ [S0]) = nu2 w.
Proof.
  induction n as [|n IH]; intros [|[|] [|b w]] Hl; cbn [length] in Hl;
    try reflexivity; try lia.
  cbn [app]. destruct b as [|]; cbn [nu2]; rewrite (IH w ltac:(lia)); reflexivity.
Qed.

Lemma nu2_pad : forall w, nu2 (w ++ [S0]) = nu2 w.
Proof. intro w. apply (nu2_pad_len (length w) w). lia. Qed.

Lemma nu2_cons11 : forall w, nu2 (S1 :: S1 :: w) = 2 * nu2 w.
Proof. reflexivity. Qed.

Lemma nu2_cons10 : forall w, nu2 (S1 :: S0 :: w) = 1 + 2 * nu2 w.
Proof. reflexivity. Qed.

Lemma nu2_rep1 : forall k w, nu2 (rep S1 (2 * k) ++ w) = 2 ^ k * nu2 w.
Proof.
  induction k as [|k IH]; intros w; [cbn; lia|].
  replace (2 * S k) with (S (S (2 * k))) by lia.
  cbn [rep app]. rewrite nu2_cons11, IH. cbn [Nat.pow]. lia.
Qed.

Lemma nu2_rep2 : forall t r,
  nu2 (S1 :: rep2 t ++ S1 :: r) = 2 ^ t * (2 * nu2 r) + (2 ^ t - 1).
Proof.
  induction t as [|t IH]; intros r.
  - cbn [rep2 app]. rewrite nu2_cons11. cbn [Nat.pow]. lia.
  - replace (S1 :: rep2 (S t) ++ S1 :: r)
      with (S1 :: S0 :: (S1 :: rep2 t ++ S1 :: r)) by reflexivity.
    rewrite nu2_cons10, IH.
    pose proof (pow2_pos t). cbn [Nat.pow]. nia.
Qed.

Section MD.

  Variable tm : TM.
  Variable qA qB qC qD : St.
  Hypothesis Hst : forall q, q = qA \/ q = qB \/ q = qC \/ q = qD.
  Variable wA : Sym.
  Variable dA : Dir.
  Hypothesis HA0 : tm qA S0 = Some (mkTrans wA dA qC).
  Hypothesis HA1 : tm qA S1 = Some (mkTrans S1 DL qD).
  Hypothesis HB0 : tm qB S0 = Some (mkTrans S1 DL qA).
  Hypothesis HB1 : tm qB S1 = Some (mkTrans S1 DR qB).
  Hypothesis HD0 : tm qD S0 = Some (mkTrans S0 DR qB).
  Hypothesis HD1 : tm qD S1 = Some (mkTrans S0 DL qA).

  Local Notation Hits cc :=
    (exists k c', stepn tm k (lift cc) = Some c' /\ fst c' = qC).

  Lemma md_here : forall ct, Hits (qC, ct).
  Proof.
    intro ct. exists 0, (lift (qC, ct)).
    split; [reflexivity | apply lift_state].
  Qed.

  Lemma md_after : forall k cc cc', csteps tm k cc = Some cc' -> Hits cc' -> Hits cc.
  Proof.
    intros k cc cc' Hk (m & c & Hm & Hq).
    exists (k + m), c. split; [| exact Hq].
    rewrite stepn_add, (csteps_lift tm k cc cc' Hk). exact Hm.
  Qed.

  (** The rightward sweep fills the blank and turns onto the run's last
      cell -- in [qA], the writer. *)
  Lemma md_sweep : forall m l r,
    csteps tm (S (S m)) (qB, (l, S1, rep S1 m ++ S0 :: r))
    = Some (qA, (rep S1 m ++ l, S1, S1 :: r)).
  Proof.
    induction m as [|m IH]; intros l r.
    - cru. rewrite HB1. cru. rewrite HB0. cru. reflexivity.
    - cbn [rep app].
      replace (S (S (S m))) with (1 + S (S m)) by lia.
      rewrite csteps_add, csteps_1. cru1. rewrite HB1. cru1.
      rewrite (IH (S1 :: l) r), (rep_app_cons S1 m l). reflexivity.
  Qed.

  (** The leftward alternation, two cells at a time. *)
  Lemma md_peel : forall t l r,
    csteps tm (2 * t) (qA, (rep S1 (2 * t) ++ l, S1, r))
    = Some (qA, (l, S1, rep2 t ++ r)).
  Proof.
    induction t as [|t IH]; intros l r; [reflexivity|].
    replace (rep S1 (2 * S t) ++ l) with (S1 :: S1 :: (rep S1 (2 * t) ++ l))
      by (replace (2 * S t) with (S (S (2 * t))) by lia; reflexivity).
    replace (2 * S t) with (1 + (1 + 2 * t)) by lia.
    rewrite csteps_add, csteps_1. cru1. rewrite HA1. cru1.
    rewrite csteps_add, csteps_1. cru1. rewrite HD1. cru1.
    rewrite (IH l (S0 :: S1 :: r)), rep2_app_cons. reflexivity.
  Qed.

  (** The writer walks onto the barrier blank: the gate into [qC]. *)
  Lemma md_hit : forall l r, Hits (qA, (S1 :: S0 :: l, S1, r)).
  Proof.
    intros l r.
    apply (md_after 3 _ (qC, ctape_move dA wA (l, S0, S0 :: S1 :: r))).
    - cru. rewrite HA1. cru1. rewrite HD1. cru1. rewrite HA0. cru1. reflexivity.
    - apply md_here.
  Qed.

  (** The ERASER meets it instead: turn round, and that is the next
      restart -- [md] needs no refill dance. *)
  Lemma md_back : forall l r,
    csteps tm 2 (qA, (S0 :: l, S1, r)) = Some (qB, (S0 :: l, S1, r)).
  Proof.
    intros l r. cru. rewrite HA1. cru1. rewrite HD0. cru1. reflexivity.
  Qed.

  (** The round's exact measure law: one borrow. *)
  Lemma md_drop : forall t r1,
    S (nu2 (S1 :: rep2 t ++ S1 :: r1))
    = nu2 (S1 :: rep S1 (2 * t) ++ S0 :: r1).
  Proof.
    intros t r1.
    replace (S1 :: rep S1 (2 * t) ++ S0 :: r1)
      with (rep S1 (2 * t) ++ S1 :: S0 :: r1)
      by (rewrite rep_app_cons; cbn [rep app]; reflexivity).
    rewrite (nu2_rep2 t r1), (nu2_rep1 t (S1 :: S0 :: r1)).
    pose proof (pow2_pos t). cbn [nu2]. nia.
  Qed.

  Lemma md_restart : forall n l2 r, nu2 (S1 :: r) < n -> Hits (qB, (S0 :: l2, S1, r)).
  Proof.
    induction n as [|n IH]; intros l2 r Hmu; [lia|].
    rewrite <- (lift_pad_r qB (S0 :: l2) S1 r).
    assert (Hmu' : nu2 (S1 :: (r ++ [S0])) < S n).
    { replace (S1 :: (r ++ [S0])) with ((S1 :: r) ++ [S0]) by reflexivity.
      rewrite nu2_pad. exact Hmu. }
    assert (Hin : In S0 (r ++ [S0]))
      by (apply in_or_app; right; left; reflexivity).
    destruct (left_decomp (r ++ [S0]) Hin) as (m & r1 & Hd).
    rewrite Hd in Hmu' |- *.
    destruct (nat_pair m) as (t & [Ht|Ht]); subst m.
    - (* even run: the round completes and [nu2] has dropped by one *)
      apply (md_after (S (S (2 * t))) _ (qA, (rep S1 (2 * t) ++ S0 :: l2, S1, S1 :: r1)));
        [apply md_sweep|].
      apply (md_after (2 * t) _ (qA, (S0 :: l2, S1, rep2 t ++ S1 :: r1)));
        [apply md_peel|].
      apply (md_after 2 _ (qB, (S0 :: l2, S1, rep2 t ++ S1 :: r1)));
        [apply md_back|].
      apply IH. pose proof (md_drop t r1) as Hdrop. lia.
    - (* odd run: the writer meets the barrier *)
      apply (md_after (S (S (S (2 * t)))) _
               (qA, (rep S1 (S (2 * t)) ++ S0 :: l2, S1, S1 :: r1)));
        [apply md_sweep|].
      replace (rep S1 (S (2 * t)) ++ S0 :: l2)
        with (rep S1 (2 * t) ++ S1 :: S0 :: l2)
        by (rewrite rep_app_cons; reflexivity).
      apply (md_after (2 * t) _ (qA, (S1 :: S0 :: l2, S1, rep2 t ++ S1 :: r1)));
        [apply md_peel|].
      apply md_hit.
  Qed.

  Lemma md_qA : forall l h r, Hits (qA, (l, h, r)).
  Proof.
    intros l [|] r.
    - apply (md_after 1 _ (qC, ctape_move dA wA (l, S0, r)));
        [cru; rewrite HA0; cru1; reflexivity | apply md_here].
    - rewrite <- (lift_pad qA l S1 r).
      assert (Hin : In S0 (l ++ [S0]))
        by (apply in_or_app; right; left; reflexivity).
      destruct (left_decomp (l ++ [S0]) Hin) as (n & l2 & Hd). rewrite Hd.
      destruct (nat_pair n) as (t & [Ht|Ht]); subst n.
      + apply (md_after (2 * t) _ (qA, (S0 :: l2, S1, rep2 t ++ r)));
          [apply md_peel|].
        apply (md_after 2 _ (qB, (S0 :: l2, S1, rep2 t ++ r)));
          [apply md_back|].
        apply (md_restart (S (nu2 (S1 :: rep2 t ++ r)))). lia.
      + replace (rep S1 (S (2 * t)) ++ S0 :: l2)
          with (rep S1 (2 * t) ++ S1 :: S0 :: l2)
          by (rewrite rep_app_cons; reflexivity).
        apply (md_after (2 * t) _ (qA, (S1 :: S0 :: l2, S1, rep2 t ++ r)));
          [apply md_peel | apply md_hit].
  Qed.

  Lemma md_qB : forall l h r, Hits (qB, (l, h, r)).
  Proof.
    intros l [|] r.
    - apply (md_after 1 _ (qA, (ctl l, chd l, S1 :: r)));
        [cru; rewrite HB0; cru1; reflexivity | apply md_qA].
    - rewrite <- (lift_pad_r qB l S1 r).
      assert (Hin : In S0 (r ++ [S0]))
        by (apply in_or_app; right; left; reflexivity).
      destruct (left_decomp (r ++ [S0]) Hin) as (m & r1 & Hd). rewrite Hd.
      apply (md_after (S (S m)) _ (qA, (rep S1 m ++ l, S1, S1 :: r1)));
        [apply md_sweep | apply md_qA].
  Qed.

  Lemma md_qD : forall l h r, Hits (qD, (l, h, r)).
  Proof.
    intros l [|] r.
    - apply (md_after 1 _ (qB, (S0 :: l, chd r, ctl r)));
        [cru; rewrite HD0; cru1; reflexivity | apply md_qB].
    - apply (md_after 1 _ (qA, (ctl l, chd l, S0 :: r)));
        [cru; rewrite HD1; cru1; reflexivity | apply md_qA].
  Qed.

  Theorem md_ReachSt : ReachSt tm qC.
  Proof.
    intros [q [[l h] r]]. try unfold ctape, cconf in *.
    destruct (Hst q) as [E|[E|[E|E]]]; subst q.
    - apply md_qA.
    - apply md_qB.
    - apply md_here.
    - apply md_qD.
  Qed.

End MD.
