(** * BNC_0RB0RB_1LA1LC_0LD0LC_1RD1RB: machine 0RB0RB_1LA1LC_0LD0LC_1RD1RB never quasihalts.

    One of the residue's `no anchor` rows, and the class John read off the
    tape (WAVE29_FINDINGS.md section 6, on this row's sibling
    0RB0LD_1LA1LC_0LD0LC_1RD1RB -- the three differ only in row A):

      "keeps bouncing back and forth with c and d states.  then when it
       passes the wall on the right it moves the wall over one and heads
       back left and then goes back to bouncing"

    THE COUNTER IS NOT A WORD, IT IS THE WALL POSITION.  That is why eight
    waves of digit-alphabet anchor enumeration returned nothing here: the
    machine never rests in a decodable digit configuration, and the thing
    that grows monotonically is a COLUMN.  The family is [BounceGlue]'s
    wall-indexed pair

      wA StB n   = (StB, (repeat S1 n, S0, []))
      wM StB a r = (StB, (repeat S1 r, S1, repeat S1 a))

    and [BounceGlue.WallBounce] supplies everything not involving [StA]:
    one bounce is [wM (S a) r --> wM a (r+3)] in exactly [2*r+5] steps,
    the terminal [wM 0 r --> wA (r+3)] is the SAME derivation read at
    [a = 0] (which is why they cost the same), and [wmchain] composes [a]
    of them.  The wall moves by exactly ONE cell per bounce and the cost
    is affine in it, so the bounce count is explicit in the anchor and
    plain induction suffices -- no [MeasureGlue], no measure, no
    well-founded recursion.

    What is left, and all this file adds, is the COLLAPSE, the only place
    [StA] appears: it walks the solid block from its near end to its far
    end at 5 steps per cell LEAVING THE TAPE UNCHANGED, and 6 more
    steps turn the walk around into the first bounce:

      wA n  -->  wM (n-2) 3   in  5*(n-1) + 7  steps.

    The macro lap is therefore [wA n --> wA (3 * n)] and the block sizes
    are 3, 9, 27, 81, ...  Every state recurs inside one lap
    ([StB] at index 0, [StA] at 1, [StC] and [StD] inside the first
    bounce), so the closer is [LapGlue.glue_neverqh] directly -- Bounce_8's
    pattern, on a family indexed by the wall rather than by a counter.

    Measured off the raw simulator by [tools/counters/bouncecert.py]
    (turnaround columns, wall step +1 per cycle, the affine cost law, and
    the wall-indexed turnaround families) and differentially validated --
    the bounce and terminal over an (a, r) grid, the collapse at every
    n = 3..40, and the anchor sequence against the blank-tape replay --
    before any Coq was written.

    [Print Assumptions] = [functional_extensionality_dep] only. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Census Require Import TNF_QH.
From BBB4.Counters Require Import LapGlue BounceGlue.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 0RB0RB_1LA1LC_0LD0LC_1RD1RB *)
Definition tm_0RB0RB_1LA1LC_0LD0LC_1RD1RB : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S0 DR StB
  | StB, S0 => mk S1 DL StA | StB, S1 => mk S1 DL StC
  | StC, S0 => mk S0 DL StD | StC, S1 => mk S0 DL StC
  | StD, S0 => mk S1 DR StD | StD, S1 => mk S1 DR StB end.
Local Notation tm := tm_0RB0RB_1LA1LC_0LD0LC_1RD1RB.

Local Notation aA := (wA StB).
Local Notation aM := (wM StB).

Lemma chain_0RB0RB_1LA1LC_0LD0LC_1RD1RB : forall n1 n2 c c1 c2,
  csteps tm n1 c = Some c1 -> csteps tm n2 c1 = Some c2 ->
  csteps tm (n1 + n2) c = Some c2.
Proof. intros. rewrite csteps_add, H. assumption. Qed.

(** ** The bounce, straight from [BounceGlue.WallBounce] *)

Definition mchain_0RB0RB_1LA1LC_0LD0LC_1RD1RB := wmchain tm StB StC StD
  eq_refl eq_refl eq_refl eq_refl eq_refl.
Definition visC_0RB0RB_1LA1LC_0LD0LC_1RD1RB := wvisC tm StB StC eq_refl.
Definition visD_0RB0RB_1LA1LC_0LD0LC_1RD1RB := wvisD tm StB StC StD eq_refl eq_refl eq_refl.

(** ** The collapse: [StA] walks the block at 5 steps per cell *)

(** One cell of the walk.  The tape is UNCHANGED -- the cell is cleared
    and rewritten -- which is what makes the walk a pure translation. *)
Lemma rip1_0RB0RB_1LA1LC_0LD0LC_1RD1RB : forall L R,
  csteps tm 5 (StA, (S1 :: L, S1, S1 :: R))
    = Some (StA, (L, S1, S1 :: S1 :: R)).
Proof. intros L R. reflexivity. Qed.

Lemma ripn_0RB0RB_1LA1LC_0LD0LC_1RD1RB : forall k L R,
  csteps tm (5 * k) (StA, (repeat S1 k ++ L, S1, S1 :: R))
    = Some (StA, (L, S1, repeat S1 k ++ S1 :: R)).
Proof.
  induction k as [|k IH]; intros L R; [reflexivity|].
  cbn [repeat app].
  replace (5 * S k) with (5 + 5 * k) by lia.
  apply (chain_0RB0RB_1LA1LC_0LD0LC_1RD1RB 5 (5 * k) _
           (StA, (repeat S1 k ++ L, S1, S1 :: S1 :: R))).
  - apply rip1_0RB0RB_1LA1LC_0LD0LC_1RD1RB.
  - rewrite IH, rep_snoc. reflexivity.
Qed.

(** The turn at the far end: the walk becomes the first bounce. *)
Lemma tail_0RB0RB_1LA1LC_0LD0LC_1RD1RB : forall X,
  csteps tm 6 (StA, ([], S1, S1 :: X))
    = Some (StB, ([S1; S1; S1], chd X, ctl X)).
Proof. intro X. reflexivity. Qed.

Lemma wcol_0RB0RB_1LA1LC_0LD0LC_1RD1RB : forall m,
  csteps tm (5 * (S m) + 7) (aA (S (S m))) = Some (aM m 3).
Proof.
  intro m. unfold wA.
  replace (5 * (S m) + 7) with (1 + (5 * (S m) + 6)) by lia.
  cbn [repeat].
  apply (chain_0RB0RB_1LA1LC_0LD0LC_1RD1RB 1 _ _ (StA, (repeat S1 (S m), S1, [S1]))).
  { reflexivity. }
  apply (chain_0RB0RB_1LA1LC_0LD0LC_1RD1RB (5 * (S m)) 6 _
           (StA, ([], S1, repeat S1 (S m) ++ [S1]))).
  { pose proof (ripn_0RB0RB_1LA1LC_0LD0LC_1RD1RB (S m) [] []) as Hr.
    rewrite app_nil_r in Hr. exact Hr. }
  rewrite rep_app1.
  exact (tail_0RB0RB_1LA1LC_0LD0LC_1RD1RB (repeat S1 (S m))).
Qed.

(** ** The macro lap *)

Lemma wlap_0RB0RB_1LA1LC_0LD0LC_1RD1RB : forall m, exists k, 0 < k /\
  csteps tm k (aA (S (S m))) = Some (aA (3 + 3 * m + 3)).
Proof.
  intro m. destruct (mchain_0RB0RB_1LA1LC_0LD0LC_1RD1RB m 3) as (k & Hk & Hrun).
  exists (5 * (S m) + 7 + k). split; [lia|].
  apply (chain_0RB0RB_1LA1LC_0LD0LC_1RD1RB (5 * (S m) + 7) k _ (aM m 3)).
  - apply wcol_0RB0RB_1LA1LC_0LD0LC_1RD1RB.
  - exact Hrun.
Qed.

(** ** The anchor family: block sizes 3, 9, 27, ... *)

Fixpoint blk_0RB0RB_1LA1LC_0LD0LC_1RD1RB (t : nat) : nat :=
  match t with 0 => 3 | S t' => 3 * blk_0RB0RB_1LA1LC_0LD0LC_1RD1RB t' end.

Lemma blk_ge_0RB0RB_1LA1LC_0LD0LC_1RD1RB : forall t, 2 <= blk_0RB0RB_1LA1LC_0LD0LC_1RD1RB t.
Proof. induction t; cbn; lia. Qed.

(** Every block the family visits is big enough to collapse. *)
Lemma anchor_0RB0RB_1LA1LC_0LD0LC_1RD1RB : forall t, exists m, blk_0RB0RB_1LA1LC_0LD0LC_1RD1RB t = (S (S m)).
Proof.
  intro t. pose proof (blk_ge_0RB0RB_1LA1LC_0LD0LC_1RD1RB t).
  exists (blk_0RB0RB_1LA1LC_0LD0LC_1RD1RB t - 2). lia.
Qed.

Definition Cc (p : positive) : cconf := aA (blk_0RB0RB_1LA1LC_0LD0LC_1RD1RB (Pos.to_nat p)).

Lemma lap_0RB0RB_1LA1LC_0LD0LC_1RD1RB : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. unfold Cc. rewrite Pos2Nat.inj_succ. cbn [blk_0RB0RB_1LA1LC_0LD0LC_1RD1RB].
  destruct (anchor_0RB0RB_1LA1LC_0LD0LC_1RD1RB (Pos.to_nat p)) as (m & Hm). rewrite Hm.
  destruct (wlap_0RB0RB_1LA1LC_0LD0LC_1RD1RB m) as (k & Hk & Hrun).
  exists k, (aA (3 + 3 * m + 3)).
  split; [exact Hrun | split; [| exact Hk]].
  replace (3 + 3 * m + 3) with (3 * (S (S m))) by lia.
  reflexivity.
Qed.

(** ** Visits: every state recurs inside one lap *)

Lemma visA_0RB0RB_1LA1LC_0LD0LC_1RD1RB : forall m,
  exists c, csteps tm 1 (aA (S (S m))) = Some c /\ fst c = StA.
Proof.
  intro m. unfold wA. cbn [repeat]. eexists. split; reflexivity.
Qed.

Lemma vis_0RB0RB_1LA1LC_0LD0LC_1RD1RB : forall p q, exists k c,
  csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q. unfold Cc.
  destruct (anchor_0RB0RB_1LA1LC_0LD0LC_1RD1RB (Pos.to_nat p)) as (m & Hm). rewrite Hm.
  destruct q.
  - destruct (visA_0RB0RB_1LA1LC_0LD0LC_1RD1RB m) as (c & Hc & Hq).
    exists 1, c. split; [exact Hc | exact Hq].
  - exists 0. eexists. split; reflexivity.
  - destruct (visC_0RB0RB_1LA1LC_0LD0LC_1RD1RB m 3) as (c & Hc & Hq).
    exists (5 * (S m) + 7 + 1), c. split; [| exact Hq].
    apply (chain_0RB0RB_1LA1LC_0LD0LC_1RD1RB (5 * (S m) + 7) 1 _ (aM m 3)).
    + apply wcol_0RB0RB_1LA1LC_0LD0LC_1RD1RB.
    + exact Hc.
  - destruct (visD_0RB0RB_1LA1LC_0LD0LC_1RD1RB m 3) as (c & Hc & Hq).
    exists (5 * (S m) + 7 + (3 + 2)), c. split; [| exact Hq].
    apply (chain_0RB0RB_1LA1LC_0LD0LC_1RD1RB (5 * (S m) + 7) (3 + 2) _ (aM m 3)).
    + apply wcol_0RB0RB_1LA1LC_0LD0LC_1RD1RB.
    + exact Hc.
Qed.

(** ** Boot and the theorem *)

Lemma boot_0RB0RB_1LA1LC_0LD0LC_1RD1RB : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 53.
  assert (H : match csteps tm 53 c0 with
              | Some c => ceqb c (Cc 1)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm 53 c0) as [c|] eqn:Eq; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ Eq).
  f_equal. apply ceqb_lift. exact H.
Qed.

Theorem nqh_0RB0RB_1LA1LC_0LD0LC_1RD1RB : NeverQuasiHaltsSt tm.
Proof.
  apply (glue_neverqh tm Cc 1).
  - exact boot_0RB0RB_1LA1LC_0LD0LC_1RD1RB.
  - intros p _. apply lap_0RB0RB_1LA1LC_0LD0LC_1RD1RB.
  - intros p q _. apply vis_0RB0RB_1LA1LC_0LD0LC_1RD1RB.
Qed.

Theorem nonhalt_0RB0RB_1LA1LC_0LD0LC_1RD1RB : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_0RB0RB_1LA1LC_0LD0LC_1RD1RB. Qed.
