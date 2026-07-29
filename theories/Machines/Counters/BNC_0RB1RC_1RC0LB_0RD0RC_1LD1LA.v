(** * BNC_0RB1RC_1RC0LB_0RD0RC_1LD1LA: machine 0RB1RC_1RC0LB_0RD0RC_1LD1LA never quasihalts.

    The `no anchor` bucket's wall bouncer again, MIRRORED: this machine's
    block grows RIGHTWARD, so every lemma below runs on the mirrored table
    and [Mirror.mirror_never_qh] transfers the conclusion back -- the
    wave-9 route, no new theory.

    Its bounce is bit-for-bit §6's and [BounceGlue.WallBounce] proves it
    unchanged:

      wA StA n   = (StA, (repeat S1 n, S0, []))
      wM StA a r = (StA, (repeat S1 r, S1, repeat S1 a))
      wM (S a) r --> wM a (r+3)   and   wM 0 r --> wA (r+3),  both 2*r+5

    What differs is the DRIFT, and it differs in exactly one measured way:
    **the drift runs with the head on a BLANK.**  The wall turn writes [S0]
    rather than [S1] (`tm StA S0 = 0 L StB`), so the walk leaves the
    head in the gap it opens rather than on the block, and the ripple is

      (StA, (S1 :: S1 :: L, S0, R)) --> (StA, (S1 :: L, S0, S1 :: R))

    in 5 steps -- one unit PEELED, because the step that turns the walk
    around reads the cell BELOW the head and the un-peeled form does not
    name it.  That is the standing lesson at the smallest possible scale.
    7 more steps turn the walk into the first bounce:

      wA n --> wM (n-2) 3   in  5*(n-1) + 12  steps,

    so the macro lap is [wA n --> wA (3*n)] and the block sizes are
    3, 9, 27, 81, ...  Every state recurs inside one lap
    (StA at index 0, StB -- the drift -- at 1, StC and StD inside
    the first bounce), so the closer is [LapGlue.glue_neverqh].

    Measured off the raw simulator by [tools/counters/bouncecert.py] and
    differentially validated (the bounce and terminal over an (a, r) grid,
    the collapse at every n = 2..40, the anchor sequence against the
    blank-tape replay) before any Coq was written.

    [Print Assumptions] = [functional_extensionality_dep] only. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From Coq Require Import FunctionalExtensionality.
From BBB4.Census Require Import TNF_QH.
From BBB4.Counters Require Import LapGlue BounceGlue.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 0RB1RC_1RC0LB_0RD0RC_1LD1LA *)
(** 0RB1RC_1RC0LB_0RD0RC_1LD1LA -- the real machine (its counter grows RIGHT). *)
Definition tm_0RB1RC_1RC0LB_0RD0RC_1LD1LA : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S1 DR StC
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S0 DL StB
  | StC, S0 => mk S0 DR StD | StC, S1 => mk S0 DR StC
  | StD, S0 => mk S1 DL StD | StD, S1 => mk S1 DL StA end.

(** Its mirror 0LB1LC_1LC0RB_0LD0LC_1RD1RA: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_0RB1RC_1RC0LB_0RD0RC_1LD1LA : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DL StB | StA, S1 => mk S1 DL StC
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S0 DR StB
  | StC, S0 => mk S0 DL StD | StC, S1 => mk S0 DL StC
  | StD, S0 => mk S1 DR StD | StD, S1 => mk S1 DR StA end.
Local Notation tm := tmm_0RB1RC_1RC0LB_0RD0RC_1LD1LA.

Lemma mirror_ok_0RB1RC_1RC0LB_0RD0RC_1LD1LA : mirror_tm tm_0RB1RC_1RC0LB_0RD0RC_1LD1LA = tmm_0RB1RC_1RC0LB_0RD0RC_1LD1LA.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Local Notation aA := (wA StA).
Local Notation aM := (wM StA).

Lemma chain_0RB1RC_1RC0LB_0RD0RC_1LD1LA : forall n1 n2 c c1 c2,
  csteps tm n1 c = Some c1 -> csteps tm n2 c1 = Some c2 ->
  csteps tm (n1 + n2) c = Some c2.
Proof. intros. rewrite csteps_add, H. assumption. Qed.

(** ** The bounce, straight from [BounceGlue.WallBounce] *)

Definition mchain_0RB1RC_1RC0LB_0RD0RC_1LD1LA := wmchain tm StA StC StD
  eq_refl eq_refl eq_refl eq_refl eq_refl.
Definition visC_0RB1RC_1RC0LB_0RD0RC_1LD1LA := wvisC tm StA StC eq_refl.
Definition visD_0RB1RC_1RC0LB_0RD0RC_1LD1LA := wvisD tm StA StC StD eq_refl eq_refl eq_refl.

(** ** The collapse: the drift walks the block with the head on a BLANK *)

Lemma rip1_0RB1RC_1RC0LB_0RD0RC_1LD1LA : forall L R,
  csteps tm 5 (StA, (S1 :: S1 :: L, S0, R))
    = Some (StA, (S1 :: L, S0, S1 :: R)).
Proof. intros L R. reflexivity. Qed.

Lemma ripn_0RB1RC_1RC0LB_0RD0RC_1LD1LA : forall k L R,
  csteps tm (5 * k) (StA, (repeat S1 k ++ S1 :: L, S0, R))
    = Some (StA, (S1 :: L, S0, repeat S1 k ++ R)).
Proof.
  induction k as [|k IH]; intros L R; [reflexivity|].
  cbn [repeat app].
  rewrite (rep_snoc S1 k L).
  replace (5 * S k) with (5 + 5 * k) by lia.
  apply (chain_0RB1RC_1RC0LB_0RD0RC_1LD1LA 5 (5 * k) _
           (StA, (S1 :: (repeat S1 k ++ L), S0, S1 :: R))).
  - apply rip1_0RB1RC_1RC0LB_0RD0RC_1LD1LA.
  - rewrite <- (rep_snoc S1 k L), IH, (rep_snoc S1 k R). reflexivity.
Qed.

(** The turn at the far end: the walk becomes the first bounce. *)
Lemma tail_0RB1RC_1RC0LB_0RD0RC_1LD1LA : forall X,
  csteps tm 7 (StA, ([S1], S0, X))
    = Some (StA, ([S1; S1; S1], chd X, ctl X)).
Proof. intro X. reflexivity. Qed.

Lemma wcol_0RB1RC_1RC0LB_0RD0RC_1LD1LA : forall m,
  csteps tm (5 * (S m) + 7) (aA (S (S m))) = Some (aM m 3).
Proof.
  intro m. unfold wA.
  apply (chain_0RB1RC_1RC0LB_0RD0RC_1LD1LA (5 * (S m)) 7 _
           (StA, ([S1], S0, repeat S1 (S m)))).
  { pose proof (ripn_0RB1RC_1RC0LB_0RD0RC_1LD1LA (S m) [] (@nil Sym)) as Hr.
    rewrite app_nil_r in Hr.
    replace (repeat S1 (S m) ++ [S1]) with (repeat S1 (S (S m))) in Hr
      by (rewrite rep_app1; reflexivity).
    exact Hr. }
  exact (tail_0RB1RC_1RC0LB_0RD0RC_1LD1LA (repeat S1 (S m))).
Qed.

(** ** The macro lap *)

Lemma wlap_0RB1RC_1RC0LB_0RD0RC_1LD1LA : forall m, exists k, 0 < k /\
  csteps tm k (aA (S (S m))) = Some (aA (3 + 3 * m + 3)).
Proof.
  intro m. destruct (mchain_0RB1RC_1RC0LB_0RD0RC_1LD1LA m 3) as (k & Hk & Hrun).
  exists (5 * (S m) + 7 + k). split; [lia|].
  apply (chain_0RB1RC_1RC0LB_0RD0RC_1LD1LA (5 * (S m) + 7) k _ (aM m 3)).
  - apply wcol_0RB1RC_1RC0LB_0RD0RC_1LD1LA.
  - exact Hrun.
Qed.

(** ** The anchor family: block sizes 3, 9, 27, ... *)

Fixpoint blk_0RB1RC_1RC0LB_0RD0RC_1LD1LA (t : nat) : nat :=
  match t with 0 => 3 | S t' => 3 * blk_0RB1RC_1RC0LB_0RD0RC_1LD1LA t' end.

Lemma blk_ge_0RB1RC_1RC0LB_0RD0RC_1LD1LA : forall t, 2 <= blk_0RB1RC_1RC0LB_0RD0RC_1LD1LA t.
Proof. induction t; cbn; lia. Qed.

Lemma anchor_0RB1RC_1RC0LB_0RD0RC_1LD1LA : forall t, exists m, blk_0RB1RC_1RC0LB_0RD0RC_1LD1LA t = S (S m).
Proof.
  intro t. pose proof (blk_ge_0RB1RC_1RC0LB_0RD0RC_1LD1LA t). exists (blk_0RB1RC_1RC0LB_0RD0RC_1LD1LA t - 2). lia.
Qed.

Definition Cc (p : positive) : cconf := aA (blk_0RB1RC_1RC0LB_0RD0RC_1LD1LA (Pos.to_nat p)).

Lemma lap_0RB1RC_1RC0LB_0RD0RC_1LD1LA : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. unfold Cc. rewrite Pos2Nat.inj_succ. cbn [blk_0RB1RC_1RC0LB_0RD0RC_1LD1LA].
  destruct (anchor_0RB1RC_1RC0LB_0RD0RC_1LD1LA (Pos.to_nat p)) as (m & Hm). rewrite Hm.
  destruct (wlap_0RB1RC_1RC0LB_0RD0RC_1LD1LA m) as (k & Hk & Hrun).
  exists k, (aA (3 + 3 * m + 3)).
  split; [exact Hrun | split; [| exact Hk]].
  replace (3 + 3 * m + 3) with (3 * (S (S m))) by lia.
  reflexivity.
Qed.

(** ** Visits: every state recurs inside one lap *)

Lemma visX_0RB1RC_1RC0LB_0RD0RC_1LD1LA : forall m,
  exists c, csteps tm 1 (aA (S (S m))) = Some c /\ fst c = StB.
Proof.
  intro m. unfold wA. cbn [repeat]. eexists. split; reflexivity.
Qed.

Lemma vis_0RB1RC_1RC0LB_0RD0RC_1LD1LA : forall p q, exists k c,
  csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q. unfold Cc.
  destruct (anchor_0RB1RC_1RC0LB_0RD0RC_1LD1LA (Pos.to_nat p)) as (m & Hm). rewrite Hm.
  destruct q.
  - exists 0. eexists. split; reflexivity.
  - destruct (visX_0RB1RC_1RC0LB_0RD0RC_1LD1LA m) as (c & Hc & Hq).
    exists 1, c. split; [exact Hc | exact Hq].
  - destruct (visC_0RB1RC_1RC0LB_0RD0RC_1LD1LA m 3) as (c & Hc & Hq).
    exists (5 * (S m) + 7 + 1), c. split; [| exact Hq].
    apply (chain_0RB1RC_1RC0LB_0RD0RC_1LD1LA (5 * (S m) + 7) 1 _ (aM m 3)).
    + apply wcol_0RB1RC_1RC0LB_0RD0RC_1LD1LA.
    + exact Hc.
  - destruct (visD_0RB1RC_1RC0LB_0RD0RC_1LD1LA m 3) as (c & Hc & Hq).
    exists (5 * (S m) + 7 + (3 + 2)), c. split; [| exact Hq].
    apply (chain_0RB1RC_1RC0LB_0RD0RC_1LD1LA (5 * (S m) + 7) (3 + 2) _ (aM m 3)).
    + apply wcol_0RB1RC_1RC0LB_0RD0RC_1LD1LA.
    + exact Hc.
Qed.

(** ** Boot and the theorem *)

Lemma boot_0RB1RC_1RC0LB_0RD0RC_1LD1LA : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 51.
  assert (H : match csteps tm 51 c0 with
              | Some c => ceqb c (Cc 1)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm 51 c0) as [c|] eqn:Eq; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ Eq).
  f_equal. apply ceqb_lift. exact H.
Qed.

Theorem nqhm_0RB1RC_1RC0LB_0RD0RC_1LD1LA : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc 1).
  - exact boot_0RB1RC_1RC0LB_0RD0RC_1LD1LA.
  - intros p _. apply lap_0RB1RC_1RC0LB_0RD0RC_1LD1LA.
  - intros p q _. apply vis_0RB1RC_1RC0LB_0RD0RC_1LD1LA.
Qed.

Theorem nqh_0RB1RC_1RC0LB_0RD0RC_1LD1LA : NeverQuasiHaltsSt tm_0RB1RC_1RC0LB_0RD0RC_1LD1LA.
Proof. apply (mirror_never_qh tm_0RB1RC_1RC0LB_0RD0RC_1LD1LA). rewrite mirror_ok_0RB1RC_1RC0LB_0RD0RC_1LD1LA. exact nqhm_0RB1RC_1RC0LB_0RD0RC_1LD1LA. Qed.

Theorem nonhalt_0RB1RC_1RC0LB_0RD0RC_1LD1LA : NonHalt tm_0RB1RC_1RC0LB_0RD0RC_1LD1LA.
Proof. apply never_qh_nonhalt, nqh_0RB1RC_1RC0LB_0RD0RC_1LD1LA. Qed.
