(** * WrapBc_R: 1RB---_1RC0RB_0LC0RD_1LD1LB quasihalts, with bound 1.

    One of the two [1RB---] holdouts.  [StA]'s S1 transition is
    undefined, so [StA] fires once -- at configuration index 0 -- and
    [StB], [StC], [StD] are CLOSED under the table.  The machine
    therefore genuinely quasihalts (with score 1) and never halts, so
    the never-quasihalting tier can only ever reject it; the tier it
    needs is [QHBound], via [LapGlueAbs.glue_qh_abs].

    The 3-state core is the doubling bouncer of [WrapBouncer]:

      mkA K   = StB, head just left of a solid block of K ones
      mkM a r = the same block split by the head: a wall of a ones
                behind it, a run of r ones ahead

    Out (StB) writes zeros, back (StD) writes ones, and one bounce
    moves two cells of wall into four cells of run.  After (K-3)/2
    bounces the tape is solid again with 2K+1 ones.  The block
    lengths are 3, 7, 15, 31, ... = 2^(t+1) - 1.

    Every gadget below is a plain [csteps] reflexivity.  The whole
    design was validated against the raw simulator (anchors K = 3..63,
    bounces for every odd wall up to 19 and runs up to 41) before any
    Coq was written.

    [Print Assumptions] = [functional_extensionality_dep] only. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Census Require Import TNF_QH.
From BBB4.Counters Require Import LapGlueAbs WrapBouncer.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB---_1RC0RB_0LC0RD_1LD1LB *)
Definition tm_wr : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => None
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S0 DR StB
  | StC, S0 => mk S0 DL StC | StC, S1 => mk S0 DR StD
  | StD, S0 => mk S1 DL StD | StD, S1 => mk S1 DL StB
  end.

Definition mkA (K : nat) : cconf := (StB, ([], S0, repeat S1 K)).
Definition mkM (a r : nat) : cconf :=
  (StB, (repeat S1 a, S1, repeat S1 r)).

(** ** List helper *)

Lemma rep_app1 : forall (x : Sym) n, repeat x n ++ [x] = repeat x (S n).
Proof.
  induction n; simpl; [reflexivity | rewrite IHn; reflexivity].
Qed.

Lemma rep_snoc : forall (x : Sym) n l,
  repeat x n ++ x :: l = x :: repeat x n ++ l.
Proof.
  induction n; intros l; simpl; [reflexivity | rewrite IHn; reflexivity].
Qed.

(** ** The collapse sweep *)

(** Three steps move one cell of the block behind the head. *)
Lemma col1 : forall L m,
  csteps tm_wr 3 (StB, (L, S0, repeat S1 (S (S m))))
  = Some (StB, (S1 :: L, S0, repeat S1 (S m))).
Proof. reflexivity. Qed.

Lemma coln : forall j L m,
  csteps tm_wr (3 * j) (StB, (L, S0, repeat S1 (j + S m)))
  = Some (StB, (repeat S1 j ++ L, S0, repeat S1 (S m))).
Proof.
  induction j as [|j IH]; intros L m.
  - reflexivity.
  - replace (3 * S j) with (3 + 3 * j) by lia.
    replace (S j + S m) with (S (S (j + m))) by lia.
    rewrite csteps_add, col1.
    replace (S (j + m)) with (j + S m) by lia.
    rewrite IH.
    change (repeat S1 (S j) ++ L) with (S1 :: (repeat S1 j ++ L)).
    rewrite (rep_snoc S1 j L). reflexivity.
Qed.

(** The turn at the far end of the block: the head runs off it and
    comes back two cells, starting the first bounce. *)
Lemma col5 : forall M,
  csteps tm_wr 5 (StB, (S1 :: M, S0, [S1]))
  = Some (StB, (M, S1, [S1; S1; S1])).
Proof. reflexivity. Qed.

Lemma Hcol_wr : forall m,
  csteps tm_wr (3 * (2 * m + 3) + 2) (mkA (2 * m + 3))
  = Some (mkM (2 * m + 1) 3).
Proof.
  intro m. unfold mkA, mkM.
  replace (3 * (2 * m + 3) + 2) with (3 * (2 * m + 2) + 5) by lia.
  replace (2 * m + 3) with (2 * m + 2 + S 0) by lia.
  rewrite csteps_add, coln, app_nil_r.
  replace (2 * m + 2) with (S (2 * m + 1)) by lia.
  change (repeat S1 (S (2 * m + 1))) with (S1 :: repeat S1 (2 * m + 1)).
  apply col5.
Qed.

(** ** One bounce *)

(** Out: StB writes zeros over the run. *)
Lemma bstep : forall L R,
  csteps tm_wr 1 (StB, (L, S1, S1 :: R)) = Some (StB, (S0 :: L, S1, R)).
Proof. reflexivity. Qed.

Lemma bsw : forall k L,
  csteps tm_wr k (StB, (L, S1, repeat S1 k))
  = Some (StB, (repeat S0 k ++ L, S1, [])).
Proof.
  induction k as [|k IH]; intros L.
  - reflexivity.
  - replace (S k) with (1 + k) by lia.
    change (repeat S1 (1 + k)) with (S1 :: repeat S1 k).
    rewrite csteps_add, bstep, IH.
    change (repeat S0 (1 + k) ++ L) with (S0 :: (repeat S0 k ++ L)).
    rewrite (rep_snoc S0 k L). reflexivity.
Qed.

(** The turnaround at the outer end. *)
Lemma turn5 : forall M,
  csteps tm_wr 5 (StB, (M, S1, [])) = Some (StD, (S0 :: M, S0, [S1])).
Proof. reflexivity. Qed.

(** Back: StD writes ones over the zeros it just laid. *)
Lemma dstep : forall M R,
  csteps tm_wr 1 (StD, (S0 :: M, S0, R)) = Some (StD, (M, S0, S1 :: R)).
Proof. reflexivity. Qed.

Lemma dsw : forall k M R,
  csteps tm_wr k (StD, (repeat S0 k ++ M, S0, R))
  = Some (StD, (M, S0, repeat S1 k ++ R)).
Proof.
  induction k as [|k IH]; intros M R.
  - reflexivity.
  - replace (S k) with (1 + k) by lia.
    change (repeat S0 (1 + k) ++ M) with (S0 :: (repeat S0 k ++ M)).
    rewrite csteps_add, dstep, IH.
    change (repeat S1 (1 + k) ++ R) with (S1 :: (repeat S1 k ++ R)).
    rewrite (rep_snoc S1 k R). reflexivity.
Qed.

(** The head eats two cells of wall and the next bounce begins. *)
Lemma fin2 : forall a R,
  csteps tm_wr 2 (StD, (repeat S1 (S (S a)), S0, R))
  = Some (StB, (repeat S1 a, S1, S1 :: S1 :: R)).
Proof. reflexivity. Qed.

(** ...unless the wall is one cell, in which case the head runs off
    its end and the tape is solid again. *)
Lemma fin2e : forall R,
  csteps tm_wr 2 (StD, ([S1], S0, R))
  = Some (StB, ([], S0, S1 :: S1 :: R)).
Proof. reflexivity. Qed.

Lemma Hbounce_wr : forall a r,
  csteps tm_wr (2 * r + 8) (mkM (S (S a)) r) = Some (mkM a (r + 4)).
Proof.
  intros a r. unfold mkM.
  replace (2 * r + 8) with (r + (5 + (S r + 2))) by lia.
  rewrite csteps_add, bsw, csteps_add, turn5, csteps_add.
  change (S0 :: repeat S0 r ++ repeat S1 (S (S a)))
    with (repeat S0 (S r) ++ repeat S1 (S (S a))).
  rewrite dsw, fin2, rep_app1.
  replace (r + 4) with (S (S (S (S r)))) by lia.
  reflexivity.
Qed.

Lemma Hterm_wr : forall r,
  csteps tm_wr (2 * r + 8) (mkM 1 r) = Some (mkA (r + 4)).
Proof.
  intro r. unfold mkM, mkA.
  replace (2 * r + 8) with (r + (5 + (S r + 2))) by lia.
  change (repeat S1 1) with [S1].
  rewrite csteps_add, bsw, csteps_add, turn5, csteps_add.
  change (S0 :: repeat S0 r ++ [S1]) with (repeat S0 (S r) ++ [S1]).
  rewrite dsw, fin2e, rep_app1.
  replace (r + 4) with (S (S (S (S r)))) by lia.
  reflexivity.
Qed.

(** ** Boot, visits, and the theorem *)

Lemma boot_wr : exists t0, stepn tm_wr t0 InitES = Some (lift (Cw mkA 1)).
Proof.
  exists 7.
  assert (H : match csteps tm_wr 7 c0 with
              | Some c => ceqb c (Cw mkA 1)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm_wr 7 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
  f_equal. apply ceqb_lift. exact H.
Qed.

Lemma vis_wr : forall m q, In q [StB; StC; StD] ->
  exists k c, csteps tm_wr k (mkA (2 * m + 3)) = Some c /\ fst c = q.
Proof.
  intros m q Hq. unfold mkA.
  replace (2 * m + 3) with (S (S (S (2 * m)))) by lia.
  destruct Hq as [<-|[<-|[<-|[]]]].
  - exists 0. eexists. split; reflexivity.
  - exists 1. eexists. split; reflexivity.
  - exists 2. eexists. split; reflexivity.
Qed.

(** 1RB---_1RC0RB_0LC0RD_1LD1LB: never halts, quasihalts, and every
    quiet state made its last visit by index 1. *)
Definition iqh (tm : TM) : Prop :=
  NonHalt tm /\ QHBound 2000 tm /\ QuasiHaltsSt tm.

Theorem iqh_1RB_1RC0RB_0LC0RD_1LD1LB : iqh tm_wr.
Proof.
  apply (wrap_qh tm_wr mkA mkM Hcol_wr Hbounce_wr Hterm_wr
           [StB; StC; StD] boot_wr vis_wr
           ltac:(vm_compute; reflexivity)
           ltac:(eexists; split; [vm_compute; reflexivity | cbn; tauto])
           ltac:(cbn; intuition discriminate)).
Qed.
