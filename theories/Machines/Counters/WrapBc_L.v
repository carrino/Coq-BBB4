(** * WrapBc_L: 1RB---_1LC0LB_0RC0LD_1RD1RB quasihalts, with bound 1.

    The second [1RB---] holdout, and the LEFT/RIGHT mirror of
    [WrapBc_R]'s 3-state core: same doubling bouncer, same step counts
    (collapse [3K+2], bounce [2r+8]), sides swapped.  The two machines
    are not [Mirror] transports of each other -- mirroring would flip
    [StA]'s [1RB] out of TNF -- so this is a transcription, not a
    transport, and the boot differs (6 here, 7 there).

      mkA K   = StB, head just right of a solid block of K ones
      mkM a r = wall of a ones ahead of the head, run of r behind

    Out (StB) writes zeros, back (StD) writes ones.  See [WrapBouncer]
    for the derivation and [WrapBc_R] for the reading.

    [Print Assumptions] = [functional_extensionality_dep] only. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Census Require Import TNF_QH.
From BBB4.Counters Require Import LapGlueAbs WrapBouncer.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB---_1LC0LB_0RC0LD_1RD1RB *)
Definition tm_wl : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => None
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S0 DL StB
  | StC, S0 => mk S0 DR StC | StC, S1 => mk S0 DL StD
  | StD, S0 => mk S1 DR StD | StD, S1 => mk S1 DR StB
  end.

Definition mkA (K : nat) : cconf := (StB, (repeat S1 K, S0, [])).
Definition mkM (a r : nat) : cconf :=
  (StB, (repeat S1 r, S1, repeat S1 a)).

(** ** List helpers *)

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

Lemma col1 : forall R m,
  csteps tm_wl 3 (StB, (repeat S1 (S (S m)), S0, R))
  = Some (StB, (repeat S1 (S m), S0, S1 :: R)).
Proof. reflexivity. Qed.

Lemma coln : forall j R m,
  csteps tm_wl (3 * j) (StB, (repeat S1 (j + S m), S0, R))
  = Some (StB, (repeat S1 (S m), S0, repeat S1 j ++ R)).
Proof.
  induction j as [|j IH]; intros R m.
  - reflexivity.
  - replace (3 * S j) with (3 + 3 * j) by lia.
    replace (S j + S m) with (S (S (j + m))) by lia.
    rewrite csteps_add, col1.
    replace (S (j + m)) with (j + S m) by lia.
    rewrite IH.
    change (repeat S1 (S j) ++ R) with (S1 :: (repeat S1 j ++ R)).
    rewrite (rep_snoc S1 j R). reflexivity.
Qed.

Lemma col5 : forall M,
  csteps tm_wl 5 (StB, ([S1], S0, S1 :: M))
  = Some (StB, ([S1; S1; S1], S1, M)).
Proof. reflexivity. Qed.

Lemma Hcol_wl : forall m,
  csteps tm_wl (3 * (2 * m + 3) + 2) (mkA (2 * m + 3))
  = Some (mkM (2 * m + 1) 3).
Proof.
  intro m. unfold mkA, mkM.
  replace (3 * (2 * m + 3) + 2) with (3 * (2 * m + 2) + 5) by lia.
  replace (2 * m + 3) with (2 * m + 2 + S 0) by lia.
  rewrite csteps_add, coln, app_nil_r.
  replace (2 * m + 2) with (S (2 * m + 1)) by lia.
  change (repeat S1 (S (2 * m + 1))) with (S1 :: repeat S1 (2 * m + 1)).
  change (repeat S1 (S 0)) with [S1].
  apply col5.
Qed.

(** ** One bounce *)

Lemma bstep : forall L R,
  csteps tm_wl 1 (StB, (S1 :: L, S1, R)) = Some (StB, (L, S1, S0 :: R)).
Proof. reflexivity. Qed.

Lemma bsw : forall k R,
  csteps tm_wl k (StB, (repeat S1 k, S1, R))
  = Some (StB, ([], S1, repeat S0 k ++ R)).
Proof.
  induction k as [|k IH]; intros R.
  - reflexivity.
  - replace (S k) with (1 + k) by lia.
    change (repeat S1 (1 + k)) with (S1 :: repeat S1 k).
    rewrite csteps_add, bstep, IH.
    change (repeat S0 (1 + k) ++ R) with (S0 :: (repeat S0 k ++ R)).
    rewrite (rep_snoc S0 k R). reflexivity.
Qed.

Lemma turn5 : forall M,
  csteps tm_wl 5 (StB, ([], S1, M)) = Some (StD, ([S1], S0, S0 :: M)).
Proof. reflexivity. Qed.

Lemma dstep : forall M R,
  csteps tm_wl 1 (StD, (M, S0, S0 :: R)) = Some (StD, (S1 :: M, S0, R)).
Proof. reflexivity. Qed.

Lemma dsw : forall k M R,
  csteps tm_wl k (StD, (M, S0, repeat S0 k ++ R))
  = Some (StD, (repeat S1 k ++ M, S0, R)).
Proof.
  induction k as [|k IH]; intros M R.
  - reflexivity.
  - replace (S k) with (1 + k) by lia.
    change (repeat S0 (1 + k) ++ R) with (S0 :: (repeat S0 k ++ R)).
    rewrite csteps_add, dstep, IH.
    change (repeat S1 (1 + k) ++ M) with (S1 :: (repeat S1 k ++ M)).
    rewrite (rep_snoc S1 k M). reflexivity.
Qed.

Lemma fin2 : forall a R,
  csteps tm_wl 2 (StD, (R, S0, repeat S1 (S (S a))))
  = Some (StB, (S1 :: S1 :: R, S1, repeat S1 a)).
Proof. reflexivity. Qed.

Lemma fin2e : forall R,
  csteps tm_wl 2 (StD, (R, S0, [S1]))
  = Some (StB, (S1 :: S1 :: R, S0, [])).
Proof. reflexivity. Qed.

Lemma Hbounce_wl : forall a r,
  csteps tm_wl (2 * r + 8) (mkM (S (S a)) r) = Some (mkM a (r + 4)).
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

Lemma Hterm_wl : forall r,
  csteps tm_wl (2 * r + 8) (mkM 1 r) = Some (mkA (r + 4)).
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

Lemma boot_wl : exists t0, stepn tm_wl t0 InitES = Some (lift (Cw mkA 1)).
Proof.
  exists 6.
  assert (H : match csteps tm_wl 6 c0 with
              | Some c => ceqb c (Cw mkA 1)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm_wl 6 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
  f_equal. apply ceqb_lift. exact H.
Qed.

Lemma vis_wl : forall m q, In q [StB; StC; StD] ->
  exists k c, csteps tm_wl k (mkA (2 * m + 3)) = Some c /\ fst c = q.
Proof.
  intros m q Hq. unfold mkA.
  replace (2 * m + 3) with (S (S (S (2 * m)))) by lia.
  destruct Hq as [<-|[<-|[<-|[]]]].
  - exists 0. eexists. split; reflexivity.
  - exists 1. eexists. split; reflexivity.
  - exists 2. eexists. split; reflexivity.
Qed.

(** 1RB---_1LC0LB_0RC0LD_1RD1RB: never halts, quasihalts, and every
    quiet state made its last visit by index 1. *)
Definition iqh (tm : TM) : Prop :=
  NonHalt tm /\ QHBound 2000 tm /\ QuasiHaltsSt tm.

Theorem iqh_1RB_1LC0LB_0RC0LD_1RD1RB : iqh tm_wl.
Proof.
  apply (wrap_qh tm_wl mkA mkM Hcol_wl Hbounce_wl Hterm_wl
           [StB; StC; StD] boot_wl vis_wl
           ltac:(vm_compute; reflexivity)
           ltac:(eexists; split; [vm_compute; reflexivity | cbn; tauto])
           ltac:(cbn; intuition discriminate)).
Qed.
