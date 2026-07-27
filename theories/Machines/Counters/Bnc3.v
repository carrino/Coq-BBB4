(** * Bnc3: 1RB1RA_0RC0RB_1LC1LD_0RA0LA never quasihalts.

    The one holdout of the eleven that is not a BBB counter at all:
    BBB decides it with the generic inductive-rules engine at v4, whose
    blocker for us is a whole mechanism layer (vector-valued meta
    growth, [nvar]/[mmrow]/[tplrunmv] -- PHASE2_DESIGN section 3.4).

    John read it off the picture instead: "it appears to bounce the
    same way, but the zero 'wall' moves one right each macro cycle.
    Then it extends back out using state A and starts bouncing again",
    and "it is just a bouncer, should be easier than bouncer counter
    even".  Both are right -- there is no counter here, only a wall and
    a block:

      anc w m  = StA, tape 1^m 0 1^w, head on the blank past the right
                 end.  The wall is the [0] with [w] ones behind it.
      mkB w j k = StB, tape 0^(3k) 1^j 0 1^w, same head.  [j + k] is
                 conserved, so the bounce count is EXPLICIT.

    One bounce is [mkB w (j+1) k --> mkB w j (k+1)] in [6k+10] steps:
    StC walks left over the zeros turning them into ones on the far
    side, five steps turn around, StB walks back right turning ones
    into zeros.  After [m-1] of them the block is down to two, the wall
    moves one right, and state A extends the block back out:

      anc w m -->+ anc (w+1) (3m)   in   3m^2 + 7m + 3 steps

    with [m = 3^(w+1)].  BBB's own decode agrees: its meta matrix is
    [x -> M x + c] with rows [3 0], [0 1] and [c = (-2, 1)], i.e.
    [m+1 -> 3(m+1) - 2] and [w -> w+1].

    Because the bounce count [m-1] is explicit in the anchor, the chain
    is a plain induction -- no measure, no [MeasureGlue], exactly as in
    [WrapBouncer].

    Anchors measured at t = 9, 60, 369, 2748, 23001, 201852, 1801281,
    16165500, 145351593, 1307750844; every lemma below was validated
    cell-for-cell against the raw simulator before any Coq was written.

    [Print Assumptions] = [functional_extensionality_dep] only. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import LapGlue.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB1RA_0RC0RB_1LC1LD_0RA0LA *)
Definition tm_v4 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DR StA
  | StB, S0 => mk S0 DR StC | StB, S1 => mk S0 DR StB
  | StC, S0 => mk S1 DL StC | StC, S1 => mk S1 DL StD
  | StD, S0 => mk S0 DR StA | StD, S1 => mk S0 DL StA
  end.

Definition anc (w m : nat) : cconf :=
  (StA, (repeat S1 m ++ S0 :: repeat S1 w, S0, [])).

Definition mkB (w j k : nat) : cconf :=
  (StB, (repeat S0 (3 * k) ++ repeat S1 j ++ S0 :: repeat S1 w, S0, [])).

(** ** List helper *)

Lemma rep_snoc : forall (x : Sym) n l,
  repeat x n ++ x :: l = x :: repeat x n ++ l.
Proof.
  induction n; intros l; simpl; [reflexivity | rewrite IHn; reflexivity].
Qed.

(** ** The sweeps

    Three walks, each one induction, each uniform in what lies beyond. *)

(** StC walks left over a run of zeros, laying ones on the far side.
    The head stays [S0] throughout: each step pops one zero and that
    zero becomes the new head. *)
Lemma cstep1 : forall M R,
  csteps tm_v4 1 (StC, (S0 :: M, S0, R)) = Some (StC, (M, S0, S1 :: R)).
Proof. reflexivity. Qed.

Lemma cwalk : forall n M R,
  csteps tm_v4 n (StC, (repeat S0 n ++ M, S0, R))
  = Some (StC, (M, S0, repeat S1 n ++ R)).
Proof.
  induction n as [|n IH]; intros M R.
  - reflexivity.
  - replace (S n) with (1 + n) by lia.
    change (repeat S0 (1 + n) ++ M) with (S0 :: (repeat S0 n ++ M)).
    rewrite csteps_add, cstep1, IH.
    change (repeat S1 (1 + n) ++ R) with (S1 :: (repeat S1 n ++ R)).
    rewrite (rep_snoc S1 n R). reflexivity.
Qed.

(** StB walks right over a run of ones, turning them into zeros. *)
Lemma bstepr : forall L R,
  csteps tm_v4 1 (StB, (L, S1, R)) = Some (StB, (S0 :: L, chd R, ctl R)).
Proof. reflexivity. Qed.

Lemma bwalkS : forall n L R,
  csteps tm_v4 (S n) (StB, (L, S1, repeat S1 n ++ R))
  = Some (StB, (repeat S0 (S n) ++ L, chd R, ctl R)).
Proof.
  induction n as [|n IH]; intros L R.
  - reflexivity.
  - replace (S (S n)) with (1 + S n) by lia.
    change (repeat S1 (S n) ++ R) with (S1 :: (repeat S1 n ++ R)).
    rewrite csteps_add, bstepr.
    change (chd (S1 :: (repeat S1 n ++ R))) with S1.
    change (ctl (S1 :: (repeat S1 n ++ R))) with (repeat S1 n ++ R).
    rewrite IH.
    change (repeat S0 (S (S n)) ++ L) with (S0 :: (repeat S0 (S n) ++ L)).
    rewrite (rep_snoc S0 (S n) L). reflexivity.
Qed.

(** StA walks right over a run of ones, leaving them alone -- the
    "extends back out using state A" phase. *)
Lemma astepr : forall L R,
  csteps tm_v4 1 (StA, (L, S1, R)) = Some (StA, (S1 :: L, chd R, ctl R)).
Proof. reflexivity. Qed.

Lemma awalkS : forall n L R,
  csteps tm_v4 (S n) (StA, (L, S1, repeat S1 n ++ R))
  = Some (StA, (repeat S1 (S n) ++ L, chd R, ctl R)).
Proof.
  induction n as [|n IH]; intros L R.
  - reflexivity.
  - replace (S (S n)) with (1 + S n) by lia.
    change (repeat S1 (S n) ++ R) with (S1 :: (repeat S1 n ++ R)).
    rewrite csteps_add, astepr.
    change (chd (S1 :: (repeat S1 n ++ R))) with S1.
    change (ctl (S1 :: (repeat S1 n ++ R))) with (repeat S1 n ++ R).
    rewrite IH.
    change (repeat S1 (S (S n)) ++ L) with (S1 :: (repeat S1 (S n) ++ L)).
    rewrite (rep_snoc S1 (S n) L). reflexivity.
Qed.

(** ** The fixed gadgets *)

Lemma bstep1 : forall L,
  csteps tm_v4 1 (StB, (L, S0, [])) = Some (StC, (S0 :: L, S0, [])).
Proof. reflexivity. Qed.

Lemma astep1 : forall L R,
  csteps tm_v4 1 (StA, (L, S0, R)) = Some (StB, (S1 :: L, chd R, ctl R)).
Proof. reflexivity. Qed.

(** The turn at the block: five steps eat one cell of block and hand
    the head back to StB, two cells further right. *)
Lemma mid5 : forall L R,
  csteps tm_v4 5 (StC, (S1 :: S1 :: S1 :: L, S0, R))
  = Some (StB, (S1 :: S1 :: L, S1, S1 :: R)).
Proof. reflexivity. Qed.

(** The turn at the WALL: seven steps move the wall one right and hand
    the head to StA to extend the block back out. *)
Lemma term7 : forall w R,
  csteps tm_v4 7 (StC, (S1 :: S1 :: S0 :: repeat S1 w, S0, R))
  = Some (StA, (S0 :: repeat S1 (S w), S1, S1 :: R)).
Proof. reflexivity. Qed.

(** ** One bounce *)

Lemma round : forall w j k,
  csteps tm_v4 (6 * k + 10) (mkB w (S (S (S j))) k)
  = Some (mkB w (S (S j)) (S k)).
Proof.
  intros w j k. unfold mkB.
  replace (6 * k + 10) with (1 + ((3 * k + 1) + (5 + (3 * k + 3)))) by lia.
  rewrite csteps_add, bstep1.
  replace (S0 :: repeat S0 (3 * k)
             ++ repeat S1 (S (S (S j))) ++ S0 :: repeat S1 w)
     with (repeat S0 (3 * k + 1)
             ++ repeat S1 (S (S (S j))) ++ S0 :: repeat S1 w)
     by (replace (3 * k + 1) with (S (3 * k)) by lia; reflexivity).
  rewrite csteps_add, cwalk, app_nil_r.
  change (repeat S1 (S (S (S j))) ++ S0 :: repeat S1 w)
    with (S1 :: S1 :: S1 :: (repeat S1 j ++ S0 :: repeat S1 w)).
  rewrite csteps_add, mid5.
  replace (S1 :: repeat S1 (3 * k + 1)) with (repeat S1 (3 * k + 2) ++ (@nil Sym))
    by (rewrite app_nil_r; replace (3 * k + 2) with (S (3 * k + 1)) by lia;
        reflexivity).
  replace (3 * k + 3) with (S (3 * k + 2)) by lia.
  rewrite bwalkS.
  replace (3 * S k) with (S (3 * k + 2)) by lia.
  reflexivity.
Qed.

(** ** The turn at the wall *)

Lemma term : forall w k,
  csteps tm_v4 (6 * k + 12) (mkB w 2 k) = Some (anc (S w) (3 * k + 3)).
Proof.
  intros w k. unfold mkB, anc.
  replace (6 * k + 12) with (1 + ((3 * k + 1) + (7 + (3 * k + 3)))) by lia.
  rewrite csteps_add, bstep1.
  replace (S0 :: repeat S0 (3 * k) ++ repeat S1 2 ++ S0 :: repeat S1 w)
     with (repeat S0 (3 * k + 1) ++ repeat S1 2 ++ S0 :: repeat S1 w)
     by (replace (3 * k + 1) with (S (3 * k)) by lia; reflexivity).
  rewrite csteps_add, cwalk, app_nil_r.
  change (repeat S1 2 ++ S0 :: repeat S1 w)
    with (S1 :: S1 :: S0 :: repeat S1 w).
  replace (3 * k + 3) with (S (3 * k + 2)) by lia.
  rewrite csteps_add, term7.
  replace (S1 :: repeat S1 (3 * k + 1)) with (repeat S1 (3 * k + 2) ++ (@nil Sym))
    by (rewrite app_nil_r; replace (3 * k + 2) with (S (3 * k + 1)) by lia;
        reflexivity).
  rewrite awalkS. reflexivity.
Qed.

(** ** The chain: [n] bounces then the wall turn *)

Lemma chain : forall n w k, exists t, 0 < t /\
  csteps tm_v4 t (mkB w (n + 2) k) = Some (anc (S w) (3 * (k + n) + 3)).
Proof.
  induction n as [|n IH]; intros w k.
  - exists (6 * k + 12). split; [lia|].
    replace (0 + 2) with 2 by lia.
    replace (3 * (k + 0) + 3) with (3 * k + 3) by lia.
    apply term.
  - destruct (IH w (S k)) as (t & Ht & Hr).
    exists ((6 * k + 10) + t). split; [lia|].
    rewrite csteps_add.
    replace (S n + 2) with (S (S (S n))) by lia.
    rewrite round.
    replace (S (S n)) with (n + 2) in * by lia.
    rewrite Hr. f_equal. f_equal. lia.
Qed.

(** ** The macro lap *)

Lemma lapv4 : forall w m, 1 <= m -> exists t, 0 < t /\
  csteps tm_v4 t (anc w m) = Some (anc (S w) (3 * m)).
Proof.
  intros w m Hm.
  destruct (chain (m - 1) w 0) as (t & Ht & Hr).
  exists (1 + t). split; [lia|].
  unfold anc at 1.
  rewrite csteps_add, astep1.
  replace (StB, (S1 :: repeat S1 m ++ S0 :: repeat S1 w,
                 chd (@nil Sym), ctl (@nil Sym)))
     with (mkB w (m - 1 + 2) 0)
     by (unfold mkB; replace (m - 1 + 2) with (S m) by lia; reflexivity).
  rewrite Hr. f_equal. f_equal. lia.
Qed.

(** ** Visits: all four states inside one lap *)

Lemma vis : forall w m' q,
  exists k c, csteps tm_v4 k (anc w (S m')) = Some c /\ fst c = q.
Proof.
  intros w m' q. unfold anc. destruct q.
  - exists 0. eexists. split; reflexivity.
  - exists 1. eexists. split; reflexivity.
  - exists 2. eexists. split; reflexivity.
  - exists 5. eexists. split; reflexivity.
Qed.

(** ** Boot and the theorem *)

Definition wid (p : positive) : nat := Pos.to_nat p - 1.
Definition blk (p : positive) : nat := 3 ^ Pos.to_nat p.

Lemma blk_pos : forall p, 1 <= blk p.
Proof.
  intro p. unfold blk.
  induction (Pos.to_nat p) as [|n IH]; simpl; lia.
Qed.

Definition Cf (p : positive) : cconf := anc (wid p) (blk p).

Lemma boot : exists t0, stepn tm_v4 t0 InitES = Some (lift (Cf 1)).
Proof.
  exists 9.
  assert (H : match csteps tm_v4 9 c0 with
              | Some c => ceqb c (Cf 1)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm_v4 9 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
  f_equal. apply ceqb_lift. exact H.
Qed.

(** bbchallenge 1RB1RA_0RC0RB_1LC1LD_0RA0LA never quasihalts. *)
Theorem nqh_1RB1RA_0RC0RB_1LC1LD_0RA0LA : NeverQuasiHaltsSt tm_v4.
Proof.
  apply (glue_neverqh tm_v4 Cf 1).
  - exact boot.
  - intros p _.
    destruct (lapv4 (wid p) (blk p) (blk_pos p)) as (t & Ht & Hr).
    exists t, (anc (S (wid p)) (3 * blk p)).
    split; [exact Hr | split; [|exact Ht]].
    unfold Cf, wid, blk.
    rewrite Pos2Nat.inj_succ.
    replace (S (Pos.to_nat p) - 1) with (S (Pos.to_nat p - 1))
      by (pose proof (Pos2Nat.is_pos p); lia).
    reflexivity.
  - intros p q _.
    unfold Cf.
    destruct (blk p) as [|m'] eqn:E.
    + pose proof (blk_pos p). lia.
    + apply vis.
Qed.

Theorem tm_v4_nonhalt : NonHalt tm_v4.
Proof. apply never_qh_nonhalt, nqh_1RB1RA_0RC0RB_1LC1LD_0RA0LA. Qed.
