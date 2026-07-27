(** * WrapBouncer: the doubling bouncer on a 3-state core.

    John, on 1RB---_1RC0RB_0LC0RD_1LD1LB: "it keeps bouncing until it
    finds zero on the right then moves the wall over one and heads
    back out until it finds 0 again then goes back to bouncing.  it's
    only 3 states with very simple tape behavior zeros on the way out,
    1s on the way back.  1s on the way out after it moves the wall."

    That is exactly the shape, and it makes the machine cheap.  The
    two [1RB---] holdouts have an undefined [StA] transition, so
    [StA] fires once (at index 0) and the remaining three states are
    CLOSED under the table: they genuinely quasihalt, and the tier
    they need is [QHBound], not never-quasihalting.
    [LapGlueAbs.glue_qh_abs] wants a lap anyway, and this file builds
    it.

    TWO LEVELS, both elementary.

      macro   mkA K  = one solid block of K ones, head just off its
                       far end, StB.  K doubles:  K -> 2*K+1.
      micro   mkM a r = the same block split by the bouncing head into
                       a WALL of a ones behind it and a RUN of r ones
                       ahead.  One bounce is
                         mkM (a+2) r  -->  mkM a (r+4)
                       (out writing zeros, back writing ones; the wall
                       gives up two cells and the run gains four).

    The macro lap is therefore [(K-3)/2] bounces after one collapse
    sweep, and -- unlike the nested counters that needed
    [MeasureGlue] -- the bounce COUNT is explicit in the anchor, so a
    plain induction on it suffices.  No measure, no well-founded
    recursion.

    The section is stated over abstract [mkA]/[mkM] so the same
    derivation serves a left-growing machine and its right-growing
    mirror image; only the three gadget hypotheses change orientation.

    Customers: theories/Machines/Counters/WrapB_1RB.v and WrapA_1RB.v.
    This file is axiom-free. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Census Require Import TNF_QH.
From BBB4.Counters Require Import LapGlueAbs.
Import ListNotations.

(** The macro block length after [t] doublings. *)
Definition bl (t : nat) : nat := 2 * 2 ^ t - 1.

Lemma pow2_pos : forall t, 1 <= 2 ^ t.
Proof. induction t; simpl; lia. Qed.

Lemma pow2_ge2 : forall t, 1 <= t -> 2 <= 2 ^ t.
Proof.
  intros [|t] H; [lia|]. simpl. pose proof (pow2_pos t). lia.
Qed.

Lemma bl_succ : forall t, bl (S t) = 2 * bl t + 1.
Proof.
  intro t. unfold bl. simpl (2 ^ S t). pose proof (pow2_pos t). lia.
Qed.

(** Every block the family visits is odd and at least 3. *)
Lemma bl_form : forall t, 1 <= t -> bl t = 2 * (2 ^ t - 2) + 3.
Proof.
  intros t H. pose proof (pow2_ge2 t H). unfold bl. lia.
Qed.

Section Wrap.

Variable tm : TM.

(** [mkA K]: the solid block of [K] ones, head just off its far end.
    [mkM a r]: wall of [a] ones behind the head, run of [r] ahead. *)
Variable mkA : nat -> cconf.
Variable mkM : nat -> nat -> cconf.

(** The collapse sweep: the anchor's block is split into a wall of
    [K-2] and a run of 3, in [3*K+2] steps. *)
Hypothesis Hcol : forall m,
  csteps tm (3 * (2 * m + 3) + 2) (mkA (2 * m + 3)) = Some (mkM (2 * m + 1) 3).

(** One bounce: out writing zeros, back writing ones. *)
Hypothesis Hbounce : forall a r,
  csteps tm (2 * r + 8) (mkM (S (S a)) r) = Some (mkM a (r + 4)).

(** The last bounce, where the wall is one cell and the head runs off
    its end: the tape is a solid block again, four cells longer. *)
Hypothesis Hterm : forall r,
  csteps tm (2 * r + 8) (mkM 1 r) = Some (mkA (r + 4)).

(** [d] bounces left to run. *)
Lemma wchain : forall d r, exists n, 0 < n /\
  csteps tm n (mkM (2 * d + 1) r) = Some (mkA (r + 4 * d + 4)).
Proof.
  induction d as [|d IH]; intros r.
  - exists (2 * r + 8). split; [lia|].
    replace (2 * 0 + 1) with 1 by lia.
    replace (r + 4 * 0 + 4) with (r + 4) by lia.
    apply Hterm.
  - destruct (IH (r + 4)) as (n & Hn & Hrun).
    exists ((2 * r + 8) + n). split; [lia|].
    rewrite csteps_add.
    replace (2 * S d + 1) with (S (S (2 * d + 1))) by lia.
    rewrite Hbounce, Hrun.
    replace (r + 4 + 4 * d + 4) with (r + 4 * S d + 4) by lia.
    reflexivity.
Qed.

(** The macro lap: the block doubles. *)
Lemma wlap : forall m, exists n, 0 < n /\
  csteps tm n (mkA (2 * m + 3)) = Some (mkA (2 * (2 * m + 3) + 1)).
Proof.
  intro m. destruct (wchain m 3) as (n & Hn & Hrun).
  exists (3 * (2 * m + 3) + 2 + n). split; [lia|].
  rewrite csteps_add, Hcol, Hrun.
  replace (3 + 4 * m + 4) with (2 * (2 * m + 3) + 1) by lia.
  reflexivity.
Qed.

Definition Cw (p : positive) : cconf := mkA (bl (Pos.to_nat p)).

Lemma wlap_pos : forall p, exists n c',
  csteps tm n (Cw p) = Some c' /\ lift c' = lift (Cw (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. unfold Cw.
  assert (H1 : 1 <= Pos.to_nat p) by (pose proof (Pos2Nat.is_pos p); lia).
  rewrite (bl_form _ H1).
  destruct (wlap (2 ^ Pos.to_nat p - 2)) as (n & Hn & Hrun).
  exists n, (mkA (2 * (2 * (2 ^ Pos.to_nat p - 2) + 3) + 1)).
  split; [exact Hrun | split; [|exact Hn]].
  rewrite Pos2Nat.inj_succ, bl_succ, (bl_form _ H1).
  reflexivity.
Qed.

(** ** The closer

    [StA] fires only at index 0; the other three states are closed
    under the table and each recurs once per anchor, so the only quiet
    state is [StA] and its last visit is at index 0. *)

Variable Sset : list St.

Hypothesis Hboot : exists t0, stepn tm t0 InitES = Some (lift (Cw 1)).
Hypothesis Hvis : forall m q, In q Sset ->
  exists k c, csteps tm k (mkA (2 * m + 3)) = Some c /\ fst c = q.
Hypothesis Hclosed : closed_b tm Sset = true.
Hypothesis Hin1 : exists cd, csteps tm 1 c0 = Some cd /\ In (fst cd) Sset.
Hypothesis HAout : ~ In StA Sset.

Theorem wrap_qh : NonHalt tm /\ QHBound 2000 tm /\ QuasiHaltsSt tm.
Proof.
  destruct (glue_qh_abs tm Cw 1 Sset 1
              Hboot
              (fun p _ => wlap_pos p)
              (fun p q _ Hq =>
                 let H1 : 1 <= Pos.to_nat p :=
                   ltac:(pose proof (Pos2Nat.is_pos p); lia) in
                 eq_ind_r (fun K => exists k c, csteps tm k (mkA K) = Some c
                                                /\ fst c = q)
                          (Hvis (2 ^ Pos.to_nat p - 2) q Hq)
                          (bl_form _ H1))
              (closed_b_sound tm Sset Hclosed)
              Hin1 HAout)
    as (Hn & Hb & Hq).
  split; [exact Hn | split; [| exact Hq]].
  apply (qhbound_mono 1 2000); [lia | exact Hb].
Qed.

End Wrap.
