(** * BounceGlue: the ERASE/FILL bouncer, indexed by the WALL POSITION.

    The `no anchor` bucket's route.  Every other counter family in this
    tree rests in a decodable digit word and is anchored by
    [Cc p = (q, E p ++ tail, S0, far)]; eight waves of anchor enumeration
    return nothing on these machines, and John's read of
    [0RB0LD_1LA1LC_0LD0LC_1RD1RB] says why:

      "keeps bouncing back and forth with c and d states.  then when it
       passes the wall on the right it moves the wall over one and heads
       back left and then goes back to bouncing"

    THE COUNTER IS NOT A WORD, IT IS THE WALL POSITION.  So the family
    here is indexed by [j], the number of cells between the head and the
    wall, and not by any counter value:

      mkB j = (E, (repeat S0 j ++ [S1], S0, []))

    -- the head sitting on the blank frontier in the ERASER state, [j]
    erased cells behind it, and one surviving [S1] (the wall) at the far
    end.  [LapGlueAbs]'s closer takes an arbitrary family, so nothing in
    the closing theory has to change to accept it.

    THE MACHINE, abstractly.  Three states and a two-phase cycle,
    measured off the tape by [tools/counters/bouncecert.py] before any of
    this was written:

      E (the eraser) sweeps RIGHT over ones writing zeros; on the blank
        frontier it writes a one and turns.
      X, Y (the fillers) sweep LEFT over zeros writing ones, ALTERNATING
        with each other; on a one they write a one and turn back to E.

    So one bounce restores the block and moves the frontier one cell out:

      mkB (S i)  -->  mkB (S (S i))   in exactly  2*i+5  steps.

    The wall moves by exactly one cell per cycle and the cost is affine in
    the wall index -- a PLAIN bouncer.  The bounce count is therefore
    explicit in the anchor and, exactly as in [WrapBouncer], no measure
    and no well-founded recursion are needed: the macro lap IS the micro
    lap, and one [csteps] chain proves it.

    THE TIER.  The customers are the three [1RB---] rows of the bucket,
    whose [StA] transition on [S1] is undefined.  [StA] fires once, at
    configuration index 0, and [E], [X], [Y] are closed under the table:
    they genuinely QUASIHALT, so the tier is [QHBound] via
    [LapGlueAbs.glue_qh_abs] and never the never-quasihalting one.

    The section is stated over an abstract [(E, X, Y)] so the same
    derivation serves every assignment of the three roles to the three
    states; the six hypotheses ARE the transition table, and a board
    discharges each by [reflexivity].

    Customers: theories/Machines/Counters/BNC_*.v.
    This file is axiom-free. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Census Require Import TNF_QH.
From BBB4.Counters Require Import LapGlueAbs.
Import ListNotations.

(** ** List helpers (as in WrapBc_*: [repeat] snoc, both directions) *)

Lemma rep_snoc : forall (x : Sym) n l,
  repeat x n ++ x :: l = x :: repeat x n ++ l.
Proof.
  induction n; intros l; simpl; [reflexivity | rewrite IHn; reflexivity].
Qed.

Lemma rep_app1 : forall (x : Sym) n, repeat x n ++ [x] = repeat x (S n).
Proof.
  induction n; simpl; [reflexivity | rewrite IHn; reflexivity].
Qed.

Section EraseFill.

Variable tm : TM.

(** The eraser and the two alternating fillers. *)
Variable E X Y : St.

(** The six transitions.  A board discharges every one by [reflexivity];
    together they say exactly "E erases rightward, X and Y fill leftward
    in alternation, and a one turns the sweep around". *)
Hypothesis HE0 : tm E S0 = Some (mkTrans S1 DL X).
Hypothesis HE1 : tm E S1 = Some (mkTrans S0 DR E).
Hypothesis HX0 : tm X S0 = Some (mkTrans S1 DL Y).
Hypothesis HX1 : tm X S1 = Some (mkTrans S1 DR E).
Hypothesis HY0 : tm Y S0 = Some (mkTrans S1 DL X).
Hypothesis HY1 : tm Y S1 = Some (mkTrans S1 DR E).

(** ** One step, in each direction *)

(** Forward composition.  Stated locally rather than imported from
    [WTape] so this file's dependency cone stays [CTape] + the closer. *)
Lemma bchain : forall n1 n2 c c1 c2,
  csteps tm n1 c = Some c1 -> csteps tm n2 c1 = Some c2 ->
  csteps tm (n1 + n2) c = Some c2.
Proof. intros. rewrite csteps_add, H. assumption. Qed.

Lemma moveL : forall q q' w l h r,
  tm q h = Some (mkTrans w DL q') ->
  csteps tm 1 (q, (l, h, r)) = Some (q', (ctl l, chd l, w :: r)).
Proof. intros q q' w l h r H. cbn. rewrite H. reflexivity. Qed.

Lemma moveR : forall q q' w l h r,
  tm q h = Some (mkTrans w DR q') ->
  csteps tm 1 (q, (l, h, r)) = Some (q', (w :: l, chd r, ctl r)).
Proof. intros q q' w l h r H. cbn. rewrite H. reflexivity. Qed.

(** ** The fill sweep: X and Y alternate leftward over the zeros *)

(** A filler is X or Y; which one is a parity fact the sweep carries and
    nothing downstream reads, because both turn to [E] on a one. *)
Definition fill (q : St) : Prop := q = X \/ q = Y.

Lemma fill_pop : forall q l r, fill q ->
  exists q', fill q' /\
    csteps tm 1 (q, (l, S0, r)) = Some (q', (ctl l, chd l, S1 :: r)).
Proof.
  intros q l r [-> | ->].
  - exists Y. split; [right; reflexivity |].
    exact (moveL _ _ _ _ _ _ HX0).
  - exists X. split; [left; reflexivity |].
    exact (moveL _ _ _ _ _ _ HY0).
Qed.

Lemma fill_step : forall q l r, fill q ->
  exists q', fill q' /\
    csteps tm 1 (q, (S0 :: l, S0, r)) = Some (q', (l, S0, S1 :: r)).
Proof. intros q l r Hq. exact (fill_pop q (S0 :: l) r Hq). Qed.

Lemma fill_sweep : forall n q l r, fill q ->
  exists q', fill q' /\
    csteps tm n (q, (repeat S0 n ++ l, S0, r))
      = Some (q', (l, S0, repeat S1 n ++ r)).
Proof.
  induction n as [|n IH]; intros q l r Hq.
  - exists q. split; [exact Hq | reflexivity].
  - destruct (fill_step q (repeat S0 n ++ l) r Hq) as (q1 & Hq1 & Hs).
    destruct (IH q1 l (S1 :: r) Hq1) as (q2 & Hq2 & Hrun).
    exists q2. split; [exact Hq2 |].
    cbn [repeat app].
    apply (bchain 1 n _ (q1, (repeat S0 n ++ l, S0, S1 :: r))).
    + exact Hs.
    + rewrite Hrun, rep_snoc. reflexivity.
Qed.

(** The turn: a filler on a one writes a one, steps right and hands over
    to the eraser. *)
Lemma fill_turn : forall q l r, fill q ->
  csteps tm 1 (q, (l, S1, r)) = Some (E, (S1 :: l, chd r, ctl r)).
Proof.
  intros q l r [-> | ->].
  - exact (moveR _ _ _ _ _ _ HX1).
  - exact (moveR _ _ _ _ _ _ HY1).
Qed.

(** ** The erase sweep: E rightward over the ones, writing zeros *)

Lemma erase_sweep : forall n l r,
  csteps tm n (E, (l, S1, repeat S1 n ++ r))
    = Some (E, (repeat S0 n ++ l, S1, r)).
Proof.
  induction n as [|n IH]; intros l r; [reflexivity|].
  cbn [repeat app].
  apply (bchain 1 n _ (E, (S0 :: l, S1, repeat S1 n ++ r))).
  - exact (moveR _ _ _ _ _ _ HE1).
  - rewrite IH, rep_snoc. reflexivity.
Qed.

(** Off the end of the block: the head lands on the new blank frontier. *)
Lemma erase_off : forall l,
  csteps tm 1 (E, (l, S1, [])) = Some (E, (S0 :: l, S0, [])).
Proof. intro l. exact (moveR _ _ _ _ _ _ HE1). Qed.

(** The frontier turn: the eraser on a blank writes a one and hands over
    to the first filler. *)
Lemma front_turn : forall l r,
  csteps tm 1 (E, (S0 :: l, S0, r)) = Some (X, (l, S0, S1 :: r)).
Proof. intros l r. exact (moveL _ _ _ _ _ _ HE0). Qed.

(** ** The family and its lap *)

Definition mkB (j : nat) : cconf := (E, (repeat S0 j ++ [S1], S0, [])).

(** One bounce: the wall moves out by exactly one cell, and the cost is
    affine in the wall index.  This is the whole machine. *)
Lemma blap : forall i,
  csteps tm (2 * i + 5) (mkB (S i)) = Some (mkB (S (S i))).
Proof.
  intro i.
  destruct (fill_sweep i X [S1] [S1] (or_introl eq_refl)) as (q1 & Hq1 & Hs1).
  destruct (fill_pop q1 [S1] (repeat S1 i ++ [S1]) Hq1) as (q2 & Hq2 & Hs2).
  unfold mkB.
  replace (2 * i + 5) with (1 + (i + (1 + (1 + (S i + 1))))) by lia.
  cbn [repeat app].
  (* the frontier turn *)
  apply (bchain 1 _ _ (X, (repeat S0 i ++ [S1], S0, [S1]))).
  { exact (front_turn _ _). }
  (* the fill sweep, back over the zeros the previous erase left *)
  apply (bchain i _ _ (q1, ([S1], S0, repeat S1 i ++ [S1]))).
  { exact Hs1. }
  (* one more fill step lands the head ON the wall *)
  apply (bchain 1 _ _ (q2, ([], S1, S1 :: repeat S1 i ++ [S1]))).
  { exact Hs2. }
  (* the wall turns the sweep around *)
  apply (bchain 1 _ _ (E, ([S1], S1, repeat S1 i ++ [S1]))).
  { exact (fill_turn q2 [] (S1 :: repeat S1 i ++ [S1]) Hq2). }
  (* the erase sweep back out... *)
  apply (bchain (S i) _ _ (E, (repeat S0 (S i) ++ [S1], S1, []))).
  { replace (repeat S1 i ++ [S1]) with (repeat S1 (S i) ++ [])
      by (rewrite app_nil_r, rep_app1; reflexivity).
    apply erase_sweep. }
  (* ...and one step off the NEW frontier, one cell further out *)
  rewrite erase_off. cbn [repeat app]. reflexivity.
Qed.

(** ** The anchor family, in the wall index *)

Definition Cb (p : positive) : cconf := mkB (Pos.to_nat p).

Lemma blap_pos : forall p, exists n c',
  csteps tm n (Cb p) = Some c' /\ lift c' = lift (Cb (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. unfold Cb.
  destruct (Pos.to_nat p) as [|i] eqn:Ep.
  { pose proof (Pos2Nat.is_pos p). lia. }
  exists (2 * i + 5), (mkB (S (S i))).
  split; [apply blap | split; [| lia]].
  rewrite Pos2Nat.inj_succ, Ep. reflexivity.
Qed.

(** ** Visits: all three live states fire in the first two steps *)

Lemma bvis : forall j q, In q [E; X; Y] ->
  exists k c, csteps tm k (mkB (S j)) = Some c /\ fst c = q.
Proof.
  intros j q Hq. unfold mkB. cbn [repeat app].
  destruct Hq as [<- | [<- | [<- | []]]].
  - exists 0. eexists. split; reflexivity.
  - exists 1. eexists. split; [apply front_turn | reflexivity].
  - exists 2. eexists. split.
    + apply (bchain 1 1 _ (X, (repeat S0 j ++ [S1], S0, [S1]))).
      * exact (front_turn _ _).
      * exact (moveL _ _ _ _ _ _ HX0).
    + reflexivity.
Qed.

(** ** The closer

    [StA] fires only at index 0; [E], [X] and [Y] are closed under the
    table and each recurs once per anchor, so the only quiet state is
    [StA] and its last visit is at index 0. *)

Hypothesis Hboot : exists t0, stepn tm t0 InitES = Some (lift (Cb 1)).
Hypothesis Hclosed : closed_b tm [E; X; Y] = true.
Hypothesis Hin1 : exists cd, csteps tm 1 c0 = Some cd /\ In (fst cd) [E; X; Y].
Hypothesis HAout : ~ In StA [E; X; Y].

Theorem bounce_qh : NonHalt tm /\ QHBound 2000 tm /\ QuasiHaltsSt tm.
Proof.
  destruct (glue_qh_abs tm Cb 1 [E; X; Y] 1
              Hboot
              (fun p _ => blap_pos p)
              (fun p q _ Hq =>
                 let H1 : Pos.to_nat p = S (Nat.pred (Pos.to_nat p)) :=
                   ltac:(pose proof (Pos2Nat.is_pos p); lia) in
                 eq_ind_r (fun j => exists k c, csteps tm k (mkB j) = Some c
                                                /\ fst c = q)
                          (bvis (Nat.pred (Pos.to_nat p)) q Hq)
                          H1)
              (closed_b_sound tm [E; X; Y] Hclosed)
              Hin1 HAout)
    as (Hn & Hb & Hq).
  split; [exact Hn | split; [| exact Hq]].
  apply (qhbound_mono 1 2000); [lia | exact Hb].
Qed.

End EraseFill.
