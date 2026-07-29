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

(** * The WALL BOUNCE: a solid block, a wall that marches one cell per bounce

    The second shape the reader found in the bucket, and the one John read
    off [0RB0LD_1LA1LC_0LD0LC_1RD1RB] directly.  The tape is one SOLID
    BLOCK of ones with the head inside it; the wall is the head's own
    column, and it moves out by exactly one cell per bounce while the
    block grows by two on the far side:

      wA n   = (B, (repeat S1 n, S0, []))          the head just off the
                                                   block's near end
      wM a r = (B, (repeat S1 r, S1, repeat S1 a)) the head INSIDE it, [r]
                                                   cells of rebuilt run
                                                   behind, [a] of wall ahead

    One bounce is [wM (S a) r --> wM a (r+3)] in exactly [2*r+5] steps --
    the eraser sweeps back over the run turning it to zeros, the filler
    sweeps out again turning them to ones and overshooting by three, and
    the wall gives up one cell.  When the wall is spent the same chain
    lands on [wA (r+3)] instead, so [Hbounce] and [Hterm] are ONE
    derivation read at two values of [a] -- which is why they cost the
    same.

    The macro lap is therefore [a] bounces after a collapse sweep, the
    bounce count is explicit in the anchor, and (as in [WrapBouncer], and
    unlike the nested counters) plain induction suffices: no
    [MeasureGlue].  The COLLAPSE differs from machine to machine -- it is
    the only place the fourth state appears -- so it stays in the board,
    and this section supplies the part that does not: the bounce, the
    terminal, the chain, and the three visit witnesses. *)

Section WallBounce.

Variable tm : TM.

(** [Bq] turns at the wall, [Cq] erases the run leftward, [Dq] fills it
    back rightward.  Read off the table by [bouncecert.py]; the board
    discharges each hypothesis by [reflexivity]. *)
Variable Bq Cq Dq : St.

Hypothesis HB1 : tm Bq S1 = Some (mkTrans S1 DL Cq).
Hypothesis HC1 : tm Cq S1 = Some (mkTrans S0 DL Cq).
Hypothesis HC0 : tm Cq S0 = Some (mkTrans S0 DL Dq).
Hypothesis HD0 : tm Dq S0 = Some (mkTrans S1 DR Dq).
Hypothesis HD1 : tm Dq S1 = Some (mkTrans S1 DR Bq).

Definition wA (n : nat) : cconf := (Bq, (repeat S1 n, S0, [])).
Definition wM (a r : nat) : cconf :=
  (Bq, (repeat S1 r, S1, repeat S1 a)).

Lemma wchain0 : forall n1 n2 c c1 c2,
  csteps tm n1 c = Some c1 -> csteps tm n2 c1 = Some c2 ->
  csteps tm (n1 + n2) c = Some c2.
Proof. intros. rewrite csteps_add, H. assumption. Qed.

(** The eraser's leftward sweep, ending on the blank past the run. *)
Lemma cerase : forall k R,
  csteps tm (S k) (Cq, (repeat S1 k, S1, R))
    = Some (Cq, ([], S0, repeat S0 (S k) ++ R)).
Proof.
  induction k as [|k IH]; intros R.
  - cbn. rewrite HC1. reflexivity.
  - cbn [repeat].
    apply (wchain0 1 (S k) _ (Cq, (repeat S1 k, S1, S0 :: R))).
    + cbn. rewrite HC1. reflexivity.
    + rewrite IH. cbn [repeat app]. rewrite rep_snoc. reflexivity.
Qed.

(** The turn at the wall, then the whole erase sweep. *)
Lemma wce : forall r R,
  csteps tm (S r) (Bq, (repeat S1 r, S1, R))
    = Some (Cq, ([], S0, repeat S0 r ++ S1 :: R)).
Proof.
  destruct r as [|r]; intros R.
  - cbn. rewrite HB1. reflexivity.
  - cbn [repeat].
    apply (wchain0 1 (S r) _ (Cq, (repeat S1 r, S1, S1 :: R))).
    + cbn. rewrite HB1. reflexivity.
    + rewrite cerase. reflexivity.
Qed.

(** One more blank and the sweep hands over to the filler. *)
Lemma wcd : forall R,
  csteps tm 1 (Cq, ([], S0, R)) = Some (Dq, ([], S0, S0 :: R)).
Proof. intro R. cbn. rewrite HC0. reflexivity. Qed.

(** The filler's rightward sweep back over the zeros. *)
Lemma wdf : forall k L R,
  csteps tm (S k) (Dq, (L, S0, repeat S0 k ++ R))
    = Some (Dq, (repeat S1 (S k) ++ L, chd R, ctl R)).
Proof.
  induction k as [|k IH]; intros L R.
  - cbn. rewrite HD0. reflexivity.
  - cbn [repeat app].
    apply (wchain0 1 (S k) _ (Dq, (S1 :: L, S0, repeat S0 k ++ R))).
    + cbn. rewrite HD0. reflexivity.
    + rewrite IH. cbn [repeat app]. rewrite rep_snoc. reflexivity.
Qed.

(** The filler meets the wall and hands back to [Bq]. *)
Lemma wdb : forall L R,
  csteps tm 1 (Dq, (L, S1, R)) = Some (Bq, (S1 :: L, chd R, ctl R)).
Proof. intros L R. cbn. rewrite HD1. reflexivity. Qed.

(** ONE derivation, read at two values of the wall.  [a] is opaque here;
    the two customers below just instantiate it. *)
Lemma wrun : forall r X,
  csteps tm (2 * r + 5) (Bq, (repeat S1 r, S1, X))
    = Some (Bq, (repeat S1 (r + 3), chd X, ctl X)).
Proof.
  intros r X.
  replace (2 * r + 5) with (S r + (1 + (S (S r) + 1))) by lia.
  apply (wchain0 (S r) _ _ (Cq, ([], S0, repeat S0 r ++ S1 :: X))).
  { apply wce. }
  apply (wchain0 1 _ _ (Dq, ([], S0, repeat S0 (S r) ++ S1 :: X))).
  { rewrite wcd. cbn [repeat app]. reflexivity. }
  apply (wchain0 (S (S r)) _ _ (Dq, (repeat S1 (S (S r)), S1, X))).
  { rewrite (wdf (S r) [] (S1 :: X)).
    cbn [chd ctl]. rewrite app_nil_r. reflexivity. }
  rewrite wdb.
  replace (r + 3) with (S (S (S r))) by lia.
  cbn [repeat]. reflexivity.
Qed.

(** The wall gives up one cell. *)
Lemma wbounce : forall a r,
  csteps tm (2 * r + 5) (wM (S a) r) = Some (wM a (r + 3)).
Proof.
  intros a r. unfold wM. rewrite wrun. reflexivity.
Qed.

(** ...and when it is spent, the block is solid again, three cells longer. *)
Lemma wterm : forall r,
  csteps tm (2 * r + 5) (wM 0 r) = Some (wA (r + 3)).
Proof.
  intro r. unfold wM, wA. cbn [repeat]. rewrite wrun. reflexivity.
Qed.

(** [d] bounces, then the terminal. *)
Lemma wmchain : forall d r, exists n, 0 < n /\
  csteps tm n (wM d r) = Some (wA (r + 3 * d + 3)).
Proof.
  induction d as [|d IH]; intros r.
  - exists (2 * r + 5). split; [lia|].
    replace (r + 3 * 0 + 3) with (r + 3) by lia.
    apply wterm.
  - destruct (IH (r + 3)) as (n & Hn & Hrun).
    exists ((2 * r + 5) + n). split; [lia|].
    rewrite csteps_add, wbounce, Hrun.
    replace (r + 3 + 3 * d + 3) with (r + 3 * S d + 3) by lia.
    reflexivity.
Qed.

(** ** Visit witnesses inside the bounce

    [Bq] at index 0, [Cq] one step later, [Dq] once the erase sweep has
    run out.  Every board's lap passes through a [wM], so these three
    plus the fourth state's own witness in the collapse cover [glue_neverqh]'s
    obligation. *)

Lemma wvisB : forall a r, exists c,
  csteps tm 0 (wM a r) = Some c /\ fst c = Bq.
Proof. intros a r. eexists. split; reflexivity. Qed.

Lemma wvisC : forall a r, exists c,
  csteps tm 1 (wM a r) = Some c /\ fst c = Cq.
Proof.
  intros a r. unfold wM. eexists. split.
  - cbn. rewrite HB1. reflexivity.
  - reflexivity.
Qed.

Lemma wvisD : forall a r, exists c,
  csteps tm (r + 2) (wM a r) = Some c /\ fst c = Dq.
Proof.
  intros a r. unfold wM. eexists. split.
  - replace (r + 2) with (S r + 1) by lia.
    apply (wchain0 (S r) 1 _
             (Cq, ([], S0, repeat S0 r ++ S1 :: repeat S1 a))).
    + apply wce.
    + apply wcd.
  - reflexivity.
Qed.

End WallBounce.
