(** Exact quantitative certificate for current union residual index53.
    Machine 0RB---_0LC0RB_1LD1RD_1RB0LD. Three active states B/C/D;
    total nonblank count grows by at most one, while target-specific scalar
    count-plus-control-potential ranks strictly decrease on avoiding edges. *)
From Coq Require Import Arith Lia Bool List NArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import RepWL.
From BBB4.Census Require Import TNF_QH.
From BBBWait42 Require Import Spec Transport.
From BBBWait42 Require Import InvariantTimedRank.
Import ListNotations.
Definition counter : TM := fun q h =>
  match q, h with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StB)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.
Definition active (cc : cconf) := fst cc <> StA.
Definition targets (q : St) := q <> StA.
Definition ones (cc : cconf) :=
  let '(_, (l,h,r)) := cc in countnb l + zc h + countnb r.
Definition phi (q s : St) :=
  match q,s with
  | StB,StC => 2 | StC,StD => 2 | StD,StB => 1 | _,_ => 0 end.
Definition target_rank (q : St) (cc : cconf) := ones cc + phi q (fst cc).
Definition anchor : cconf := (StC, ([], S0, [S0])).
Example anchor_checked : csteps counter 2 c0 = Some anchor.
Proof. reflexivity. Qed.
Example anchor_active : active anchor.
Proof. discriminate. Qed.
Example anchor_ones : ones anchor = 0.
Proof. reflexivity. Qed.
Lemma active_step : forall cc cc',
  active cc -> cstep counter cc = Some cc' -> active cc'.
Proof.
 intros [s [[l h] r]] cc' HI Hstep.
 destruct s; unfold active in HI; simpl in HI; try contradiction;
   destruct h; cbn [cstep counter] in Hstep; injection Hstep as <-;
   unfold active; simpl; discriminate.
Qed.
Lemma active_step_defined : forall cc, active cc ->
 exists cc', cstep counter cc = Some cc'.
Proof.
 intros [s [[l h] r]] HI. destruct s; unfold active in HI; simpl in HI;
   try contradiction; destruct h; eexists; reflexivity.
Qed.
Lemma ones_move : forall s l h r dir w,
  ones (s, ctape_move dir w (l,h,r)) + zc h =
  ones (s,(l,h,r)) + zc w.
Proof.
  intros s l h r dir w.
  pose proof (countnb_hd l) as HL.
  pose proof (countnb_hd r) as HR.
  destruct dir; cbv beta iota zeta delta [ones ctape_move];
    rewrite countnb_cons; lia.
Qed.

Lemma ones_step_exact : forall tm cc cc' tr,
  tm (fst cc) (let '(_,h,_) := snd cc in h) = Some tr ->
  cstep tm cc = Some cc' ->
  ones cc' + (let '(_,h,_) := snd cc in zc h) = ones cc + zc (t_write tr).
Proof.
  intros tm [s [[l h] r]] cc' tr Htm Hstep.
  cbn [fst snd] in Htm.
  unfold cstep in Hstep. rewrite Htm in Hstep. injection Hstep as <-.
  change (ones (t_next tr, ctape_move (t_dir tr) (t_write tr) (l,h,r)) + zc h =
    ones (t_next tr,(l,h,r)) + zc (t_write tr)).
  apply ones_move.
Qed.

Lemma ones_growth : forall cc cc',
  active cc -> cstep counter cc = Some cc' -> ones cc' <= ones cc + 1.
Proof.
  intros [s [[l h] r]] cc' _ Hstep.
  unfold cstep in Hstep.
  destruct (counter s h) as [tr|] eqn:Et; [|discriminate].
  injection Hstep as <-.
  change (ones (t_next tr, ctape_move (t_dir tr) (t_write tr) (l,h,r)) <=
    ones (t_next tr,(l,h,r)) + 1).
  pose proof (ones_move (t_next tr) l h r (t_dir tr) (t_write tr)) as He.
  assert (Hw : zc (t_write tr) <= 1) by (destruct (t_write tr); cbn [zc]; lia).
  lia.
Qed.


Lemma rank_domination : forall q cc, target_rank q cc <= ones cc + 2.
Proof.
 intros q [s [[l h] r]]. destruct q,s;
   cbv beta iota zeta delta [target_rank phi fst]; lia.
Qed.
Lemma rank_avoiding_decrease : forall q cc cc',
 targets q -> active cc -> cstep counter cc = Some cc' ->
 fst cc <> q -> fst cc' <> q -> target_rank q cc' < target_rank q cc.
Proof.
 intros q [s [[l h] r]] cc' Hq HI Hstep Hs Hs'.
 unfold targets in Hq. unfold active in HI. cbn [fst] in HI,Hs.
 destruct q; try contradiction;
 destruct s; try contradiction;
 destruct h; cbn [cstep counter] in Hstep; injection Hstep as <-;
 cbn [fst] in Hs'; try contradiction;
 pose proof (countnb_hd l) as HL;
 pose proof (countnb_hd r) as HR;
 cbv beta iota zeta delta [target_rank phi ones ctape_move fst];
 repeat rewrite countnb_cons;
 cbv beta iota zeta delta [zc] in *; lia.
Qed.
Theorem counter_window : forall B, 2 <= B -> WindowBound counter B (B+1).
Proof.
 intros B HB.
 eapply (c_invariant_active_ranks_window_bound counter active targets
   target_rank ones 1 0 (fun _ => 1) (fun _ => 2) 2 anchor B (B+1)).
 - exact anchor_checked.
 - exact anchor_active.
 - exact HB.
 - exact active_step.
 - intros c Hc. exact Hc.
 - intros q Hq c c' HI Hstep Hn Hn'.
   exact (rank_avoiding_decrease q c c' Hq HI Hstep Hn Hn').
 - exact ones_growth.
 - rewrite anchor_ones. lia.
 - intros q _ c _. cbn. pose proof (rank_domination q c). lia.
 - intros q _. cbn. lia.
Qed.
Lemma active_run : forall n cc, active cc ->
 exists cc', csteps counter n cc = Some cc' /\ active cc'.
Proof.
 induction n as [|n IH]; intros cc HI.
 - exists cc. auto.
 - destruct (active_step_defined cc HI) as [cc1 Hstep].
   destruct (IH cc1 (active_step cc cc1 HI Hstep)) as [cc' [Hrun HI']].
   exists cc'. split; [cbn [csteps]; rewrite Hstep; exact Hrun|exact HI'].
Qed.
Theorem counter_nonhalt : NonHalt counter.
Proof.
 intros n Hnone.
 destruct (active_run n anchor anchor_active) as [cc [Htail _]].
 assert (Hrun : stepn counter (2+n) InitES = Some (lift cc)).
 { rewrite <- lift_c0. apply csteps_lift.
   rewrite csteps_add, anchor_checked. exact Htail. }
 replace (2+n) with (n+2) in Hrun by lia.
 rewrite stepn_add, Hnone in Hrun. discriminate.
Qed.
Theorem counter_window_all_completions : forall tm' B,
 2 <= B -> TM_le counter tm' -> WindowBound tm' B (B+1).
Proof.
 intros tm' B HB Hle.
 apply (proj2 (window_bound_completion counter tm' B (B+1) counter_nonhalt Hle)).
 apply counter_window. exact HB.
Qed.

Definition cutoff : nat := N.to_nat 32779478%N.
Definition width : nat := N.to_nat 32779479%N.
Lemma cutoff_ge_two : 2 <= cutoff.
Proof.
 unfold cutoff. change (N.to_nat 2%N <= N.to_nat 32779478%N).
 apply Nat.compare_le_iff. rewrite <- N2Nat.inj_compare.
 apply N.compare_le_iff. lia.
Qed.
Lemma width_eq : width = cutoff+1.
Proof.
 unfold width,cutoff.
 change (N.to_nat 32779479%N = N.to_nat 32779478%N + N.to_nat 1%N).
 rewrite <- N2Nat.inj_add. reflexivity.
Qed.
Local Opaque cutoff width.
Theorem counter_cutoff_window : forall tm', TM_le counter tm' ->
 WindowBound tm' cutoff width.
Proof.
 intros tm' Hle. rewrite width_eq.
 apply counter_window_all_completions; [exact cutoff_ge_two|exact Hle].
Qed.
Print Assumptions counter_cutoff_window.
