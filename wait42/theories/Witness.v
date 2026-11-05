From Coq Require Import Arith Lia Bool NArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBBWait42 Require Import Spec BinaryScan.

Definition state_hit (q : St) (c : cconf) := st_eqb (fst c) q.

Theorem first_state_hitN_lower : forall tm q B L,
  first_hitN tm (state_hit q) B L = true ->
  forall w, WaitBound (N.to_nat B) w -> N.to_nat L <= w.
Proof.
  intros tm q B L HC w HW.
  destruct (first_hitN_sound _ _ _ _ HC) as [(d&HD&Hhit) Hnone].
  assert (HQ : fst d = q) by (apply st_eqb_spec; exact Hhit).
  assert (HV : VisitsAt tm q (N.to_nat B + N.to_nat L)).
  { exists (lift d). split; [rewrite <- lift_c0; apply csteps_lift; exact HD|exact HQ]. }
  destruct (HW tm q (ex_intro _ _ (conj (Nat.le_add_r _ _) HV))) as (t&Ht&Htw&HVt).
  destruct (le_dec (N.to_nat B + N.to_nat L) t) as [Hle|Hlt]; [lia|].
  destruct (csteps_prefix tm t (N.to_nat B + N.to_nat L) c0 d) as (e&HE&_); [lia|exact HD|].
  assert (Hfalse : state_hit q e = false) by (eapply Hnone; eauto; lia).
  destruct HVt as (E&Hrun&Hstate).
  assert (Hlift : stepn tm t InitES = Some (lift e)).
  { rewrite <- lift_c0; apply csteps_lift; exact HE. }
  rewrite Hlift in Hrun; injection Hrun as <-.
  unfold state_hit in Hfalse. change (fst e = q) in Hstate.
  assert (st_eqb (fst e) q = true) by (apply st_eqb_spec; exact Hstate). congruence.
Qed.

(** 1RB0LC_1LA1LD_1RC1RB_0LC0LD *)
Definition state_wait_machine : TM := fun q a => Some
  (match q,a with
   | StA,S0 => mkTrans S1 DR StB | StA,S1 => mkTrans S0 DL StC
   | StB,S0 => mkTrans S1 DL StA | StB,S1 => mkTrans S1 DL StD
   | StC,S0 => mkTrans S1 DR StC | StC,S1 => mkTrans S1 DR StB
   | StD,S0 => mkTrans S0 DL StC | StD,S1 => mkTrans S0 DL StD
   end).
Definition wait_start : N := 32779478%N.
Definition state_wait : N := 112552385%N.

Theorem state_wait_check :
  first_hitN state_wait_machine (state_hit StA) wait_start state_wait = true.
Proof. vm_compute. reflexivity. Qed.

Theorem state_wait_lower_bound : forall w,
  WaitBound (N.to_nat wait_start) w -> N.to_nat state_wait <= w.
Proof. intros; eapply first_state_hitN_lower; [exact state_wait_check|assumption]. Qed.
